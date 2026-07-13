import telebot
import requests
import hashlib
import base64
import json
import logging
import threading
import socketio
import random
import time
import string
import math
import os

from flask import Flask
from collections import deque
from datetime import datetime, timedelta

# =========================
# FLASK KEEP ALIVE (RENDER)
# =========================
app = Flask(__name__)

@app.route("/")
def home():
    return "🤖 LC79 BOT ONLINE"

@app.route("/health")
def health():
    return {
        "status": "online",
        "bot": "LC79",
        "server": "Render"
    }

def run_web():
    port = int(os.environ.get("PORT", 10000))
    app.run(host="0.0.0.0", port=port, debug=False, use_reloader=False)
# ==========================================
# 👑 CẤU HÌNH HỆ THỐNG BOT & LOGGING
# ==========================================
logging.basicConfig(level=logging.DEBUG, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)
logging.getLogger('engineio').setLevel(logging.WARNING)
logging.getLogger('urllib3').setLevel(logging.WARNING)

BOT_TOKEN = '8791487026:AAHOo6tqwrUyKcHD4JcKb-l-_83b4joT4jE'
ADMIN_ID = 7338417401
ADMIN_USERNAME = "@phong296"
bot = telebot.TeleBot(BOT_TOKEN)

bot.set_my_commands([
    telebot.types.BotCommand("/start", "🏠 Mở menu chính hệ thống"),
    telebot.types.BotCommand("/huongdan", "📖 Bảng hướng dẫn sử dụng"),
    telebot.types.BotCommand("/nhapkey", "🔑 Nhập key kích hoạt bản quyền"),
    telebot.types.BotCommand("/thongtin", "💎 Xem thông tin tài khoản & hạn dùng"),
    telebot.types.BotCommand("/login", "🔐 Đăng nhập tài khoản game"),
    telebot.types.BotCommand("/autobet", "⚡ Bật / tắt tự động đặt cược"),
    telebot.types.BotCommand("/x2", "💸 Bật / tắt X2 cược khi thua VIP"),
    telebot.types.BotCommand("/lichsucau", "📊 Xem lịch sử cầu gần nhất"),
    telebot.types.BotCommand("/stop", "⏹️ Ngắt kết nối an toàn"),
    telebot.types.BotCommand("/taokey", "👑 [ADMIN] Tạo key bản quyền"),
    telebot.types.BotCommand("/danhsachkey", "📋 [ADMIN] Xem danh sách key còn lại"),
])

HISTORY_API_URL = "https://wtxmd52.tele68.com/v1/txmd5/lite-sessions"
API_URL_FALLBACK = "https://living-telecommunications-start-consoles.trycloudflare.com/api/txmd5"
MAX_HISTORY_STORE = 500
MIN_CONFIDENCE_AUTO_BET = 55
AUTO_BET_RUN_UNTIL_STOP = True
MAX_MARTINGALE_LEVEL = 6
MARTINGALE_MULTIPLIER = 2

active_sockets = {}
user_states = {}
valid_keys = {}
authorized_users = {}

# ============================================================
# 🧠 TOÀN BỘ 14 THUẬT TOÁN + ENSEMBLE - NHẬN DIỆN CẦU 1-1, 2-2, 2-1-2, 1-3, BỆT, 3-2
# ============================================================
FEATURE_CACHE = {}
CACHE_MAX = 10
CACHE_TTL = 1.5

def _hist_key(h):
    if not h: return "empty"
    return f"{len(h)}_{h[-1]['session']}_{h[-1]['tx']}"

def _cache_features(key, feat):
    FEATURE_CACHE[key] = {"t": time.time(), "d": feat}
    while len(FEATURE_CACHE) > CACHE_MAX:
        FEATURE_CACHE.pop(next(iter(FEATURE_CACHE)))

def _get_cache(key):
    c = FEATURE_CACHE.get(key)
    return c["d"] if c and time.time()-c["t"] < CACHE_TTL else None

def parse_lines(data):
    if not data or not isinstance(data.get("list"), list): return []
    arr = sorted(data["list"], key=lambda x: x["id"])
    out = []
    for it in arr:
        p = it.get("point", sum(it.get("dices",[0,0,0])))
        r = it.get("resultTruyenThong")
        if r in ("TAI","XIU"):
            out.append({"session":it["id"],"dice":it["dices"],"total":p,"result":r,"tx":"T" if p>=11 else "X"})
    return out

def _entropy(arr):
    if not arr: return 0.0
    f={}; n=len(arr)
    for v in arr: f[v]=f.get(v,0)+1
    return -sum((c/n)*math.log2(c/n) for c in f.values() if c>0)

def _similarity(a,b):
    if len(a)!=len(b) or not a: return 0
    return sum(1 for x,y in zip(a,b) if x==y)/len(a)

def extract_features(history):
    if not history:
        return {"tx":[],"totals":[],"freq":{},"runs":[],"maxRun":0,"meanTotal":0,"stdTotal":0,
                "entropy":0,"last3":"","last5":"","last8":"","trends":{"up":0,"down":0},
                "lastRun":None,"prevRun":None,"runLengths":[],"avgRun":0,"stdRun":0,
                "tRatio":0,"xRatio":0,"is11":False,"isLong":False,"runDev":0}
    key = _hist_key(history)
    c = _get_cache(key)
    if c: return c
    tx = [h["tx"] for h in history]
    totals = [h["total"] for h in history]
    freq = {}
    for v in tx: freq[v]=freq.get(v,0)+1
    runs=[]
    cur=tx[0]; ln=1
    for v in tx[1:]:
        if v==cur: ln+=1
        else: runs.append({"val":cur,"len":ln}); cur=v; ln=1
    runs.append({"val":cur,"len":ln})
    mean_t = sum(totals)/len(totals)
    var = sum((x-mean_t)**2 for x in totals)/len(totals)
    l10=tx[-10:]; l10t=totals[-10:]
    up=sum(1 for i in range(1,len(l10t)) if l10t[i]>l10t[i-1])
    dn=sum(1 for i in range(1,len(l10t)) if l10t[i]<l10t[i-1])
    rl = [r["len"] for r in runs]
    avg_r = sum(rl)/len(rl) if rl else 0
    std_r = math.sqrt(sum((x-avg_r)**2 for x in rl)/len(rl)) if rl and avg_r else 0
    n=len(tx)
    feat = {
        "tx":tx,"totals":totals,"freq":freq,"runs":runs,
        "maxRun":max(rl) if rl else 0,
        "meanTotal":mean_t,"stdTotal":math.sqrt(var),
        "entropy":_entropy(tx),
        "last3":"".join(tx[-3:]),"last5":"".join(tx[-5:]),"last8":"".join(tx[-8:]),
        "trends":{"up":up,"down":dn},
        "lastRun":runs[-1] if runs else None,
        "prevRun":runs[-2] if len(runs)>=2 else None,
        "runLengths":rl,"avgRun":avg_r,"stdRun":std_r,
        "tRatio":freq.get("T",0)/n,"xRatio":freq.get("X",0)/n,
        "is11":len(runs)>=4 and all(l==1 for l in rl[-4:]),
        "isLong":runs[-1]["len"]>=4 if runs else False,
        "runDev":((runs[-1]["len"]-avg_r)/std_r) if runs and std_r>0 else 0
    }
    _cache_features(key,feat)
    return feat

# ========== NHẬN DIỆN CẦU 1-1, 2-2, 2-1-2, 1-3, BỆT, 3-2 ==========
PATTERN_LIB = [
    ([1,1,1,1,1,1],"1_1"),
    ([2,2,2,2],"2_2"),
    ([2,1,2,1,2],"2_1_2"),
    ([1,3,1,3,1],"1_3_1"),
    ([3,2,3,2,3],"3_2_3"),
    ([3,3,3],"3_3"),
    ([4,2,4,2,4],"4_2_4"),
    ([2,2,1,2,2],"2_2_1"),
]

def detect_pattern(runs):
    if not runs or len(runs)<3: return None
    lr = runs[-6:]
    lens = [r["len"] for r in lr]
    vals = [r["val"] for r in lr]
    alt = all(i==0 or vals[i]!=vals[i-1] for i in range(len(vals)))
    
    for pat, name in PATTERN_LIB:
        if len(lens) >= len(pat) and lens[-len(pat):] == pat and alt:
            return f"{name}_pattern"
    
    if lr[-1]["len"] >= 5:
        return "long_run_pattern"
    
    return "random_pattern"

def predict_by_pattern(pt, runs, last):
    if not pt or not runs: return None
    lr = runs[-1]
    
    # Cầu 1-1: đảo ngược
    if pt == "1_1_pattern":
        return "X" if last == "T" else "T"
    
    # Cầu 2-2: nếu run cuối =2 → đảo, ngược lại giữ
    if pt == "2_2_pattern":
        return ("X" if lr["val"] == "T" else "T") if lr["len"] == 2 else lr["val"]
    
    # Cầu 2-1-2
    if pt == "2_1_2_pattern":
        if lr["len"] == 2: return "X" if lr["val"] == "T" else "T"
        if lr["len"] == 1: return lr["val"]
    
    # Cầu 1-3-1 (1-3)
    if pt == "1_3_1_pattern":
        if lr["len"] == 1: return "X" if lr["val"] == "T" else "T"
        if lr["len"] == 3: return lr["val"]
    
    # Cầu 3-2-3 (3-2)
    if pt == "3_2_3_pattern":
        if lr["len"] == 3: return "X" if lr["val"] == "T" else "T"
        if lr["len"] == 2: return lr["val"]
    
    if pt in ("3_3_pattern", "4_2_4_pattern"):
        a = 3 if pt == "3_3_pattern" else 4
        if lr["len"] == a: return "X" if lr["val"] == "T" else "T"
        if lr["len"] == 2: return lr["val"]
    
    # Bệt dài
    if pt == "long_run_pattern":
        if lr["len"] > 7: return "X" if lr["val"] == "T" else "T"
        if 4 <= lr["len"] <= 7: return lr["val"]
    
    return None

# ========== 14 THUẬT TOÁN ==========
def a5_freq(h):
    if len(h)<20: return None
    f=extract_features(h); e=f["entropy"]
    t=f["freq"].get("T",0); x=f["freq"].get("X",0); tot=t+x
    thr = 0.45 if e>0.9 else (0.65 if e<0.4 else 0.55)
    r30=h[-30:]; rt=sum(1 for x in r30 if x["tx"]=="T"); rx=len(r30)-rt
    lt=abs(t-x)/tot if tot else 0; st=abs(rt-rx)/len(r30) if r30 else 0
    cb = lt*0.4+st*0.6
    if cb>thr:
        if rt>rx+2: return "X"
        if rx>rt+2: return "T"
    return None

def aA_markov(h):
    if len(h)<15: return None
    tx=[x["tx"] for x in h]
    mx=4 if len(h)>=30 else (3 if len(h)>=20 else 2)
    bp=None; bs=-1
    for o in range(2,mx+1):
        if len(tx)<o+8: continue
        tr={}; n=len(tx)-o
        for i in range(n):
            k="".join(tx[i:i+o]); nx=tx[i+o]
            w=0.95**(n-i-1)
            tr.setdefault(k,{"T":0,"X":0})[nx]+=w
        lk="".join(tx[-o:]); c=tr.get(lk)
        if c and c["T"]+c["X"]>0.5:
            sm=c["T"]+c["X"]; conf=abs(c["T"]-c["X"])/sm
            sc=conf*(o/mx)*(min(1,sm/10))
            if sc>bs: bs=sc; bp="T" if c["T"]>c["X"] else "X"
    return bp

def aB_ngram(h):
    if len(h)<30: return None
    tx=[x["tx"] for x in h]
    sz=[3,2]
    if len(h)>=40: sz.append(4)
    if len(h)>=50: sz+=[5,6]
    bp=None; bc=0
    for n in sz:
        if len(tx)<n*2: continue
        tgt="".join(tx[-n:]); mt=[]
        for i in range(len(tx)-n):
            if "".join(tx[i:i+n])==tgt:
                mt.append({"next":tx[i+n],"d":len(tx)-i})
        if len(mt)>=2:
            wt={"T":0,"X":0}; sw=0
            for m in mt: w=1/(m["d"]*0.5+1); wt[m["next"]]+=w; sw+=w
            if sw>0:
                tr=abs(wt["T"]-wt["X"])/sw
                if tr>bc: bc=tr; bp="T" if wt["T"]>wt["X"] else "X"
    return bp if bc>0.3 else None

def aS_neo(h):
    if len(h)<25: return None
    f=extract_features(h); pt=detect_pattern(f["runs"])
    if not pt or pt=="random_pattern": return None
    p=predict_by_pattern(pt,f["runs"],f["tx"][-1])
    if p and f["runs"]:
        rr=f["runs"][-8:]
        if sum(1 for r in rr if r["len"]>=2)/max(1,len(rr))>0.6: return p
    return None

def aF_deep(h):
    if len(h)<60: return None
    tf=[(10,0.3),(30,0.4),(60,0.3)]; sc={"T":0,"X":0}; sw=0
    for lb,w in tf:
        if len(h)<lb: continue
        sl=h[-lb:]; stx=[x["tx"] for x in sl]; stt=[x["total"] for x in sl]
        t=stx.count("T"); x=len(stx)-t; mt=sum(stt)/len(stt); vol=math.sqrt(sum((v-mt)**2 for v in stt)/len(stt))
        ts=xs=0
        if mt>12: xs+=0.4
        if mt<9: ts+=0.4
        if t>x+3: xs+=0.3
        if x>t+3: ts+=0.3
        if vol>4:
            if stx[-1]=="T": ts+=0.2
            else: xs+=0.2
        td=stt[-1]-stt[0]
        if td>3: xs+=0.1
        if td<-3: ts+=0.1
        ww=w*(len(stx)/lb)
        sc["T"]+=ts*ww; sc["X"]+=xs*ww; sw+=ww
    if sw>0 and abs(sc["T"]-sc["X"])/sw>0.15:
        return "T" if sc["T"]>sc["X"] else "X"
    return None

def aE_trans(h):
    if len(h)<100: return None
    tx=[x["tx"] for x in h]; at={"T":0,"X":0}
    for L in (6,8,10,12):
        if len(tx)<L*2: continue
        tgt=tx[-L:]; nm=0
        for i in range(len(tx)-L):
            s=_similarity(tx[i:i+L],tgt)
            if s>=0.7:
                w=s*(1/(len(tx)-i))*(L/12); at[tx[i+L]]+=w; nm+=1
        if nm>=3: bf=min(1.5,nm/2); at["T"]*=bf; at["X"]*=bf
    tot=at["T"]+at["X"]
    if tot>0.2 and abs(at["T"]-at["X"])/tot>0.25:
        return "T" if at["T"]>at["X"] else "X"
    return None

def aG_bridge(h):
    f=extract_features(h); r=f["runs"]
    if len(r)<4: return None
    lr=r[-1]
    p=None; cf=0
    if lr["len"]>=5:
        if lr["len"]>=8: p="X" if lr["val"]=="T" else "T"; cf=0.8
        elif 5<=lr["len"]<=7:
            ar=f["avgRun"]
            if lr["len"]>ar*1.8: p="X" if lr["val"]=="T" else "T"; cf=0.65
            else: p=lr["val"]; cf=0.6
    if not p and len(r)>=5:
        L=[x["len"] for x in r[-5:]]
        if L[:3]==[1,1,3] and lr["len"]>=3: p="X" if lr["val"]=="T" else "T"; cf=0.7
        if len(L)>=4 and L[:4]==[2,3,2,3]: p=lr["val"]; cf=0.6
    if not p and len(r)>=8 and f["stdRun"]>0:
        rl=[x["len"] for x in r[-8:]]; ml=sum(rl)/len(rl); sl=math.sqrt(sum((x-ml)**2 for x in rl)/len(rl))
        if lr["len"]>ml+sl*1.5: p="X" if lr["val"]=="T" else "T"; cf=0.6
    return p if cf>0.55 else None

def aH_adapt(h):
    if len(h)<25: return None
    tx=[x["tx"] for x in h]; vt={"T":0,"X":0}
    for o in (2,3,4):
        if len(tx)<o+5: continue
        tr={}
        for i in range(len(tx)-o):
            k="".join(tx[i:i+o]); tr.setdefault(k,{"T":0,"X":0})[tx[i+o]]+=1
        c=tr.get("".join(tx[-o:]))
        if c and c["T"]+c["X"]>=2:
            pr="T" if c["T"]>c["X"] else "X"
            vt[pr]+=abs(c["T"]-c["X"])/(c["T"]+c["X"])*(o/10)
    for lb in (10,20,30):
        if len(tx)<lb: continue
        rc=tx[-lb:]; t=rc.count("T"); x=lb-t
        if abs(t-x)>lb*0.2:
            pr="X" if t>x else "T"
            vt[pr]+=abs(t-x)/lb*0.5
    for w in (5,10,15):
        if len(tx)<w*2: continue
        a=tx[-2*w:-w]; b=tx[-w:]
        mt=b.count("T")-a.count("T"); mx=b.count("X")-a.count("X")
        if abs(mt-mx)>w*0.3:
            pr="T" if mt>mx else "X"
            vt[pr]+=abs(mt-mx)/w*0.3
    return "T" if vt["T"]>vt["X"] else "X" if sum(vt.values())>0.3 else None

def aI_master(h):
    if len(h)<35: return None
    f=extract_features(h); r=f["runs"]; tx=f["tx"]
    if len(r)<5: return None
    rr=r[-8:]; rl=[x["len"] for x in rr]; rv=[x["val"] for x in rr]
    ps={"T":0,"X":0}; rp="".join(map(str,rl)); vp="".join(rv)
    LIB=[("12121",0.7),("21212",0.7),("13131",0.6),("31313",0.6),("24242",0.65),("42424",0.65)]
    for pat,w in LIB:
        if pat in rp:
            pr = "X" if vp[-1]=="T" else "T" if pat in ("12121","31313","24242") else vp[-1]
            ps[pr]+=w
    TXP=[("TXTXTXTX","X",0.8),("XTXTXTXT","T",0.8),("TTXXTTXX","X",0.7),("XXTTXXTT","T",0.7),
         ("TTTXXXTT","T",0.75),("XXXTTTXX","X",0.75),("TTXTTXTT","X",0.7),("XXTXXTXX","T",0.7)]
    l10="".join(tx[-10:])
    for pat,pr,w in TXP:
        if pat in l10: ps[pr]+=w
    if rr:
        lr=rr[-1]; ar=sum(rl)/len(rl) if rl else 0
        if ar>0 and lr["len"]>ar*1.8: ps["X" if lr["val"]=="T" else "T"]+=0.5
        elif ar>0 and lr["len"]<ar*0.6: ps[lr["val"]]+=0.4
    tot=ps["T"]+ps["X"]
    if tot>0 and abs(ps["T"]-ps["X"])/tot>0.3:
        return "T" if ps["T"]>ps["X"] else "X"
    return None

def aJ_entropy(h):
    if len(h)<40: return None
    f=extract_features(h); e=f["entropy"]; tx=f["tx"]; r=f["runs"]
    ep={"T":0,"X":0}
    for W in (10,20,30):
        if len(tx)<W: continue
        w=tx[-W:]; we=_entropy(w)
        if we<0.3: ep[w[-1]]+=0.6
        elif we>0.9:
            t=w.count("T"); x=W-t
            if t>x: ep["X"]+=0.5
            elif x>t: ep["T"]+=0.5
        elif len(r)>=4:
            rr=r[-4:]
            if max(x["len"] for x in rr)-min(x["len"] for x in rr)<=2: ep[tx[-1]]+=0.4
    if e<0.4: ep[tx[-1]]+=0.3
    elif e>0.95:
        t=tx[-20:].count("T"); x=20-t
        if t>x: ep["X"]+=0.4
        elif x>t: ep["T"]+=0.4
    return "T" if ep["T"]>ep["X"] else "X" if sum(ep.values())>0.4 else None

def aK_11ultra(h):
    if len(h)<8: return None
    f=extract_features(h); r=f["runs"][-12:]
    if len(r)<4 or not all(x["len"]==1 for x in r): return None
    if not all(i==0 or r[i]["val"]!=r[i-1]["val"] for i in range(len(r))): return None
    n=len(r); b=1.0
    if n>=4: b=1.8
    if n>=6: b=2.2
    if n>=8: b=2.6
    if n>=10: b=max(1.3,2.6-(n-10)*0.15)
    aK_11ultra._b=b
    return "X" if f["tx"][-1]=="T" else "T"
aK_11ultra._b=1.0

def aL_dragon(h):
    if len(h)<15: return None
    f=extract_features(h); lr=f["lastRun"]
    if not lr or lr["len"]<4: return None
    z=(lr["len"]-f["avgRun"])/f["stdRun"] if f["stdRun"]>0 else 0
    w=1.0; p=lr["val"]
    MAP={4:1.2,5:1.5,6:1.8,7:2.0,8:1.6,9:1.25}
    if lr["len"] in MAP: w=MAP[lr["len"]]
    if lr["len"]>=8: p="X" if lr["val"]=="T" else "T"
    if lr["len"]>9: w=max(0.7,1.25-(lr["len"]-9)*0.15); p="X" if lr["val"]=="T" else "T"
    if z>2.2: w*=0.85; p="X" if lr["val"]=="T" else "T"
    if z<0.8 and lr["len"]<=6: w*=1.15
    aL_dragon._b=w
    return p
aL_dragon._b=1.0

def aM_fast(h):
    if len(h)<12: return None
    f=extract_features(h); r=f["runs"]
    if len(r)<4: return None
    lr,pr,ppr=r[-1],r[-2],r[-3]
    p=None; w=1.0
    if len(r)>=4 and all(x["len"]==2 for x in r[-4:]):
        p=("X" if lr["val"]=="T" else "T") if lr["len"]==2 else lr["val"]
        w=1.9 if lr["len"]==2 else 1.4
    pat=[ppr["len"],pr["len"],lr["len"]]
    if pat==[2,1,2] or pat==[1,2,1]:
        p=("X" if lr["val"]=="T" else "T") if lr["len"]==1 else lr["val"]; w=1.7
    if lr["len"]==1 and pr["len"]==1 and ppr["len"]==1:
        p="X" if f["tx"][-1]=="T" else "T"; w=1.5
    aM_fast._b=w
    return p
aM_fast._b=1.0

def aN_safe(h):
    if len(h)<20: return None
    f=extract_features(h); tx=f["tx"]
    rt20=sum(1 for v in tx[-20:] if v=="T")/20; rx20=1-rt20
    p=None; w=1.0
    if f["entropy"]<0.55 and abs(rt20-rx20)>=0.35:
        p="X" if rt20>rx20 else "T"; w=1.3+min(0.6,abs(rt20-rx20))
    lr=f["lastRun"]
    if lr and 5<=lr["len"]<=7 and f["entropy"]<0.5: p=lr["val"]; w=1.4
    aN_safe._b=w
    return p
aN_safe._b=1.0

ALL_ALGS=[
    ("a5_freq",a5_freq,1.0,False),("aA_markov",aA_markov,1.15,False),
    ("aB_ngram",aB_ngram,1.1,False),("aS_neo",aS_neo,1.25,False),
    ("aF_deep",aF_deep,1.2,False),("aE_trans",aE_trans,1.3,False),
    ("aG_bridge",aG_bridge,1.2,False),("aH_adapt",aH_adapt,1.1,False),
    ("aI_master",aI_master,1.25,False),("aJ_entropy",aJ_entropy,1.15,False),
    ("aK_11",aK_11ultra,1.0,True),("aL_dragon",aL_dragon,1.0,True),
    ("aM_fast",aM_fast,1.0,True),("aN_safe",aN_safe,1.0,True)
]

PAT_WEIGHT={
    "1_1_pattern":{"b":2.4,"cap":2.7,"dc":10},
    "2_2_pattern":{"b":2.0,"cap":2.4,"dc":8},
    "2_1_2_pattern":{"b":1.9,"cap":2.25,"dc":7},
    "1_3_1_pattern":{"b":1.85,"cap":2.2,"dc":7},
    "3_2_3_pattern":{"b":1.8,"cap":2.15,"dc":5},
    "3_3_pattern":{"b":1.85,"cap":2.2,"dc":6},
    "4_2_4_pattern":{"b":1.7,"cap":2.0,"dc":5},
    "long_run_pattern":{"b":1.6,"cap":2.3,"dc":7},
    "random_pattern":{"b":1.0,"cap":1.2,"dc":0}
}

BEST_FOR={
    "1_1_pattern":["aK_11","aS_neo","aI_master","aM_fast"],
    "2_2_pattern":["aM_fast","aI_master","aS_neo"],
    "2_1_2_pattern":["aM_fast","aS_neo"],
    "1_3_1_pattern":["aS_neo","aI_master"],
    "3_2_3_pattern":["aS_neo","aG_bridge"],
    "long_run_pattern":["aL_dragon","aG_bridge","aJ_entropy","aN_safe"],
    "random_pattern":["aA_markov","aB_ngram","aF_deep","aH_adapt","aE_trans"]
}

class SEIU:
    def __init__(self):
        self.w={n:bw for n,_,bw,_ in ALL_ALGS}
        s=sum(self.w.values())
        self.w={k:v/s for k,v in self.w.items()}
        self.ph={n:deque(maxlen=80) for n,_,_,_ in ALL_ALGS}
        self.pm={}
        self.mn=0.02; self.mx=2.8
        
    def update(self,hist,real):
        if len(hist)<10: return
        f=extract_features(hist); pt=detect_pattern(f["runs"]) or "random_pattern"
        rl=f["lastRun"]["len"] if f["lastRun"] else 0
        for n,fn,bw,dyn in ALL_ALGS:
            try:
                pr=fn(hist); ok=1 if pr==real else 0
                self.ph[n].append(ok)
                ph=list(self.ph[n])
                r25=ph[-25:]; wa=ws=0
                for i,v in enumerate(r25):
                    k=0.92**(len(r25)-i-1); wa+=v*k; ws+=k
                a25=wa/ws if ws else 0.5; aa=sum(ph)/len(ph) if ph else 0.5
                acc=a25*0.7+aa*0.3
                pb=0.18 if n in BEST_FOR.get(pt,[]) else 0
                kk=f"{n}_{pt}"; ps=self.pm.get(kk,0)
                if ps>5: pb+=0.12
                elif ps>2: pb+=0.06
                db=getattr(fn,"_b",1.0) if dyn else 1.0
                al=0.18 if rl<=2 else (0.04 if rl>=5 else 0.06)
                tgt=max(self.mn,min(self.mx,(acc+0.15)*bw*db+pb))
                nw=al*tgt+(1-al)*self.w[n]
                pc=PAT_WEIGHT[pt]
                if pc["dc"] and rl>pc["dc"]: nw*=max(0.55,1-(rl-pc["dc"])*0.08)
                nw=max(self.mn,min(pc["cap"],nw))
                if len(r25)==3 and sum(r25)==0: nw*=0.72
                self.w[n]=nw
                if ok: self.pm[kk]=ps+1
            except Exception: self.w[n]=max(self.mn,self.w[n]*0.9)
        s=sum(self.w.values())
        if s>0: self.w={k:v/s for k,v in self.w.items()}
        
    def predict(self,hist):
        if len(hist)<12: return {"pred":"TAI","conf":0.5,"pt":"n/a","vt":{"T":0,"X":0},"n":0}
        f=extract_features(hist); pt=detect_pattern(f["runs"]) or "random_pattern"
        pc=PAT_WEIGHT[pt]; rl=f["lastRun"]["len"] if f["lastRun"] else 0
        vt={"T":0,"X":0}; det=[]
        for n,fn,bw,dyn in ALL_ALGS:
            try:
                pr=fn(hist)
                if not pr: continue
                w=self.w[n]*pc["b"]
                if n in BEST_FOR.get(pt,[]): w*=1.22
                if dyn: w*=getattr(fn,"_b",1.0)
                w=min(self.mx,w); vt[pr]+=w; det.append((n,pr,round(w,4)))
            except Exception: pass
        if vt["T"]==0 and vt["X"]==0:
            fb=a5_freq(hist)
            if fb is None:
                fb = "X" if f["tx"][-1] == "T" else "T"
            return {"pred":"TAI" if fb=="T" else "XIU","conf":0.52,"pt":pt,"vt":vt,"n":0}
        best="T" if vt["T"]>vt["X"] else "X"
        tot=vt["T"]+vt["X"]; base=max(vt["T"],vt["X"])/tot
        tn=sum(1 for _,p,_ in det if p=="T"); xn=len(det)-tn; an=len(det)
        con=0
        if an>0:
            r=max(tn,xn)/an
            con=0.18 if r>=0.9 else (0.13 if r>=0.8 else (0.07 if r>=0.7 else 0))
        sf=0
        if pt=="long_run_pattern" and rl>=8: sf-=0.08
        if pt=="1_1_pattern" and rl>=10: sf-=0.05
        if f["entropy"]>0.92: sf-=0.06
        conf=min(0.97,max(0.52,base+con+sf))
        return {"pred":"TAI" if best=="T" else "XIU","conf":round(conf,4),"pt":pt,
                "vt":{"T":round(vt["T"],3),"X":round(vt["X"],3)},"n":an}

AI = SEIU()

# ==========================================
# 🛡️ HỆ THỐNG CHÍNH
# ==========================================
def init_user_state(chat_id):
    if chat_id not in user_states:
        user_states[chat_id] = {
            "raw_hist":[],"history":[],"points_history":[],
            "auto_bet_enabled":False,"bet_amount":10000,
            "base_bet":10000,
            "martingale_enabled":False,
            "martingale_level":0,
            "current_prediction":None,"waiting_for_result":False,
            "has_bet_this_session":False,"session_id":None,"balance":0,
            "win_streak":0,"lose_streak":0,"total_win":0,"total_lose":0
        }

def fetch_history_from_api(limit=60):
    for url in (HISTORY_API_URL, API_URL_FALLBACK):
        try:
            r=requests.get(url,headers={"User-Agent":"Mozilla/5.0","Origin":"https://lc79b.bet"},timeout=10)
            if r.status_code!=200: continue
            d=r.json(); arr=parse_lines(d)
            if arr: return arr[-limit:]
        except Exception: continue
    return []

def check_auth(chat_id):
    if chat_id==ADMIN_ID: return True
    if chat_id in authorized_users:
        if time.time()<=authorized_users[chat_id]: return True
        else: del authorized_users[chat_id]
    return False

def require_auth(fn):
    def wr(m,*a,**kw):
        if not check_auth(m.chat.id):
            bot.reply_to(m,f"""╔════════════════════════╗
║   🔒 CHƯA KÍCH HOẠT VIP   ║
╠════════════════════════╣
║ /nhapkey MÃ_KEY         ║
║ 📩 {ADMIN_USERNAME}      ║
╚════════════════════════╝""",parse_mode="HTML")
            return
        return fn(m,*a,**kw)
    return wr

def format_expire_time(ts):
    r=ts-time.time()
    if r<=0: return "❌ HẾT HẠN"
    d=int(r//86400); h=int((r%86400)//3600); m=int((r%3600)//60)
    if d>0: return f"✅ CÒN {d} NGÀY {h}G {m}P"
    return f"✅ CÒN {h}G {m}P"

def make_prediction_vip(history, points=None, cid=None):
    if cid and cid in user_states and user_states[cid]["raw_hist"]:
        return AI.predict(user_states[cid]["raw_hist"])["pred"]
    return random.choice(["TAI","XIU"])

def tinh_do_tin_cay(history, points=None, cid=None):
    if cid and cid in user_states and user_states[cid]["raw_hist"]:
        return int(AI.predict(user_states[cid]["raw_hist"])["conf"]*100)
    return 50

def tinh_tien_cuoc(cid):
    st=user_states[cid]
    if not st["martingale_enabled"]: return st["bet_amount"]
    lv=st["martingale_level"]
    if lv<=0: return st["base_bet"]
    return min(st["base_bet"]*(MARTINGALE_MULTIPLIER**lv), st["base_bet"]*(MARTINGALE_MULTIPLIER**MAX_MARTINGALE_LEVEL))

def ai_tu_hoc(cid, du_doan, thuc_te):
    st=user_states[cid]; raw=st["raw_hist"]
    if len(raw)>=2: AI.update(raw[:-1], "T" if thuc_te=="TAI" else "X")
    if du_doan==thuc_te:
        st["win_streak"]+=1; st["lose_streak"]=0; st["total_win"]+=1
        st["martingale_level"]=0
    else:
        st["lose_streak"]+=1; st["win_streak"]=0; st["total_lose"]+=1
        if st["martingale_enabled"] and st["martingale_level"]<MAX_MARTINGALE_LEVEL:
            st["martingale_level"]+=1

# ==========================================
# 🌐 LOGIN + SOCKET
# ==========================================
def md5_hash(t): return hashlib.md5(t.encode()).hexdigest()

def login_and_get_token(u,p):
    try:
        r=requests.get(f"https://apifo88daigia.tele68.com/api?c=3&un={u}&pw={md5_hash(p)}&cp=R&cl=R&pf=web&at=",timeout=12).json()
        if not r.get("success"): return {"_error":"Sai TK/MK"}
        sk=r["sessionKey"]+"="*((4-len(r["sessionKey"])%4)%4)
        nn=json.loads(base64.b64decode(sk)).get("nickname")
        r2=requests.post("https://wlb.tele68.com/v1/lobby/auth/login?cp=R&cl=R&pf=web&at=",
            json={"nickName":nn,"accessToken":r["accessToken"]},timeout=12).json()
        if not r2.get("token"): return {"_error":"Không nhận token"}
        return {"token":r2["token"],"nickname":nn,"money":r2.get("remoteLoginResp",{}).get("money",0)}
    except Exception as e: return {"_error":str(e)}

def start_websocket(cid,token):
    if cid in active_sockets:
        try: active_sockets[cid].disconnect()
        except Exception: pass
    sio=socketio.Client(reconnection=True,reconnection_attempts=99999,reconnection_delay=3,logger=False,engineio_logger=False)
    active_sockets[cid]=sio
    init_user_state(cid)
    
    @sio.event(namespace='/txmd5')
    def connect():
        arr=fetch_history_from_api(60)
        st=user_states[cid]
        if arr:
            st["raw_hist"]=arr; st["history"]=[x["result"] for x in arr]; st["points_history"]=[x["total"] for x in arr]
            bot.send_message(cid,f"""╔════════════════════════╗
║     🟢 KẾT NỐI VIP OK     ║
╠════════════════════════╣
║ 📥 TẢI {len(arr):>3} PHIÊN API ✅ ║
║ 🧠 14 THUẬT TOÁN SẴN SÀNG ║
╚════════════════════════╝""",parse_mode="HTML")
        else:
            bot.send_message(cid,"🟢 Kết nối OK, đang thu thập dữ liệu",parse_mode="HTML")
    
    @sio.on('new-session',namespace='/txmd5')
    def new_sess(d):
        st=user_states[cid]; st["session_id"]=d.get("id"); st["has_bet_this_session"]=False
        res=AI.predict(st["raw_hist"]) if st["raw_hist"] else None
        if res:
            st["current_prediction"]=res["pred"]; dt=int(res["conf"]*100)
            tien=tinh_tien_cuoc(cid)
            x2_st=f"💸 X2: {'🟢 BẬT C'+str(st['martingale_level']) if st['martingale_enabled'] else '🔴 TẮT'}"
            bot.send_message(cid,f"""╔════════════════════════╗
║    💎 PHIÊN MỚI VIP      ║
╠════════════════════════╣
║ 🎯 #{st['session_id']}
║ 🤖 <b>{res['pred']}</b>
║ 📈 ĐỘ TIN: <b>{dt}%</b>
║ 🧠 LOẠI CẦU: {res['pt']}
║ ⚖️ T={res['vt']['T']} X={res['vt']['X']}
║ 🧮 {res['n']} THUẬT TOÁN
║ 💰 CƯỢC: <b>{tien:,}</b>
║ {x2_st}
╚════════════════════════╝""",parse_mode="HTML")
    
    @sio.on('tick-update',namespace='/txmd5')
    def tk(d):
        st=user_states[cid]
        if d.get("state")=="BETTING" and st["auto_bet_enabled"] and st["current_prediction"] and AUTO_BET_RUN_UNTIL_STOP:
            dt=tinh_do_tin_cay([],cid=cid)
            if not st["has_bet_this_session"] and dt>=MIN_CONFIDENCE_AUTO_BET:
                tien=tinh_tien_cuoc(cid)
                sio.emit("bet",{"type":st["current_prediction"],"amount":tien},namespace="/txmd5")
                st["has_bet_this_session"]=True
                bot.send_message(cid,f"🚀 ĐÃ ĐẶT {st['current_prediction']} | {tien:,}",parse_mode="HTML")
    
    @sio.on('bet-result',namespace='/txmd5')
    def br(d):
        st=user_states[cid]
        if "postBalance" in d: st["balance"]=d["postBalance"]
    
    @sio.on('session-result',namespace='/txmd5')
    def sr(d):
        res=d.get("resultTruyenThong"); st=user_states[cid]
        if res in ("TAI","XIU"):
            rec={"session":d.get("id"),"dice":d["dices"],"total":sum(d["dices"]),"result":res,"tx":"T" if sum(d["dices"])>=11 else "X"}
            st["raw_hist"].append(rec); st["history"].append(res); st["points_history"].append(rec["total"])
            if len(st["raw_hist"])>MAX_HISTORY_STORE: st["raw_hist"].pop(0); st["history"].pop(0); st["points_history"].pop(0)
            ai_tu_hoc(cid,st["current_prediction"],res)
            tt="🟢 THẮNG" if st["current_prediction"]==res else "🔴 THUA"
            bot.send_message(cid,f"🎲 KQ: {res} → {tt}\nSL THUA LIÊN: {st['lose_streak']} | CẤP X2: {st['martingale_level']}",parse_mode="HTML")
    
    try:
        sio.connect("https://wtxmd52.tele68.com",socketio_path="txmd5/",namespaces=["/txmd5"],
            transports=["websocket"],auth={"token":token},
            headers={"User-Agent":"Mozilla/5.0","Origin":"https://lc79b.bet"})
        sio.wait()
    except Exception as e: bot.send_message(cid,f"⚠️ Lỗi WS: {e}")

# ==========================================
# 🎨 MENU VIP
# ==========================================
def vip_menu():
    kb=telebot.types.InlineKeyboardMarkup(row_width=2)
    kb.add(
        telebot.types.InlineKeyboardButton("🔐 ĐĂNG NHẬP",callback_data="login"),
        telebot.types.InlineKeyboardButton("⚡ AUTO BET",callback_data="auto"),
        telebot.types.InlineKeyboardButton("💸 X2 KHI THUA",callback_data="x2"),
        telebot.types.InlineKeyboardButton("📊 LỊCH SỬ",callback_data="ls"),
        telebot.types.InlineKeyboardButton("💎 THÔNG TIN",callback_data="tt"),
        telebot.types.InlineKeyboardButton("⏹️ DỪNG",callback_data="stop")
    )
    return kb

@bot.message_handler(commands=['start'])
def cmd_start(m):
    cid=m.chat.id; init_user_state(cid)
    if check_auth(cid):
        han="👑 QUẢN TRỊ VIÊN VĨNH VIỄN" if cid==ADMIN_ID else format_expire_time(authorized_users[cid])
        bot.send_message(cid,f"""╔════════════════════════╗
║    💎 CHÀO MỪNG VIP     ║
║     ✨ ANH PHONG ✨        ║
╠════════════════════════╣
║ ✅ BẢN QUYỀN ĐÃ KÍCH HOẠT
║ ⏳ {han}
╠════════════════════════╣
║ CHỌN CHỨC NĂNG DƯỚI ⤵️
╚════════════════════════╝""",parse_mode="HTML",reply_markup=vip_menu())
    else:
        bot.send_message(cid,f"""╔════════════════════════╗
║   🏠 TRANG CHỦ VIP      ║
╠════════════════════════╣
║ 🔒 CHƯA KÍCH HOẠT BẢN QUYỀN
║ 🔑 /nhapkey MÃ_KEY
║ 📩 {ADMIN_USERNAME}
╚════════════════════════╝""",parse_mode="HTML")

@bot.callback_query_handler(func=lambda c:True)
def cb(c):
    cid=c.message.chat.id
    if c.data=="login": bot.send_message(cid,"✅ Gõ: /login TAIKHOAN MATKHAU")
    elif c.data=="auto": bot.send_message(cid,"✅ Bật: /autobet on 10000\n❌ Tắt: /autobet off")
    elif c.data=="x2": bot.send_message(cid,"💸 Bật X2: /x2 on\n❌ Tắt: /x2 off\n👉 Tối đa 6 cấp an toàn")
    elif c.data=="ls": bot.send_message(cid,"📊 /lichsucau")
    elif c.data=="tt": bot.send_message(cid,"💎 /thongtin")
    elif c.data=="stop": bot.send_message(cid,"⏹️ /stop")

@bot.message_handler(commands=['huongdan'])
def cmd_hd(m):
    bot.send_message(m.chat.id,f"""╔════════════════════════╗
║    📖 HƯỚNG DẪN VIP      ║
╠════════════════════════╣
║ 🔑 /nhapkey KEY
║ 🔐 /login TK MK
║ ⚡ /autobet on 10000 | off
║ 💸 /x2 on | off  (X2 THUA)
║ 📊 /lichsucau
║ 💎 /thongtin
║ ⏹️ /stop
╠════════════════════════╣
║ 🧠 14 THUẬT + ENSEMBLE
║ 💸 X2 AN TOÀN 6 CẤP
║ 📩 {ADMIN_USERNAME}
╚════════════════════════╝""",parse_mode="HTML")

@bot.message_handler(commands=['taokey'])
def gk(m):
    if m.chat.id!=ADMIN_ID: return bot.reply_to(m,"⛔ Chỉ ADMIN")
    try:
        p=m.text.split(); d=int(p[1]) if len(p)>1 else 30
        k="VIP-"+''.join(random.choices(string.ascii_uppercase+string.digits,k=10)); valid_keys[k]=d
        ht=(datetime.now()+timedelta(days=d)).strftime("%d/%m/%Y %H:%M")
        bot.reply_to(m,f"""╔════════════════════════╗
║    👑 TẠO KEY THÀNH CÔNG  ║
╠════════════════════════╣
║ 🔑 <code>{k}</code>
║ ⏳ {d} NGÀY
║ 📅 {ht}
╚════════════════════════╝""",parse_mode="HTML")
    except: bot.reply_to(m,"/taokey 30")

@bot.message_handler(commands=['danhsachkey'])
def lk(m):
    if m.chat.id!=ADMIN_ID: return
    if not valid_keys: return bot.reply_to(m,"📭 Kho trống")
    ds="\n".join([f"🔑 <code>{k}</code> → {v}N" for k,v in valid_keys.items()])
    bot.reply_to(m,f"""╔════════════════════════╗
║    📋 DANH SÁCH KEY      ║
╠════════════════════════╣
{ds}
║ 📊 TỔNG: <b>{len(valid_keys)}</b>
╚════════════════════════╝""",parse_mode="HTML")

@bot.message_handler(commands=['nhapkey'])
def ak(m):
    p=m.text.split()
    if len(p)<2: return bot.reply_to(m,"/nhapkey VIP‑XXX")
    k=p[1].upper()
    if k in valid_keys:
        authorized_users[m.chat.id]=time.time()+valid_keys[k]*86400; del valid_keys[k]
        ht=datetime.fromtimestamp(authorized_users[m.chat.id]).strftime("%d/%m/%Y %H:%M")
        bot.reply_to(m,f"""╔════════════════════════╗
║  ✅ KÍCH HOẠT VIP THÀNH CÔNG ║
╠════════════════════════╣
║ ⏳ {valid_keys.get(k,'')} NGÀY
║ 📅 HẾT HẠN {ht}
╚════════════════════════╝""",parse_mode="HTML",reply_markup=vip_menu())
    else: bot.reply_to(m,f"❌ KEY KHÔNG HỢP LỆ\n📩 {ADMIN_USERNAME}")

@bot.message_handler(commands=['thongtin'])
def tt(m):
    cid=m.chat.id; init_user_state(cid)
    if not check_auth(cid): return
    st=user_states[cid]
    han="👑 ADMIN VĨNH VIỄN" if cid==ADMIN_ID else format_expire_time(authorized_users[cid])
    x2=f"🟢 BẬT | CẤP {st['martingale_level']}/{MAX_MARTINGALE_LEVEL}" if st["martingale_enabled"] else "🔴 TẮT"
    bot.reply_to(m,f"""╔════════════════════════╗
║     💎 THÔNG TIN VIP     ║
╠════════════════════════╣
║ 🆔 <code>{cid}</code>
║ ⏳ HẠN: {han}
║ ⚡ AUTO: {'🟢 BẬT' if st['auto_bet_enabled'] else '🔴 TẮT'}
║ 💸 X2: {x2}
║ 💰 GỐC: <b>{st['base_bet']:,}</b>
║ 🎯 HIỆN TẠI: <b>{tinh_tien_cuoc(cid):,}</b>
║ 📊 DƯ: <b>{st['balance']:,}</b>
║ ✅ THẮNG: {st['total_win']} | ❌ THUA: {st['total_lose']}
║ 🔥 THẮNG DÃY: {st['win_streak']} | 💀 THUA DÃY: {st['lose_streak']}
║ 📈 LỊCH SỬ: {len(st['history'])}
╚════════════════════════╝""",parse_mode="HTML",reply_markup=vip_menu())

@bot.message_handler(commands=['lichsucau'])
@require_auth
def ls(m):
    st=user_states[m.chat.id]
    if not st["history"]: return bot.reply_to(m,"📭 Chưa dữ liệu")
    s="".join("🔵" if x=="TAI" else "🔴" for x in st["history"][-20:])
    bot.reply_to(m,f"""╔════════════════════════╗
║     📊 LỊCH SỬ CẦU       ║
╠════════════════════════╣
║ 🔵 TÀI: <b>{st['history'].count('TAI')}</b>
║ 🔴 XỈU: <b>{st['history'].count('XIU')}</b>
║ {s}
╚════════════════════════╝""",parse_mode="HTML")

@bot.message_handler(commands=['login'])
@require_auth
def lg(m):
    p=m.text.split()
    if len(p)!=3: return bot.reply_to(m,"✅ /login TAIKHOAN MATKHAU")
    mm=bot.reply_to(m,"🔄 Đang kết nối server...")
    res=login_and_get_token(p[1],p[2])
    if "_error" in res: return bot.edit_message_text(f"❌ {res['_error']}",m.chat.id,mm.message_id)
    init_user_state(m.chat.id)
    st=user_states[m.chat.id]
    st["balance"]=res["money"]; st["base_bet"]=st["bet_amount"]
    bot.edit_message_text(f"""╔════════════════════════╗
║   ✅ ĐĂNG NHẬP THÀNH CÔNG  ║
╠════════════════════════╣
║ 📛 {res['nickname']}
║ 💰 {res['money']:,}
║ 🟢 SOCKET ĐANG CHẠY
╚════════════════════════╝""",m.chat.id,mm.message_id,parse_mode="HTML",reply_markup=vip_menu())
    threading.Thread(target=start_websocket,args=(m.chat.id,res["token"]),daemon=True).start()

@bot.message_handler(commands=['autobet'])
@require_auth
def ab(m):
    cid=m.chat.id
    if cid not in active_sockets: return bot.reply_to(m,"⚠️ Phải /login trước")
    p=m.text.split()
    if len(p)<2: return bot.reply_to(m,"/autobet on 10000 | off")
    st=user_states[cid]
    if p[1].lower()=="on":
        amt=int(p[2]) if len(p)>2 else 10000
        st["auto_bet_enabled"]=True; st["bet_amount"]=amt; st["base_bet"]=amt; st["martingale_level"]=0
        bot.reply_to(m,f"""╔════════════════════════╗
║     🟢 AUTO VIP BẬT      ║
╠════════════════════════╣
║ 💰 {amt:,} / PHIÊN
║ ⏳ CHẠY ĐẾN KHI GÕ OFF
╚════════════════════════╝""",parse_mode="HTML",reply_markup=vip_menu())
    else:
        st["auto_bet_enabled"]=False
        bot.reply_to(m,"🔴 AUTO ĐÃ DỪNG",reply_markup=vip_menu())

@bot.message_handler(commands=['x2'])
@require_auth
def cmd_x2(m):
    cid=m.chat.id
    st=user_states[cid]
    p=m.text.split()
    if len(p)<2:
        tt=f"🟢 BẬT C{st['martingale_level']}" if st["martingale_enabled"] else "🔴 TẮT"
        return bot.reply_to(m,f"""╔════════════════════════╗
║     💸 X2 KHI THUA VIP   ║
╠════════════════════════╣
║ TRẠNG THÁI: {tt}
║ GỐC: {st['base_bet']:,}
║ TỐI ĐA: {MAX_MARTINGALE_LEVEL} CẤP
║ /x2 on  |  /x2 off
╚════════════════════════╝""",parse_mode="HTML")
    if p[1].lower()=="on":
        st["martingale_enabled"]=True; st["martingale_level"]=0
        bot.reply_to(m,f"""╔════════════════════════╗
║   💸 X2 VIP ĐÃ BẬT ✅    ║
╠════════════════════════╣
║ THUA → NHÂN {MARTINGALE_MULTIPLIER}X
║ THẮNG → RESET GỐC
║ AN TOÀN TỐI ĐA {MAX_MARTINGALE_LEVEL} CẤP
╚════════════════════════╝""",parse_mode="HTML",reply_markup=vip_menu())
    else:
        st["martingale_enabled"]=False; st["martingale_level"]=0
        bot.reply_to(m,"🔴 X2 ĐÃ TẮT, về mức gốc",reply_markup=vip_menu())

@bot.message_handler(commands=['stop'])
@require_auth
def sp(m):
    cid=m.chat.id
    if cid in active_sockets:
        try:active_sockets[cid].disconnect()
        except Exception: pass
        del active_sockets[cid]
    st=user_states[cid]
    st["auto_bet_enabled"]=False; st["martingale_enabled"]=False; st["martingale_level"]=0
    bot.reply_to(m,"""╔════════════════════════╗
║   ⏹️ NGẮT AN TOÀN VIP    ║
╠════════════════════════╣
║ ✅ ĐÓNG WS + TẮT AUTO
║ ✅ TẮT X2 + RESET CẤP
╚════════════════════════╝""",parse_mode="HTML")

if __name__=="__main__":
    threading.Thread(target=run_web, daemon=True).start()

    print("👑 ANHPHONG ELITE PRO MAX")
    bot.infinity_polling()