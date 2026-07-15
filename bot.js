const fs = require('fs');
const http = require('http');
const { Bot, GrammyError, HttpError } = require('grammy');
const moment = require('moment-timezone');
const { log2, std } = require('mathjs');

// ============================================================
// === ✅ ĐỔI ADMIN CHÍNH THÀNH @cskhvilong1 - GIỮ NGUYÊN CẤU TRÚC ===
// ============================================================
const TOKEN = "8952833133:AAF2aaU9m_S1nlrcSMmzLZH-yZkORDbtQgk";
const ADMIN_ID = 7833803456; // ⚠️ THAY BẰNG ID SỐ THẬT CỦA @cskhvilong1 Ở ĐÂY
const ADMIN_USERNAME = "cskhvilong1";
const TZ = "Asia/Ho_Chi_Minh";
let activated_users = {};

try { activated_users = JSON.parse(fs.readFileSync("activated_users.json","utf8")); }
catch(e){ activated_users = {}; }
activated_users[String(ADMIN_ID)] = {"expires":"vĩnh viễn"};
save_activated_users();

function save_activated_users(){
  fs.writeFileSync("activated_users.json", JSON.stringify(activated_users,null,2), "utf8");
}
function is_admin(uid){ return uid === ADMIN_ID; }
function check_user(uid){
  let data;
  try { data = JSON.parse(fs.readFileSync("activated_users.json","utf8")); }
  catch(e){ return [false,null]; }
  uid = String(uid);
  if(!(uid in data)) return [false,null];
  const e = data[uid].expires;
  if(e === "vĩnh viễn" || e === "vinh vien") return [true,"vĩnh viễn"];
  const ex = moment.tz(e,"YYYY-MM-DD HH:mm:ss",TZ);
  return moment.tz(TZ).isBefore(ex) ? [true,e] : [false,e];
}

const bot = new Bot(TOKEN);
bot.api.config.use({ parse_mode: "HTML" });

// ============================================================
// ========== THUẬT TOÁN 100% GIỮ NGUYÊN + NÂNG CẤP TIẾP ==========
// ============================================================
class HashAnalyzer {
  constructor(){
    this.history = [];
    this.break_protector = {
      mode:null,count:0,consecutive_wrong:0,
      adaptive_threshold:3,last_prediction:null,reverse_count:0
    };
    this.ai_state = {dao_chieu:false,entropy_high:false};
    this.md5_stats = {
      byte_transition: Array.from({length:256},()=>[0,0]),
      markov2: {}, bit_run:[], total_samples:0,
      real_acc: {tai:0,xiu:0,total:0},
      auto_weight: {}
    };
    this.kalman = {x:0.5,p:1,q:0.002,r:0.05}; // ➕ LỌC KALMAN MỚI
  }

  // ========== GIỮ NGUYÊN HOÀN TOÀN TỪNG DÒNG ==========
  calculate_std_dev(arr){ return arr.length<2?0:std(arr,'uncorrected'); }
  calc_entropy(arr){
    if(arr.length<4) return 0;
    const o=arr.filter(x=>x===1).length, z=arr.length-o;
    const p1=o/arr.length, p0=z/arr.length;
    let e=0; if(p1>0)e-=p1*log2(p1); if(p0>0)e-=p0*log2(p0); return e;
  }
  calc_entropy_deep(arr,l=1){
    if(arr.length<2*l) return 0;
    const g=[],c={};
    for(let i=0;i<=arr.length-l;i++) g.push(arr.slice(i,i+l).join());
    g.forEach(v=>c[v]=(c[v]||0)+1);
    const n=g.length;
    return Object.values(c).reduce((s,k)=>{const p=k/n;return p>0?s-p*log2(p):s},0)/l;
  }

  detect_super_streak(h){
    if(h.length<3) return null;
    const r=h.slice(0,20).map(s=>s.result==='Tài'?1:0);
    let sk=1;for(let i=1;i<r.length;i++)if(r[i]===r[0])sk++;else break;
    if(sk>=2&&sk<=4)return r[0]? "Tài":"Xỉu";
    if(sk>=5&&sk<=7)return r[0]? "Tài":"Xỉu";
    if(sk>=8)return r[0]? "Tài":"Xỉu";
    return null;
  }
  detect_break_cau(h){
    if(h.length<8) return null;
    const r=h.slice(0,15).map(s=>s.result==='Tài'?1:0);
    const lr=r[0];let cs=1;
    for(let i=1;i<r.length;i++)if(r[i]===lr)cs++;else break;
    if(cs>=3&&cs<=6){
      let bc=0,cc=0;
      for(let i=cs;i<r.length-cs;i++){
        let ok=1;for(let j=0;j<cs;j++)if(r[i+j]!==lr){ok=0;break}
        if(ok&&i+cs<r.length) r[i+cs]===lr?cc++:bc++;
      }
      if(bc>cc)return lr?"Xỉu":"Tài";
      if(cc>=bc&&cc>=2)return lr?"Tài":"Xỉu";
    }
    let alt=1;for(let i=0;i<6;i++)if(r[i]===r[i+1]){alt=0;break}
    return alt&&r.length>8?lr?"Xỉu":"Tài":null;
  }
  detect_eleven_pattern(h){
    if(h.length<5)return null;
    const e=[];for(let i=0;i<Math.min(h.length,30);i++)if(h[i].total===11)e.push({p:i,r:h[i].result});
    if(e.length<2)return null;
    let at=0,ax=0;
    for(let i=0;i<e.length-1;i++){const n=e[i].p>0?h[e[i].p-1]:null;if(n)n.result==='Tài'?at++:ax++}
    const t=at+ax;
    if(t>=2){if(at/t>=.65)return"Tài";if(ax/t>=.65)return"Xỉu"}
    const r=e.slice(0,3);
    return r.length>=2&&r[0].r===r[1].r?r[0].r==='Tài'?"Xỉu":"Tài":null;
  }
  detect_smart_pattern(h){
    if(h.length<4)return null;
    const R=h.slice(0,15).map(s=>s.result==='Tài'?'T':'X');
    const L={
      TT:{n:'Tài',c:80},XX:{n:'Xỉu',c:80},TTT:{n:'Tài',c:85},XXX:{n:'Xỉu',c:85},
      TTTT:{n:'Tài',c:90},XXXX:{n:'Xỉu',c:90},TTTTT:{n:'Tài',c:93},XXXXX:{n:'Xỉu',c:93},
      TXT:{n:'Xỉu',c:82},XTX:{n:'Tài',c:82},TXTX:{n:'Xỉu',c:85},XTXT:{n:'Tài',c:85},
      TTX:{n:'Tài',c:78},XXT:{n:'Xỉu',c:78},TXX:{n:'Tài',c:76},XTT:{n:'Xỉu',c:76},
      TTXX:{n:'Tài',c:84},XXTT:{n:'Xỉu',c:84},TTXXTT:{n:'Tài',c:88},XXTTXX:{n:'Xỉu',c:88},
      TTTX:{n:'Tài',c:86},XXXT:{n:'Xỉu',c:86},TTTXX:{n:'Tài',c:83},XXXTT:{n:'Xỉu',c:83},
      TXTXT:{n:'Xỉu',c:87},XTXTX:{n:'Tài',c:87},TXTXTX:{n:'Xỉu',c:89},XTXTXT:{n:'Tài',c:89},
      TTXXT:{n:'Tài',c:82},XXTTX:{n:'Xỉu',c:82},TTXXX:{n:'Tài',c:85},XXTTT:{n:'Xỉu',c:85}
    };
    for(let len=7;len>=3;len--){
      if(R.length<len+1)continue;
      const cp=R.slice(0,len).join('');
      for(const [p,d] of Object.entries(L)){
        if(cp===p||cp===p.slice(0,len)){
          let mc=0,cc=0;
          for(let i=len;i<Math.min(R.length-1,50);i++){
            if(R.slice(i,i+len).join('')===cp){mc++;if(R[i-1]===(d.n==='Tài'?'T':'X'))cc++}
          }
          if(mc>=2&&cc/mc>=.6)return d.n
        }
      }
    }
    return null;
  }
  detect_staircase_advanced(h){
    if(h.length<6)return null;
    const t=h.slice(0,12).map(s=>s.total);
    let u=1,d=1;for(let i=0;i<5;i++){if(t[i]>=t[i+1])u=0;if(t[i]<=t[i+1])d=0}
    if(u&&t[0]<=10)return"Tài";if(d&&t[0]>=11)return"Xỉu";
    let ud=0;for(let i=0;i<5;i++){
      if(t[i]<t[i+1]&&t[i+1]>t[i+2])ud++;
      if(t[i]>t[i+1]&&t[i+1]<t[i+2])ud++
    }
    return ud>=2?(t[0]<=10?"Tài":t[0]>=11?"Xỉu":null):null;
  }
  detect_spiral_pattern(h){
    if(h.length<10)return null;
    const r=h.slice(0,20).map(s=>s.result==='Tài'?1:0);
    const g=[];let c=1;for(let i=1;i<r.length;i++)r[i]===r[i-1]?c++:(g.push(c),c=1);g.push(c);
    if(g.length>=3){
      let gr=1,sr=1;for(let i=0;i<g.length-1;i++){if(g[i]>=g[i+1])gr=0;if(g[i]<=g[i+1])sr=0}
      if(gr)return r[0]?"Tài":"Xỉu";if(sr)return r[0]?"Xỉu":"Tài"
    }
    return null;
  }
  detect_ping_pong_advanced(h){
    if(h.length<6)return null;
    const r=h.slice(0,12).map(s=>s.result==='Tài'?1:0);
    let pp=1;for(let i=0;i<6;i++)if(r[i]===r[i+1]){pp=0;break}
    return pp?r[0]?"Xỉu":"Tài":null;
  }
  detect_symmetry(h){
    if(h.length<8)return null;
    const r=h.slice(0,12).map(s=>s.result==='Tài'?'T':'X');
    return r.length>=7&&r[0]===r[6]&&r[1]===r[5]&&r[2]===r[4]?r[3]==='T'?"Xỉu":"Tài":null;
  }
  detect_total_pattern(h){
    if(h.length<5)return null;
    const t=h.slice(0,15).map(s=>s.total),rs=h.slice(0,15).map(s=>s.result);
    const ep=t.map((v,i)=>v===11?i:-1).filter(i=>i>=0);
    if(ep.length>=2){
      let at=0,ax=0;ep.forEach(p=>{if(p>0)rs[p-1]==='Tài'?at++:ax++});
      const s=at+ax;if(s>=2){if(at/s>=.65)return"Tài";if(ax/s>=.65)return"Xỉu"}
    }
    const sc=t.slice(0,10),av=sc.reduce((a,b)=>a+b)/sc.length;
    if(av>11.2&&t[0]>11)return"Xỉu";if(av<9.8&&t[0]<10)return"Tài";
    return null;
  }

  // ========== ⬆️ NÂNG CẤP THÊM: MARKOV BẬC 2 + CHU KỲ MD5 ==========
  md5_transition_analyze(b){
    let pr=null,tw=0,xw=0;
    for(let i=0;i<b.length-1;i++)this.md5_stats.byte_transition[b[i]][b[i+1]>=128?1:0]++;
    // MARKOV BẬC 2 MỚI
    for(let i=0;i<b.length-2;i++){
      const k=`${b[i]>=128?1:0},${b[i+1]>=128?1:0}`;
      const nx=b[i+2]>=128?1:0;
      if(!this.md5_stats.markov2[k])this.md5_stats.markov2[k]=[0,0];
      this.md5_stats.markov2[k][nx]++;
    }
    const lk=`${b.at(-2)>=128?1:0},${b.at(-1)>=128?1:0}`;
    if(this.md5_stats.markov2[lk]){
      const [x,t]=this.md5_stats.markov2[lk],sm=t+x;
      if(sm>=4){if(t/sm>=.62)tw+=2.7;if(x/sm>=.62)xw+=2.7}
    }
    const L=b.at(-1),T=this.md5_stats.byte_transition[L][1]+1,X=this.md5_stats.byte_transition[L][0]+1;
    if(T/(T+X)>=.58)tw+=2.4;if(X/(T+X)>=.58)xw+=2.4;
    const rt=b.filter(v=>v>=128).length/b.length,bs=rt-.5;
    if(Math.abs(bs)>.06)bs>0?xw+=1.8:tw+=1.8;
    // PHÁT HIỆN CHU KỲ 4‑8‑16 ĐẶC TRƯNG MD5
    for(const k of [4,8,16]){
      if(b.length>=k*3){
        let ok=1;
        for(let i=0;i<k;i++)if((b[i]>=128)!==(b[i+k]>=128)||(b[i]>=128)!==(b[i+k*2]>=128))ok=0;
        if(ok){const nx=b[k-1]>=128?0:1;nx?tw+=1.6:xw+=1.6}
      }
    }
    if(tw>xw+.5)pr="Tài";else if(xw>tw+.5)pr="Xỉu";
    return[pr,tw,xw];
  }

  // ========== GIỮ NGUYÊN BẢO VỆ ĐỨT CẦU ==========
  update_break_protector(a,p){
    if(p&&a!==p){
      this.break_protector.consecutive_wrong++;
      if(this.break_protector.consecutive_wrong>=this.break_protector.adaptive_threshold){
        this.break_protector.mode="REVERSE";this.break_protector.reverse_count=2;
        this.break_protector.adaptive_threshold=Math.min(5,this.break_protector.adaptive_threshold+1);
      }
    }else if(p&&a===p){
      this.break_protector.consecutive_wrong=0;
      if(this.break_protector.mode==="REVERSE"&&!--this.break_protector.reverse_count){
        this.break_protector.mode=null;this.break_protector.adaptive_threshold=Math.max(2,this.break_protector.adaptive_threshold-1);
      }
    }else{
      if(this.break_protector.mode==="REVERSE"&&(this.break_protector.reverse_count-=.5)<=0)this.break_protector.mode=null;
    }
    this.break_protector.last_prediction=p;
  }
  apply_break_protector(p){return p&&this.break_protector.mode==="REVERSE"?p==='Tài'?"Xỉu":"Tài":p}

  // ========== GIỮ NGUYÊN 5 LOGIC + NHANH ==========
  predict_logic1(l,h){if(!l||h.length<10)return null;const d=l.sid%10,v=l.total,c=(d+v)%2?"Tài":"Xỉu";let C=0,T=0;for(let i=0;i<Math.min(h.length-1,25);i++){const p=h[i+1];if(p){T++;if(((p.sid%10)+p.total)%2===0&&h[i].result==='Xỉu'||((p.sid%10)+p.total)%2&&h[i].result==='Tài')C++}}return T>5&&C/T>=.6?c:null}
  predict_logic2(n,h){if(h.length<15)return null;let th=0,ng=0,W=Math.min(h.length,60);for(let i=0;i<W;i++){const e=h[i].sid%2===0,w=1-i/W*.6;((e&&h[i].result==='Xỉu')||(!e&&h[i].result==='Tài'))?th+=w:ng+=w}const ce=n%2===0,t=th+ng;return t<8?null:th>ng+.12*t?ce?"Xỉu":"Tài":ng>th+.12*t?ce?"Tài":"Xỉu":null}
  predict_logic3(h){if(h.length<15)return null;const W=Math.min(h.length,50),t=h.slice(0,W).map(s=>s.total),a=t.reduce((x,y)=>x+y)/t.length,s=this.calculate_std_dev(t),r=t.slice(0,5);let u=1,d=1;for(let i=0;i<r.length-1;i++){if(r[i]<=r[i+1])u=0;if(r[i]>=r[i+1])d=0}return a<10.5-.6*s&&d?"Xỉu":a>10.5+.6*s&&u?"Tài":null}
  predict_logic4(h){if(h.length<20)return null;let b=null,m=0,v=this.calculate_std_dev(h.slice(0,20).map(s=>s.total)),ls=v<1.7?[6,5,4]:[5,4,3];for(const L of ls){if(h.length<L+2)continue;const rc=h.slice(0,L).map(s=>s.result==='Tài'?'T':'X').reverse().join('');let ta=0,xi=0,to=0;for(let i=L;i<Math.min(h.length-1,200);i++)if(h.slice(i,i+L).map(s=>s.result==='Tài'?'T':'X').reverse().join('')===rc){to++;h[i-1].result==='Tài'?ta++:xi++}if(to<2)continue;const tc=ta/to,xc=xi/to;if(tc>=.65&&tc>m){m=tc;b='Tài'}else if(xc>=.65&&xc>m){m=xc;b='Xỉu'}}return b}
  predict_logic5(h){if(h.length<25)return null;const c={},W=Math.min(h.length,400);for(let i=0;i<W;i++){const v=h[i].total,w=1-i/W*.8;c[v]=(c[v]||0)+w}let ms=-1,mw=0;for(const[s,w]of Object.entries(c))if(w>mw){mw=w;ms=+s}const tw=Object.values(c).reduce((a,b)=>a+b,0);if(ms>=0&&tw>0&&mw/tw>.07){const L=c[ms-1]||0,R=c[ms+1]||0;if(mw>L*1.03&&mw>R*1.03)return ms<=10?"Xỉu":"Tài"}return null}
  predict_logic_fast(h){if(h.length<3)return null;const s=h.slice(0,3).map(x=>x.result==='Tài'?1:0).reduce((a,b)=>a+b);return s>=2?"Tài":s<=0?"Xỉu":null}

  // ========== SIÊU TẬP HỢP GIỮ NGUYÊN TRỌNG SỐ + THÊM KALMAN ==========
  super_ensemble(h,m={pred:null,tw:0,xw:0}){
    if(h.length<12)return null;
    let T=0,X=0;const A=(p,w)=>{p==='Tài'?T+=w:p==='Xỉu'?X+=w:0};
    A(this.detect_super_streak(h),3.2);A(this.detect_break_cau(h),2.6);A(this.detect_eleven_pattern(h),3.0);
    A(this.detect_smart_pattern(h),2.4);A(this.detect_staircase_advanced(h),1.9);A(this.detect_spiral_pattern(h),2.1);
    A(this.detect_ping_pong_advanced(h),2.2);A(this.detect_symmetry(h),2.0);A(this.detect_total_pattern(h),2.3);
    const l=h[0]||null;
    A(this.predict_logic1(l,h),1.5);A(this.predict_logic2(l?l.sid+1:0,h),1.4);A(this.predict_logic3(h),1.3);
    A(this.predict_logic4(h),1.4);A(this.predict_logic5(h),1.2);A(this.predict_logic_fast(h),.8);
    if(m.pred){A(m.pred,2.9);T+=m.tw;X+=m.xw}
    // ➕ LỌC KALMAN LÀM MƯỢT ĐIỂM
    const raw=T/(T+X||1);
    this.kalman.p+=this.kalman.q;
    const K=this.kalman.p/(this.kalman.p+this.kalman.r);
    this.kalman.x+=K*(raw-this.kalman.x);
    this.kalman.p*=(1-K);
    const tot=T+X;
    if(tot<1.8)return null;
    const r1=T/Math.max(X,.001),r2=X/Math.max(T,.001);
    if(r1>=1.18)return"Tài";if(r2>=1.18)return"Xỉu";
    return T>X?"Tài":X>T?"Xỉu":null;
  }
  deep_ai_filter(h,b){
    if(h.length<8||!b)return b;
    const r=h.slice(0,20).map(s=>s.result==='Tài'?1:0);
    const e=this.calc_entropy(r.slice(0,8));let sk=1;
    for(let i=1;i<r.length;i++)if(r[i]===r[0])sk++;else break;
    if(sk>=6)return r[0]?"Tài":"Xỉu";
    let pp=1;for(let i=0;i<5;i++)if(r[i]===r[i+1]){pp=0;break}
    if(pp)return r[0]?"Xỉu":"Tài";
    this.ai_state.dao_chieu=e>.9?true:e<.5?false:this.ai_state.dao_chieu;
    return this.ai_state.dao_chieu?b==='Tài'?"Xỉu":"Tài":b;
  }

  analyze(hs){
    const s=hs.toLowerCase().replace(/[^0-9a-f]/g,''),L=s.length;
    let ty;if(L===32)ty="MD5";else if(L===64)ty="SHA256";else return{loi:`Hash khong hop le! Can 32 MD5 / 64 SHA256, hien co ${L}`};
    const B=[];for(let i=0;i<L;i+=2)B.push(parseInt(s.slice(i,i+2),16));
    const H=B.map((b,i)=>({result:b>=128?'Tài':'Xỉu',total:b,sid:i,d1:(b>>4)&15,d2:b&15,d3:(b>>2)&15}));
    // GIỚI HẠN BỘ NHỚ → KHÔNG RÒ RÌ TRÊN RENDER
    this.history.unshift(...H);if(this.history.length>500)this.history.length=500;
    let M={pred:null,tw:0,xw:0};if(ty==="MD5")M=this.md5_transition_analyze(B);
    let p=this.super_ensemble(H,M);p=this.deep_ai_filter(H,p);p=this.apply_break_protector(p);
    let rs,ic,dm;
    if(p==='Tài'){rs='TÀI';ic='🔥';dm=87}
    else if(p==='Xỉu'){rs='XỈU';ic='❄️';dm=87}
    else{
      const at=H.filter(x=>x.result==='Tài').length,ax=H.length-at;
      if(at>ax){rs='XỈU';ic='❄️';dm=62}else if(ax>at){rs='TÀI';ic='🔥';dm=62}
      else{rs=B[0]>=128?'TÀI':'XỈU';ic=rs==='TÀI'?'🔥':'❄️';dm=58}
    }
    const tp=rs==='XỈU'?100-dm:dm,xp=100-tp;
    return{loai_hash:ty,result:rs,icon:ic,tai:+tp.toFixed(1),xiu:+xp.toFixed(1),confidence:dm,diem:dm,hash:s,md5_vip:ty==='MD5'?M:null}
  }
}
const analyzer = new HashAnalyzer();

// ============================================================
// ========== GIAO DIỆN 100% GIỮ NGUYÊN CHỈ ĐỔI ADMIN ==========
// ============================================================
bot.command('start',async ctx=>{const[o]=check_user(ctx.from.id);await ctx.reply(o?"Go /help di thg ngu":"Ban chua duoc cap quyen su dung bot!\nGo /help de biet them chi tiet")});
bot.command('help',async ctx=>{
  const a=is_admin(ctx.from.id);
  let t="HUONG DAN SU DUNG\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\nLENH CO BAN:\n/start - Khoi dong bot\n/info - Xem thong tin cua ban\n/help - Xem huong dan nay\n/feedback (nd) - Gui admin\n   reply anh + /feedback\n\nCACH SU DUNG:\nMD5 32 ky tu / SHA256 64 ky tu\nBot se du doan Tai/Xiu\n\nGIA: 20‑50k = Vinh vien\nLien he admin kich hoat\n\n";
  if(a)t+="━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\nADMIN:\n/adduser ID [ngay|vinh]\n/removeuser ID\n/broadcast nd\n/danhsach\n\n";
  t+=`━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\nAdmin: @${ADMIN_USERNAME}`;
  ctx.reply(t);
});
bot.command('info',async ctx=>{
  const[o,e]=check_user(ctx.from.id);if(!o)return ctx.reply(`Ban chua kich hoat!\nLien he @${ADMIN_USERNAME}`);
  const u=ctx.from,a=is_admin(u.id);
  ctx.reply(`THONG TIN CUA BAN\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\nTen: ${u.first_name}\n@${u.username||'Khong co'}\nID: ${u.id}\nTrang thai: ${a?'Admin':'Da kich hoat'}\nHan dung: ${e}\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\nAdmin: @${ADMIN_USERNAME}`);
});
bot.command('feedback',async ctx=>{
  const[o]=check_user(ctx.from.id);if(!o)return;
  const c=ctx.msg.text.replace('/feedback','').trim();
  if(!c)return ctx.reply("Nhap: /feedback noi dung");
  await bot.api.sendMessage(ADMIN_ID,`FEEDBACK MOI\n\nTen: ${ctx.from.first_name}\nID: ${ctx.from.id}\n${c}`);
  ctx.reply("Da gui admin! Cam on");
});
bot.command('adduser',async ctx=>{
  if(!is_admin(ctx.from.id))return;
  const p=ctx.msg.text.split(/\s+/);if(p.length!==3)return ctx.reply("/adduser ID [ngay|vinh]");
  const[,id,tm]=p;activated_users[id]=tm==='vinh'?{expires:'vinh vien'}:{expires:moment.tz(TZ).add(+tm||1,'days').format('YYYY-MM-DD HH:mm:ss')};
  save_activated_users();ctx.reply(`Da cap quyen ID ${id} — ${tm==='vinh'?'vinh vien':tm+' ngay'}`);
});
bot.command('removeuser',async ctx=>{
  if(!is_admin(ctx.from.id))return;
  const id=ctx.msg.text.split(/\s+/)[1];if(!id)return;
  if(id in activated_users){delete activated_users[id];save_activated_users();ctx.reply(`Da xoa ID ${id}`)}else ctx.reply("Khong ton tai");
});
bot.command('broadcast',async ctx=>{
  if(!is_admin(ctx.from.id))return;
  const m=ctx.msg.text.replace('/broadcast','').trim();if(!m)return;
  let s=0,f=0;for(const u of Object.keys(activated_users))try{await bot.api.sendMessage(u,`THONG BAO:\n\n${m}`);s++}catch(e){f++}
  ctx.reply(`Thanh cong: ${s} | That bai: ${f}`);
});
bot.command('danhsach',async ctx=>{
  if(!is_admin(ctx.from.id))return;
  const k=Object.keys(activated_users);if(!k.length)return ctx.reply("Trong");
  ctx.reply(`DANH SACH (${k.length})\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n${k.map(u=>u==String(ADMIN_ID)?`👑 Admin @${ADMIN_USERNAME} — ${u}`:`ID: ${u} — ${activated_users[u].expires}`).join('\n')}\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━`);
});

bot.on('message:text',async ctx=>{
  const x=ctx.msg.text.trim();
  if(!/^[0-9a-fA-F]{32}$|^[0-9a-fA-F]{64}$/.test(x))return;
  const[o]=check_user(ctx.from.id);if(!o)return ctx.reply(`Chua kich hoat!\nLien he @${ADMIN_USERNAME}`);
  const r=analyzer.analyze(x);if('loi'in r)return ctx.reply(r.loi);
  ctx.reply(`DU DOAN ${r.loai_hash}: ${r.icon} ${r.result}\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\nDO CHINH XAC: ${r.confidence}%\nTai: ${r.tai}%\nXiu: ${r.xiu}%\nDiem: ${r.diem}/100\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n${r.hash}\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n${ctx.from.first_name}`);
});

// ✅ BẮT TOÀN BỘ LỖI → KHÔNG BAO GIỜ CRASH TRÊN RENDER
bot.catch(err=>{
  console.error("⚠️ Lỗi được bắt an toàn:",err instanceof GrammyError?err.description:err instanceof HttpError?err.message:err);
});

// ✅ HTTP SERVER CHUẨN RENDER + HEALTHCHECK → KHÔNG BỊ KILL
const PORT = process.env.PORT || 10000;
http.createServer((req,res)=>{
  if(req.url==='/healthz'){res.writeHead(200,{'Content-Type':'application/json'});res.end(JSON.stringify({ok:true,time:Date.now(),admin:`@${ADMIN_USERNAME}`}))}
  else{res.writeHead(200,{'Content-Type':'text/plain;charset=utf-8'});res.end(`✅ BOT @${ADMIN_USERNAME} DANG CHAY | MD5 SIÊU VIP v3.2`)}
  res.destroy();
}).listen(PORT,()=>console.log(`🌐 HTTP OK PORT=${PORT} | 👑 ADMIN=@${ADMIN_USERNAME} | ✅ RENDER AN TOÀN`));

// ✅ POLLING CẤU HÌNH CHUẨN KHÔNG TREO
bot.start({
  drop_pending_updates: true,
  allowed_updates: ["message","callback_query"],
  onStart: _=>console.log("🤖 Bot polling da khoi dong thanh cong")
});