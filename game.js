'use strict';
const $=s=>document.querySelector(s),esc=s=>(s||'').replace(/[<>&"']/g,''),W=['東','南','西','北'];
const ch=k=>String.fromCodePoint(k<9?0x1F007+k:k<18?0x1F019+k-9:k<27?0x1F010+k-18:k<31?0x1F000+k-27:[0x1F006,0x1F005,0x1F004][k-31])+'\uFE0E';
const col=k=>k<9?'#b01818':k<18?'#1a4fa0':k<27?'#177a2a':k==33?'#c00':k==32?'#177a2a':'#222';
const T=(id,c,e)=>`<span class="t ${c}" style="color:${col(id>>2)}" ${e||''}>${ch(id>>2)}</span>`;
const KO=[0,8,9,17,18,26,27,28,29,30,31,32,33];
let G=null,isHost=false,me=0,peer,hc,room='',names=['あなた','CPU1','CPU2','CPU3'],bots=[0,1,1,1],seatConn={},ar=0,cs=0,V=null;
const sorted=h=>h.slice().sort((a,b)=>a-b),cnt=h=>{const c=Array(34).fill(0);h.forEach(t=>c[t>>2]++);return c};

/* ---------- 麻雀ロジック ---------- */
function mk(c){const i=c.findIndex(x=>x>0);if(i<0)return true;
 if(c[i]>=3){c[i]-=3;const r=mk(c);c[i]+=3;if(r)return true}
 if(i<27&&i%9<7&&c[i+1]&&c[i+2]){c[i]--;c[i+1]--;c[i+2]--;const r=mk(c);c[i]++;c[i+1]++;c[i+2]++;if(r)return true}
 return false}
function win(c,nm){
 if(!nm){if(c.every(x=>x==0||x==2)&&c.filter(x=>x==2).length==7)return true;
  if(KO.every(k=>c[k])&&KO.reduce((a,k)=>a+c[k],0)==14)return true}
 for(let i=0;i<34;i++)if(c[i]>=2){c[i]-=2;const r=mk(c);c[i]+=2;if(r)return true}
 return false}
function tenpai(c,nm){for(let k=0;k<34;k++)if(c[k]<4){c[k]++;const r=win(c,nm);c[k]--;if(r)return true}return false}
function han(s,c,ts){const m=G.melds[s],ct=!m.length,all=c.slice();let h=0;
 m.forEach(x=>x.t.forEach(t=>all[t>>2]++));
 if(ct&&KO.every(k=>c[k])&&KO.reduce((a,k)=>a+c[k],0)==14)return 13;
 if(G.rii[s])h++;if(ct&&ts)h++;
 if(all.every((x,k)=>!x||(k<27&&k%9>0&&k%9<8)))h++;
 [31,32,33,27+(s-G.dealer+4)%4,27+(G.kyoku>3?1:0)].forEach(k=>{if(all[k]>=3)h++});
 if(ct&&c.filter(x=>x==2).length==7)h+=2;
 return h}
function dOpts(s){const h=G.hands[s],c=cnt(h),o={};
 if(win(c,G.melds[s].length)&&han(s,c,1)>0)o.tsumo=1;
 if(!G.rii[s]&&!G.melds[s].length&&G.sc[s]>=1000)o.rii=h.filter(t=>{const d=cnt(h);d[t>>2]--;return tenpai(d,0)});
 return o}
function cOpts(s,t,f){const c=cnt(G.hands[s]),k=t>>2,o={},nm=G.melds[s].length;
 c[k]++;if(win(c,nm)&&han(s,c,0)>0)o.ron=1;c[k]--;
 if(!G.rii[s]){if(c[k]>=2)o.pon=1;
  if((f+1)%4==s&&k<27){const l=[];[[-2,-1],[-1,1],[1,2]].forEach(([a,b])=>{const x=k%9+a,y=k%9+b;if(x>=0&&y<=8&&c[k+a]&&c[k+b])l.push([k+a,k+b])});if(l.length)o.chi=l}}
 return Object.keys(o).length?o:null}

/* ---------- 進行(ホストのみ) ---------- */
function newK(){const w=[...Array(136).keys()];
 for(let i=135;i>0;i--){const j=Math.random()*(i+1)|0;[w[i],w[j]]=[w[j],w[i]]}
 G.wall=w;G.hands=[0,1,2,3].map(()=>w.splice(0,13));G.melds=[[],[],[],[]];G.river=[[],[],[],[]];
 G.rii=[0,0,0,0];G.res=null;G.rep=false;G.turn=G.dealer;G.calls=null;G.drawn=-1;draw()}
function draw(){if(G.wall.length<=14){G.res={draw:1,ch:[0,0,0,0]};G.ph='e';G.rep=true;return send()}
 const t=G.wall.pop();G.hands[G.turn].push(t);G.drawn=t;G.ph='d';G.calls=null;send();bot()}
function disc(s,t,r){const h=G.hands[s];h.splice(h.indexOf(t),1);G.river[s].push(t);G.last=t;G.from=s;G.drawn=-1;
 if(r){G.rii[s]=1;G.sc[s]-=1000;G.pot++}
 const c={};let n=0;for(let i=1;i<4;i++){const p=(s+i)%4,o=cOpts(p,t,s);if(o){c[p]=o;n++}}
 if(n){G.ph='c';G.calls=c;G.resp={};send();bot()}else{G.turn=(s+1)%4;draw()}}
function meld(s,k){const h=G.hands[s],t=G.last,kk=t>>2,need=k=='pon'?[kk,kk]:G.calls[s].chi[+k.slice(3)],u=[];
 need.forEach(x=>u.push(h.splice(h.findIndex(y=>y>>2==x),1)[0]));
 G.river[G.from].pop();G.melds[s].push({t:[t,...u],f:G.from});G.turn=s;G.ph='d';G.calls=null;G.drawn=-1;send();bot()}
function win_(s,f){const ts=s==f,c=cnt(G.hands[s]);if(!ts)c[G.last>>2]++;
 const h=han(s,c,ts),b=h>=13?8000:h>=11?6000:h>=8?4000:h>=6?3000:h>=5?2000:Math.min(2000,30*2**(h+2)),d=s==G.dealer,u=x=>Math.ceil(x/100)*100,ch=[0,0,0,0];
 if(ts){for(let i=0;i<4;i++)if(i!=s){const v=u(b*(d||i==G.dealer?2:1));ch[i]-=v;ch[s]+=v}}
 else{const v=u(b*(d?6:4));ch[f]-=v;ch[s]+=v}
 ch[s]+=G.pot*1000;G.pot=0;ch.forEach((v,i)=>G.sc[i]+=v);
 G.res={w:s,f,h,ch,ts,hands:G.hands.map(sorted),tile:ts?G.drawn:G.last};G.ph='e';G.rep=d;send()}
function resolve(){if(G.ph!='c')return;const p=Object.keys(G.calls);if(!p.every(x=>x in G.resp))return;
 let q=p.find(x=>G.resp[x]=='ron');if(q!=null)return win_(+q,G.from);
 q=p.find(x=>G.resp[x]=='pon');if(q!=null)return meld(+q,'pon');
 q=p.find(x=>G.resp[x].startsWith('chi'));if(q!=null)return meld(+q,G.resp[q]);
 G.turn=(G.from+1)%4;draw()}
function bot(){setTimeout(()=>{if(!G||G.ph=='e'||G.ph=='o')return;
 if(G.ph=='d'){const s=G.turn,o=dOpts(s);
  if(bots[s]&&o.tsumo)return win_(s,s);
  if(bots[s]||(G.rii[s]&&!o.tsumo)){
   if(G.rii[s])return disc(s,G.drawn,0);
   const h=G.hands[s],c=cnt(h);let best=h[0],bs=1e9;
   h.forEach(t=>{const k=t>>2,x=k%9,n=(d,v)=>(k<27&&x+d>=0&&x+d<=8&&c[k+d])?v:0;
    const sc=c[k]*10+n(-1,4)+n(1,4)+n(-2,2)+n(2,2)+(k<27&&x>0&&x<8?1:0);if(sc<bs){bs=sc;best=t}});
   return disc(s,best,o.rii&&o.rii.includes(best)?1:0)}}
 else if(G.ph=='c'){for(const p in G.calls)if(bots[p]&&!(p in G.resp))G.resp[p]=G.calls[p].ron?'ron':'pass';resolve()}},700)}
function act(s,a){if(!G)return;
 if(a.k=='next'){if(G.ph=='e'&&s==0){G.kyoku+=G.rep?0:1;G.dealer=G.kyoku%4;if(G.kyoku>=8){G.ph='o';send()}else newK()}return}
 if(G.ph=='d'&&G.turn==s){
  if(a.k=='d'&&G.hands[s].includes(a.t)){if(G.rii[s]&&a.t!=G.drawn)return;
   if(a.r&&!(dOpts(s).rii||[]).includes(a.t))return;return disc(s,a.t,a.r?1:0)}
  if(a.k=='tsumo'&&dOpts(s).tsumo)return win_(s,s)}
 if(G.ph=='c'&&G.calls[s]&&!(s in G.resp)){const o=G.calls[s];
  if((a.k=='ron'&&o.ron)||(a.k=='pon'&&o.pon)||(a.k=='chi'&&o.chi&&o.chi[a.i])||a.k=='pass'){G.resp[s]=a.k=='chi'?'chi'+a.i:a.k;resolve()}}}
function view(s){const g=G,v={me:s,n:names,sc:g.sc,dealer:g.dealer,kyoku:g.kyoku,turn:g.turn,ph:g.ph,river:g.river,melds:g.melds,rii:g.rii,
 hn:g.hands?g.hands.map(h=>h.length):[],hand:g.hands?sorted(g.hands[s].filter(t=>t!=g.drawn||g.turn!=s||g.ph!='d')):[],
 drawn:g.turn==s&&g.ph=='d'?g.drawn:-1,wall:g.wall?g.wall.length:0,res:g.res,pot:g.pot,room};
 if(g.ph=='d'&&g.turn==s)v.o=dOpts(s);
 if(g.ph=='c'&&g.calls[s]&&!(s in g.resp))v.o=g.calls[s];return v}
function send(){for(let s=0;s<4;s++){if(bots[s])continue;const v=view(s);if(s==0)render(v);else seatConn[s]&&seatConn[s].send({t:'v',v})}}
function A(a){if(isHost)act(0,a);else hc.send({t:'a',a})}

/* ---------- 通信(PeerJS: 部屋コード方式) ---------- */
const ICE={iceServers:[{urls:'stun:stun.l.google.com:19302'},{urls:'stun:stun1.l.google.com:19302'},{urls:'stun:global.stun.twilio.com:3478'}]};
const ERR={'peer-unavailable':'その部屋コードの部屋が見つかりません。コードと、ホストが待機中かを確認してください','network':'PeerJSサーバーに接続できません。少し待って再試行してください','server-error':'PeerJSサーバーが応答しません','socket-error':'サーバーとの通信に失敗しました','webrtc':'WebRTC通信のエラーです','browser-incompatible':'このブラウザは対応していません'};
function note(t,bad){const e=$('#nt');if(e){e.textContent=t;e.style.color=bad?'#ff9a8a':'#b9e6b0'}else alert(t)}
function setName(){names[0]=esc($('#nm')&&$('#nm').value)||'あなた'}
let hostTm;
function host(){setName();if(typeof Peer==='undefined')return note('通信ライブラリ(PeerJS)を読み込めませんでした。ネット接続を確認して再読み込みしてください',1);
 isHost=true;me=0;note('部屋を作成中…');clearTimeout(hostTm);
 hostTm=setTimeout(()=>{if(!$('#rm').textContent){isHost=false;if(peer)peer.destroy();lobby();note('部屋を作れません。PeerJSの公開サーバーに接続できていません。少し待って再試行するか、「ひとりで遊ぶ」をお使いください',1)}},12000);
 tryRoom()}
function solo(){setName();isHost=true;me=0;room='';start()}
function tryRoom(){room=''+(1000+Math.random()*9000|0);if(peer)peer.destroy();peer=new Peer('mjrm-'+room,{config:ICE});
 peer.on('error',e=>{if(e.type=='unavailable-id')return tryRoom();isHost=false;lobby();note('エラー: '+(ERR[e.type]||e.type),1)});
 peer.on('disconnected',()=>{try{peer.reconnect()}catch(e){}});
 peer.on('open',()=>{clearTimeout(hostTm);$('#rm').textContent='部屋コード '+room;lobby()});
 peer.on('connection',c=>{const s=[1,2,3].find(i=>!seatConn[i]);
  if(!s||G){c.on('open',()=>{c.send({t:'full'});setTimeout(()=>c.close(),300)});return}
  c.on('open',()=>{seatConn[s]=c;bots[s]=0;names[s]=esc(c.metadata&&c.metadata.name)||'プレイヤー'+s;c.send({t:'seat',s});lobby()});
  c.on('data',m=>{if(m.t=='a')act(s,m.a)});
  c.on('close',()=>{if(seatConn[s]!==c)return;delete seatConn[s];bots[s]=1;names[s]='CPU'+s;lobby();if(G){send();if(G.ph=='d'||G.ph=='c')bot()}})})}
function join(){setName();const code=($('#code').value||'').trim();
 if(!/^\d{4}$/.test(code))return note('4桁の部屋コードを入力してください',1);
 note('接続中…');let ok=0,inRoom=0;if(peer)peer.destroy();peer=new Peer({config:ICE});
 const tm=setTimeout(()=>{if(!ok){note('接続できませんでした。コードとホストの待機状態を確認してください。回線が違う相手とは繋がらない場合があります',1);peer.destroy()}},15000);
 peer.on('error',e=>{clearTimeout(tm);note('入室できません: '+(ERR[e.type]||e.type),1)});
 peer.on('open',()=>{note('部屋を探しています…');hc=peer.connect('mjrm-'+code,{metadata:{name:names[0]},reliable:true});
  hc.on('open',()=>{ok=1;clearTimeout(tm);note('入室処理中…')});
  hc.on('error',e=>note('通信エラー: '+e,1));
  hc.on('data',m=>{ok=1;clearTimeout(tm);
   if(m.t=='seat'){inRoom=1;me=m.s;room=code;$('#rm').textContent='部屋コード '+code;$('#lb').innerHTML=shell('<h3>入室しました</h3><p>ホストの開始を待っています…</p>')}
   if(m.t=='full')note('満席、または対局が始まっています',1);
   if(m.t=='v'){$('#lb').style.display='none';render(m.v)}});
  hc.on('close',()=>{if(inRoom)alert('ホストとの接続が切れました。ページを再読み込みしてください')})})}
function start(){G={sc:[25000,25000,25000,25000],dealer:0,kyoku:0,pot:0};$('#lb').style.display='none';newK()}
function dec(){return [[33,'5%','10%',-12],[4,'86%','16%',10],[31,'9%','68%',8],[27,'84%','66%',-8],[13,'44%','84%',5],[22,'48%','2%',-6],[12,'70%','40%',14],[0,'20%','38%',-16]].map(([k,l,t,r])=>`<span class="dc" style="left:${l};top:${t};transform:rotate(${r}deg);color:${col(k)}">${ch(k)}</span>`).join('')}
function shell(x){return dec()+`<div class="box"><h1>麻雀</h1><div class="sub">オンライン対戦</div>${x}<div id="nt" class="nt"></div></div>`}
function lobby(){const L=$('#lb');if(G)return;
 if(!isHost){L.innerHTML=shell(`<input id="nm" placeholder="あなたの名前" maxlength="8"><div class="two"><div><h3>部屋を作る</h3><p style="margin:0 0 12px">友達を招待します</p><button onclick="host()">部屋を作る</button><p style="margin-top:14px"><button onclick="solo()" style="background:linear-gradient(#4aa0d8,#216aa0);box-shadow:0 3px 0 #123e60">ひとりで遊ぶ(CPU対戦)</button></p></div><i></i><div><h3>部屋に入る</h3><input id="code" placeholder="部屋コード4桁" maxlength="4"><button onclick="join()">入室</button></div></div><p>空席はCPUが入ります</p>`);return}
 L.innerHTML=shell(`<h3>部屋コード</h3><div class="code">${room}</div><div class="seats">${names.map((n,i)=>`<div class="seat${i==0?' me':''}"><b>${W[i]}</b>${n}<br><span>${bots[i]?'CPU':'プレイヤー'}</span></div>`).join('')}</div><button onclick="start()">対局開始</button><p>このコードを友達に伝えてください</p>`)}

/* ---------- 描画(画像のレイアウトに合わせる) ---------- */
function render(v){V=v;const p=i=>(i-v.me+4)%4,at=v.ph=='d'&&v.turn==v.me,o=v.o||{};
 let h='',pos=[null,null,null,null];
 const seat=pp=>[0,1,2,3].find(i=>p(i)==pp);
 // 河
 const R=[[295,360,180,'flex-start'],[480,240,180,'flex-start'],[295,102,180,'flex-end'],[100,240,180,'flex-start']];
 for(let q=0;q<4;q++){const i=seat(q),r=R[q];
  h+=`<div class="a" style="left:${r[0]}px;top:${r[1]}px;width:${r[2]}px;height:122px;display:flex;flex-wrap:wrap;align-content:${r[3]}">${v.river[i].map(t=>T(t,'s')).join('')}</div>`}
 // 相手の手牌
 const t2=seat(2),t1=seat(1),t3=seat(3);
 h+=`<div class="a" style="left:210px;top:10px">${'<span class="t b bk"></span>'.repeat(v.hn[t2]||0)}</div>`;
 h+=`<div class="a" style="left:18px;top:130px;width:30px">${'<span class="t b bk" style="display:block;height:18px;width:32px;margin-bottom:1px"></span>'.repeat(v.hn[t3]||0)}</div>`;
 h+=`<div class="a" style="left:712px;top:130px;width:30px">${'<span class="t b bk" style="display:block;height:18px;width:32px;margin-bottom:1px"></span>'.repeat(v.hn[t1]||0)}</div>`;
 // 副露・名前
 const M=[[480,470],[560,230],[500,56],[60,92]],NP=[[20,452],[640,200],[300,50],[60,60]];
 for(let q=0;q<4;q++){const i=seat(q);
  h+=`<div class="a" style="left:${M[q][0]}px;top:${M[q][1]}px;max-width:240px">${v.melds[i].map(m=>m.t.map(t=>T(t,'s')).join('')+' ').join('')}</div>`;
  h+=`<div class="nm" style="left:${NP[q][0]}px;top:${NP[q][1]}px">${W[(i-v.dealer+4)%4]} ${esc(v.n[i])}${v.rii[i]?' <b style="color:#d22">リーチ</b>':''}${v.turn==i&&v.ph=='d'?' ◀':''}</div>`}
 // 中央
 const lab=(v.kyoku<4?'東':'南')+'一二三四'[v.kyoku%4]+'局';
 const sc=q=>v.sc[seat(q)];
 h+=`<div class="a" id="ctr"><div style="margin-top:36px;font-size:15px">${lab}</div><div style="font-size:12px">残り ${Math.max(0,v.wall-14)}枚 ／ 供託 ${v.pot*1000}</div>
 <b style="left:0;right:0;bottom:2px">${W[(seat(0)-v.dealer+4)%4]} ${sc(0)}</b><b style="left:0;right:0;top:2px">${W[(seat(2)-v.dealer+4)%4]} ${sc(2)}</b>
 <b style="left:4px;top:48px;writing-mode:vertical-rl">${W[(seat(3)-v.dealer+4)%4]} ${sc(3)}</b><b style="right:4px;top:48px;writing-mode:vertical-rl">${W[(seat(1)-v.dealer+4)%4]} ${sc(1)}</b></div>`;
 // 自分の手牌
 const okR=ar&&o.rii,can=t=>at&&(!v.rii[v.me]||t==v.drawn)&&(!okR||o.rii.includes(t));
 const ht=t=>T(t,'h'+(at&&!can(t)?' dim':''),at&&can(t)?`onclick="A({k:'d',t:${t},r:${ar?1:0});ar=0"`:'');
 h+=`<div class="a" style="left:30px;bottom:6px;white-space:nowrap">${v.hand.map(ht).join('')}${v.drawn>=0?'<span style="display:inline-block;width:14px"></span>'+ht(v.drawn):''}</div>`;
 // ボタン
 const B=[['ポン',o.pon,"A({k:'pon'})"],['チー',o.chi,o.chi&&o.chi.length>1?'cs=1;render(V)':"A({k:'chi',i:0})"],['カン',0,''],['リーチ',o.rii&&o.rii.length,'ar=!ar;render(V)'],['ロン',o.ron,"A({k:'ron'})"],['ツモ',o.tsumo,"A({k:'tsumo'})"],['パス',v.ph=='c'&&v.o,"A({k:'pass'})"]];
 B.forEach((b,i)=>h+=`<div class="btn ${b[1]?'on':''}" style="left:${72+i*70}px" ${b[1]?`onclick="${b[2]}"`:''}>${b[0]=='リーチ'&&ar?'取消':b[0]}</div>`);
 if(cs&&o.chi)h+=`<div class="a" style="left:100px;bottom:170px;background:#fff;padding:4px;border-radius:4px">${o.chi.map((q,i)=>`<span style="cursor:pointer;margin:0 6px" onclick="cs=0;A({k:'chi',i:${i}})">${T(q[0]*4,'s')}${T(q[1]*4,'s')}</span>`).join('')}</div>`;
 // 結果
 if(v.ph=='e'||v.ph=='o'){const r=v.res;let x='';
  if(v.ph=='o'){const rk=[0,1,2,3].sort((a,b)=>v.sc[b]-v.sc[a]);x=`<h2>対局終了</h2>${rk.map((i,n)=>`${n+1}位 ${esc(v.n[i])} ${v.sc[i]}`).join('<br>')}`}
  else if(r.draw)x='<h2>流局</h2>';
  else x=`<h2>${esc(v.n[r.w])} ${r.ts?'ツモ':'ロン'}!</h2><div>${r.h>=13?'役満':r.h+'翻'}</div><div>${r.hands[r.w].map(t=>T(t,'s')).join('')} ${T(r.tile,'s')}</div><div>${[0,1,2,3].map(i=>`${esc(v.n[i])} ${r.ch[i]>0?'+':''}${r.ch[i]}`).join(' ／ ')}</div>`;
  if(v.ph=='e')x+=v.me==0?`<button onclick="A({k:'next'})">次の局へ</button>`:'<div style="font-size:14px">ホストが進めるのを待っています</div>';
  h+=`<div id="ov">${x}</div>`}
 $('#bd').innerHTML=h+'<div class="a" style="left:6px;top:4px;font-size:22px">🏠 🎵</div><div class="a" style="right:8px;top:8px;background:#1b6fd8;color:#fff;font-size:12px;padding:2px 8px;border-radius:3px">鳴きON</div>'}

function fit(){const k=Math.min(innerWidth/960,innerHeight/600);$('#st').style.transform=`scale(${k}) translate(-50%,-50%)`}
addEventListener('resize',fit);fit();lobby();
