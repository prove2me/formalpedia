-- Prove2me | solution 1 for Lax808846Proofs.Simulation.compileProgram_runsTo
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:21:49.460399+00:00
-- url     : https://prove2.me/submissions/e9a88922-a48a-4e0a-baf7-33869384c6dc

import Mathlib.Tactic
import Definitions.Def_EdgeSublinearMWIS_Main_NativeSchemeInterfaces

section

namespace Lax808846Proofs.Imp

@[simp] theorem Bop.apply_add (m n:ℕ):Bop.add.apply m n=m + n:=rfl
@[simp] theorem Bop.apply_sub (m n:ℕ):Bop.sub.apply m n=m - n:=rfl
@[simp] theorem Bop.apply_mul (m n:ℕ):Bop.mul.apply m n=m * n:=rfl
@[simp] theorem Bop.apply_div (m n:ℕ):Bop.div.apply m n=m / n:=rfl
@[simp] theorem Bop.apply_and (m n:ℕ):Bop.and.apply m n=Nat.land m n:=rfl
@[simp] theorem Bop.apply_or (m n:ℕ):Bop.or.apply m n=Nat.lor m n:=rfl
@[simp] theorem Bop.apply_xor (m n:ℕ):Bop.xor.apply m n=Nat.xor m n:=rfl
@[simp] theorem Bop.apply_shiftl (m n:ℕ):Bop.shiftl.apply m n=m * 2 ^ n:=rfl
@[simp] theorem Bop.apply_shiftr (m n:ℕ):Bop.shiftr.apply m n=m / 2 ^ n:=rfl

@[simp] theorem Expr.add_def (e f:Expr):Expr.add e f=.bin .add e f:=rfl
@[simp] theorem Expr.sub_def (e f:Expr):Expr.sub e f=.bin .sub e f:=rfl
@[simp] theorem Expr.mul_def (e f:Expr):Expr.mul e f=.bin .mul e f:=rfl
@[simp] theorem Expr.div_def (e f:Expr):Expr.div e f=.bin .div e f:=rfl
@[simp] theorem Expr.and_def (e f:Expr):Expr.and e f=.bin .and e f:=rfl
@[simp] theorem Expr.or_def (e f:Expr):Expr.or e f=.bin .or e f:=rfl
@[simp] theorem Expr.xor_def (e f:Expr):Expr.xor e f=.bin .xor e f:=rfl
@[simp] theorem Expr.shiftl_def (e f:Expr):Expr.shiftl e f=.bin .shiftl e f:=rfl
@[simp] theorem Expr.shiftr_def (e f:Expr):Expr.shiftr e f=.bin .shiftr e f:=rfl

def Expr.eval:Expr→ Env→ Option ℕ
  | lit n,_ => some n
  | var x,σ => some (σ.vars x)
  | get a i,σ => (i.eval σ).bind fun k => (σ.arrs a)[k]?
  | bin op e f,σ => (e.eval σ).bind fun m => (f.eval σ).map fun n => op.apply m n

def Cond.eval:Cond→ Env→ Option Bool
  | eq e f,σ => (e.eval σ).bind fun m => (f.eval σ).map fun n => m == n
  | lt e f,σ => (e.eval σ).bind fun m => (f.eval σ).map fun n => decide (m < n)

inductive BigStep:Com→ Env→ Env→ ℕ→ Prop

  | skip {σ:Env}:BigStep .skip σ σ 1

  | assign {σ:Env} {x:String} {e:Expr} {v:ℕ} (h:e.eval σ=some v):
      BigStep (.assign x e) σ (σ.setVar x v) (1 + e.size)

  | store {σ:Env} {a:String} {i e:Expr} {k v:ℕ}
      (hi:i.eval σ=some k) (he:e.eval σ=some v)
      (hk:k < (σ.arrs a).length):
      BigStep (.store a i e) σ (σ.setArr a k v) (1 + i.size + e.size)

  | seq {c d:Com} {σ σ' σ'':Env} {k k':ℕ}:
      BigStep c σ σ' k→ BigStep d σ' σ'' k'→
      BigStep (.seq c d) σ σ'' (k + k')

  | ite_true {b:Cond} {c d:Com} {σ σ':Env} {k:ℕ}
      (hb:b.eval σ=some true) (hc:BigStep c σ σ' k):
      BigStep (.ite b c d) σ σ' (1 + b.size + k)

  | ite_false {b:Cond} {c d:Com} {σ σ':Env} {k:ℕ}
      (hb:b.eval σ=some false) (hd:BigStep d σ σ' k):
      BigStep (.ite b c d) σ σ' (1 + b.size + k)

  | while_true {b:Cond} {c:Com} {σ σ' σ'':Env} {k k':ℕ}
      (hb:b.eval σ=some true) (hc:BigStep c σ σ' k)
      (hw:BigStep (.while b c) σ' σ'' k'):
      BigStep (.while b c) σ σ'' (1 + b.size + k + k')

  | while_false {b:Cond} {c:Com} {σ:Env} (hb:b.eval σ=some false):
      BigStep (.while b c) σ σ (1 + b.size)

  | read {σ:Env} {x:String} {v:ℕ} {rest:List ℕ} (h:σ.inp=v::rest):
      BigStep (.read x) σ { σ.setVar x v with inp:=rest } 1

  | write {σ:Env} {e:Expr} {v:ℕ} (h:e.eval σ=some v):
      BigStep (.write e) σ { σ with out:=σ.out ++ [v] } (1 + e.size)

end Lax808846Proofs.Imp

end

section

namespace Lax808846Proofs.Imp

theorem fit_eq_some {B v u:ℕ}:fit B v=some u↔ u=v∧ v < B:=by
  constructor
  · intro h
    by_cases hv:v < B
    · rw [fit,if_pos hv] at h
      exact ⟨(Option.some.inj h).symm,hv⟩
    · rw [fit,if_neg hv] at h; exact absurd h (by simp)
  · rintro ⟨rfl,h⟩; rw [fit,if_pos h]

theorem fit_self {B v:ℕ} (h:v < B):fit B v=some v:=by rw [fit,if_pos h]

theorem Expr.eval_and_lt_of_evalB {B:ℕ} {σ:Env} {e:Expr} {v:ℕ}
    (h:e.evalB B σ=some v):e.eval σ=some v∧ v < B:=by
  induction e generalizing v with
  | lit n =>
      rw [Expr.evalB,fit_eq_some] at h
      obtain ⟨rfl,hn⟩:=h
      exact ⟨rfl,hn⟩
  | var x =>
      rw [Expr.evalB,fit_eq_some] at h
      obtain ⟨rfl,hn⟩:=h
      exact ⟨rfl,hn⟩
  | get a i ih =>
      rw [Expr.evalB,Option.bind_eq_some_iff] at h
      obtain ⟨k,hk,h⟩:=h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨u,hu,h⟩:=h
      rw [fit_eq_some] at h
      obtain ⟨rfl,hlt⟩:=h
      exact ⟨by rw [Expr.eval, (ih hk).1]; exact hu,hlt⟩
  | bin op e f ihe ihf =>
      rw [Expr.evalB,Option.bind_eq_some_iff] at h
      obtain ⟨m,hm,h⟩:=h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨n,hn,h⟩:=h
      rw [fit_eq_some] at h
      obtain ⟨rfl,hlt⟩:=h
      exact ⟨by rw [Expr.eval, (ihe hm).1, (ihf hn).1]; rfl,hlt⟩

theorem Expr.lt_of_evalB {B:ℕ} {σ:Env} {e:Expr} {v:ℕ}
    (h:e.evalB B σ=some v):v < B:=(eval_and_lt_of_evalB h).2

theorem BigStepB.inpBounded {B:ℕ} {c:Com} {σ σ':Env} {k:ℕ}
    (h:BigStepB B c σ σ' k) (hσ:σ.InpBounded B):σ'.InpBounded B:=by
  induction h with
  | skip => exact hσ
  | assign _ => exact fun v hv => hσ v hv
  | store _ _ _ => exact fun v hv => hσ v hv
  | seq _ _ ih ih' => exact ih' (ih hσ)
  | ite_true _ _ ih => exact ih hσ
  | ite_false _ _ ih => exact ih hσ
  | while_true _ _ _ ih ih' => exact ih' (ih hσ)
  | while_false _ => exact hσ
  | read h =>
      intro v hv
      refine hσ v ?_
      rw [h]
      exact List.mem_cons_of_mem _ hv
  | write _ => exact fun v hv => hσ v hv

theorem initEnv_inpBounded {B:ℕ} (ext:String→ ℕ) {x:List ℕ}
    (hx:∀ v∈ x,v < B):(initEnv ext x).InpBounded B:=hx

end Lax808846Proofs.Imp

end

section

namespace Lax808846Proofs.Compile

open Lax808846.Ram Lax808846Proofs.Imp

def Layout.arrAddr (L:Layout) (a:String) (i:ℕ):ℕ:=
  L.arrBase a + L.arrays.length * i

theorem Layout.temps_add_one_lt_two_pow {L:Layout} {B w:ℕ} (h:L.FitsWords B w):
    L.temps + 1 < 2 ^ w:=by
  have hs:=h.span
  simp only [Layout.span] at hs
  omega

theorem Layout.varAddr_lt_two_pow {L:Layout} {B w:ℕ} (h:L.FitsWords B w) {x:String}
    (hx:x∈ L.scalars):L.varAddr x < 2 ^ w:=by
  have hidx:L.scalars.idxOf x < L.scalars.length:=List.idxOf_lt_length_of_mem hx
  have hs:=h.span
  simp only [Layout.span] at hs
  simp only [Layout.varAddr]
  omega

theorem Layout.arrays_length_lt_two_pow {L:Layout} {B w:ℕ} (h:L.FitsWords B w):
    L.arrays.length < 2 ^ w:=by
  have hs:=h.span
  have h1:1≤ B:=le_of_lt h.one_lt
  have hmul:L.arrays.length * 1≤ L.arrays.length * B:=Nat.mul_le_mul_left _ h1
  simp only [Layout.span] at hs
  omega

theorem Layout.arrBase_lt_two_pow {L:Layout} {B w:ℕ} (h:L.FitsWords B w) {a:String}
    (ha:a∈ L.arrays):L.arrBase a < 2 ^ w:=by
  have hidx:L.arrays.idxOf a < L.arrays.length:=List.idxOf_lt_length_of_mem ha
  have h1:1≤ B:=le_of_lt h.one_lt
  have hmul:L.arrays.length * 1≤ L.arrays.length * B:=Nat.mul_le_mul_left _ h1
  have hs:=h.span
  simp only [Layout.span] at hs
  simp only [Layout.arrBase]
  omega

theorem Layout.arrAddr_lt_two_pow {L:Layout} {B w:ℕ} (h:L.FitsWords B w) {a:String}
    (ha:a∈ L.arrays) {k:ℕ} (hk:k < B):L.arrAddr a k < 2 ^ w:=by
  have hidx:L.arrays.idxOf a < L.arrays.length:=List.idxOf_lt_length_of_mem ha
  have hmul:L.arrays.length * (k + 1)≤ L.arrays.length * B:=Nat.mul_le_mul_left _ hk
  have hexp:L.arrays.length * (k + 1)=L.arrays.length * k + L.arrays.length:=by ring
  have hs:=h.span
  simp only [Layout.span] at hs
  simp only [Layout.arrAddr,Layout.arrBase]
  omega

theorem Layout.mul_le_arrAddr (L:Layout) (a:String) (k:ℕ):
    L.arrays.length * k≤ L.arrAddr a k:=by
  simp only [Layout.arrAddr]; omega

@[simp] theorem binCode_length (op:Bop) (d:ℕ):(binCode op d).length=binLen op:=by
  cases op <;> rfl

theorem binLen_le_four (op:Bop):binLen op≤ 4:=by cases op <;> simp [binLen]

@[simp] theorem idxCode_length (L:Layout) (a:String) (d:ℕ):
    (L.idxCode a d).length=L.idxLen:=by
  simp [Layout.idxCode,Layout.idxLen]

@[simp] theorem compileExpr_length (L:Layout) (e:Expr) (d:ℕ):
    (compileExpr L e d).length=esize L e:=by
  induction e generalizing d with
  | lit n => simp [compileExpr,esize]
  | var x => simp [compileExpr,esize]
  | get a i ih => simp [compileExpr,esize,ih]; omega
  | bin op e f ihe ihf => simp [compileExpr,esize,ihe,ihf]; omega

@[simp] theorem compileCond_length (L:Layout) (b:Cond) (d:ℕ):
    (compileCond L b d).length=bsize L b:=by
  simp [compileCond,bsize]

@[simp] theorem compile_length (L:Layout) (c:Com) (a:ℕ):
    (compile L c a).length=size L c:=by
  induction c generalizing a with
  | skip => simp [compile,size]
  | assign x e => simp [compile,size]
  | store x i e => simp [compile,size]; omega
  | seq c d ihc ihd => simp [compile,size,ihc,ihd]
  | ite b c d ihc ihd => simp [compile,size,ihc,ihd]; omega
  | «while» b c ih => simp [compile,size,ih]; omega
  | read x => simp [compile,size]
  | write e => simp [compile,size]

theorem index_inj {q ja jb i j:ℕ} (hja:ja < q) (hjb:jb < q)
    (h:ja + q * i=jb + q * j):ja=jb∧ i=j:=by
  have hq:0 < q:=Nat.lt_of_le_of_lt (Nat.zero_le _) hja
  refine ⟨?_, ?_⟩
  · have:=congrArg (· % q) h
    simpa [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hja,Nat.mod_eq_of_lt hjb] using this
  · have:=congrArg (· / q) h
    simpa [Nat.add_mul_div_left _ _ hq,Nat.div_eq_of_lt hja,Nat.div_eq_of_lt hjb] using this

theorem temps_le_varAddr (L:Layout) (x:String):L.temps + 2≤ L.varAddr x:=
  Nat.le_add_right _ _

theorem varAddr_lt (L:Layout) {x:String} (h:x∈ L.scalars):
    L.varAddr x < L.temps + 2 + L.scalars.length:=
  Nat.add_lt_add_left (List.idxOf_lt_length_of_mem h) _

theorem le_arrAddr (L:Layout) (a:String) (i:ℕ):
    L.temps + 2 + L.scalars.length≤ L.arrAddr a i:=
  Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)

theorem temps_le_arrAddr (L:Layout) (a:String) (i:ℕ):
    L.temps + 2≤ L.arrAddr a i:=
  Nat.le_trans (Nat.le_add_right _ _) (le_arrAddr L a i)

theorem varAddr_inj (L:Layout) {x y:String} (hx:x∈ L.scalars) (hy:y∈ L.scalars)
    (h:L.varAddr x=L.varAddr y):x=y:=by
  have hx':=List.idxOf_lt_length_of_mem hx
  have hy':=List.idxOf_lt_length_of_mem hy
  have:L.scalars.idxOf x=L.scalars.idxOf y:=by
    simp only [Layout.varAddr] at h; omega
  calc x=L.scalars[L.scalars.idxOf x]:=(List.getElem_idxOf hx').symm
    _=L.scalars[L.scalars.idxOf y]'(by omega):=by simp [this]
    _=y:=List.getElem_idxOf hy'

theorem arrAddr_inj (L:Layout) {a b:String} {i j:ℕ} (ha:a∈ L.arrays)
    (hb:b∈ L.arrays) (h:L.arrAddr a i=L.arrAddr b j):a=b∧ i=j:=by
  have ha':=List.idxOf_lt_length_of_mem ha
  have hb':=List.idxOf_lt_length_of_mem hb
  have h':L.arrays.idxOf a + L.arrays.length * i=L.arrays.idxOf b + L.arrays.length * j:=by
    simp only [Layout.arrAddr,Layout.arrBase] at h; omega
  obtain ⟨hidx,hij⟩:=index_inj ha' hb' h'
  refine ⟨?_,hij⟩
  calc a=L.arrays[L.arrays.idxOf a]:=(List.getElem_idxOf ha').symm
    _=L.arrays[L.arrays.idxOf b]'(by omega):=by simp [hidx]
    _=b:=List.getElem_idxOf hb'

theorem varAddr_ne_arrAddr (L:Layout) {x a:String} (hx:x∈ L.scalars) (i:ℕ):
    L.varAddr x ≠ L.arrAddr a i:=by
  have:=varAddr_lt L hx
  have:=le_arrAddr L a i
  omega

theorem condExpr_evalB {B:ℕ} {b:Cond} {σ:Env} {r:Bool} (hB:1 < B)
    (h:b.evalB B σ=some r):
    ∃ v, (condExpr b).evalB B σ=some v∧ (v=0↔ r=true):=by
  cases b with
  | eq e f =>
      rw [Cond.evalB,Option.bind_eq_some_iff] at h
      obtain ⟨m,hm,h⟩:=h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨n,hn,rfl⟩:=h
      have hmB:=Expr.lt_of_evalB hm
      have hnB:=Expr.lt_of_evalB hn
      have h1:(Expr.bin Bop.sub e f).evalB B σ=some (m - n):=by
        show ((e.evalB B σ).bind fun p => (f.evalB B σ).bind fun q => fit B (Bop.sub.apply p q))
         =some (m - n)
        rw [hm,hn]
        exact fit_self (show m - n < B by omega)
      have h2:(Expr.bin Bop.sub f e).evalB B σ=some (n - m):=by
        show ((f.evalB B σ).bind fun p => (e.evalB B σ).bind fun q => fit B (Bop.sub.apply p q))
         =some (n - m)
        rw [hm,hn]
        exact fit_self (show n - m < B by omega)
      refine ⟨(m - n) + (n - m), ?_,by simp only [beq_iff_eq]; omega⟩
      show ((Expr.bin Bop.sub e f).evalB B σ).bind
          (fun p => ((Expr.bin Bop.sub f e).evalB B σ).bind fun q => fit B (Bop.add.apply p q))
       =some ((m - n) + (n - m))
      rw [h1,h2]
      exact fit_self (show (m - n) + (n - m) < B by omega)
  | lt e f =>
      rw [Cond.evalB,Option.bind_eq_some_iff] at h
      obtain ⟨m,hm,h⟩:=h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨n,hn,rfl⟩:=h
      have hmB:=Expr.lt_of_evalB hm
      have hnB:=Expr.lt_of_evalB hn
      have h2:(Expr.bin Bop.sub f e).evalB B σ=some (n - m):=by
        show ((f.evalB B σ).bind fun p => (e.evalB B σ).bind fun q => fit B (Bop.sub.apply p q))
         =some (n - m)
        rw [hm,hn]
        exact fit_self (show n - m < B by omega)
      refine ⟨1 - (n - m), ?_,by simp only [decide_eq_true_eq]; omega⟩
      show (fit B 1).bind
          (fun p => ((Expr.bin Bop.sub f e).evalB B σ).bind fun q => fit B (Bop.sub.apply p q))
       =some (1 - (n - m))
      rw [fit_self hB,h2]
      exact fit_self (show 1 - (n - m) < B by omega)

end Lax808846Proofs.Compile

end

section

namespace Lax808846Proofs.Machine

open Lax808846.Ram

theorem two_pow_pos (w:ℕ):0 < 2 ^ w:=by positivity

theorem setCell_eq (w:ℕ) (m:ℕ→ ℕ) (a v b:ℕ):
    setCell w m a v b=if b=a % 2 ^ w then v % 2 ^ w else m b:=rfl

theorem setCell_self {w a v:ℕ} (m:ℕ→ ℕ) (ha:a < 2 ^ w) (hv:v < 2 ^ w):
    setCell w m a v a=v:=by
  rw [setCell_eq,Nat.mod_eq_of_lt ha,if_pos rfl,Nat.mod_eq_of_lt hv]

theorem setCell_self_mod {w a:ℕ} (m:ℕ→ ℕ) (v:ℕ) (ha:a < 2 ^ w):
    setCell w m a v a=v % 2 ^ w:=by
  rw [setCell_eq,Nat.mod_eq_of_lt ha,if_pos rfl]

theorem setCell_of_ne {w a b:ℕ} (m:ℕ→ ℕ) (v:ℕ) (ha:a < 2 ^ w) (hb:b ≠ a):
    setCell w m a v b=m b:=by
  rw [setCell_eq,Nat.mod_eq_of_lt ha,if_neg hb]

theorem effect_set (w a n:ℕ) (s:State):
    (Instr.set a n).effect w s =
      some { s with pc:=s.pc + 1,mem:=setCell w s.mem a n }:=rfl

theorem effect_load_eq (w a b:ℕ) (s:State):
    (Instr.load a b).effect w s =
      some
        { s with
          pc:=s.pc + 1
          mem:=setCell w s.mem a (s.mem (s.mem (b % 2 ^ w) % 2 ^ w)) }:=rfl

theorem effect_load {w a b:ℕ} {s:State} (hb:b < 2 ^ w) (hm:s.mem b < 2 ^ w):
    (Instr.load a b).effect w s =
      some { s with pc:=s.pc + 1,mem:=setCell w s.mem a (s.mem (s.mem b)) }:=by
  rw [effect_load_eq,Nat.mod_eq_of_lt hb,Nat.mod_eq_of_lt hm]

theorem effect_store_eq (w a b:ℕ) (s:State):
    (Instr.store a b).effect w s =
      some
        { s with
          pc:=s.pc + 1
          mem:=setCell w s.mem (s.mem (a % 2 ^ w)) (s.mem (b % 2 ^ w)) }:=rfl

theorem effect_store {w a b:ℕ} {s:State} (ha:a < 2 ^ w) (hb:b < 2 ^ w):
    (Instr.store a b).effect w s =
      some { s with pc:=s.pc + 1,mem:=setCell w s.mem (s.mem a) (s.mem b) }:=by
  rw [effect_store_eq,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb]

theorem effect_add_eq (w a b c:ℕ) (s:State):
    (Instr.add a b c).effect w s =
      some
        { s with
          pc:=s.pc + 1
          mem:=setCell w s.mem a (s.mem (b % 2 ^ w) + s.mem (c % 2 ^ w)) }:=rfl

theorem effect_add {w a b c:ℕ} {s:State} (hb:b < 2 ^ w) (hc:c < 2 ^ w):
    (Instr.add a b c).effect w s =
      some { s with pc:=s.pc + 1,mem:=setCell w s.mem a (s.mem b + s.mem c) }:=by
  rw [effect_add_eq,Nat.mod_eq_of_lt hb,Nat.mod_eq_of_lt hc]

theorem effect_sub_eq (w a b c:ℕ) (s:State):
    (Instr.sub a b c).effect w s =
      some
        { s with
          pc:=s.pc + 1
          mem:=setCell w s.mem a (s.mem (b % 2 ^ w) - s.mem (c % 2 ^ w)) }:=rfl

theorem effect_sub {w a b c:ℕ} {s:State} (hb:b < 2 ^ w) (hc:c < 2 ^ w):
    (Instr.sub a b c).effect w s =
      some { s with pc:=s.pc + 1,mem:=setCell w s.mem a (s.mem b - s.mem c) }:=by
  rw [effect_sub_eq,Nat.mod_eq_of_lt hb,Nat.mod_eq_of_lt hc]

theorem effect_mul_eq (w a b c:ℕ) (s:State):
    (Instr.mul a b c).effect w s =
      some
        { s with
          pc:=s.pc + 1
          mem:=setCell w s.mem a (s.mem (b % 2 ^ w) * s.mem (c % 2 ^ w)) }:=rfl

theorem effect_mul {w a b c:ℕ} {s:State} (hb:b < 2 ^ w) (hc:c < 2 ^ w):
    (Instr.mul a b c).effect w s =
      some { s with pc:=s.pc + 1,mem:=setCell w s.mem a (s.mem b * s.mem c) }:=by
  rw [effect_mul_eq,Nat.mod_eq_of_lt hb,Nat.mod_eq_of_lt hc]

theorem effect_div_eq (w a b c:ℕ) (s:State):
    (Instr.div a b c).effect w s =
      some
        { s with
          pc:=s.pc + 1
          mem:=setCell w s.mem a (s.mem (b % 2 ^ w) / s.mem (c % 2 ^ w)) }:=rfl

theorem effect_div {w a b c:ℕ} {s:State} (hb:b < 2 ^ w) (hc:c < 2 ^ w):
    (Instr.div a b c).effect w s =
      some { s with pc:=s.pc + 1,mem:=setCell w s.mem a (s.mem b / s.mem c) }:=by
  rw [effect_div_eq,Nat.mod_eq_of_lt hb,Nat.mod_eq_of_lt hc]

theorem effect_and_eq (w a b c:ℕ) (s:State):
    (Instr.and a b c).effect w s =
      some
        { s with
          pc:=s.pc + 1
          mem:=setCell w s.mem a (Nat.land (s.mem (b % 2 ^ w)) (s.mem (c % 2 ^ w))) }:=rfl

theorem effect_and {w a b c:ℕ} {s:State} (hb:b < 2 ^ w) (hc:c < 2 ^ w):
    (Instr.and a b c).effect w s =
      some
        { s with
          pc:=s.pc + 1
          mem:=setCell w s.mem a (Nat.land (s.mem b) (s.mem c)) }:=by
  rw [effect_and_eq,Nat.mod_eq_of_lt hb,Nat.mod_eq_of_lt hc]

theorem effect_shiftl_eq (w a b c:ℕ) (s:State):
    (Instr.shiftl a b c).effect w s =
      some
        { s with
          pc:=s.pc + 1
          mem:=setCell w s.mem a (s.mem (b % 2 ^ w) * 2 ^ s.mem (c % 2 ^ w)) }:=rfl

theorem effect_shiftl {w a b c:ℕ} {s:State} (hb:b < 2 ^ w) (hc:c < 2 ^ w):
    (Instr.shiftl a b c).effect w s =
      some
        { s with
          pc:=s.pc + 1
          mem:=setCell w s.mem a (s.mem b * 2 ^ s.mem c) }:=by
  rw [effect_shiftl_eq,Nat.mod_eq_of_lt hb,Nat.mod_eq_of_lt hc]

theorem effect_jzero_eq (w a l:ℕ) (s:State):
    (Instr.jzero a l).effect w s =
      some { s with pc:=if s.mem (a % 2 ^ w)=0 then l else s.pc + 1 }:=rfl

theorem effect_jzero {w a l:ℕ} {s:State} (ha:a < 2 ^ w):
    (Instr.jzero a l).effect w s =
      some { s with pc:=if s.mem a=0 then l else s.pc + 1 }:=by
  rw [effect_jzero_eq,Nat.mod_eq_of_lt ha]

theorem effect_write_eq (w a:ℕ) (s:State):
    (Instr.write a).effect w s =
      some { s with pc:=s.pc + 1,out:=s.out ++ [s.mem (a % 2 ^ w) % 2 ^ w] }:=rfl

theorem effect_write {w a:ℕ} {s:State} (ha:a < 2 ^ w) (hv:s.mem a < 2 ^ w):
    (Instr.write a).effect w s =
      some { s with pc:=s.pc + 1,out:=s.out ++ [s.mem a] }:=by
  rw [effect_write_eq,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hv]

theorem effect_read_eq (w a:ℕ) (s:State):
    (Instr.read a).effect w s =
      s.inp.head?.map fun v =>
        { s with pc:=s.pc + 1,mem:=setCell w s.mem a v,inp:=s.inp.tail }:=rfl

theorem effect_read {w:ℕ} {s:State} {v:ℕ} {rest:List ℕ} (a:ℕ)
    (h:s.inp=v::rest):
    (Instr.read a).effect w s =
      some { s with pc:=s.pc + 1,mem:=setCell w s.mem a v,inp:=rest }:=by
  rw [effect_read_eq,h]; rfl

theorem step_eq (w:ℕ) (p:Program) (s:State):
    step w p s=p[s.pc]?.bind fun i => i.effect w s:=rfl

@[simp] theorem run_zero (w:ℕ) (p:Program) (s:State):run w p 0 s=some s:=rfl

theorem run_succ (w:ℕ) (p:Program) (t:ℕ) (s:State):
    run w p (t + 1) s=(step w p s).bind (run w p t):=rfl

theorem run_add (w:ℕ) (p:Program) (t t':ℕ) (s:State):
    run w p (t + t') s=(run w p t s).bind (run w p t'):=by
  induction t generalizing s with
  | zero => simp
  | succ t ih =>
      rw [Nat.succ_add,run_succ,run_succ]
      cases h:step w p s with
      | none => simp
      | some s₁ => simpa using ih s₁

theorem run_trans {w:ℕ} {p:Program} {t₁ t₂:ℕ} {s s₁ s₂:State}
    (h₁:run w p t₁ s=some s₁) (h₂:run w p t₂ s₁=some s₂):
    run w p (t₁ + t₂) s=some s₂:=by
  rw [run_add,h₁]; exact h₂

theorem run_one {w:ℕ} {p:Program} {s:State} {ins:Instr} (h:p[s.pc]?=some ins):
    run w p 1 s=ins.effect w s:=by
  rw [show (1:ℕ)=0 + 1 from rfl,run_succ,step_eq,h]
  show (ins.effect w s).bind (run w p 0)=ins.effect w s
  cases ins.effect w s <;> rfl

theorem terminalCost_eq (p:Program) (s:State):
    terminalCost p s=if s.pc < p.length then 1 else 0:=rfl

theorem terminalCost_of_getElem? {p:Program} {s:State} {i:Instr}
    (h:p[s.pc]?=some i):terminalCost p s=1:=by
  rw [terminalCost_eq,if_pos]
  exact List.getElem?_eq_some_iff.mp h |>.1

theorem add_eq_lor_add_land (a b:ℕ):a + b=(a ||| b) + (a &&& b):=by
  induction a using Nat.strong_induction_on generalizing b with
  | _ a ih =>
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · simp
      · have ihh:=ih (a / 2) (Nat.div_lt_self ha (by norm_num)) (b / 2)
        have hor:2 * (a / 2 ||| b / 2) + (a ||| b) % 2=a ||| b:=by
          rw [← Nat.or_div_two]; exact Nat.div_add_mod _ 2
        have hand:2 * (a / 2 &&& b / 2) + (a &&& b) % 2=a &&& b:=by
          rw [← Nat.and_div_two]; exact Nat.div_add_mod _ 2
        have ha2:=Nat.div_add_mod a 2
        have hb2:=Nat.div_add_mod b 2
        have h1:((a ||| b) % 2=1)↔ (a % 2=1∨ b % 2=1):=Nat.or_mod_two_eq_one
        have h2:((a &&& b) % 2=1)↔ (a % 2=1∧ b % 2=1):=Nat.and_mod_two_eq_one
        have h3:=Nat.mod_two_eq_zero_or_one (a ||| b)
        have h4:=Nat.mod_two_eq_zero_or_one (a &&& b)
        have h5:=Nat.mod_two_eq_zero_or_one a
        have h6:=Nat.mod_two_eq_zero_or_one b
        omega

theorem land_le_left (a b:ℕ):Nat.land a b≤ a:=Nat.and_le_left

theorem lor_lt_two_pow {a b n:ℕ} (ha:a < 2 ^ n) (hb:b < 2 ^ n):
    Nat.lor a b < 2 ^ n:=Nat.or_lt_two_pow ha hb

theorem lor_eq_add_sub_land (a b:ℕ):Nat.lor a b=a + (b - Nat.land a b):=by
  have hland:(a &&& b)=Nat.land a b:=rfl
  have hlor:(a ||| b)=Nat.lor a b:=rfl
  have h:=add_eq_lor_add_land a b
  have hb:a &&& b≤ b:=Nat.and_le_right
  rw [hland,hlor] at h
  rw [hland] at hb
  omega

theorem xor_add_land (a b:ℕ):(a ^^^ b) + (a &&& b)=a ||| b:=by
  have hdisj:(a ^^^ b) &&& (a &&& b)=0:=by
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit]
    cases Nat.testBit a i <;> cases Nat.testBit b i <;> simp
  have hor:((a ^^^ b) ||| (a &&& b))=a ||| b:=by
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_or,Nat.testBit_and,Nat.testBit_xor]
    cases Nat.testBit a i <;> cases Nat.testBit b i <;> simp
  rw [add_eq_lor_add_land,hdisj,hor,Nat.add_zero]

theorem xor_eq_sub_add_sub_land (a b:ℕ):
    Nat.xor a b=(a + (b - Nat.land a b)) - Nat.land a b:=by
  have hland:(a &&& b)=Nat.land a b:=rfl
  have hlor:(a ||| b)=Nat.lor a b:=rfl
  have hxor:(a ^^^ b)=Nat.xor a b:=rfl
  have h:=xor_add_land a b
  rw [hland,hlor,hxor] at h
  have h':=lor_eq_add_sub_land a b
  omega

theorem div_two_pow_mod_two_pow {a w:ℕ} (n:ℕ) (ha:a < 2 ^ w):
    a / (2 ^ n % 2 ^ w)=a / 2 ^ n:=by
  rcases lt_or_ge n w with hn | hn
  · rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) hn)]
  · obtain ⟨k,hk⟩:=pow_dvd_pow 2 hn
    have hle:2 ^ w≤ 2 ^ w * k:=by
      rw [← hk]; exact Nat.pow_le_pow_right (by norm_num) hn
    rw [hk,Nat.mul_mod_right,Nat.div_zero,Nat.div_eq_of_lt (lt_of_lt_of_le ha hle)]

def Fits (p:Program) (a:ℕ) (q:Program):Prop:=
  ∀ i,i < q.length→ p[a + i]?=q[i]?

theorem Fits.head {p:Program} {a:ℕ} {ins:Instr} {q:Program}
    (h:Fits p a (ins::q)):p[a]?=some ins:=by
  simpa using h 0 (by simp)

theorem fits_append {p:Program} {a:ℕ} {q r:Program}:
    Fits p a (q ++ r)↔ Fits p a q∧ Fits p (a + q.length) r:=by
  constructor
  · intro h
    refine ⟨fun i hi => ?_,fun i hi => ?_⟩
    · have:=h i (by simp; omega)
      rwa [List.getElem?_append_left hi] at this
    · have:=h (q.length + i) (by simp; omega)
      rw [List.getElem?_append_right (by omega)] at this
      simpa [Nat.add_assoc] using this
  · rintro ⟨h₁,h₂⟩ i hi
    rcases lt_or_ge i q.length with hlt | hge
    · rw [List.getElem?_append_left hlt]; exact h₁ i hlt
    · rw [List.getElem?_append_right hge]
      have:=h₂ (i - q.length) (by simp at hi; omega)
      rwa [Nat.add_assoc,Nat.add_sub_cancel' hge] at this

theorem Fits.congr {p:Program} {a a':ℕ} {q:Program} (h:Fits p a q) (ha:a=a'):
    Fits p a' q:=ha ▸ h

theorem fits_singleton {p:Program} {a:ℕ} {ins:Instr}:
    Fits p a [ins]↔ p[a]?=some ins:=by
  constructor
  · exact fun h => h.head
  · intro h i hi
    have:i=0:=by simp at hi; omega
    subst this
    simpa using h

theorem fits_self (q r:Program):Fits (q ++ r) 0 q:=by
  intro i hi
  simpa using List.getElem?_append_left (l₂:=r) hi

end Lax808846Proofs.Machine

end

section

namespace Lax808846Proofs.Simulation

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Machine

structure Represents (L:Layout) (σ:Env) (s:State):Prop where

  vars:∀ x∈ L.scalars,s.mem (L.varAddr x)=σ.vars x

  arrs:∀ a∈ L.arrays, ∀ i,i < (σ.arrs a).length→
    s.mem (L.arrAddr a i)=(σ.arrs a).getD i 0

  inp:s.inp=σ.inp

  out:s.out=σ.out

structure Reaches (w:ℕ) (p:Program) (L:Layout) (d len:ℕ) (s s':State):Prop where

  steps:∃ t≤ len,run w p t s=some s'

  pc:s'.pc=s.pc + len

  inp:s'.inp=s.inp

  out:s'.out=s.out

  frame:∀ i,i < d∨ L.temps + 2≤ i→ s'.mem i=s.mem i

theorem Reaches.trans {w p L d d' l₁ l₂ s s₁ s₂}
    (h₁:Reaches w p L d l₁ s s₁) (h₂:Reaches w p L d' l₂ s₁ s₂) (hd:d≤ d'):
    Reaches w p L d (l₁ + l₂) s s₂ where
  steps:=by
    obtain ⟨t₁,ht₁,hr₁⟩:=h₁.steps
    obtain ⟨t₂,ht₂,hr₂⟩:=h₂.steps
    exact ⟨t₁ + t₂,by omega,run_trans hr₁ hr₂⟩
  pc:=by rw [h₂.pc,h₁.pc]; omega
  inp:=by rw [h₂.inp,h₁.inp]
  out:=by rw [h₂.out,h₁.out]
  frame i hi:=by
    rw [h₂.frame i (by omega),h₁.frame i hi]

theorem Reaches.congr {w p L d l l' s s'} (h:Reaches w p L d l s s') (hl:l=l'):
    Reaches w p L d l' s s':=hl ▸ h

theorem reaches_write {w:ℕ} {p:Program} {L:Layout} {d a v:ℕ} {s:State} {ins:Instr}
    (hf:p[s.pc]?=some ins)
    (he:ins.effect w s=some { s with pc:=s.pc + 1,mem:=setCell w s.mem a v })
    (haw:a < 2 ^ w) (hlo:d≤ a) (hhi:a≤ L.temps + 1):
    ∃ s',Reaches w p L d 1 s s'∧ s'.mem=setCell w s.mem a v∧ s'.pc=s.pc + 1:=by
  refine ⟨{ s with pc:=s.pc + 1,mem:=setCell w s.mem a v },
    ⟨⟨1,le_refl 1,by rw [run_one hf,he]⟩,rfl,rfl,rfl,fun i hi => ?_⟩,rfl,rfl⟩
  show setCell w s.mem a v i=s.mem i
  exact setCell_of_ne _ _ haw (by omega)

theorem Represents.reaches {w L σ s p d len s'} (h:Represents L σ s)
    (hr:Reaches w p L d len s s'):Represents L σ s' where
  vars x hx:=by rw [hr.frame _ (Or.inr (temps_le_varAddr L x))]; exact h.vars x hx
  arrs a ha i hi:=by
    rw [hr.frame _ (Or.inr (temps_le_arrAddr L a i))]
    exact h.arrs a ha i hi
  inp:=by rw [hr.inp]; exact h.inp
  out:=by rw [hr.out]; exact h.out

theorem Represents.setPc {L σ s} (h:Represents L σ s) (n:ℕ):
    Represents L σ { s with pc:=n }:=
  ⟨h.vars,h.arrs,h.inp,h.out⟩

theorem one_lt_two_pow {L:Layout} {B w:ℕ} (h:L.FitsWords B w):1 < 2 ^ w:=
  lt_of_le_of_lt (Nat.le_add_left 1 L.temps) (L.temps_add_one_lt_two_pow h)

theorem lt_two_pow_of_le_temps {L:Layout} {B w d:ℕ} (h:L.FitsWords B w)
    (hd:d≤ L.temps + 1):d < 2 ^ w:=
  lt_of_le_of_lt hd (L.temps_add_one_lt_two_pow h)

theorem reaches_binCode {w B:ℕ} {p:Program} {L:Layout} {op:Bop} {d m n:ℕ}
    {s:State} (hfit:L.FitsWords B w) (hd:d < L.temps)
    (hn:s.mem d=n) (hm:s.mem (d + 1)=m) (hnB:n < B) (hmB:m < B)
    (hvB:op.apply m n < B) (hfits:Fits p s.pc (binCode op d)):
    ∃ s',Reaches w p L d (binLen op) s s'∧ s'.mem d=op.apply m n:=by
  have hdw:d < 2 ^ w:=lt_two_pow_of_le_temps hfit (by omega)
  have hd1w:d + 1 < 2 ^ w:=lt_two_pow_of_le_temps hfit (by omega)
  have hd2w:d + 2 < 2 ^ w:=lt_two_pow_of_le_temps hfit (by omega)
  have hnw:n < 2 ^ w:=lt_of_lt_of_le hnB hfit.bound
  have hmw:m < 2 ^ w:=lt_of_lt_of_le hmB hfit.bound
  have hvw:op.apply m n < 2 ^ w:=lt_of_lt_of_le hvB hfit.bound
  have hlandw:Nat.land m n < 2 ^ w:=lt_of_le_of_lt (land_le_left m n) hmw
  cases op with
  | add =>
      obtain ⟨s',hr,hmem, -⟩:=reaches_write (L:=L) (d:=d)
        (fits_singleton.mp hfits) (by rw [effect_add hd1w hdw,hm,hn]) hdw (le_refl d)
        (by omega)
      exact ⟨s',hr.congr (by simp [binLen]),
        by rw [hmem]; exact setCell_self _ hdw (by simpa using hvw)⟩
  | sub =>
      obtain ⟨s',hr,hmem, -⟩:=reaches_write (L:=L) (d:=d)
        (fits_singleton.mp hfits) (by rw [effect_sub hd1w hdw,hm,hn]) hdw (le_refl d)
        (by omega)
      exact ⟨s',hr.congr (by simp [binLen]),
        by rw [hmem]; exact setCell_self _ hdw (by simpa using hvw)⟩
  | mul =>
      obtain ⟨s',hr,hmem, -⟩:=reaches_write (L:=L) (d:=d)
        (fits_singleton.mp hfits) (by rw [effect_mul hd1w hdw,hm,hn]) hdw (le_refl d)
        (by omega)
      exact ⟨s',hr.congr (by simp [binLen]),
        by rw [hmem]; exact setCell_self _ hdw (by simpa using hvw)⟩
  | div =>
      obtain ⟨s',hr,hmem, -⟩:=reaches_write (L:=L) (d:=d)
        (fits_singleton.mp hfits) (by rw [effect_div hd1w hdw,hm,hn]) hdw (le_refl d)
        (by omega)
      exact ⟨s',hr.congr (by simp [binLen]),
        by rw [hmem]; exact setCell_self _ hdw (by simpa using hvw)⟩
  | and =>
      obtain ⟨s',hr,hmem, -⟩:=reaches_write (L:=L) (d:=d)
        (fits_singleton.mp hfits) (by rw [effect_and hd1w hdw,hm,hn]) hdw (le_refl d)
        (by omega)
      exact ⟨s',hr.congr (by simp [binLen]),
        by rw [hmem]; exact setCell_self _ hdw (by simpa using hvw)⟩
  | shiftl =>
      obtain ⟨s',hr,hmem, -⟩:=reaches_write (L:=L) (d:=d)
        (fits_singleton.mp hfits) (by rw [effect_shiftl hd1w hdw,hm,hn]) hdw (le_refl d)
        (by omega)
      exact ⟨s',hr.congr (by simp [binLen]),
        by rw [hmem]; exact setCell_self _ hdw (by simpa using hvw)⟩
  | or =>
      rw [show binCode .or d=[Instr.and (d + 2) (d + 1) d] ++
            ([Instr.sub (d + 2) d (d + 2)] ++ [Instr.add d (d + 1) (d + 2)]) from rfl,
        fits_append,fits_append] at hfits
      obtain ⟨hf₁,hf₂,hf₃⟩:=hfits

      obtain ⟨s₁,h₁,hmem₁,hpc₁⟩:=reaches_write (L:=L) (d:=d)
        (fits_singleton.mp hf₁) (by rw [effect_and hd1w hdw,hm,hn]) hd2w (by omega) (by omega)
      have e₁d:s₁.mem d=n:=by rw [hmem₁,setCell_of_ne _ _ hd2w (by omega),hn]
      have e₁d1:s₁.mem (d + 1)=m:=by rw [hmem₁,setCell_of_ne _ _ hd2w (by omega),hm]
      have e₁d2:s₁.mem (d + 2)=Nat.land m n:=by
        rw [hmem₁]; exact setCell_self _ hd2w hlandw

      obtain ⟨s₂,h₂,hmem₂,hpc₂⟩:=reaches_write (L:=L) (d:=d)
        (fits_singleton.mp (by rw [hpc₁]; simpa using hf₂))
        (by rw [effect_sub hdw hd2w,e₁d,e₁d2]) hd2w (by omega) (by omega)
      have e₂d1:s₂.mem (d + 1)=m:=by rw [hmem₂,setCell_of_ne _ _ hd2w (by omega),e₁d1]
      have e₂d2:s₂.mem (d + 2)=n - Nat.land m n:=by
        rw [hmem₂]; exact setCell_self _ hd2w (by omega)

      obtain ⟨s₃,h₃,hmem₃, -⟩:=reaches_write (L:=L) (d:=d)
        (fits_singleton.mp (by rw [hpc₂,hpc₁]; simpa [Nat.add_assoc] using hf₃))
        (by rw [effect_add hd1w hd2w,e₂d1,e₂d2]) hdw (le_refl d) (by omega)
      refine ⟨s₃, ((h₁.trans h₂ (le_refl d)).trans h₃ (le_refl d)).congr (by simp [binLen]), ?_⟩
      rw [hmem₃,setCell_self _ hdw (by rw [← lor_eq_add_sub_land]; simpa using hvw),
        ← lor_eq_add_sub_land]
      rfl
  | xor =>
      rw [show binCode .xor d=[Instr.and (d + 2) (d + 1) d] ++
            ([Instr.sub d d (d + 2)] ++
              ([Instr.add d (d + 1) d] ++ [Instr.sub d d (d + 2)])) from rfl,
        fits_append,fits_append,fits_append] at hfits
      obtain ⟨hf₁,hf₂,hf₃,hf₄⟩:=hfits
      have hlorw:Nat.lor m n < 2 ^ w:=lor_lt_two_pow hmw hnw

      obtain ⟨s₁,h₁,hmem₁,hpc₁⟩:=reaches_write (L:=L) (d:=d)
        (fits_singleton.mp hf₁) (by rw [effect_and hd1w hdw,hm,hn]) hd2w (by omega) (by omega)
      have e₁d:s₁.mem d=n:=by rw [hmem₁,setCell_of_ne _ _ hd2w (by omega),hn]
      have e₁d1:s₁.mem (d + 1)=m:=by rw [hmem₁,setCell_of_ne _ _ hd2w (by omega),hm]
      have e₁d2:s₁.mem (d + 2)=Nat.land m n:=by
        rw [hmem₁]; exact setCell_self _ hd2w hlandw

      obtain ⟨s₂,h₂,hmem₂,hpc₂⟩:=reaches_write (L:=L) (d:=d)
        (fits_singleton.mp (by rw [hpc₁]; simpa using hf₂))
        (by rw [effect_sub hdw hd2w,e₁d,e₁d2]) hdw (le_refl d) (by omega)
      have e₂d:s₂.mem d=n - Nat.land m n:=by
        rw [hmem₂]; exact setCell_self _ hdw (by omega)
      have e₂d1:s₂.mem (d + 1)=m:=by rw [hmem₂,setCell_of_ne _ _ hdw (by omega),e₁d1]
      have e₂d2:s₂.mem (d + 2)=Nat.land m n:=by
        rw [hmem₂,setCell_of_ne _ _ hdw (by omega),e₁d2]

      obtain ⟨s₃,h₃,hmem₃,hpc₃⟩:=reaches_write (L:=L) (d:=d)
        (fits_singleton.mp (by rw [hpc₂,hpc₁]; simpa [Nat.add_assoc] using hf₃))
        (by rw [effect_add hd1w hdw,e₂d1,e₂d]) hdw (le_refl d) (by omega)
      have e₃d:s₃.mem d=Nat.lor m n:=by
        rw [hmem₃,setCell_self _ hdw (by rw [← lor_eq_add_sub_land]; exact hlorw),
          ← lor_eq_add_sub_land]
      have e₃d2:s₃.mem (d + 2)=Nat.land m n:=by
        rw [hmem₃,setCell_of_ne _ _ hdw (by omega),e₂d2]

      obtain ⟨s₄,h₄,hmem₄, -⟩:=reaches_write (L:=L) (d:=d)
        (fits_singleton.mp (by rw [hpc₃,hpc₂,hpc₁]; simpa [Nat.add_assoc] using hf₄))
        (by rw [effect_sub hdw hd2w,e₃d,e₃d2]) hdw (le_refl d) (by omega)
      refine ⟨s₄, (((h₁.trans h₂ (le_refl d)).trans h₃ (le_refl d)).trans h₄
        (le_refl d)).congr (by simp [binLen]), ?_⟩
      have hxor:Nat.lor m n - Nat.land m n=Nat.xor m n:=by
        rw [xor_eq_sub_add_sub_land,lor_eq_add_sub_land]
      rw [hmem₄,setCell_self _ hdw (by rw [hxor]; simpa using hvw),hxor]
      rfl
  | shiftr =>
      rw [show binCode .shiftr d=[Instr.set (d + 2) 1] ++
            ([Instr.shiftl (d + 2) (d + 2) d] ++ [Instr.div d (d + 1) (d + 2)]) from rfl,
        fits_append,fits_append] at hfits
      obtain ⟨hf₁,hf₂,hf₃⟩:=hfits
      have h1w:1 < 2 ^ w:=one_lt_two_pow hfit

      obtain ⟨s₁,h₁,hmem₁,hpc₁⟩:=reaches_write (L:=L) (d:=d)
        (fits_singleton.mp hf₁) (effect_set w (d + 2) 1 s) hd2w (by omega) (by omega)
      have e₁d:s₁.mem d=n:=by rw [hmem₁,setCell_of_ne _ _ hd2w (by omega),hn]
      have e₁d1:s₁.mem (d + 1)=m:=by rw [hmem₁,setCell_of_ne _ _ hd2w (by omega),hm]
      have e₁d2:s₁.mem (d + 2)=1:=by rw [hmem₁]; exact setCell_self _ hd2w h1w

      obtain ⟨s₂,h₂,hmem₂,hpc₂⟩:=reaches_write (L:=L) (d:=d)
        (fits_singleton.mp (by rw [hpc₁]; simpa using hf₂))
        (by rw [effect_shiftl hd2w hdw,e₁d,e₁d2]) hd2w (by omega) (by omega)
      have e₂d1:s₂.mem (d + 1)=m:=by rw [hmem₂,setCell_of_ne _ _ hd2w (by omega),e₁d1]
      have e₂d2:s₂.mem (d + 2)=2 ^ n % 2 ^ w:=by
        rw [hmem₂,setCell_self_mod _ _ hd2w,Nat.one_mul]

      obtain ⟨s₃,h₃,hmem₃, -⟩:=reaches_write (L:=L) (d:=d)
        (fits_singleton.mp (by rw [hpc₂,hpc₁]; simpa [Nat.add_assoc] using hf₃))
        (by rw [effect_div hd1w hd2w,e₂d1,e₂d2]) hdw (le_refl d) (by omega)
      refine ⟨s₃, ((h₁.trans h₂ (le_refl d)).trans h₃ (le_refl d)).congr (by simp [binLen]), ?_⟩
      rw [hmem₃,div_two_pow_mod_two_pow n hmw,
        setCell_self _ hdw (by simpa using hvw)]
      rfl

theorem reaches_idxCode {w B:ℕ} {p:Program} {L:Layout} {a:String} {d k:ℕ}
    {s:State} (hfit:L.FitsWords B w) (ha:a∈ L.arrays) (hd:d < L.temps)
    (hk:s.mem d=k) (hkB:k < B) (hfits:Fits p s.pc (L.idxCode a d)):
    ∃ s',Reaches w p L d L.idxLen s s'∧ s'.mem d=L.arrAddr a k:=by
  have hdw:d < 2 ^ w:=lt_two_pow_of_le_temps hfit (by omega)
  have hd1w:d + 1 < 2 ^ w:=lt_two_pow_of_le_temps hfit (by omega)
  have hqw:L.arrays.length < 2 ^ w:=L.arrays_length_lt_two_pow hfit
  have hbw:L.arrBase a < 2 ^ w:=L.arrBase_lt_two_pow hfit ha
  have haddr:L.arrAddr a k < 2 ^ w:=L.arrAddr_lt_two_pow hfit ha hkB
  have hmulw:k * L.arrays.length < 2 ^ w:=by
    have:=L.mul_le_arrAddr a k
    have:L.arrays.length * k=k * L.arrays.length:=Nat.mul_comm _ _
    omega
  rw [show L.idxCode a d=[Instr.set (d + 1) L.arrays.length] ++
        ([Instr.mul d d (d + 1)] ++
          ([Instr.set (d + 1) (L.arrBase a)] ++ [Instr.add d d (d + 1)])) from rfl,
    fits_append,fits_append,fits_append] at hfits
  obtain ⟨hf₁,hf₂,hf₃,hf₄⟩:=hfits

  obtain ⟨s₁,h₁,hmem₁,hpc₁⟩:=reaches_write (L:=L) (d:=d)
    (fits_singleton.mp hf₁) (effect_set w (d + 1) L.arrays.length s) hd1w (by omega) (by omega)
  have e₁d:s₁.mem d=k:=by rw [hmem₁,setCell_of_ne _ _ hd1w (by omega),hk]
  have e₁d1:s₁.mem (d + 1)=L.arrays.length:=by
    rw [hmem₁]; exact setCell_self _ hd1w hqw

  obtain ⟨s₂,h₂,hmem₂,hpc₂⟩:=reaches_write (L:=L) (d:=d)
    (fits_singleton.mp (by rw [hpc₁]; simpa using hf₂))
    (by rw [effect_mul hdw hd1w,e₁d,e₁d1]) hdw (le_refl d) (by omega)
  have e₂d:s₂.mem d=k * L.arrays.length:=by
    rw [hmem₂]; exact setCell_self _ hdw hmulw

  obtain ⟨s₃,h₃,hmem₃,hpc₃⟩:=reaches_write (L:=L) (d:=d)
    (fits_singleton.mp (by rw [hpc₂,hpc₁]; simpa [Nat.add_assoc] using hf₃))
    (effect_set w (d + 1) (L.arrBase a) s₂) hd1w (by omega) (by omega)
  have e₃d:s₃.mem d=k * L.arrays.length:=by
    rw [hmem₃,setCell_of_ne _ _ hd1w (by omega),e₂d]
  have e₃d1:s₃.mem (d + 1)=L.arrBase a:=by
    rw [hmem₃]; exact setCell_self _ hd1w hbw

  obtain ⟨s₄,h₄,hmem₄, -⟩:=reaches_write (L:=L) (d:=d)
    (fits_singleton.mp (by rw [hpc₃,hpc₂,hpc₁]; simpa [Nat.add_assoc] using hf₄))
    (by rw [effect_add hdw hd1w,e₃d,e₃d1]) hdw (le_refl d) (by omega)
  have hsum:k * L.arrays.length + L.arrBase a=L.arrAddr a k:=by
    simp only [Layout.arrAddr]; rw [Nat.mul_comm]; omega
  refine ⟨s₄, (((h₁.trans h₂ (le_refl d)).trans h₃ (le_refl d)).trans h₄
    (le_refl d)).congr (by simp [Layout.idxLen]), ?_⟩
  rw [hmem₄,hsum]
  exact setCell_self _ hdw haddr

theorem compileExpr_correct {L:Layout} {B w:ℕ} {σ:Env} {p:Program}
    (hfit:L.FitsWords B w) (e:Expr):
    ∀ (d v:ℕ) (s:State),d≤ L.temps + 1→ Expr.Ok L e d→ e.evalB B σ=some v→
      Represents L σ s→ Fits p s.pc (compileExpr L e d)→
      ∃ s',Reaches w p L d (esize L e) s s'∧ s'.mem d=v:=by
  induction e with
  | lit n =>
      intro d v s hdt _ hv _ hfits
      simp only [Expr.evalB] at hv
      rw [fit_eq_some] at hv
      obtain ⟨rfl,hn⟩:=hv
      have hdw:d < 2 ^ w:=lt_two_pow_of_le_temps hfit hdt
      obtain ⟨s',hr,hmem, -⟩:=reaches_write (L:=L) (d:=d)
        (fits_singleton.mp hfits) (effect_set w d v s) hdw (le_refl d) hdt
      exact ⟨s',hr.congr (by simp [esize]),
        by rw [hmem]; exact setCell_self _ hdw (lt_of_lt_of_le hn hfit.bound)⟩
  | var x =>
      intro d v s hdt hok hv hrep hfits
      simp only [Expr.evalB] at hv
      rw [fit_eq_some] at hv
      obtain ⟨rfl,hn⟩:=hv
      have hdw:d < 2 ^ w:=lt_two_pow_of_le_temps hfit hdt
      have hxw:L.varAddr x < 2 ^ w:=L.varAddr_lt_two_pow hfit hok
      have hxt:L.temps + 2≤ L.varAddr x:=temps_le_varAddr L x
      rw [show compileExpr L (.var x) d
           =[Instr.set d (L.varAddr x)] ++ [Instr.load d d] from rfl,
        fits_append] at hfits
      obtain ⟨hf₁,hf₂⟩:=hfits
      obtain ⟨s₁,h₁,hmem₁,hpc₁⟩:=reaches_write (L:=L) (d:=d)
        (fits_singleton.mp hf₁) (effect_set w d (L.varAddr x) s) hdw (le_refl d) hdt
      have e₁d:s₁.mem d=L.varAddr x:=by rw [hmem₁]; exact setCell_self _ hdw hxw
      have e₁x:s₁.mem (L.varAddr x)=σ.vars x:=by
        rw [hmem₁,setCell_of_ne _ _ hdw (by omega)]; exact hrep.vars x hok
      obtain ⟨s₂,h₂,hmem₂, -⟩:=reaches_write (L:=L) (d:=d)
        (fits_singleton.mp (by rw [hpc₁]; simpa using hf₂))
        (by rw [effect_load hdw (by rw [e₁d]; exact hxw),e₁d,e₁x]) hdw (le_refl d) hdt
      exact ⟨s₂, (h₁.trans h₂ (le_refl d)).congr (by simp [esize]),
        by rw [hmem₂]; exact setCell_self _ hdw (lt_of_lt_of_le hn hfit.bound)⟩
  | get a i ih =>
      intro d v s hdt hok hv hrep hfits
      obtain ⟨ha,hoki,hd⟩:=hok
      simp only [Expr.evalB] at hv
      rw [Option.bind_eq_some_iff] at hv
      obtain ⟨k,hk,hv⟩:=hv
      rw [Option.bind_eq_some_iff] at hv
      obtain ⟨u,hu,hv⟩:=hv
      rw [fit_eq_some] at hv
      obtain ⟨rfl,hvB⟩:=hv
      have hkB:k < B:=Expr.lt_of_evalB hk
      have hdw:d < 2 ^ w:=lt_two_pow_of_le_temps hfit hdt
      have haddr:L.arrAddr a k < 2 ^ w:=L.arrAddr_lt_two_pow hfit ha hkB
      have hat:L.temps + 2≤ L.arrAddr a k:=temps_le_arrAddr L a k
      rw [List.getElem?_eq_some_iff] at hu
      obtain ⟨hklt,hkv⟩:=hu
      rw [show compileExpr L (.get a i) d
           =compileExpr L i d ++ (L.idxCode a d ++ [Instr.load d d]) from by
          simp [compileExpr,List.append_assoc],
          fits_append,fits_append] at hfits
      obtain ⟨hf₁,hf₂,hf₃⟩:=hfits
      obtain ⟨s₁,h₁,e₁d⟩:=ih d k s hdt hoki hk hrep hf₁
      obtain ⟨s₂,h₂,e₂d⟩:=reaches_idxCode hfit ha hd e₁d hkB
        (by rw [h₁.pc]; simpa using hf₂)
      have e₂a:s₂.mem (L.arrAddr a k)=v:=by
        rw [h₂.frame _ (Or.inr hat),h₁.frame _ (Or.inr hat),hrep.arrs a ha k hklt,
          List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hklt,hkv]
        rfl
      obtain ⟨s₃,h₃,hmem₃, -⟩:=reaches_write (L:=L) (d:=d)
        (fits_singleton.mp (by rw [h₂.pc,h₁.pc]; simpa [Nat.add_assoc] using hf₃))
        (by rw [effect_load hdw (by rw [e₂d]; exact haddr),e₂d,e₂a]) hdw (le_refl d) hdt
      exact ⟨s₃, ((h₁.trans h₂ (le_refl d)).trans h₃ (le_refl d)).congr (by simp [esize]),
        by rw [hmem₃]; exact setCell_self _ hdw (lt_of_lt_of_le hvB hfit.bound)⟩
  | bin op e f ihe ihf =>
      intro d v s hdt hok hv hrep hfits
      obtain ⟨hokf,hoke,hd⟩:=hok
      simp only [Expr.evalB] at hv
      rw [Option.bind_eq_some_iff] at hv
      obtain ⟨m,hm,hv⟩:=hv
      rw [Option.bind_eq_some_iff] at hv
      obtain ⟨n,hn,hv⟩:=hv
      rw [fit_eq_some] at hv
      obtain ⟨rfl,hvB⟩:=hv
      have hmB:m < B:=Expr.lt_of_evalB hm
      have hnB:n < B:=Expr.lt_of_evalB hn
      rw [show compileExpr L (.bin op e f) d
           =compileExpr L f d ++ (compileExpr L e (d + 1) ++ binCode op d) from by
          simp [compileExpr,List.append_assoc],
          fits_append,fits_append] at hfits
      obtain ⟨hf₁,hf₂,hf₃⟩:=hfits
      obtain ⟨s₁,h₁,e₁d⟩:=ihf d n s hdt hokf hn hrep hf₁
      obtain ⟨s₂,h₂,e₂d1⟩:=ihe (d + 1) m s₁ (by omega) hoke hm
        (hrep.reaches h₁) (by rw [h₁.pc]; simpa using hf₂)
      have e₂d:s₂.mem d=n:=by rw [h₂.frame d (Or.inl (by omega)),e₁d]
      obtain ⟨s₃,h₃,e₃d⟩:=reaches_binCode hfit hd e₂d e₂d1 hnB hmB hvB
        (by rw [h₂.pc,h₁.pc]; simpa [Nat.add_assoc] using hf₃)
      exact ⟨s₃, ((h₁.trans h₂ (by omega)).trans h₃ (le_refl d)).congr (by simp [esize]),e₃d⟩

theorem compileCond_correct {L:Layout} {B w:ℕ} {σ:Env} {p:Program} {b:Cond} {d:ℕ}
    {r:Bool} {s:State} (hfit:L.FitsWords B w) (hdt:d≤ L.temps + 1)
    (hok:Cond.Ok L b d) (hv:b.evalB B σ=some r) (hrep:Represents L σ s)
    (hfits:Fits p s.pc (compileCond L b d)):
    ∃ (s':State) (v:ℕ),Reaches w p L d (bsize L b) s s'∧ s'.mem d=v∧
      (v=0↔ r=true):=by
  obtain ⟨v,hev,hiff⟩:=condExpr_evalB hfit.one_lt hv
  obtain ⟨s',hr,hval⟩:=compileExpr_correct hfit (condExpr b) d v s hdt hok hev hrep hfits
  exact ⟨s',v,hr,hval,hiff⟩

theorem esize_le_size (L:Layout) (e:Expr):esize L e≤ 5 * e.size:=by
  induction e with
  | lit n => simp [esize,Expr.size]
  | var x => simp [esize,Expr.size]
  | get a i ih =>
      simp only [esize,Expr.size,Layout.idxLen,Nat.mul_add,Nat.mul_one]
      omega
  | bin op e f ihe ihf =>
      have:=binLen_le_four op
      simp only [esize,Expr.size,Nat.mul_add,Nat.mul_one]
      omega

theorem esize_le (L:Layout) (e:Expr):esize L e≤ L.const * e.size:=
  le_trans (esize_le_size L e)
    (Nat.mul_le_mul_right _ (by simp only [Layout.const]; omega))

theorem bsize_le (L:Layout) (b:Cond):bsize L b≤ L.const * b.size:=by
  cases b with
  | eq e f =>
      have he:=esize_le_size L e
      have hf:=esize_le_size L f
      have h1:2 * (5 * e.size)≤ L.const * e.size:=by
        rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (by simp only [Layout.const]; omega)
      have h2:2 * (5 * f.size)≤ L.const * f.size:=by
        rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (by simp only [Layout.const]; omega)
      have hc:(10:ℕ)≤ L.const:=by simp only [Layout.const]; omega
      simp only [bsize,condExpr,esize,binLen,Cond.size,Nat.mul_add,Nat.mul_one]
      omega
  | lt e f =>
      have he:=esize_le_size L e
      have hf:=esize_le_size L f
      have h1:5 * e.size≤ L.const * e.size:=
        Nat.mul_le_mul_right _ (by simp only [Layout.const]; omega)
      have h2:5 * f.size≤ L.const * f.size:=
        Nat.mul_le_mul_right _ (by simp only [Layout.const]; omega)
      have hc:(10:ℕ)≤ L.const:=by simp only [Layout.const]; omega
      simp only [bsize,condExpr,esize,binLen,Cond.size,Nat.mul_add,Nat.mul_one]
      omega

theorem idxLen_le_const (L:Layout):L.idxLen + 1≤ L.const:=by
  simp only [Layout.const,Layout.idxLen]; omega

theorem one_le_const (L:Layout):1≤ L.const:=by simp only [Layout.const]; omega

theorem two_le_const (L:Layout):2≤ L.const:=by simp only [Layout.const]; omega

theorem run_jump {w:ℕ} {p:Program} {s:State} {l:ℕ}
    (h:p[s.pc]?=some (Instr.jump l)):
    run w p 1 s=some { s with pc:=l }:=by rw [run_one h]; rfl

theorem run_jzero {w:ℕ} {p:Program} {s:State} {a l:ℕ} (ha:a < 2 ^ w)
    (h:p[s.pc]?=some (Instr.jzero a l)):
    run w p 1 s=some { s with pc:=if s.mem a=0 then l else s.pc + 1 }:=by
  rw [run_one h,effect_jzero ha]

theorem compile_correct {L:Layout} {B w:ℕ} {p:Program} {c:Com} {σ σ':Env} {k:ℕ}
    (hfit:L.FitsWords B w) (hbs:BigStepB B c σ σ' k):
    Com.Ok L c→ σ.InpBounded B→ ∀ (a:ℕ) (s:State),s.pc=a→ Represents L σ s→
      Fits p a (compile L c a)→
      ∃ (t:ℕ) (s':State),t≤ L.const * k∧ run w p t s=some s'∧
        s'.pc=a + size L c∧ Represents L σ' s':=by
  have hzw:(0:ℕ) < 2 ^ w:=two_pow_pos w
  have h1w:1 < 2 ^ w:=one_lt_two_pow hfit
  induction hbs with
  | @skip σ =>
      intro _ _ a s hpc hrep _
      exact ⟨0,s,by simp,rfl,by simp [size,hpc],hrep⟩
  | @assign σ x e v hev =>
      intro hok _ a s hpc hrep hfits
      obtain ⟨hx,hoke⟩:=hok
      have hvw:v < 2 ^ w:=lt_of_lt_of_le (Expr.lt_of_evalB hev) hfit.bound
      have hxw:L.varAddr x < 2 ^ w:=L.varAddr_lt_two_pow hfit hx
      have hxt:L.temps + 2≤ L.varAddr x:=temps_le_varAddr L x
      rw [show compile L (.assign x e) a
           =compileExpr L e 0 ++ ([Instr.set 1 (L.varAddr x)] ++ [Instr.store 1 0]) from by
          simp [compile],fits_append,fits_append] at hfits
      obtain ⟨hf₁,hf₂,hf₃⟩:=hfits
      obtain ⟨s₁,h₁,e₁0⟩:=
        compileExpr_correct hfit e 0 v s (by omega) hoke hev hrep (hf₁.congr hpc.symm)
      obtain ⟨s₂,h₂,hmem₂,hpc₂⟩:=reaches_write (L:=L) (d:=0)
        (fits_singleton.mp (by rw [h₁.pc,hpc]; simpa using hf₂))
        (effect_set w 1 (L.varAddr x) s₁) h1w (by omega) (by omega)
      have e₂0:s₂.mem 0=v:=by rw [hmem₂,setCell_of_ne _ _ h1w (by omega),e₁0]
      have e₂1:s₂.mem 1=L.varAddr x:=by rw [hmem₂]; exact setCell_self _ h1w hxw
      have hf₃':p[s₂.pc]?=some (Instr.store 1 0):=by
        rw [hpc₂,h₁.pc,hpc]
        exact fits_singleton.mp (by simpa [Nat.add_assoc] using hf₃)
      obtain ⟨t₁,ht₁,hr₁⟩:=(h₁.trans h₂ (le_refl 0)).steps
      refine ⟨t₁ + 1,_, ?_,run_trans hr₁ (by rw [run_one hf₃',effect_store h1w hzw]), ?_, ?_⟩
      · simp only [Nat.mul_add,Nat.mul_one]
        have:=esize_le L e
        have:=two_le_const L
        omega
      · show s₂.pc + 1=a + size L (.assign x e)
        rw [hpc₂,h₁.pc,hpc]; simp [size]; omega
      · refine ⟨fun y hy => ?_,fun b hb i hi => ?_, ?_, ?_⟩
        · show setCell w s₂.mem (s₂.mem 1) (s₂.mem 0) (L.varAddr y)=_
          rw [e₂0,e₂1]
          by_cases hxy:y=x
          · subst hxy
            rw [setCell_self _ hxw hvw]
            simp [Env.setVar]
          · rw [setCell_of_ne _ _ hxw (fun hc => hxy (varAddr_inj L hy hx hc)),
              h₂.frame _ (Or.inr (temps_le_varAddr L y)),
              h₁.frame _ (Or.inr (temps_le_varAddr L y)),hrep.vars y hy]
            simp [Env.setVar,hxy]
        · show setCell w s₂.mem (s₂.mem 1) (s₂.mem 0) (L.arrAddr b i)=_
          rw [e₂0,e₂1,setCell_of_ne _ _ hxw (fun hc => varAddr_ne_arrAddr L hx i hc.symm),
            h₂.frame _ (Or.inr (temps_le_arrAddr L b i)),
            h₁.frame _ (Or.inr (temps_le_arrAddr L b i))]
          exact hrep.arrs b hb i hi
        · show s₂.inp=_; rw [h₂.inp,h₁.inp]; exact hrep.inp
        · show s₂.out=_; rw [h₂.out,h₁.out]; exact hrep.out
  | @seq c d σ σ₁ σ₂ k k' hbs₁ _ ih ih' =>
      intro hok hinp a s hpc hrep hfits
      obtain ⟨hokc,hokd⟩:=hok
      rw [show compile L (.seq c d) a=compile L c a ++ compile L d (a + size L c) from rfl,
        fits_append] at hfits
      obtain ⟨hf₁,hf₂⟩:=hfits
      obtain ⟨t₁,s₁,ht₁,hr₁,hpc₁,hrep₁⟩:=ih hokc hinp a s hpc hrep hf₁
      obtain ⟨t₂,s₂,ht₂,hr₂,hpc₂,hrep₂⟩:=
        ih' hokd (hbs₁.inpBounded hinp) (a + size L c) s₁ hpc₁ hrep₁ (by simpa using hf₂)
      refine ⟨t₁ + t₂,s₂, ?_,run_trans hr₁ hr₂, ?_,hrep₂⟩
      · simp only [Nat.mul_add]; omega
      · rw [hpc₂]; simp [size]; omega
  | @read σ x v rest hinp' =>
      intro hok hinp a s hpc hrep hfits
      have hvB:v < B:=hinp v (by rw [hinp']; exact List.mem_cons_self ..)
      have hvw:v < 2 ^ w:=lt_of_lt_of_le hvB hfit.bound
      have hxw:L.varAddr x < 2 ^ w:=L.varAddr_lt_two_pow hfit hok
      have hs:s.inp=v::rest:=by rw [hrep.inp]; exact hinp'
      have hf:p[s.pc]?=some (Instr.read (L.varAddr x)):=
        fits_singleton.mp (by rw [hpc]; simpa [compile] using hfits)
      refine ⟨1,_, ?_,by rw [run_one hf,effect_read _ hs], ?_, ?_⟩
      · simp only [Nat.mul_one]; exact one_le_const L
      · show s.pc + 1=a + size L (.read x); rw [hpc]; simp [size]
      · refine ⟨fun y hy => ?_,fun b hb i hi => ?_,rfl, ?_⟩
        · show setCell w s.mem (L.varAddr x) v (L.varAddr y)=_
          by_cases hxy:y=x
          · subst hxy; rw [setCell_self _ hxw hvw]; simp [Env.setVar]
          · rw [setCell_of_ne _ _ hxw (fun hc => hxy (varAddr_inj L hy hok hc)),hrep.vars y hy]
            simp [Env.setVar,hxy]
        · show setCell w s.mem (L.varAddr x) v (L.arrAddr b i)=_
          rw [setCell_of_ne _ _ hxw (fun hc => varAddr_ne_arrAddr L hok i hc.symm)]
          exact hrep.arrs b hb i hi
        · show s.out=_; exact hrep.out
  | @write σ e v hev =>
      intro hok _ a s hpc hrep hfits
      obtain ⟨hoke,htemps⟩:=hok
      have hvw:v < 2 ^ w:=lt_of_lt_of_le (Expr.lt_of_evalB hev) hfit.bound
      rw [show compile L (.write e) a=compileExpr L e 0 ++ [Instr.write 0] from rfl,
        fits_append] at hfits
      obtain ⟨hf₁,hf₂⟩:=hfits
      obtain ⟨s₁,h₁,e₁0⟩:=
        compileExpr_correct hfit e 0 v s (by omega) hoke hev hrep (hf₁.congr hpc.symm)
      obtain ⟨t₁,ht₁,hr₁⟩:=h₁.steps
      have hf₂':p[s₁.pc]?=some (Instr.write 0):=by
        rw [h₁.pc,hpc]; exact fits_singleton.mp (by simpa using hf₂)
      refine ⟨t₁ + 1,_, ?_,
        run_trans hr₁ (by rw [run_one hf₂',effect_write hzw (by rw [e₁0]; exact hvw)]), ?_, ?_⟩
      · simp only [Nat.mul_add,Nat.mul_one]
        have:=esize_le L e
        have:=one_le_const L
        omega
      · show s₁.pc + 1=a + size L (.write e)
        rw [h₁.pc,hpc]; simp [size]; omega
      · refine ⟨fun y hy => ?_,fun b hb i hi => ?_, ?_, ?_⟩
        · show s₁.mem (L.varAddr y)=_
          rw [h₁.frame _ (Or.inr (temps_le_varAddr L y))]; exact hrep.vars y hy
        · show s₁.mem (L.arrAddr b i)=_
          rw [h₁.frame _ (Or.inr (temps_le_arrAddr L b i))]; exact hrep.arrs b hb i hi
        · show s₁.inp=_; rw [h₁.inp]; exact hrep.inp
        · show s₁.out ++ [s₁.mem 0]=_
          rw [e₁0,h₁.out,hrep.out]
  | @store σ arr i e kk v hi hev hk =>
      intro hok _ a s hpc hrep hfits
      obtain ⟨ha,hoki,hoke,htemps⟩:=hok
      have hkkB:kk < B:=Expr.lt_of_evalB hi
      have hvw:v < 2 ^ w:=lt_of_lt_of_le (Expr.lt_of_evalB hev) hfit.bound
      have haddr:L.arrAddr arr kk < 2 ^ w:=L.arrAddr_lt_two_pow hfit ha hkkB
      rw [show compile L (.store arr i e) a
           =compileExpr L i 0 ++ (L.idxCode arr 0 ++
                (compileExpr L e 1 ++ [Instr.store 0 1])) from by
          simp [compile,List.append_assoc],fits_append,fits_append,fits_append] at hfits
      obtain ⟨hf₁,hf₂,hf₃,hf₄⟩:=hfits
      obtain ⟨s₁,h₁,e₁0⟩:=
        compileExpr_correct hfit i 0 kk s (by omega) hoki hi hrep (hf₁.congr hpc.symm)
      obtain ⟨s₂,h₂,e₂0⟩:=reaches_idxCode hfit ha htemps e₁0 hkkB
        (by rw [h₁.pc,hpc]; simpa using hf₂)
      obtain ⟨s₃,h₃,e₃1⟩:=compileExpr_correct hfit e 1 v s₂ (by omega) hoke hev
        ((hrep.reaches h₁).reaches h₂)
        (by rw [h₂.pc,h₁.pc,hpc]; simpa [Nat.add_assoc] using hf₃)
      have e₃0:s₃.mem 0=L.arrAddr arr kk:=by
        rw [h₃.frame 0 (Or.inl (by omega))]; exact e₂0
      have hf₄':p[s₃.pc]?=some (Instr.store 0 1):=by
        rw [h₃.pc,h₂.pc,h₁.pc,hpc]
        exact fits_singleton.mp (by simpa [Nat.add_assoc] using hf₄)
      obtain ⟨t₁,ht₁,hr₁⟩:=((h₁.trans h₂ (le_refl 0)).trans h₃ (by omega)).steps
      refine ⟨t₁ + 1,_, ?_,
        run_trans hr₁ (by rw [run_one hf₄',effect_store hzw h1w]), ?_, ?_⟩
      · simp only [Nat.mul_add,Nat.mul_one]
        have:=esize_le L i
        have:=esize_le L e
        have:=idxLen_le_const L
        omega
      · show s₃.pc + 1=a + size L (.store arr i e)
        rw [h₃.pc,h₂.pc,h₁.pc,hpc]; simp [size]; omega
      · have hlen:((σ.arrs arr).set kk v).length=(σ.arrs arr).length:=by simp
        refine ⟨fun y hy => ?_,fun b hb j hj => ?_, ?_, ?_⟩
        · show setCell w s₃.mem (s₃.mem 0) (s₃.mem 1) (L.varAddr y)=_
          rw [e₃0,e₃1,setCell_of_ne _ _ haddr (fun hc => varAddr_ne_arrAddr L hy kk hc),
            h₃.frame _ (Or.inr (temps_le_varAddr L y)),
            h₂.frame _ (Or.inr (temps_le_varAddr L y)),
            h₁.frame _ (Or.inr (temps_le_varAddr L y))]
          exact hrep.vars y hy
        · show setCell w s₃.mem (s₃.mem 0) (s₃.mem 1) (L.arrAddr b j)=_
          have hjlen:j < (σ.arrs b).length:=by
            by_cases hb':b=arr
            · subst hb'; simpa [Env.setArr] using hj
            · simpa [Env.setArr,hb'] using hj
          rw [e₃0,e₃1]
          by_cases hcase:b=arr∧ j=kk
          · obtain ⟨rfl,rfl⟩:=hcase
            rw [setCell_self _ haddr hvw]
            simp [Env.setArr,List.getD_eq_getElem?_getD,hk]
          · have hne:L.arrAddr b j ≠ L.arrAddr arr kk:=fun hc => by
              obtain ⟨rfl,rfl⟩:=arrAddr_inj L hb ha hc
              exact hcase ⟨rfl,rfl⟩
            rw [setCell_of_ne _ _ haddr hne,
              h₃.frame _ (Or.inr (temps_le_arrAddr L b j)),
              h₂.frame _ (Or.inr (temps_le_arrAddr L b j)),
              h₁.frame _ (Or.inr (temps_le_arrAddr L b j)),hrep.arrs b hb j hjlen]
            by_cases hb':b=arr
            · subst hb'
              have hjk:j ≠ kk:=fun hc => hcase ⟨rfl,hc⟩
              simp [Env.setArr,List.getD_eq_getElem?_getD,Ne.symm hjk]
            · simp [Env.setArr,hb']
        · show s₃.inp=_
          rw [h₃.inp,h₂.inp,h₁.inp]; exact hrep.inp
        · show s₃.out=_
          rw [h₃.out,h₂.out,h₁.out]; exact hrep.out
  | @ite_true b c d σ σ' k hb _ ih =>
      intro hok hinp a s hpc hrep hfits
      obtain ⟨hokb,hokc,hokd⟩:=hok
      rw [show compile L (.ite b c d) a
           =compileCond L b 0 ++ ([Instr.jzero 0 (a + bsize L b + 1 + size L d + 1)] ++
                (compile L d (a + bsize L b + 1) ++
                  ([Instr.jump (a + bsize L b + 1 + size L d + 1 + size L c)] ++
                    compile L c (a + bsize L b + 1 + size L d + 1)))) from by
          simp [compile,List.append_assoc],
        fits_append,fits_append,fits_append,fits_append] at hfits
      obtain ⟨hf₁,hf₂,hf₃,hf₄,hf₅⟩:=hfits
      obtain ⟨s₁,v,h₁,e₁0,hv⟩:=
        compileCond_correct hfit (by omega) hokb hb hrep (hf₁.congr hpc.symm)
      obtain ⟨t₁,ht₁,hr₁⟩:=h₁.steps
      have hzero:s₁.mem 0=0:=by rw [e₁0]; exact hv.mpr rfl
      have hf₂':p[s₁.pc]?=some (Instr.jzero 0 (a + bsize L b + 1 + size L d + 1)):=by
        rw [h₁.pc,hpc]; exact fits_singleton.mp (by simpa using hf₂)
      have hjz:run w p 1 s₁=some { s₁ with pc:=a + bsize L b + 1 + size L d + 1 }:=by
        rw [run_jzero hzw hf₂',hzero]; simp
      obtain ⟨t₂,s₂,ht₂,hr₂,hpc₂,hrep₂⟩:=
        ih hokc hinp (a + bsize L b + 1 + size L d + 1)
          { s₁ with pc:=a + bsize L b + 1 + size L d + 1 } rfl ((hrep.reaches h₁).setPc _)
          (by simpa [Nat.add_assoc] using hf₅)
      refine ⟨t₁ + 1 + t₂,s₂, ?_,run_trans (run_trans hr₁ hjz) hr₂, ?_,hrep₂⟩
      · simp only [Nat.mul_add,Nat.mul_one]
        have:=bsize_le L b
        have:=one_le_const L
        omega
      · rw [hpc₂]; simp [size]; omega
  | @ite_false b c d σ σ' k hb _ ih =>
      intro hok hinp a s hpc hrep hfits
      obtain ⟨hokb,hokc,hokd⟩:=hok
      rw [show compile L (.ite b c d) a
           =compileCond L b 0 ++ ([Instr.jzero 0 (a + bsize L b + 1 + size L d + 1)] ++
                (compile L d (a + bsize L b + 1) ++
                  ([Instr.jump (a + bsize L b + 1 + size L d + 1 + size L c)] ++
                    compile L c (a + bsize L b + 1 + size L d + 1)))) from by
          simp [compile,List.append_assoc],
        fits_append,fits_append,fits_append,fits_append] at hfits
      obtain ⟨hf₁,hf₂,hf₃,hf₄,hf₅⟩:=hfits
      obtain ⟨s₁,v,h₁,e₁0,hv⟩:=
        compileCond_correct hfit (by omega) hokb hb hrep (hf₁.congr hpc.symm)
      obtain ⟨t₁,ht₁,hr₁⟩:=h₁.steps
      have hne:s₁.mem 0 ≠ 0:=by
        rw [e₁0]; intro hc; exact absurd (hv.mp hc) (by simp)
      have hf₂':p[s₁.pc]?=some (Instr.jzero 0 (a + bsize L b + 1 + size L d + 1)):=by
        rw [h₁.pc,hpc]; exact fits_singleton.mp (by simpa using hf₂)
      have hjz:run w p 1 s₁=some { s₁ with pc:=a + bsize L b + 1 }:=by
        rw [run_jzero hzw hf₂']
        have:s₁.pc + 1=a + bsize L b + 1:=by rw [h₁.pc,hpc]
        simp [hne,this]
      obtain ⟨t₂,s₂,ht₂,hr₂,hpc₂,hrep₂⟩:=
        ih hokd hinp (a + bsize L b + 1) { s₁ with pc:=a + bsize L b + 1 } rfl
          ((hrep.reaches h₁).setPc _) (by simpa [Nat.add_assoc] using hf₃)
      have hf₄':p[s₂.pc]? =
          some (Instr.jump (a + bsize L b + 1 + size L d + 1 + size L c)):=by
        rw [hpc₂]; exact fits_singleton.mp (by simpa [Nat.add_assoc] using hf₄)
      refine ⟨t₁ + 1 + t₂ + 1,_, ?_,
        run_trans (run_trans (run_trans hr₁ hjz) hr₂) (run_jump hf₄'), ?_, ?_⟩
      · simp only [Nat.mul_add,Nat.mul_one]
        have:=bsize_le L b
        have:=two_le_const L
        omega
      · show a + bsize L b + 1 + size L d + 1 + size L c=a + size L (.ite b c d)
        simp [size]; omega
      · exact hrep₂.setPc _
  | @while_true b c σ σ₁ σ₂ k k' hb hbody _ ih ih' =>
      intro hok hinp a s hpc hrep hfits
      obtain ⟨hokb,hokc⟩:=hok
      have hcode:compile L (.while b c) a
         =compileCond L b 0 ++ ([Instr.jzero 0 (a + bsize L b + 2)] ++
              ([Instr.jump (a + bsize L b + 2 + size L c + 1)] ++
                (compile L c (a + bsize L b + 2) ++ [Instr.jump a]))):=by
        simp [compile,List.append_assoc]
      rw [hcode,fits_append,fits_append,fits_append,fits_append] at hfits
      obtain ⟨hf₁,hf₂,hf₃,hf₄,hf₅⟩:=hfits
      obtain ⟨s₁,v,h₁,e₁0,hv⟩:=
        compileCond_correct hfit (by omega) hokb hb hrep (hf₁.congr hpc.symm)
      obtain ⟨t₁,ht₁,hr₁⟩:=h₁.steps
      have hzero:s₁.mem 0=0:=by rw [e₁0]; exact hv.mpr rfl
      have hf₂':p[s₁.pc]?=some (Instr.jzero 0 (a + bsize L b + 2)):=by
        rw [h₁.pc,hpc]; exact fits_singleton.mp (by simpa using hf₂)
      have hjz:run w p 1 s₁=some { s₁ with pc:=a + bsize L b + 2 }:=by
        rw [run_jzero hzw hf₂',hzero]; simp
      obtain ⟨t₂,s₂,ht₂,hr₂,hpc₂,hrep₂⟩:=
        ih hokc hinp (a + bsize L b + 2) { s₁ with pc:=a + bsize L b + 2 } rfl
          ((hrep.reaches h₁).setPc _) (by simpa [Nat.add_assoc] using hf₄)
      have hf₅':p[s₂.pc]?=some (Instr.jump a):=by
        rw [hpc₂]; exact fits_singleton.mp (by simpa [Nat.add_assoc] using hf₅)
      obtain ⟨t₃,s₃,ht₃,hr₃,hpc₃,hrep₃⟩:=
        ih' (⟨hokb,hokc⟩:Com.Ok L (.while b c)) (hbody.inpBounded hinp) a
          { s₂ with pc:=a } rfl (hrep₂.setPc _) (by rw [hcode]; exact
          (fits_append.mpr ⟨hf₁,fits_append.mpr ⟨hf₂,fits_append.mpr ⟨hf₃,
            fits_append.mpr ⟨hf₄,hf₅⟩⟩⟩⟩))
      refine ⟨t₁ + 1 + t₂ + 1 + t₃,s₃, ?_,
        run_trans (run_trans (run_trans (run_trans hr₁ hjz) hr₂)
          (run_jump hf₅')) hr₃,hpc₃,hrep₃⟩
      simp only [Nat.mul_add,Nat.mul_one]
      have:=bsize_le L b
      have:=two_le_const L
      omega
  | @while_false b c σ hb =>
      intro hok _ a s hpc hrep hfits
      obtain ⟨hokb,hokc⟩:=hok
      rw [show compile L (.while b c) a
           =compileCond L b 0 ++ ([Instr.jzero 0 (a + bsize L b + 2)] ++
                ([Instr.jump (a + bsize L b + 2 + size L c + 1)] ++
                  (compile L c (a + bsize L b + 2) ++ [Instr.jump a]))) from by
          simp [compile,List.append_assoc],
        fits_append,fits_append,fits_append,fits_append] at hfits
      obtain ⟨hf₁,hf₂,hf₃,hf₄,hf₅⟩:=hfits
      obtain ⟨s₁,v,h₁,e₁0,hv⟩:=
        compileCond_correct hfit (by omega) hokb hb hrep (hf₁.congr hpc.symm)
      obtain ⟨t₁,ht₁,hr₁⟩:=h₁.steps
      have hne:s₁.mem 0 ≠ 0:=by
        rw [e₁0]; intro hc; exact absurd (hv.mp hc) (by simp)
      have hf₂':p[s₁.pc]?=some (Instr.jzero 0 (a + bsize L b + 2)):=by
        rw [h₁.pc,hpc]; exact fits_singleton.mp (by simpa using hf₂)
      have hf₃':p[s₁.pc + 1]?=some (Instr.jump (a + bsize L b + 2 + size L c + 1)):=by
        rw [h₁.pc,hpc]; exact fits_singleton.mp (by simpa [Nat.add_assoc] using hf₃)
      have hjz:run w p 1 s₁=some { s₁ with pc:=s₁.pc + 1 }:=by
        rw [run_jzero hzw hf₂']; simp [hne]
      have hf₃'':p[({ s₁ with pc:=s₁.pc + 1 }:State).pc]? =
          some (Instr.jump (a + bsize L b + 2 + size L c + 1)):=hf₃'
      refine ⟨t₁ + 1 + 1,_, ?_,
        run_trans (run_trans hr₁ hjz) (run_jump hf₃''), ?_, ?_⟩
      · simp only [Nat.mul_add,Nat.mul_one]
        have:=bsize_le L b
        have:=two_le_const L
        omega
      · show a + bsize L b + 2 + size L c + 1=a + size L (.while b c)
        simp [size]; omega
      · exact (hrep.reaches h₁).setPc _

theorem represents_initState (L:Layout) (ext:String→ ℕ) (x:List ℕ):
    Represents L (initEnv ext x) (initState x) where
  vars _ _:=rfl
  arrs a _ i _:=by
    show (0:ℕ)=(List.replicate (ext a) 0).getD i 0
    rw [List.getD_eq_getElem?_getD]
    rcases h:(List.replicate (ext a) 0)[i]? with _ | u
    · rfl
    · have:=List.mem_of_getElem? h
      simp only [List.mem_replicate] at this
      rw [this.2]; rfl
  inp:=rfl
  out:=rfl

theorem compileProgram_runsTo {L:Layout} {B w:ℕ} {c:Com} {ext:String→ ℕ}
    {x:List ℕ} {σ':Env} {k:ℕ} (hfit:L.FitsWords B w) (hok:Com.Ok L c)
    (hx:∀ v∈ x,v < B) (hbs:BigStepB B c (initEnv ext x) σ' k):
    ∃ t≤ L.const * k + 1,RunsTo w (compileProgram L c) x σ'.out t:=by
  obtain ⟨t,s',ht,hr,hpc,hrep⟩:=
    compile_correct hfit hbs hok (initEnv_inpBounded ext hx) 0 (initState x) rfl
      (represents_initState L ext x) (fits_self _ _)
  have hhalt:(compileProgram L c)[s'.pc]?=some Instr.halt:=by
    rw [hpc,compileProgram]
    rw [List.getElem?_append_right (by simp)]
    simp
  refine ⟨t + 1,Nat.add_le_add_right ht 1,t,s',hr, ?_, ?_, ?_⟩
  · rw [step_eq,hhalt]; rfl
  · rw [← hrep.out]
  · rw [terminalCost_of_getElem? hhalt]

example:
    ∃ t≤ 21,RunsTo 3 (compileProgram ⟨[], [],1⟩ (.write (.lit 5))) [] [5] t:=by
  have hfit:(⟨[], [],1⟩:Layout).FitsWords 8 3:=
    ⟨by norm_num,by norm_num,by simp [Layout.span]⟩
  have hbs:BigStepB 8 (.write (.lit 5)) (initEnv (fun _ => 0) [])
      { initEnv (fun _ => 0) [] with out:=(initEnv (fun _ => 0) []).out ++ [5] }
      (1 + (Expr.lit 5).size):=.write (fit_self (by norm_num))
  have hok:Com.Ok (⟨[], [],1⟩:Layout) (.write (.lit 5)):= ⟨trivial,by norm_num⟩
  obtain ⟨t,ht,hrun⟩:=compileProgram_runsTo hfit hok (by simp) hbs
  exact ⟨t,le_trans ht (by norm_num [Layout.const,Expr.size]),
    by simpa [initEnv] using hrun⟩

end Lax808846Proofs.Simulation

end

theorem solution:∀ {L:Lax808846Proofs.Compile.Layout} {B w:ℕ} {c:Lax808846Proofs.Imp.Com} {ext:String→ ℕ} {x:List ℕ}
  {σ':Lax808846Proofs.Imp.Env} {k:ℕ},
  L.FitsWords B w→
    Lax808846Proofs.Compile.Com.Ok L c→
      (∀ v∈ x,v < B)→
        Lax808846Proofs.Imp.BigStepB B c (Lax808846Proofs.Imp.initEnv ext x) σ' k→
          ∃ t≤ L.const * k + 1,Lax808846.Ram.RunsTo w (Lax808846Proofs.Compile.compileProgram L c) x σ'.out t:= @Lax808846Proofs.Simulation.compileProgram_runsTo
