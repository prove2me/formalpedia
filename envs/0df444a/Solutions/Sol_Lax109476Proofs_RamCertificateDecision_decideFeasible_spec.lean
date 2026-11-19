-- Prove2me | solution 1 for Lax109476Proofs.RamCertificateDecision.decideFeasible_spec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T13:46:43.009206+00:00
-- url     : https://prove2.me/submissions/5c17f571-9b06-401c-b25b-07b3690d4661

import Mathlib.Tactic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Cast.Field
import Definitions.Def_EdgeSublinearMWIS_Main_NativeOracleInterfaces
import Theorems.Thm_Lax109476Proofs_RamStoredFeasibility_decideFeasible_condition_spec

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

theorem Expr.eval_of_evalB {B:ℕ} {σ:Env} {e:Expr} {v:ℕ}
    (h:e.evalB B σ=some v):e.eval σ=some v:=(eval_and_lt_of_evalB h).1

theorem Cond.eval_of_evalB {B:ℕ} {σ:Env} {b:Cond} {r:Bool}
    (h:b.evalB B σ=some r):b.eval σ=some r:=by
  cases b with
  | eq e f =>
      rw [Cond.evalB,Option.bind_eq_some_iff] at h
      obtain ⟨m,hm,h⟩:=h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨n,hn,rfl⟩:=h
      rw [Cond.eval,Expr.eval_of_evalB hm,Expr.eval_of_evalB hn]; rfl
  | lt e f =>
      rw [Cond.evalB,Option.bind_eq_some_iff] at h
      obtain ⟨m,hm,h⟩:=h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨n,hn,rfl⟩:=h
      rw [Cond.eval,Expr.eval_of_evalB hm,Expr.eval_of_evalB hn]; rfl

theorem BigStepB.bigStep {B:ℕ} {c:Com} {σ σ':Env} {k:ℕ}
    (h:BigStepB B c σ σ' k):BigStep c σ σ' k:=by
  induction h with
  | skip => exact .skip
  | assign h => exact .assign (Expr.eval_of_evalB h)
  | store hi he hk => exact .store (Expr.eval_of_evalB hi) (Expr.eval_of_evalB he) hk
  | seq _ _ ih ih' => exact .seq ih ih'
  | ite_true hb _ ih => exact .ite_true (Cond.eval_of_evalB hb) ih
  | ite_false hb _ ih => exact .ite_false (Cond.eval_of_evalB hb) ih
  | while_true hb _ _ ih ih' => exact .while_true (Cond.eval_of_evalB hb) ih ih'
  | while_false hb => exact .while_false (Cond.eval_of_evalB hb)
  | read h => exact .read h
  | write h => exact .write (Expr.eval_of_evalB h)

end Lax808846Proofs.Imp

end

section

namespace Lax808846Proofs.Reasoning

open Lax808846Proofs.Imp Lax808846Proofs.Compile

@[simp] theorem vars_setVar (σ:Env) (x:String) (v:ℕ) (y:String):
    (σ.setVar x v).vars y=if y=x then v else σ.vars y:=rfl

@[simp] theorem arrs_setVar (σ:Env) (x:String) (v:ℕ):
    (σ.setVar x v).arrs=σ.arrs:=rfl

@[simp] theorem inp_setVar (σ:Env) (x:String) (v:ℕ):
    (σ.setVar x v).inp=σ.inp:=rfl

@[simp] theorem out_setVar (σ:Env) (x:String) (v:ℕ):
    (σ.setVar x v).out=σ.out:=rfl

@[simp] theorem vars_setArr (σ:Env) (a:String) (i v:ℕ):
    (σ.setArr a i v).vars=σ.vars:=rfl

@[simp] theorem arrs_setArr (σ:Env) (a:String) (i v:ℕ) (b:String):
    (σ.setArr a i v).arrs b=if b=a then (σ.arrs a).set i v else σ.arrs b:=rfl

@[simp] theorem inp_setArr (σ:Env) (a:String) (i v:ℕ):
    (σ.setArr a i v).inp=σ.inp:=rfl

@[simp] theorem out_setArr (σ:Env) (a:String) (i v:ℕ):
    (σ.setArr a i v).out=σ.out:=rfl

@[simp] theorem length_arrs_setArr (σ:Env) (a:String) (i v:ℕ) (b:String):
    ((σ.setArr a i v).arrs b).length=(σ.arrs b).length:=by
  rw [arrs_setArr]; split
  · subst_vars; exact List.length_set ..
  · rfl

def arrOf (n:ℕ) (f:ℕ→ ℕ):List ℕ:=(List.range n).map f

@[simp] theorem length_arrOf (n:ℕ) (f:ℕ→ ℕ):(arrOf n f).length=n:=by
  simp [arrOf]

theorem replicate_eq_arrOf (n v:ℕ):List.replicate n v=arrOf n (fun _ => v):=by
  simp [arrOf,List.map_const']

theorem arrOf_congr {n:ℕ} {f g:ℕ→ ℕ} (h:∀ i < n,f i=g i):
    arrOf n f=arrOf n g:=by
  refine List.ext_getElem (by simp) fun k h₁ _ => ?_
  simp only [arrOf,List.length_map,List.length_range] at h₁
  simp [arrOf,h k h₁]

theorem set_arrOf {n i:ℕ} (f:ℕ→ ℕ) (v:ℕ):
    (arrOf n f).set i v=arrOf n (fun k => if k=i then v else f k):=by
  refine List.ext_getElem (by simp) fun k h₁ h₂ => ?_
  rw [List.getElem_set]
  by_cases hk:k=i
  · subst hk; simp [arrOf]
  · simp [arrOf,hk,Ne.symm hk]

@[simp] theorem evalB_lit_iff {B n v:ℕ} {σ:Env}:
    (Expr.lit n).evalB B σ=some v↔ v=n∧ n < B:=by
  rw [Expr.evalB,fit_eq_some]

@[simp] theorem evalB_var_iff {B:ℕ} {x:String} {σ:Env} {v:ℕ}:
    (Expr.var x).evalB B σ=some v↔ v=σ.vars x∧ σ.vars x < B:=by
  rw [Expr.evalB,fit_eq_some]

@[simp] theorem evalB_bin_iff {B:ℕ} {op:Bop} {e f:Expr} {σ:Env} {v:ℕ}:
    (Expr.bin op e f).evalB B σ=some v↔
      ∃ m n,e.evalB B σ=some m∧ f.evalB B σ=some n∧ v=op.apply m n∧ v < B:=by
  rw [Expr.evalB]
  simp only [Option.bind_eq_some_iff,fit_eq_some]
  constructor
  · rintro ⟨m,hm,n,hn,rfl,hlt⟩; exact ⟨m,n,hm,hn,rfl,hlt⟩
  · rintro ⟨m,n,hm,hn,rfl,hlt⟩; exact ⟨m,hm,n,hn,rfl,hlt⟩

@[simp] theorem evalB_condLt_iff {B:ℕ} {e f:Expr} {σ:Env} {r:Bool}:
    (Cond.lt e f).evalB B σ=some r↔
      ∃ m n,e.evalB B σ=some m∧ f.evalB B σ=some n∧ r=decide (m < n):=by
  rw [Cond.evalB]
  simp only [Option.bind_eq_some_iff,Option.map_eq_some_iff]
  constructor
  · rintro ⟨m,hm,n,hn,rfl⟩; exact ⟨m,n,hm,hn,rfl⟩
  · rintro ⟨m,n,hm,hn,rfl⟩; exact ⟨m,hm,n,hn,rfl⟩

theorem evalB_lit {B n:ℕ} {σ:Env} (h:n < B):(Expr.lit n).evalB B σ=some n:=
  fit_self h

theorem evalB_var {B:ℕ} {x:String} {σ:Env} (h:σ.vars x < B):
    (Expr.var x).evalB B σ=some (σ.vars x):=fit_self h

theorem evalB_get {B:ℕ} {a:String} {i:Expr} {σ:Env} {k v:ℕ}
    (hi:i.evalB B σ=some k) (hk:(σ.arrs a)[k]?=some v) (hv:v < B):
    (Expr.get a i).evalB B σ=some v:=by
  rw [Expr.evalB,hi,Option.bind_some,hk,Option.bind_some,fit_self hv]

theorem evalB_bin {B:ℕ} {op:Bop} {e f:Expr} {σ:Env} {m n:ℕ}
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:op.apply m n < B):
    (Expr.bin op e f).evalB B σ=some (op.apply m n):=by
  rw [Expr.evalB,he,Option.bind_some,hf,Option.bind_some,fit_self h]

theorem evalB_condEq {B:ℕ} {e f:Expr} {σ:Env} {m n:ℕ}
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n):
    (Cond.eq e f).evalB B σ=some (m == n):=by
  rw [Cond.evalB,he,Option.bind_some,hf,Option.map_some]

theorem evalB_condLt {B:ℕ} {e f:Expr} {σ:Env} {m n:ℕ}
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n):
    (Cond.lt e f).evalB B σ=some (decide (m < n)):=by
  rw [Cond.evalB,he,Option.bind_some,hf,Option.map_some]

theorem evalB_condLt_vars {B:ℕ} {x y:String} {σ:Env}
    (hx:σ.vars x < B) (hy:σ.vars y < B):
    ∃ v, (Cond.lt (.var x) (.var y)).evalB B σ=some v:=
  ⟨_,evalB_condLt (evalB_var hx) (evalB_var hy)⟩

@[simp] theorem size_lit (n:ℕ):(Expr.lit n).size=1:=rfl
@[simp] theorem size_var (x:String):(Expr.var x).size=1:=rfl
@[simp] theorem size_get (a:String) (i:Expr):(Expr.get a i).size=i.size + 1:=rfl
@[simp] theorem size_bin (op:Bop) (e f:Expr):
    (Expr.bin op e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_add (e f:Expr):(Expr.add e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_sub (e f:Expr):(Expr.sub e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_mul (e f:Expr):(Expr.mul e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_div (e f:Expr):(Expr.div e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_and (e f:Expr):(Expr.and e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_or (e f:Expr):(Expr.or e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_xor (e f:Expr):(Expr.xor e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_shiftl (e f:Expr):(Expr.shiftl e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_shiftr (e f:Expr):(Expr.shiftr e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_condEq (e f:Expr):(Cond.eq e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_condLt (e f:Expr):(Cond.lt e f).size=e.size + f.size + 1:=rfl

theorem Run.of_bigStepB {B:ℕ} {c:Com} {σ σ':Env} {k:ℕ} (h:BigStepB B c σ σ' k):
    Run B c σ σ' k:= ⟨k,le_rfl,h⟩

theorem Run.bigStep {B:ℕ} {c:Com} {σ σ':Env} {K:ℕ} (h:Run B c σ σ' K):
    ∃ k≤ K,BigStep c σ σ' k:=by
  obtain ⟨k,hk,hbs⟩:=h; exact ⟨k,hk,hbs.bigStep⟩

theorem Run.mono {B:ℕ} {c:Com} {σ σ':Env} {K K':ℕ} (h:Run B c σ σ' K) (hK:K≤ K'):
    Run B c σ σ' K':=by
  obtain ⟨k,hk,hbs⟩:=h; exact ⟨k,hk.trans hK,hbs⟩

theorem Run.skip {B:ℕ} {σ:Env}:Run B .skip σ σ 1:=.of_bigStepB .skip

theorem Run.assign {B:ℕ} {σ:Env} {x:String} {e:Expr} {v:ℕ}
    (h:e.evalB B σ=some v):
    Run B (.assign x e) σ (σ.setVar x v) (1 + e.size):=.of_bigStepB (.assign h)

theorem Run.store {B:ℕ} {σ:Env} {a:String} {i e:Expr} {idx v:ℕ}
    (hi:i.evalB B σ=some idx) (he:e.evalB B σ=some v)
    (hidx:idx < (σ.arrs a).length):
    Run B (.store a i e) σ (σ.setArr a idx v) (1 + i.size + e.size):=
  .of_bigStepB (.store hi he hidx)

theorem Run.read {B:ℕ} {σ:Env} {x:String} {v:ℕ} {rest:List ℕ}
    (h:σ.inp=v::rest):
    Run B (.read x) σ { σ.setVar x v with inp:=rest } 1:=.of_bigStepB (.read h)

theorem Run.write {B:ℕ} {σ:Env} {e:Expr} {v:ℕ} (h:e.evalB B σ=some v):
    Run B (.write e) σ { σ with out:=σ.out ++ [v] } (1 + e.size):=.of_bigStepB (.write h)

theorem Run.seq {B:ℕ} {c d:Com} {σ σ' σ'':Env} {K K':ℕ}
    (h:Run B c σ σ' K) (h':Run B d σ' σ'' K'):Run B (.seq c d) σ σ'' (K + K'):=by
  obtain ⟨k,hk,hbs⟩:=h
  obtain ⟨k',hk',hbs'⟩:=h'
  exact ⟨k + k',by omega, .seq hbs hbs'⟩

theorem Run.ite_true {B:ℕ} {b:Cond} {c d:Com} {σ σ':Env} {K:ℕ}
    (hb:b.evalB B σ=some true) (h:Run B c σ σ' K):
    Run B (.ite b c d) σ σ' (1 + b.size + K):=by
  obtain ⟨k,hk,hbs⟩:=h
  exact ⟨1 + b.size + k,by omega, .ite_true hb hbs⟩

theorem Run.ite_false {B:ℕ} {b:Cond} {c d:Com} {σ σ':Env} {K:ℕ}
    (hb:b.evalB B σ=some false) (h:Run B d σ σ' K):
    Run B (.ite b c d) σ σ' (1 + b.size + K):=by
  obtain ⟨k,hk,hbs⟩:=h
  exact ⟨1 + b.size + k,by omega, .ite_false hb hbs⟩

theorem Run.while_false {B:ℕ} {b:Cond} {c:Com} {σ:Env}
    (hb:b.evalB B σ=some false):Run B (.while b c) σ σ (1 + b.size):=
  .of_bigStepB (.while_false hb)

theorem Run.while_potential {B:ℕ} {b:Cond} {c:Com} (I:Env→ Prop) (Φ:Env→ ℕ)
    (hdef:∀ σ,I σ→ ∃ v,b.evalB B σ=some v)
    (hstep:∀ σ,I σ→ b.evalB B σ=some true→
      ∃ σ' K,Run B c σ σ' K∧ I σ'∧ 1 + b.size + K + Φ σ'≤ Φ σ)
    {σ:Env} (hI:I σ):
    ∃ σ' K,Run B (.while b c) σ σ' K∧ I σ'∧ b.evalB B σ'=some false∧
      K + Φ σ'≤ Φ σ + 1 + b.size:=by
  suffices H:∀ n σ,I σ→ Φ σ≤ n→
      ∃ σ' K,Run B (.while b c) σ σ' K∧ I σ'∧ b.evalB B σ'=some false∧
        K + Φ σ'≤ Φ σ + 1 + b.size from H (Φ σ) σ hI le_rfl
  clear hI σ
  intro n
  induction n with
  | zero =>
      intro σ hI hΦ
      obtain ⟨v,hv⟩:=hdef σ hI
      cases v with
      | false => exact ⟨σ,_,Run.while_false hv,hI,hv,by omega⟩
      | true =>
          obtain ⟨σ₁,K,hrun,_,hpay⟩:=hstep σ hI hv
          omega
  | succ n ih =>
      intro σ hI hΦ
      obtain ⟨v,hv⟩:=hdef σ hI
      cases v with
      | false => exact ⟨σ,_,Run.while_false hv,hI,hv,by omega⟩
      | true =>
          obtain ⟨σ₁,K,hrun,hI₁,hpay⟩:=hstep σ hI hv
          obtain ⟨σ',K',hrun',hI',hfalse,hpay'⟩:=ih σ₁ hI₁ (by omega)
          obtain ⟨k,hk,hbs⟩:=hrun
          obtain ⟨k',hk',hbs'⟩:=hrun'
          exact ⟨σ',1 + b.size + k + k', ⟨1 + b.size + k + k',le_rfl,
            .while_true hv hbs hbs'⟩,hI',hfalse,by omega⟩

def _root_.Lax808846Proofs.Imp.Com.NoWrite:Com→ Prop
  | .skip => True
  | .assign _ _ => True
  | .store _ _ _ => True
  | .read _ => True
  | .write _ => False
  | .seq c d => c.NoWrite∧ d.NoWrite
  | .ite _ c d => c.NoWrite∧ d.NoWrite
  | .while _ c => c.NoWrite

theorem _root_.Lax808846Proofs.Imp.BigStep.out_eq {c:Com} {σ σ':Env} {k:ℕ}
    (h:BigStep c σ σ' k):c.NoWrite→ σ'.out=σ.out:=by
  induction h with
  | skip => intro _; rfl
  | assign _ => intro _; rfl
  | store _ _ _ => intro _; rfl
  | seq _ _ ih ih' => intro hc; rw [ih' hc.2,ih hc.1]
  | ite_true _ _ ih => intro hc; exact ih hc.1
  | ite_false _ _ ih => intro hc; exact ih hc.2
  | while_true _ _ _ ih ih' => intro hc; rw [ih' hc,ih hc]
  | while_false _ => intro _; rfl
  | read _ => intro _; rfl
  | write _ => intro hc; exact absurd hc not_false

theorem Run.out_eq {B:ℕ} {c:Com} {σ σ':Env} {K:ℕ} (h:Run B c σ σ' K)
    (hc:c.NoWrite):σ'.out=σ.out:=by
  obtain ⟨_,_,hbs⟩:=h.bigStep; exact hbs.out_eq hc

end Lax808846Proofs.Reasoning

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RationalSizeBounds

variable {ι:Type*} [Fintype ι]

theorem size_le_self (a:ℕ):Nat.size a≤ a:=
  Nat.size_le.mpr (Nat.lt_two_pow_self (n:=a))

end Lax109476Proofs.RationalSizeBounds

end

section

open scoped BigOperators

namespace Lax109476Proofs.EncodingSize

open Lax759944.BinaryWordEncoding Lax109476.RationalEncoding
open Lax109476.LinearProgram

theorem bitSize_append (x y:List ℕ):bitSize (x ++ y)=bitSize x + bitSize y:=by
  simp [bitSize,encode]

theorem bitSize_cons (n:ℕ) (x:List ℕ):
    bitSize (n::x)=Nat.size n + 1 + bitSize x:=by
  simp [bitSize,encode,encodeNat,Nat.size_eq_bits_len]
  omega

theorem bitSize_nil:bitSize []=0:=rfl

theorem bitSize_flatMap {α:Type*} (x:List α) (f:α→ List ℕ):
    bitSize (x.flatMap f)=(x.map (fun a => bitSize (f a))).sum:=by
  induction x with
  | nil => rfl
  | cons a x ih => simp only [List.flatMap_cons,bitSize_append,
      List.map_cons,List.sum_cons,ih]

theorem rational_size_upper (q:ℚ):
    bitSize (encodeRational q)≤ 4 + Nat.size q.num.natAbs + Nat.size q.den:=by
  unfold encodeRational
  rw [bitSize_cons,bitSize_cons,bitSize_cons,bitSize_nil]
  split_ifs <;> norm_num [Nat.size] <;> omega

theorem vector_size {n:ℕ} (x:Fin n→ ℚ):
    bitSize (encodeVector x)=∑ j,bitSize (encodeRational (x j)):=by
  rw [encodeVector,bitSize_flatMap,List.map_ofFn,List.sum_ofFn]
  rfl

theorem bounded_vector_size {n:ℕ} (x:Fin n→ ℚ) (B:ℕ)
    (hx:∀ j, (x j).num.natAbs≤ B∧ (x j).den≤ B):
    bitSize (encodeVector x)≤ n * (4 + 2 * Nat.size B):=by
  rw [vector_size]
  calc
    _≤ ∑ _j:Fin n, (4 + 2 * Nat.size B):=by
      apply Finset.sum_le_sum
      intro j _
      have hn:=Nat.size_le_size (hx j).1
      have hd:=Nat.size_le_size (hx j).2
      have hu:=rational_size_upper (x j)
      omega
    _=_:=by simp

theorem program_size {m n:ℕ} (P:Program ℚ m n):
    bitSize (encodeProgram P)=Nat.size m + Nat.size n + 2 +
      (∑ i, ∑ j,bitSize (encodeRational (P.A i j))) +
      (∑ i,bitSize (encodeRational (P.b i))) +
      (∑ j,bitSize (encodeRational (P.c j))):=by
  have hmatrix:bitSize ((List.ofFn fun i => List.ofFn (P.A i)).flatten.flatMap
      encodeRational)=∑ i, ∑ j,bitSize (encodeRational (P.A i j)):=by
    rw [List.flatten_eq_flatMap,List.flatMap_assoc,bitSize_flatMap,
      List.map_ofFn,List.sum_ofFn]
    apply Finset.sum_congr rfl
    intro i _
    change bitSize ((List.ofFn (P.A i)).flatMap encodeRational)=_
    rw [bitSize_flatMap,List.map_ofFn,List.sum_ofFn]
    rfl
  unfold encodeProgram
  rw [bitSize_append,bitSize_append,bitSize_append,bitSize_cons,
    bitSize_cons,bitSize_nil,vector_size,vector_size,hmatrix]
  omega

end Lax109476Proofs.EncodingSize

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.EllipsoidSearch

open Lax109476.RationalCertificates
open RationalSeparation EllipsoidRounding EllipsoidCenter EllipsoidPrecision
open EllipsoidIteration EllipsoidSequence

def trajectory {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ) (b:Fin m→ ℚ):
    ℕ→ Matrix (Fin n) (Fin n) ℚ × (Fin n→ ℚ)
  | 0 => (1,0)
  | k + 1 => nextState A b k (trajectory A b k)

def search {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ) (b:Fin m→ ℚ)
    (K:ℕ):Option (Fin n→ ℚ):=
  (findIteration A b K).map (fun k => (trajectory A b k).2)

end Lax109476Proofs.EllipsoidSearch

end

section

namespace Lax808846Proofs.Imp

def Com.reads:Com→ Prop
  | .skip => False
  | .assign _ _ => False
  | .store _ _ _ => False
  | .seq c d => c.reads∨ d.reads
  | .ite _ c d => c.reads∨ d.reads
  | .while _ c => c.reads
  | .read _ => True
  | .write _ => False

@[simp] theorem Com.wvars_skip:Com.skip.wvars=[]:=by simp [Com.wvars]

end Lax808846Proofs.Imp

namespace Lax808846Proofs.Reasoning

open Lax808846Proofs.Imp

theorem _root_.Lax808846Proofs.Imp.BigStep.vars_eq {c:Com} {σ σ':Env} {k:ℕ}
    (h:BigStep c σ σ' k) {y:String} (hy:y∉ c.wvars):σ'.vars y=σ.vars y:=by
  induction h with
  | skip => rfl
  | assign _ => simp only [Com.wvars,List.mem_singleton] at hy; simp [Env.setVar,hy]
  | store _ _ _ => rfl
  | seq _ _ ih ih' =>
      simp only [Com.wvars,List.mem_append,not_or] at hy
      rw [ih' hy.2,ih hy.1]
  | ite_true _ _ ih => simp only [Com.wvars,List.mem_append,not_or] at hy; exact ih hy.1
  | ite_false _ _ ih => simp only [Com.wvars,List.mem_append,not_or] at hy; exact ih hy.2
  | while_true _ _ _ ih ih' =>
      simp only [Com.wvars] at hy
      rw [ih' (by simpa [Com.wvars] using hy),ih hy]
  | while_false _ => rfl
  | read _ => simp only [Com.wvars,List.mem_singleton] at hy; simp [Env.setVar,hy]
  | write _ => rfl

theorem _root_.Lax808846Proofs.Imp.BigStep.arrs_eq {c:Com} {σ σ':Env} {k:ℕ}
    (h:BigStep c σ σ' k) {a:String} (ha:a∉ c.warrs):σ'.arrs a=σ.arrs a:=by
  induction h with
  | skip => rfl
  | assign _ => rfl
  | store _ _ _ => simp only [Com.warrs,List.mem_singleton] at ha; simp [Env.setArr,ha]
  | seq _ _ ih ih' =>
      simp only [Com.warrs,List.mem_append,not_or] at ha
      rw [ih' ha.2,ih ha.1]
  | ite_true _ _ ih => simp only [Com.warrs,List.mem_append,not_or] at ha; exact ih ha.1
  | ite_false _ _ ih => simp only [Com.warrs,List.mem_append,not_or] at ha; exact ih ha.2
  | while_true _ _ _ ih ih' =>
      simp only [Com.warrs] at ha
      rw [ih' (by simpa [Com.warrs] using ha),ih ha]
  | while_false _ => rfl
  | read _ => rfl
  | write _ => rfl

theorem _root_.Lax808846Proofs.Imp.BigStep.inp_eq {c:Com} {σ σ':Env} {k:ℕ}
    (h:BigStep c σ σ' k) (hr:¬ c.reads):σ'.inp=σ.inp:=by
  induction h with
  | skip => rfl
  | assign _ => rfl
  | store _ _ _ => rfl
  | seq _ _ ih ih' =>
      simp only [Com.reads,not_or] at hr
      rw [ih' hr.2,ih hr.1]
  | ite_true _ _ ih => simp only [Com.reads,not_or] at hr; exact ih hr.1
  | ite_false _ _ ih => simp only [Com.reads,not_or] at hr; exact ih hr.2
  | while_true _ _ _ ih ih' =>
      simp only [Com.reads] at hr
      rw [ih' (by simpa [Com.reads] using hr),ih hr]
  | while_false _ => rfl
  | read _ => exact absurd (by rw [Com.reads]; trivial) hr
  | write _ => rfl

theorem Run.frame_var {B:ℕ} {c:Com} {σ σ':Env} {K:ℕ} (h:Run B c σ σ' K)
    (y:String) (hy:y∉ c.wvars):σ'.vars y=σ.vars y:=by
  obtain ⟨_,_,hbs⟩:=h.bigStep; exact hbs.vars_eq hy

theorem Run.frame_arr {B:ℕ} {c:Com} {σ σ':Env} {K:ℕ} (h:Run B c σ σ' K)
    (a:String) (ha:a∉ c.warrs):σ'.arrs a=σ.arrs a:=by
  obtain ⟨_,_,hbs⟩:=h.bigStep; exact hbs.arrs_eq ha

theorem Run.frame_inp {B:ℕ} {c:Com} {σ σ':Env} {K:ℕ} (h:Run B c σ σ' K)
    (hr:¬ c.reads):σ'.inp=σ.inp:=by
  obtain ⟨_,_,hbs⟩:=h.bigStep; exact hbs.inp_eq hr

end Lax808846Proofs.Reasoning

end

section

namespace Lax808846Proofs.Reasoning

open Lax808846Proofs.Imp

variable {B:ℕ} {P P':Env→ Prop} {Q Q' R:Env→ Env→ Prop} {c d:Com} {K K':ℕ}

theorem Spec.run (h:Spec B P c Q K) {σ:Env} (hσ:P σ):
    ∃ σ',Run B c σ σ' K∧ Q σ σ':=h σ hσ

theorem Spec.mono (h:Spec B P c Q K) (hK:K≤ K'):Spec B P c Q K':=by
  intro σ hσ
  obtain ⟨σ',hr,hq⟩:=h σ hσ
  exact ⟨σ',hr.mono hK,hq⟩

theorem Spec.conseq (h:Spec B P c Q K) (hP:∀ σ,P' σ→ P σ)
    (hQ:∀ σ σ',P' σ→ Q σ σ'→ Q' σ σ') (hK:K≤ K'):Spec B P' c Q' K':=by
  intro σ hσ
  obtain ⟨σ',hr,hq⟩:=h σ (hP σ hσ)
  exact ⟨σ',hr.mono hK,hQ σ σ' hσ hq⟩

theorem Spec.pre (h:Spec B P c Q K) (hP:∀ σ,P' σ→ P σ):Spec B P' c Q K:=
  h.conseq hP (fun _ _ _ hq => hq) le_rfl

theorem Spec.post (h:Spec B P c Q K) (hQ:∀ σ σ',P σ→ Q σ σ'→ Q' σ σ'):
    Spec B P c Q' K:=
  h.conseq (fun _ hσ => hσ) hQ le_rfl

theorem Spec.frame (h:Spec B P c Q K):
    Spec B P c (fun σ σ' => Q σ σ'∧
      (∀ y,y∉ c.wvars→ σ'.vars y=σ.vars y)∧
      (∀ a,a∉ c.warrs→ σ'.arrs a=σ.arrs a)∧
      (¬ c.reads→ σ'.inp=σ.inp)∧
      (c.NoWrite→ σ'.out=σ.out)) K:=by
  intro σ hσ
  obtain ⟨σ',hr,hq⟩:=h σ hσ
  exact ⟨σ',hr,hq,fun y hy => hr.frame_var y hy,fun a ha => hr.frame_arr a ha,
    fun hc => hr.frame_inp hc,fun hc => hr.out_eq hc⟩

theorem Spec.assign {x:String} {e:Expr} {f:Env→ ℕ}
    (h:∀ σ,P σ→ e.evalB B σ=some (f σ)):
    Spec B P (.assign x e) (fun σ σ' => σ'=σ.setVar x (f σ)) (1 + e.size):=
  fun σ hσ => ⟨_,Run.assign (h σ hσ),rfl⟩

theorem Spec.seq (h:Spec B P c Q K) (h':Spec B P' d Q' K')
    (hmid:∀ σ σ',P σ→ Q σ σ'→ P' σ')
    (hpost:∀ σ σ' σ'',P σ→ Q σ σ'→ Q' σ' σ''→ R σ σ''):
    Spec B P (.seq c d) R (K + K'):=by
  intro σ hσ
  obtain ⟨σ',hr,hq⟩:=h σ hσ
  obtain ⟨σ'',hr',hq'⟩:=h' σ' (hmid σ σ' hσ hq)
  exact ⟨σ'',hr.seq hr',hpost σ σ' σ'' hσ hq hq'⟩

theorem Spec.while_potential {b:Cond} (I:Env→ Prop) (Φ:Env→ ℕ)
    (hdef:∀ σ,I σ→ ∃ v,b.evalB B σ=some v)
    (hstep:∀ σ,I σ→ b.evalB B σ=some true→
      ∃ σ' K,Run B c σ σ' K∧ I σ'∧ 1 + b.size + K + Φ σ'≤ Φ σ)
    (hPI:∀ σ,P σ→ I σ) (hK:∀ σ,P σ→ Φ σ + 1 + b.size≤ K):
    Spec B P (.while b c) (fun _ σ' => I σ'∧ b.evalB B σ'=some false) K:=by
  intro σ hσ
  obtain ⟨σ',K₀,hr,hI,hfalse,hpay⟩:=Run.while_potential I Φ hdef hstep (hPI σ hσ)
  exact ⟨σ',hr.mono (by have:=hK σ hσ; omega),hI,hfalse⟩

theorem lt_of_condLt_true {B:ℕ} {x y:String} {ρ:Env}
    (h:(Cond.lt (.var x) (.var y)).evalB B ρ=some true):ρ.vars x < ρ.vars y:=by
  simp only [evalB_condLt_iff,evalB_var_iff] at h
  obtain ⟨a,b, ⟨rfl, -⟩, ⟨rfl, -⟩,hr⟩:=h
  simpa using hr.symm

theorem le_of_condLt_false {B:ℕ} {x y:String} {ρ:Env}
    (h:(Cond.lt (.var x) (.var y)).evalB B ρ=some false):ρ.vars y≤ ρ.vars x:=by
  simp only [evalB_condLt_iff,evalB_var_iff] at h
  obtain ⟨a,b, ⟨rfl, -⟩, ⟨rfl, -⟩,hr⟩:=h
  have:=hr.symm
  simp only [decide_eq_false_iff_not,not_lt] at this
  exact this

theorem Spec.forRange (x m:String) (I:Env→ Prop) (N Kb K:ℕ)
    (hxB:∀ σ,I σ→ σ.vars x < B) (hmB:∀ σ,I σ→ σ.vars m < B)
    (hm:∀ σ,I σ→ σ.vars m=N) (hxN:∀ σ,I σ→ σ.vars x≤ N)
    (hbody:Spec B (fun σ => I σ∧ σ.vars x < N) c
      (fun σ σ' => I σ'∧ σ'.vars x=σ.vars x + 1) Kb)
    (hPI:∀ σ,P σ→ I σ) (hK:∀ σ,P σ→ (Kb + 4) * (N - σ.vars x) + 4≤ K):
    Spec B P (.while (.lt (.var x) (.var m)) c) (fun _ σ' => I σ'∧ σ'.vars x=N) K:=by
  have hsize:(Cond.lt (Expr.var x) (Expr.var m)).size=3:=by simp
  refine ((Spec.while_potential (b:=.lt (.var x) (.var m)) (c:=c) I
    (fun σ => (Kb + 4) * (N - σ.vars x))
    (fun σ hI => evalB_condLt_vars (hxB σ hI) (hmB σ hI)) ?_ hPI ?_).post ?_)
  · intro σ hI hv
    have hlt:σ.vars x < N:=by
      have:=lt_of_condLt_true hv
      rw [hm σ hI] at this
      exact this
    obtain ⟨σ',hr,hI',hx'⟩:=hbody σ ⟨hI,hlt⟩
    refine ⟨σ',Kb,hr,hI', ?_⟩
    show 1 + 3 + Kb + (Kb + 4) * (N - σ'.vars x)≤ (Kb + 4) * (N - σ.vars x)
    have hdrop:N - σ'.vars x + 1=N - σ.vars x:=by rw [hx']; omega
    exact le_of_eq (by rw [← hdrop]; ring)
  · intro σ hσ
    show (Kb + 4) * (N - σ.vars x) + 1 + 3≤ K
    have h:=hK σ hσ
    have hre:(Kb + 4) * (N - σ.vars x) + 1 + 3=(Kb + 4) * (N - σ.vars x) + 4:=by ring
    rw [hre]
    exact h
  · intro σ σ' _ hq
    refine ⟨hq.1, ?_⟩
    have:=le_of_condLt_false hq.2
    have h₁:=hm σ' hq.1
    have h₂:=hxN σ' hq.1
    omega

theorem Spec.forRangeZero (x m:String) (I:Env→ Prop) (N Kb:ℕ) (hNB:N < B)
    (hxN:∀ σ,I σ→ σ.vars x≤ N) (hm:∀ σ,I σ→ σ.vars m=N)
    (hbody:Spec B (fun σ => I σ∧ σ.vars x < N) c
      (fun σ σ' => I σ'∧ σ'.vars x=σ.vars x + 1) Kb):
    Spec B (fun σ => I (σ.setVar x 0))
      (.seq (.assign x (.lit 0)) (.while (.lt (.var x) (.var m)) c))
      (fun _ σ' => I σ'∧ σ'.vars x=N) ((Kb + 4) * N + 6):=by
  intro σ hσ
  obtain ⟨σ',hrun,hI',hxN'⟩:=
    (Spec.forRange x m I N Kb ((Kb + 4) * N + 4)
      (fun _ hτ => lt_of_le_of_lt (hxN _ hτ) hNB) (fun _ hτ => hm _ hτ ▸ hNB) hm hxN hbody
      (fun _ h => h)
      (fun _ _ => Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) 4)).run hσ
  exact ⟨σ', (Run.seq (Run.assign (v:=0) (by simp; omega)) hrun).mono (by simp; omega),
    hI',hxN'⟩

end Lax808846Proofs.Reasoning

end

section

namespace Lax808846Proofs.Reasoning

open Lax808846Proofs.Imp

namespace RunStep

theorem eval_lit (B n:ℕ) (σ:Env) (h:n < B):
    (Expr.lit n).evalB B σ=some n:=evalB_lit h

theorem eval_var (B:ℕ) (σ:Env) (x:String) (h:σ.vars x < B):
    (Expr.var x).evalB B σ=some (σ.vars x):=evalB_var h

theorem eval_get (B:ℕ) (σ:Env) (a:String) (i:Expr) (k:ℕ)
    (hi:i.evalB B σ=some k) (hk:k < (σ.arrs a).length)
    (h:(σ.arrs a).getD k 0 < B):
    (Expr.get a i).evalB B σ=some ((σ.arrs a).getD k 0):=by
  refine evalB_get hi ?_ h
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hk]
  rfl

theorem eval_add (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:m + n < B):
    (Expr.bin .add e f).evalB B σ=some (m + n):=evalB_bin he hf h

theorem eval_mul (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:m * n < B):
    (Expr.bin .mul e f).evalB B σ=some (m * n):=evalB_bin he hf h

theorem cond_eq_true (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:m=n):
    (Cond.eq e f).evalB B σ=some true:=by
  rw [evalB_condEq he hf,h]; simp

theorem cond_eq_false (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:¬ m=n):
    (Cond.eq e f).evalB B σ=some false:=by
  rw [evalB_condEq he hf]; simp [h]

theorem skip (B:ℕ) (σ:Env):Run B .skip σ σ 1:=Run.skip

theorem assign (B:ℕ) (σ:Env) (x:String) (e:Expr) (v:ℕ)
    (h:e.evalB B σ=some v):
    Run B (.assign x e) σ (σ.setVar x v) (1 + e.size):=Run.assign h

theorem store (B:ℕ) (σ:Env) (a:String) (i e:Expr) (idx v:ℕ)
    (hi:i.evalB B σ=some idx) (he:e.evalB B σ=some v)
    (hidx:idx < (σ.arrs a).length):
    Run B (.store a i e) σ (σ.setArr a idx v) (1 + i.size + e.size):=Run.store hi he hidx

theorem read (B:ℕ) (σ:Env) (x:String) (h:σ.inp ≠ []):
    Run B (.read x) σ { σ.setVar x (σ.inp.headD 0) with inp:=σ.inp.tail } 1:=by
  refine Run.read (v:=σ.inp.headD 0) (rest:=σ.inp.tail) ?_
  cases hl:σ.inp with
  | nil => exact absurd hl h
  | cons v rest => simp

theorem write (B:ℕ) (σ:Env) (e:Expr) (v:ℕ) (h:e.evalB B σ=some v):
    Run B (.write e) σ { σ with out:=σ.out ++ [v] } (1 + e.size):=Run.write h

theorem seq (B:ℕ) (c d:Com) (σ σ' σ'':Env) (K K':ℕ)
    (h:Run B c σ σ' K) (h':Run B d σ' σ'' K'):
    Run B (.seq c d) σ σ'' (K + K'):=h.seq h'

inductive SeqSplit:Com→ Com→ Com→ Prop

  | one (a r:Com):SeqSplit a r (.seq a r)

  | cons (a p r w:Com) (h:SeqSplit p r w):SeqSplit (.seq a p) r (.seq a w)

theorem ite_true (B:ℕ) (b:Cond) (c d:Com) (σ σ':Env) (K:ℕ)
    (hb:b.evalB B σ=some true) (h:Run B c σ σ' K):
    Run B (.ite b c d) σ σ' (1 + b.size + K):=Run.ite_true hb h

theorem ite_false (B:ℕ) (b:Cond) (c d:Com) (σ σ':Env) (K:ℕ)
    (hb:b.evalB B σ=some false) (h:Run B d σ σ' K):
    Run B (.ite b c d) σ σ' (1 + b.size + K):=Run.ite_false hb h

theorem mono (B:ℕ) (c:Com) (σ σ':Env) (K K':ℕ)
    (h:Run B c σ σ' K) (hK:K≤ K'):Run B c σ σ' K':=h.mono hK

theorem use (B:ℕ) (P:Env→ Prop) (c:Com) (Q:Env→ Env→ Prop) (K:ℕ)
    (h:Spec B P c Q K) (σ:Env) (hσ:P σ):∃ σ',Run B c σ σ' K∧ Q σ σ':=h σ hσ

end RunStep

end Lax808846Proofs.Reasoning
end

section

namespace Lax109476Proofs.RamRational

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamArithmetic

def FractionOutput (q:ℚ) (σ:Env):Prop:=
  fractionValue (σ.vars "rat.s") (σ.vars "rat.n") (σ.vars "rat.d")=q∧
    σ.vars "rat.n"=q.num.natAbs∧ σ.vars "rat.d"=q.den∧ σ.vars "rat.s" ≤ 1

end Lax109476Proofs.RamRational

end

section

open scoped BigOperators

namespace Lax109476Proofs.RationalArithmeticBounds

open RationalSizeBounds
open Lax109476.RationalEncoding Lax759944.BinaryWordEncoding

theorem height_encoding (q:ℚ) (B:ℕ) (hq:Height q B):
    bitSize (encodeRational q)≤ 4 + 2 * B.size:=by
  have hn:=Nat.size_le_size hq.1
  have hd:=Nat.size_le_size hq.2
  have he:=EncodingSize.rational_size_upper q
  omega

end Lax109476Proofs.RationalArithmeticBounds

end

section

namespace Lax109476Proofs.RamEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational
open Lax109476.RationalEncoding

theorem fractionValue_sign (s n d:ℕ) (hs:s≤ 1) (hd:0 < d):
    (if (fractionValue s n d).num < 0 then 1 else 0:ℕ) =
      if n=0 then 0 else s:=by
  have hscases:s=0∨ s=1:=by omega
  rcases hscases with rfl | rfl
  · have hq:0≤ fractionValue 0 n d:=by change (0:ℚ)≤ (n:ℚ) / d; positivity
    have hnum:=Rat.num_nonneg.mpr hq
    simp [not_lt.mpr hnum]
  · by_cases hz:n=0
    · simp [fractionValue,hz]
    · have hq:fractionValue 1 n d < 0:=by
        change -(n:ℚ) / d < 0
        have hp:(0:ℚ) < (n:ℚ) / d:=by positivity
        rw [neg_div]
        linarith
      have hnum:(fractionValue 1 n d).num < 0:=by
        rw [← not_le,Rat.num_nonneg]
        exact not_le_of_gt hq
      simp [hz,hnum]

end Lax109476Proofs.RamEncoding

end

section

namespace Lax109476Proofs.RamRationalArrays

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational

theorem rationalSign_le_one (q:ℚ):rationalSign q≤ 1:=by unfold rationalSign; split_ifs <;> omega

theorem canonical_fractionValue (q:ℚ):
    fractionValue (rationalSign q) q.num.natAbs q.den=q:=by
  calc
    _=(q.num:ℚ) / q.den:=by
      by_cases h:q.num < 0
      · have hq:(q.num:ℚ) < 0:=by exact_mod_cast h
        simp [fractionValue,rationalSign,h,Nat.cast_natAbs,Int.cast_abs,abs_of_neg hq]
      · have hq:(0:ℚ)≤ q.num:=by exact_mod_cast le_of_not_gt h
        simp [fractionValue,rationalSign,h,Nat.cast_natAbs,Int.cast_abs,abs_of_nonneg hq]
    _=q:=q.num_div_den

def LeftOutput (q:ℚ) (σ:Env):Prop:=
  σ.vars "left.s"=rationalSign q∧ σ.vars "left.n"=q.num.natAbs∧ σ.vars "left.d"=q.den

theorem map_getD {α:Type*} (f:α→ ℕ) (xs:List α) (i:ℕ) (hi:i < xs.length):
    (xs.map f).getD i 0=f xs[i]:=by
  simp [List.getD_eq_getElem?_getD,hi]

theorem loadLeft_spec (B:ℕ) (a:String) (qs:List ℚ) (i:ℕ) (hi:i < qs.length)
    (hB:1 < B) (hiB:i < B) (hn:qs[i].num.natAbs < B) (hd:qs[i].den < B):
    Spec B (fun σ => Represents a qs σ∧ σ.vars "vec.i"=i) (loadLeft a)
      (fun _ τ => LeftOutput qs[i] τ) 9:=by
  rintro σ ⟨⟨hσs,hσn,hσd⟩,hσi⟩
  have hsB:=(rationalSign_le_one qs[i]).trans_lt hB
  have hsl:i < (σ.arrs (a ++ ".s")).length:=by rw [hσs,List.length_map]; exact hi
  have hnl:i < (σ.arrs (a ++ ".n")).length:=by rw [hσn,List.length_map]; exact hi
  have hdl:i < (σ.arrs (a ++ ".d")).length:=by rw [hσd,List.length_map]; exact hi
  have hsg:(σ.arrs (a ++ ".s")).getD i 0=rationalSign qs[i]:=by
    rw [hσs]; exact map_getD _ _ _ hi
  have hng:(σ.arrs (a ++ ".n")).getD i 0=qs[i].num.natAbs:=by
    rw [hσn]; exact map_getD _ _ _ hi
  have hdg:(σ.arrs (a ++ ".d")).getD i 0=qs[i].den:=by
    rw [hσd]; exact map_getD _ _ _ hi
  (expose_names;
    (refine let vcgPost0:Nat.lt (@List.getD Nat (Env.arrs σ (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".s")) (Env.vars σ "vec.i") ((0:Nat))) B:= ?_; let vcgPost1:Nat.lt (@List.getD Nat (Env.arrs (Env.setVar σ "left.s" (@List.getD Nat (Env.arrs σ (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".s")) (Env.vars σ "vec.i") ((0:Nat)))) (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".n")) (Env.vars (Env.setVar σ "left.s" (@List.getD Nat (Env.arrs σ (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".s")) (Env.vars σ "vec.i") ((0:Nat)))) "vec.i") ((0:Nat))) B:= ?_; let vcgPost2:Nat.lt (@List.getD Nat (Env.arrs (Env.setVar (Env.setVar σ "left.s" (@List.getD Nat (Env.arrs σ (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".s")) (Env.vars σ "vec.i") ((0:Nat)))) "left.n" (@List.getD Nat (Env.arrs (Env.setVar σ "left.s" (@List.getD Nat (Env.arrs σ (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".s")) (Env.vars σ "vec.i") ((0:Nat)))) (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".n")) (Env.vars (Env.setVar σ "left.s" (@List.getD Nat (Env.arrs σ (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".s")) (Env.vars σ "vec.i") ((0:Nat)))) "vec.i") ((0:Nat)))) (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".d")) (Env.vars (Env.setVar (Env.setVar σ "left.s" (@List.getD Nat (Env.arrs σ (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".s")) (Env.vars σ "vec.i") ((0:Nat)))) "left.n" (@List.getD Nat (Env.arrs (Env.setVar σ "left.s" (@List.getD Nat (Env.arrs σ (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".s")) (Env.vars σ "vec.i") ((0:Nat)))) (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".n")) (Env.vars (Env.setVar σ "left.s" (@List.getD Nat (Env.arrs σ (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".s")) (Env.vars σ "vec.i") ((0:Nat)))) "vec.i") ((0:Nat)))) "vec.i") ((0:Nat))) B:= ?_; let vcgPost3:LeftOutput (@getElem (List Rat) Nat Rat (fun (as:List Rat) (i_1:Nat) => Nat.lt i_1 (@List.length Rat as)) (@List.instGetElemNatLtLength Rat) qs i hi) (Env.setVar (Env.setVar (Env.setVar σ "left.s" (@List.getD Nat (Env.arrs σ (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".s")) (Env.vars σ "vec.i") ((0:Nat)))) "left.n" (@List.getD Nat (Env.arrs (Env.setVar σ "left.s" (@List.getD Nat (Env.arrs σ (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".s")) (Env.vars σ "vec.i") ((0:Nat)))) (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".n")) (Env.vars (Env.setVar σ "left.s" (@List.getD Nat (Env.arrs σ (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".s")) (Env.vars σ "vec.i") ((0:Nat)))) "vec.i") ((0:Nat)))) "left.d" (@List.getD Nat (Env.arrs (Env.setVar (Env.setVar σ "left.s" (@List.getD Nat (Env.arrs σ (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".s")) (Env.vars σ "vec.i") ((0:Nat)))) "left.n" (@List.getD Nat (Env.arrs (Env.setVar σ "left.s" (@List.getD Nat (Env.arrs σ (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".s")) (Env.vars σ "vec.i") ((0:Nat)))) (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".n")) (Env.vars (Env.setVar σ "left.s" (@List.getD Nat (Env.arrs σ (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".s")) (Env.vars σ "vec.i") ((0:Nat)))) "vec.i") ((0:Nat)))) (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".d")) (Env.vars (Env.setVar (Env.setVar σ "left.s" (@List.getD Nat (Env.arrs σ (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".s")) (Env.vars σ "vec.i") ((0:Nat)))) "left.n" (@List.getD Nat (Env.arrs (Env.setVar σ "left.s" (@List.getD Nat (Env.arrs σ (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".s")) (Env.vars σ "vec.i") ((0:Nat)))) (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".n")) (Env.vars (Env.setVar σ "left.s" (@List.getD Nat (Env.arrs σ (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".s")) (Env.vars σ "vec.i") ((0:Nat)))) "vec.i") ((0:Nat)))) "vec.i") ((0:Nat)))):= ?_; let c0:Env→ Prop:=(fun (x τ:Env) => LeftOutput (@getElem (List Rat) Nat Rat (fun (as:List Rat) (i_1:Nat) => Nat.lt i_1 (@List.length Rat as)) (@List.instGetElemNatLtLength Rat) qs i hi) τ) σ; let c1:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a; let c2:String:=c1 ".s"; let c3:Nat:= @List.getD Nat (Env.arrs σ c2) (Env.vars σ "vec.i") ((0:Nat)); let c4:Env:=Env.setVar σ "left.s" c3; let c5:String:=c1 ".n"; let c6:Nat:=Env.vars c4 "vec.i"; let c7:Nat:= @List.getD Nat (Env.arrs c4 c5) c6 ((0:Nat)); let c8:Env:=Env.setVar c4 "left.n" c7; let c9:String:=c1 ".d"; let c10:Nat:=Env.vars c8 "vec.i"; let c11:Nat:= @List.getD Nat (Env.arrs c8 c9) c10 ((0:Nat)); let c12:Env:=Env.setVar c8 "left.d" c11; let c13:Nat→ Nat→ Nat:=Nat.add; let c14:Nat→ Nat:=c13 ((1:Nat)); let c15:Expr:=Expr.get c2 (Expr.var "vec.i"); let c16:Nat:=c14 (Expr.size c15); let c17:Expr:=Expr.get c5 (Expr.var "vec.i"); let c18:Nat:=c14 (Expr.size c17); let c19:Expr:=Expr.get c9 (Expr.var "vec.i"); let c20:Nat:=c14 (Expr.size c19); let c21:Nat:=c13 c18 c20; let c22:Com:=Com.assign "left.n" c17; let c23:Com:=Com.assign "left.d" c19; @Exists.intro Env (fun (σ':Env) => And (Run B (loadLeft a) σ σ' ((9:Nat))) (c0 σ')) c12 (@And.intro (Run B (loadLeft a) σ c12 ((9:Nat))) (c0 c12) (RunStep.mono B (loadLeft a) σ c12 (c13 c16 c21) ((9:Nat)) (RunStep.seq B (Com.assign "left.s" c15) (Com.seq c22 c23) σ c4 c12 c16 c21 (RunStep.assign B σ "left.s" c15 c3 (RunStep.eval_get B σ c2 (Expr.var "vec.i") (Env.vars σ "vec.i") (RunStep.eval_var B σ "vec.i" (?nAX_g3955_0_0_0)) (?nAX_g3955_0_0_1) vcgPost0)) (RunStep.seq B c22 c23 c4 c8 c12 c18 c20 (RunStep.assign B c4 "left.n" c17 c7 (RunStep.eval_get B c4 c5 (Expr.var "vec.i") c6 (RunStep.eval_var B c4 "vec.i" (?nAX_g3955_0_0_2)) (?nAX_g3955_0_0_3) vcgPost1)) (RunStep.assign B c8 "left.d" c19 c11 (RunStep.eval_get B c8 c9 (Expr.var "vec.i") c10 (RunStep.eval_var B c8 "vec.i" (?nAX_g3955_0_0_4)) (?nAX_g3955_0_0_5) vcgPost2)))) (?nAX_g3955_0_0_6)) vcgPost3) <;> try dsimp +zetaDelta at *); (all_goals try clear_value vcgPost0); (all_goals try clear_value vcgPost1); (all_goals try clear_value vcgPost2); (all_goals try clear_value vcgPost3); (all_goals try clear vcgPost3); (all_goals try clear vcgPost2); (all_goals try clear vcgPost1); (all_goals try clear vcgPost0); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g3955_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3955_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3955_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3955_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3955_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3955_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3955_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals intros))
  all_goals simp_all [LeftOutput]

theorem storeReduced_spec (B:ℕ) (a:String) (qs:List ℚ) (q:ℚ) (i:ℕ)
    (hi:i < qs.length) (hB:1 < B) (hiB:i < B)
    (hn:q.num.natAbs < B) (hd:q.den < B):
    Spec B (fun σ => Represents a qs σ∧ σ.vars "vec.i"=i∧ FractionOutput q σ)
      (storeReduced a) (fun _ τ => Represents a (qs.set i q) τ) 13:=by
  rintro σ ⟨⟨hσs,hσn,hσd⟩,hσi,hv,hratn,hratd,hrats⟩
  have hnB:σ.vars "rat.n" < B:=hratn ▸ hn
  have hdB:σ.vars "rat.d" < B:=hratd ▸ hd
  have hsB:σ.vars "rat.s" < B:=hrats.trans_lt hB
  have hsl:i < (σ.arrs (a ++ ".s")).length:=by rw [hσs,List.length_map]; exact hi
  have hnl:i < (σ.arrs (a ++ ".n")).length:=by rw [hσn,List.length_map]; exact hi
  have hdl:i < (σ.arrs (a ++ ".d")).length:=by rw [hσd,List.length_map]; exact hi
  have hsn:a ++ ".s" ≠ a ++ ".n" :=by simp
  have hsd:a ++ ".s" ≠ a ++ ".d" :=by simp
  have hnd:a ++ ".n" ≠ a ++ ".d" :=by simp
  have hns:=Ne.symm hsn
  have hds:=Ne.symm hsd
  have hdn:=Ne.symm hnd
  have hsign:=RamEncoding.fractionValue_sign (σ.vars "rat.s") (σ.vars "rat.n")
    (σ.vars "rat.d") hrats (hratd ▸ q.den_pos)
  rw [hv] at hsign
  change rationalSign q=_ at hsign
  (expose_names;
    (refine let vcgPost0:@Eq Nat (Env.vars σ "rat.n") ((0:Nat))→ Represents a (@List.set Rat qs i q) (Env.setArr (Env.setArr (Env.setArr σ (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".s") (Env.vars σ "vec.i") ((0:Nat))) (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".n") (Env.vars (Env.setArr σ (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".s") (Env.vars σ "vec.i") ((0:Nat))) "vec.i") (Env.vars (Env.setArr σ (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".s") (Env.vars σ "vec.i") ((0:Nat))) "rat.n")) (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".d") (Env.vars (Env.setArr (Env.setArr σ (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".s") (Env.vars σ "vec.i") ((0:Nat))) (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".n") (Env.vars (Env.setArr σ (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".s") (Env.vars σ "vec.i") ((0:Nat))) "vec.i") (Env.vars (Env.setArr σ (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".s") (Env.vars σ "vec.i") ((0:Nat))) "rat.n")) "vec.i") (Env.vars (Env.setArr (Env.setArr σ (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".s") (Env.vars σ "vec.i") ((0:Nat))) (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".n") (Env.vars (Env.setArr σ (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".s") (Env.vars σ "vec.i") ((0:Nat))) "vec.i") (Env.vars (Env.setArr σ (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".s") (Env.vars σ "vec.i") ((0:Nat))) "rat.n")) "rat.d")):= ?_; let vcgPost1:Not (@Eq Nat (Env.vars σ "rat.n") ((0:Nat)))→ Represents a (@List.set Rat qs i q) (Env.setArr (Env.setArr (Env.setArr σ (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".s") (Env.vars σ "vec.i") (Env.vars σ "rat.s")) (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".n") (Env.vars (Env.setArr σ (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".s") (Env.vars σ "vec.i") (Env.vars σ "rat.s")) "vec.i") (Env.vars (Env.setArr σ (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".s") (Env.vars σ "vec.i") (Env.vars σ "rat.s")) "rat.n")) (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".d") (Env.vars (Env.setArr (Env.setArr σ (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".s") (Env.vars σ "vec.i") (Env.vars σ "rat.s")) (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".n") (Env.vars (Env.setArr σ (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".s") (Env.vars σ "vec.i") (Env.vars σ "rat.s")) "vec.i") (Env.vars (Env.setArr σ (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".s") (Env.vars σ "vec.i") (Env.vars σ "rat.s")) "rat.n")) "vec.i") (Env.vars (Env.setArr (Env.setArr σ (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".s") (Env.vars σ "vec.i") (Env.vars σ "rat.s")) (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".n") (Env.vars (Env.setArr σ (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".s") (Env.vars σ "vec.i") (Env.vars σ "rat.s")) "vec.i") (Env.vars (Env.setArr σ (@HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".s") (Env.vars σ "vec.i") (Env.vars σ "rat.s")) "rat.n")) "rat.d")):= ?_; let c0:Prop:= @Eq Nat (Env.vars σ "rat.n") ((0:Nat)); let c1:Prop:=Not c0; let c2:Env→ Prop:=(fun (x τ:Env) => Represents a (@List.set Rat qs i q) τ) σ; let c3:Env→ Prop:=fun (σ':Env) => And (Run B (storeReduced a) σ σ' ((13:Nat))) (c2 σ'); let c4:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a; let c5:String:=c4 ".s"; let c6:Nat→ Env:=Env.setArr σ c5 (Env.vars σ "vec.i"); let c7:Env:=c6 ((0:Nat)); let c8:String:=c4 ".n"; let c9:String→ Nat:=Env.vars c7; let c10:Nat:=c9 "vec.i"; let c11:Nat:=c9 "rat.n"; let c12:Env:=Env.setArr c7 c8 c10 c11; let c13:String:=c4 ".d"; let c14:String→ Nat:=Env.vars c12; let c15:Nat:=c14 "vec.i"; let c16:Nat:=c14 "rat.d"; let c17:Env:=Env.setArr c12 c13 c15 c16; let c18:Nat→ Nat→ Nat:=Nat.add; let c19:Nat→ Nat:=c18 ((1:Nat)); let c20:Cond:=Cond.eq (Expr.var "rat.n") (Expr.lit ((0:Nat))); let c21:Nat→ Nat:=c18 (c19 (Cond.size c20)); let c22:Nat→ Nat:=c18 (c19 (Expr.size (Expr.var "vec.i"))); let c23:Nat:=c22 (Expr.size (Expr.lit ((0:Nat)))); let c24:Nat:=c21 c23; let c25:Nat:=c22 (Expr.size (Expr.var "rat.n")); let c26:Nat:=c22 (Expr.size (Expr.var "rat.d")); let c27:Nat:=c18 c25 c26; let c28:Expr→ Com:=Com.store c5 (Expr.var "vec.i"); let c29:Com:=c28 (Expr.lit ((0:Nat))); let c30:Com:=c28 (Expr.var "rat.s"); let c31:Com:=Com.store c8 (Expr.var "vec.i") (Expr.var "rat.n"); let c32:Com:=Com.store c13 (Expr.var "vec.i") (Expr.var "rat.d"); let c33:Env:=c6 (Env.vars σ "rat.s"); let c34:String→ Nat:=Env.vars c33; let c35:Nat:=c34 "vec.i"; let c36:Nat:=c34 "rat.n"; let c37:Env:=Env.setArr c33 c8 c35 c36; let c38:String→ Nat:=Env.vars c37; let c39:Nat:=c38 "vec.i"; let c40:Nat:=c38 "rat.d"; let c41:Env:=Env.setArr c37 c13 c39 c40; let c42:Nat:=c22 (Expr.size (Expr.var "rat.s")); let c43:Nat:=c21 c42; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c3) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c3 c17 (@And.intro (Run B (storeReduced a) σ c17 ((13:Nat))) (c2 c17) (RunStep.mono B (storeReduced a) σ c17 (c18 c24 c27) ((13:Nat)) (RunStep.seq B (Com.ite c20 c29 c30) (Com.seq c31 c32) σ c7 c17 c24 c27 (RunStep.ite_true B c20 c29 c30 σ c7 c23 (RunStep.cond_eq_true B σ (Expr.var "rat.n") (Expr.lit ((0:Nat))) (Env.vars σ "rat.n") ((0:Nat)) (RunStep.eval_var B σ "rat.n" hnB) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g3962_0_0_0)) hcase) (RunStep.store B σ c5 (Expr.var "vec.i") (Expr.lit ((0:Nat))) (Env.vars σ "vec.i") ((0:Nat)) (RunStep.eval_var B σ "vec.i" (?nAX_g3962_0_0_1)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g3962_0_0_2)) (?nAX_g3962_0_0_3))) (RunStep.seq B c31 c32 c7 c12 c17 c25 c26 (RunStep.store B c7 c8 (Expr.var "vec.i") (Expr.var "rat.n") c10 c11 (RunStep.eval_var B c7 "vec.i" (?nAX_g3962_0_0_4)) (RunStep.eval_var B c7 "rat.n" (?nAX_g3962_0_0_5)) (?nAX_g3962_0_0_6)) (RunStep.store B c12 c13 (Expr.var "vec.i") (Expr.var "rat.d") c15 c16 (RunStep.eval_var B c12 "vec.i" (?nAX_g3962_0_0_7)) (RunStep.eval_var B c12 "rat.d" (?nAX_g3962_0_0_8)) (?nAX_g3962_0_0_9)))) (?nAX_g3962_0_0_10)) (vcgPost0 hcase))) fun (hcase:c1) => @Exists.intro Env c3 c41 (@And.intro (Run B (storeReduced a) σ c41 ((13:Nat))) (c2 c41) (RunStep.mono B (storeReduced a) σ c41 (c18 c43 c27) ((13:Nat)) (RunStep.seq B (Com.ite c20 c29 c30) (Com.seq c31 c32) σ c33 c41 c43 c27 (RunStep.ite_false B c20 c29 c30 σ c33 c42 (RunStep.cond_eq_false B σ (Expr.var "rat.n") (Expr.lit ((0:Nat))) (Env.vars σ "rat.n") ((0:Nat)) (RunStep.eval_var B σ "rat.n" hnB) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g3962_0_0_11)) hcase) (RunStep.store B σ c5 (Expr.var "vec.i") (Expr.var "rat.s") (Env.vars σ "vec.i") (Env.vars σ "rat.s") (RunStep.eval_var B σ "vec.i" (?nAX_g3962_0_0_12)) (RunStep.eval_var B σ "rat.s" hsB) (?nAX_g3962_0_0_13))) (RunStep.seq B c31 c32 c33 c37 c41 c25 c26 (RunStep.store B c33 c8 (Expr.var "vec.i") (Expr.var "rat.n") c35 c36 (RunStep.eval_var B c33 "vec.i" (?nAX_g3962_0_0_14)) (RunStep.eval_var B c33 "rat.n" (?nAX_g3962_0_0_15)) (?nAX_g3962_0_0_16)) (RunStep.store B c37 c13 (Expr.var "vec.i") (Expr.var "rat.d") c39 c40 (RunStep.eval_var B c37 "vec.i" (?nAX_g3962_0_0_17)) (RunStep.eval_var B c37 "rat.d" (?nAX_g3962_0_0_18)) (?nAX_g3962_0_0_19)))) (?nAX_g3962_0_0_20)) (vcgPost1 hcase)) <;> try dsimp +zetaDelta at *); (all_goals try clear_value vcgPost0); (all_goals try clear_value vcgPost1); (all_goals try clear vcgPost1); (all_goals try clear vcgPost0); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g3962_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals intros))
  all_goals simp_all [Represents,Env.setArr,List.map_set]

end Lax109476Proofs.RamRationalArrays

end

section

namespace Lax109476Proofs.RamFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def FieldsAgree (fields:List String) (σ τ:Env):Prop:=
  ∀ x∈ fields,τ.vars x=σ.vars x

theorem spec_with_fields {B K:ℕ} {c:Com} {P:Env→ Prop} {Q:Env→ Env→ Prop}
    (fields:List String) (h:Spec B P c Q K)
    (hf:∀ x∈ fields,x∉ c.wvars) (ha:c.warrs=[]):
    Spec B P c (fun σ τ => Q σ τ∧ FieldsAgree fields σ τ∧ τ.arrs=σ.arrs) K:=by
  intro σ hσ
  obtain ⟨τ,hr,hτ⟩:=h σ hσ
  refine ⟨τ,hr,hτ,fun x hx => hr.frame_var x (hf x hx), ?_⟩
  funext a
  exact hr.frame_arr a (by simp [ha])

theorem spec_with_write_frame {B K:ℕ} {c:Com} {P:Env→ Prop} {Q:Env→ Env→ Prop}
    (fields:List String) (h:Spec B P c Q K)
    (hf:∀ x∈ fields,x∉ c.wvars):
    Spec B P c (fun σ τ => Q σ τ∧ FieldsAgree fields σ τ∧
      ∀ a∉ c.warrs,τ.arrs a=σ.arrs a) K:=by
  intro σ hσ
  obtain ⟨τ,hr,hτ⟩:=h σ hσ
  exact ⟨τ,hr,hτ,fun x hx => hr.frame_var x (hf x hx),
    fun a ha => hr.frame_arr a ha⟩

end Lax109476Proofs.RamFrame

end

section

namespace Lax808846Proofs.Reasoning.Lib

open Lax808846Proofs.Imp

def upd (f:ℕ→ ℕ) (k v:ℕ):ℕ→ ℕ:=fun i => if i=k then v else f i

@[simp] theorem upd_self (f:ℕ→ ℕ) (k v:ℕ):upd f k v k=v:=by simp [upd]

@[simp] theorem upd_of_ne {f:ℕ→ ℕ} {k i:ℕ} (v:ℕ) (h:i ≠ k):upd f k v i=f i:=by
  simp [upd,h]

theorem set_arrOf_eq_upd {n:ℕ} (f:ℕ→ ℕ) (k v:ℕ):
    (arrOf n f).set k v=arrOf n (upd f k v):=set_arrOf f v

open Lax808846.Ram

def runOut (w:ℕ):ℕ→ Program→ State→ ℕ→ Option (List ℕ × ℕ)
  | 0,p,s,k => if s.pc < p.length then none else some (s.out,k)
  | fuel + 1,p,s,k =>
      if s.pc < p.length then
        match step w p s with
        | none => some (s.out,k + 1)
        | some s' => runOut w fuel p s' (k + 1)
      else some (s.out,k)

end Lax808846Proofs.Reasoning.Lib

end

section

namespace Lax808846Proofs.Reasoning.Lib

open Lax808846Proofs.Imp

variable {B n i j k v:ℕ} {a b x y m:String} {g F:ℕ→ ℕ} {σ:Env}

def Fill (a x:String) (n i:ℕ) (g F:ℕ→ ℕ) (σ:Env):Prop:=
  σ.arrs a=arrOf n g∧ σ.vars x=i∧ i≤ n∧ ∀ j,j < i→ g j=F j

theorem Fill.arr (h:Fill a x n i g F σ):σ.arrs a=arrOf n g:=h.1

theorem Fill.counter (h:Fill a x n i g F σ):σ.vars x=i:=h.2.1

theorem Fill.le (h:Fill a x n i g F σ):i≤ n:=h.2.2.1

theorem Fill.cell (h:Fill a x n i g F σ) (hj:j < i):g j=F j:=h.2.2.2 j hj

theorem Fill.length (h:Fill a x n i g F σ):(σ.arrs a).length=n:=by
  rw [h.arr,length_arrOf]

@[simp] theorem Fill.setVar_iff (a x:String) (n i:ℕ) (g F:ℕ→ ℕ) (σ:Env)
    (y:String) (v:ℕ) (hy:y ≠ x):
    Fill a x n i g F (σ.setVar y v)↔ Fill a x n i g F σ:=by
  simp [Fill,Ne.symm hy]

theorem Fill.setVar (h:Fill a x n i g F σ) (hy:y ≠ x) (v:ℕ):
    Fill a x n i g F (σ.setVar y v):=
  (Fill.setVar_iff a x n i g F σ y v hy).2 h

theorem Fill.setCell (h:Fill a x n i g F σ) (v:ℕ):
    Fill a x n i (upd g i v) F (σ.setArr a i v):=
  ⟨by rw [arrs_setArr,if_pos rfl,h.arr,set_arrOf_eq_upd],by rw [vars_setArr,h.counter],
   h.2.2.1,fun j hj => by rw [upd_of_ne _ (by omega)]; exact h.cell hj⟩

theorem Fill.bump (h:Fill a x n i g F σ) (hin:i < n) (hgi:g i=F i):
    Fill a x n (i + 1) g F (σ.setVar x (i + 1)):=
  ⟨by rw [arrs_setVar,h.arr],by simp,hin,fun j hj => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact h.cell hj
    · exact hgi⟩

namespace Fill

def Below (a x:String) (n:ℕ) (F:ℕ→ ℕ) (σ:Env):Prop:=
  ∃ g,Fill a x n (σ.vars x) g F σ

theorem Below.le (h:Below a x n F σ):σ.vars x≤ n:=by
  obtain ⟨_,hf⟩:=h; exact hf.le

theorem Below.length (h:Below a x n F σ):(σ.arrs a).length=n:=by
  obtain ⟨_,hf⟩:=h; exact hf.length

theorem below_zero (h:σ.arrs a=arrOf n g) (hx:σ.vars x=0):Below a x n F σ:=
  ⟨g,h,rfl,by omega,fun j hj => absurd hj (by omega)⟩

theorem Below.done (h:Below a x n F σ) (hx:σ.vars x=n):
    ∃ g,σ.arrs a=arrOf n g∧ ∀ j,j < n→ g j=F j:=by
  obtain ⟨g,hf⟩:=h
  exact ⟨g,hf.arr,fun j hj => hf.cell (by omega)⟩

theorem Below.step (h:Below a x n F σ) (hlt:σ.vars x < n) (hv:v=F (σ.vars x)):
    Below a x n F ((σ.setArr a (σ.vars x) v).setVar x (σ.vars x + 1)):=by
  obtain ⟨g,hf⟩:=h
  refine ⟨upd g (σ.vars x) v, ?_⟩
  rw [show ((σ.setArr a (σ.vars x) v).setVar x (σ.vars x + 1)).vars x=σ.vars x + 1 by simp]
  exact (hf.setCell v).bump hlt (by simp [hv])

@[simp] theorem wvars_put (a x:String) (e:Expr):(put a x e).wvars=[x]:=by
  simp [put,Com.wvars]

abbrev PutPost (a x:String) (n:ℕ) (F:ℕ→ ℕ) (σ σ':Env):Prop:=
  Below a x n F σ'∧ σ'.vars x=σ.vars x + 1

theorem put_spec (B n:ℕ) (a x:String) (e:Expr) (F:ℕ→ ℕ) (P:Env→ Prop)
    (hP:∀ σ,P σ→ Below a x n F σ∧ σ.vars x < n) (hnB:n < B)
    (he:∀ σ,P σ→ e.evalB B σ=some (F (σ.vars x))):
    Spec B P (put a x e) (PutPost a x n F) (6 + e.size):=by
  intro σ hσ
  obtain ⟨hb,hlt⟩:=hP σ hσ
  obtain ⟨g,hf⟩:=hb
  refine ⟨_, (Run.seq (Run.store (idx:=σ.vars x) (v:=F (σ.vars x))
        (evalB_var (by omega)) (he σ hσ) (by rw [hf.length]; omega))
      (Run.assign (v:=σ.vars x + 1) ?_)).mono (by simp; omega), ?_,by simp⟩
  · rw [evalB_bin (evalB_var (by simp; omega)) (evalB_lit (by omega)) (by simp; omega)]
    simp [Bop.apply]
  · exact Below.step ⟨g,hf⟩ hlt rfl

theorem loop_spec (B n:ℕ) (a x m:String) (e:Expr) (F:ℕ→ ℕ)
    (hxm:x ≠ m) (hnB:n < B)
    (he:∀ σ,Below a x n F σ→ σ.vars m=n→ σ.vars x < n→
      e.evalB B σ=some (F (σ.vars x))):
    Spec B (fun σ => (∃ g,σ.arrs a=arrOf n g)∧ σ.vars m=n)
      (.seq (.assign x (.lit 0)) (.while (.lt (.var x) (.var m)) (put a x e)))
      (fun _ σ' => (∃ g,σ'.arrs a=arrOf n g∧ ∀ j,j < n→ g j=F j)∧ σ'.vars x=n)
      ((10 + e.size) * n + 6):=by
  have hbody:Spec B (fun σ => (Below a x n F σ∧ σ.vars m=n)∧ σ.vars x < n) (put a x e)
      (fun σ σ' => (Below a x n F σ'∧ σ'.vars m=n)∧ σ'.vars x=σ.vars x + 1)
      (6 + e.size):=
    ((put_spec B n a x e F _ (fun _ hσ => ⟨hσ.1.1,hσ.2⟩) hnB
      (fun _ hσ => he _ hσ.1.1 hσ.1.2 hσ.2)).frame).post
      (fun _ _ hσ hq => ⟨⟨hq.1.1,by rw [hq.2.1 m (by simp [Ne.symm hxm]),hσ.1.2]⟩,hq.1.2⟩)
  refine ((Spec.forRangeZero x m (fun σ => Below a x n F σ∧ σ.vars m=n) n (6 + e.size) hnB
    (fun _ hσ => hσ.1.le) (fun _ hσ => hσ.2) hbody).pre ?_).post ?_ |>.mono (by ring_nf; omega)
  · rintro σ ⟨⟨g,harr⟩,hm⟩
    exact ⟨below_zero (by rw [arrs_setVar]; exact harr) (by simp),by simp [Ne.symm hxm,hm]⟩
  · exact fun _ σ' _ hq => ⟨hq.1.1.done hq.2,hq.2⟩

namespace Demo

def demo (a x m:String):Com:=
  .seq (.assign x (.lit 0)) (.while (.lt (.var x) (.var m)) (put a x (.var x)))

def demoWatched (a x m:String):Com:=
  .seq (.assign m (.lit 3))
    (.seq (demo a x m)
      (.seq (.write (.get a (.lit 0)))
        (.seq (.write (.get a (.lit 1))) (.write (.get a (.lit 2))))))

def layout:Lax808846Proofs.Compile.Layout:= ⟨["i", "m"], ["ar"],2⟩

def prog:Lax808846.Ram.Program:=
  Lax808846Proofs.Compile.compileProgram layout (demoWatched "ar" "i" "m")

def demoRun:Option (List ℕ × ℕ):=runOut 16 1000 prog (Lax808846.Ram.initState []) 0

end Demo

end Fill

end Lax808846Proofs.Reasoning.Lib

end

section

namespace Lax109476Proofs.RamZeroArray

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays

theorem exists_arrOf (xs:List ℕ) (n:ℕ) (h:xs.length=n):∃ g,xs=arrOf n g:=by
  refine ⟨fun i => xs.getD i 0, ?_⟩
  apply List.ext_getElem
  · simp [h]
  · intro i hi hj
    simp [arrOf,List.getD_eq_getElem?_getD,hi]

theorem fillConstant_spec (B n v:ℕ) (a:String) (hnB:n < B) (hvB:v < B):
    Spec B (fun σ => (σ.arrs a).length=n∧ σ.vars "vec.n"=n) (fillConstant a v)
      (fun σ τ => τ.arrs a=List.replicate n v∧ τ.vars "vec.n"=n∧
        ∀ b ≠ a,τ.arrs b=σ.arrs b) (11 * n + 6):=by
  have hfill:=Lib.Fill.loop_spec B n a "vec.i" "vec.n" (.lit v) (fun _ => v)
    (by decide) hnB (by intros; exact evalB_lit hvB)
  intro σ hσ
  obtain ⟨τ,hr, ⟨g,hτg,hg⟩,_⟩:=hfill σ ⟨exists_arrOf _ _ hσ.1,hσ.2⟩
  refine ⟨τ,hr, ?_, ?_, ?_⟩
  · rw [hτg,replicate_eq_arrOf]
    exact arrOf_congr hg
  · exact (hr.frame_var "vec.n" (by simp [Lib.Fill.put,Com.wvars])).trans hσ.2
  · intro b hb
    exact hr.frame_arr b (by simp [Lib.Fill.put,Com.warrs,hb])

theorem zeroRationalArray_spec (B n:ℕ) (a:String) (hnB:n < B) (h1:1 < B):
    Spec B (fun σ => (σ.arrs (a ++ ".s")).length=n∧
        (σ.arrs (a ++ ".n")).length=n∧ (σ.arrs (a ++ ".d")).length=n∧ σ.vars "vec.n"=n)
      (zeroRationalArray a)
      (fun σ τ => Represents a (List.replicate n 0) τ∧ τ.vars "vec.n"=n∧
        ∀ b∉ [a ++ ".s",a ++ ".n",a ++ ".d"],τ.arrs b=σ.arrs b)
      (33 * n + 18):=by
  have h0:0 < B:=by omega
  have hsn:a ++ ".s" ≠ a ++ ".n" :=by simp
  have hsd:a ++ ".s" ≠ a ++ ".d" :=by simp
  have hnd:a ++ ".n" ≠ a ++ ".d" :=by simp
  rintro σ ⟨hσs,hσn,hσd,hσN⟩
  obtain ⟨τ,hr₁,hτs,hτN,hτa⟩:=fillConstant_spec B n 0 (a ++ ".s") hnB h0 σ ⟨hσs,hσN⟩
  have hτn:(τ.arrs (a ++ ".n")).length=n:=by rw [hτa _ hsn.symm]; exact hσn
  obtain ⟨υ,hr₂,hυn,hυN,hυa⟩:=fillConstant_spec B n 0 (a ++ ".n") hnB h0 τ ⟨hτn,hτN⟩
  have hυd:(υ.arrs (a ++ ".d")).length=n:=by
    rw [hυa _ hnd.symm,hτa _ hsd.symm]; exact hσd
  obtain ⟨ρ,hr₃,hρd,hρN,hρa⟩:=fillConstant_spec B n 1 (a ++ ".d") hnB h1 υ ⟨hυd,hυN⟩
  have hρs:ρ.arrs (a ++ ".s")=List.replicate n 0:=by rw [hρa _ hsd,hυa _ hsn,hτs]
  have hρn:ρ.arrs (a ++ ".n")=List.replicate n 0:=by rw [hρa _ hnd,hυn]
  refine ⟨ρ, (hr₁.seq (hr₂.seq hr₃)).mono (by omega), ?_,hρN, ?_⟩
  · simp [Represents,hρs,hρn,hρd,rationalSign]
  · intro b hb
    simp at hb
    exact (hρa b hb.2.2).trans ((hυa b hb.2.1).trans (hτa b hb.1))

end Lax109476Proofs.RamZeroArray

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RamCenterUpdate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFractionInterface RamFrame RationalArithmeticBounds
open RamCenterCoordinate RamZeroArray

def filled {n:ℕ} (v:Fin n→ ℚ) (k:ℕ):List ℚ:=
  List.ofFn (fun j => if j.val < k then v j else 0)

theorem filled_zero {n:ℕ} (v:Fin n→ ℚ):filled v 0=List.replicate n 0:=by simp [filled]

theorem filled_done {n:ℕ} (v:Fin n→ ℚ):filled v n=List.ofFn v:=by
  unfold filled
  congr 1
  funext j
  simp [j.isLt]

theorem filled_step {n:ℕ} (v:Fin n→ ℚ) (i:Fin n):
    (filled v i.val).set i.val (v i)=filled v (i.val + 1):=by
  apply List.ext_getElem
  · simp [filled]
  · intro k hk hk'
    have hkn:k < n:=by simpa [filled] using hk'
    rw [List.getElem_set]
    by_cases hki:i.val=k
    · have hfin:i=(⟨k,hkn⟩:Fin n):=Fin.ext hki
      simp [filled,hfin]
    · have hnext:k < i.val + 1↔ k < i.val:=by omega
      simp only [hki, ↓reduceIte,filled,List.getElem_ofFn]
      change (if k < i.val then v ⟨k,hkn⟩ else 0)=(if k < i.val + 1 then v ⟨k,hkn⟩ else 0)
      simp only [hnext]

end Lax109476Proofs.RamCenterUpdate

end

section

namespace Lax109476Proofs.RamCopy

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds

theorem disjoint_not_mem (a b s:String) (hab:Disjoint a b) (hs:s∈ suffixes):
    a ++ s∉ [b ++ ".s",b ++ ".n",b ++ ".d"]:=by
  intro h
  simp at h
  rcases h with h | h | h
  · exact hab s hs ".s" (by simp [suffixes]) h
  · exact hab s hs ".n" (by simp [suffixes]) h
  · exact hab s hs ".d" (by simp [suffixes]) h

def loopFields:List String:= ["copy.i", "vec.i", "vec.n"]

theorem leftToResult_spec (B:ℕ) (q:ℚ) (h1:1 < B)
    (hn:q.num.natAbs < B) (hd:q.den < B):
    Spec B (LeftOutput q) leftToResult (fun _ τ => FractionOutput q τ) 6:=by
  rintro σ ⟨hσs,hσn,hσd⟩
  have hs:σ.vars "left.s" < B:=hσs ▸ (rationalSign_le_one q).trans_lt h1
  (expose_names;
    (refine let vcgPost0:FractionOutput q (Env.setVar (Env.setVar (Env.setVar σ "rat.s" (Env.vars σ "left.s")) "rat.n" (Env.vars (Env.setVar σ "rat.s" (Env.vars σ "left.s")) "left.n")) "rat.d" (Env.vars (Env.setVar (Env.setVar σ "rat.s" (Env.vars σ "left.s")) "rat.n" (Env.vars (Env.setVar σ "rat.s" (Env.vars σ "left.s")) "left.n")) "left.d")):= ?_; let c0:Nat:=Env.vars (Env.setVar σ "rat.s" (Env.vars σ "left.s")) "left.n"; let c1:Env:=Env.setVar (Env.setVar σ "rat.s" (Env.vars σ "left.s")) "rat.n" c0; let c2:Nat:=Env.vars c1 "left.d"; let c3:Env:=Env.setVar c1 "rat.d" c2; let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat→ Nat:=c4 ((1:Nat)); let c6:Nat:=c5 (Expr.size (Expr.var "left.s")); let c7:Nat:=c5 (Expr.size (Expr.var "left.n")); let c8:Nat:=c5 (Expr.size (Expr.var "left.d")); let c9:Nat:=c4 c7 c8; @Exists.intro Env (fun (σ':Env) => And (Run B leftToResult σ σ' ((6:Nat))) ((fun (x τ:Env) => FractionOutput q τ) σ σ')) c3 (@And.intro (Run B leftToResult σ c3 ((6:Nat))) ((fun (x τ:Env) => FractionOutput q τ) σ c3) (RunStep.mono B leftToResult σ c3 (c4 c6 c9) ((6:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s")) (Com.seq (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d"))) σ (Env.setVar σ "rat.s" (Env.vars σ "left.s")) c3 c6 c9 (RunStep.assign B σ "rat.s" (Expr.var "left.s") (Env.vars σ "left.s") (RunStep.eval_var B σ "left.s" hs)) (RunStep.seq B (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d")) (Env.setVar σ "rat.s" (Env.vars σ "left.s")) c1 c3 c7 c8 (RunStep.assign B (Env.setVar σ "rat.s" (Env.vars σ "left.s")) "rat.n" (Expr.var "left.n") c0 (RunStep.eval_var B (Env.setVar σ "rat.s" (Env.vars σ "left.s")) "left.n" (?nAX_g4081_0_0_0))) (RunStep.assign B c1 "rat.d" (Expr.var "left.d") c2 (RunStep.eval_var B c1 "left.d" (?nAX_g4081_0_0_1))))) (?nAX_g4081_0_0_2)) vcgPost0) <;> try dsimp +zetaDelta at *); (all_goals try clear_value vcgPost0); (all_goals try clear vcgPost0); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4081_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4081_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4081_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals intros))
  all_goals simp_all [FractionOutput,canonical_fractionValue,rationalSign_le_one]

set_option maxHeartbeats 0 in
theorem copyCoordinate_spec (B M i:ℕ) (a b:String) (xs ys:List ℚ)
    (hi:i < xs.length) (hiy:i < ys.length) (hiB:i < B) (h1:1 < B)
    (hMB:M < B) (hq:Height xs[i] M) (hab:Disjoint a b):
    Spec B (fun σ => Represents a xs σ∧ Represents b ys σ∧ σ.vars "copy.i"=i)
      (copyCoordinate a b)
      (fun _ τ => Represents b (ys.set i xs[i]) τ∧ Represents a xs τ) 30:=by
  have hload:=spec_with_fields loopFields
    (loadLeft_spec B a xs i hi h1 hiB (hq.1.trans_lt hMB) (hq.2.trans_lt hMB))
    (by intro x hx; simp [loopFields] at hx; rcases hx with rfl | rfl | rfl <;> simp [loadLeft,Com.wvars])
    (by simp [loadLeft,Com.warrs])
  have hresult:=spec_with_fields loopFields
    (leftToResult_spec B xs[i] h1 (hq.1.trans_lt hMB) (hq.2.trans_lt hMB))
    (by intro x hx; simp [loopFields] at hx; rcases hx with rfl | rfl | rfl <;> simp [leftToResult,Com.wvars])
    (by simp [leftToResult,Com.warrs])
  have hstore:=spec_with_write_frame loopFields
    (storeReduced_spec B b ys xs[i] i hiy h1 hiB (hq.1.trans_lt hMB) (hq.2.trans_lt hMB))
    (by intro x hx; simp [loopFields] at hx; rcases hx with rfl | rfl | rfl <;> simp [storeReduced,Com.wvars])
  rintro σ ⟨hσa,hσb,hσi⟩
  (expose_names;
    (refine let vcgPost0:And (Represents a xs (Env.setVar σ "vec.i" (Env.vars σ "copy.i"))) (@Eq Nat (Env.vars (Env.setVar σ "vec.i" (Env.vars σ "copy.i")) "vec.i") i):= ?_; let vcgPost1:∀ (w:Env),And (LeftOutput (@getElem (List Rat) Nat Rat (fun (as:List Rat) (i_1:Nat) => Nat.lt i_1 (@List.length Rat as)) (@List.instGetElemNatLtLength Rat) xs i hi) w) (And (FieldsAgree loopFields (Env.setVar σ "vec.i" (Env.vars σ "copy.i")) w) (@Eq (String→ List Nat) (Env.arrs w) (Env.arrs (Env.setVar σ "vec.i" (Env.vars σ "copy.i")))))→ LeftOutput (@getElem (List Rat) Nat Rat (fun (as:List Rat) (i_1:Nat) => Nat.lt i_1 (@List.length Rat as)) (@List.instGetElemNatLtLength Rat) xs i hi) w:= ?_; let vcgPost2:∀ (w:Env),And (LeftOutput (@getElem (List Rat) Nat Rat (fun (as:List Rat) (i_1:Nat) => Nat.lt i_1 (@List.length Rat as)) (@List.instGetElemNatLtLength Rat) xs i hi) w) (And (FieldsAgree loopFields (Env.setVar σ "vec.i" (Env.vars σ "copy.i")) w) (@Eq (String→ List Nat) (Env.arrs w) (Env.arrs (Env.setVar σ "vec.i" (Env.vars σ "copy.i")))))→ ∀ (w_1:Env),And (FractionOutput (@getElem (List Rat) Nat Rat (fun (as:List Rat) (i_1:Nat) => Nat.lt i_1 (@List.length Rat as)) (@List.instGetElemNatLtLength Rat) xs i hi) w_1) (And (FieldsAgree loopFields w w_1) (@Eq (String→ List Nat) (Env.arrs w_1) (Env.arrs w)))→ And (Represents b ys w_1) (And (@Eq Nat (Env.vars w_1 "vec.i") i) (FractionOutput (@getElem (List Rat) Nat Rat (fun (as:List Rat) (i_1:Nat) => Nat.lt i_1 (@List.length Rat as)) (@List.instGetElemNatLtLength Rat) xs i hi) w_1)):= ?_; let vcgPost3:∀ (w:Env),And (LeftOutput (@getElem (List Rat) Nat Rat (fun (as:List Rat) (i_1:Nat) => Nat.lt i_1 (@List.length Rat as)) (@List.instGetElemNatLtLength Rat) xs i hi) w) (And (FieldsAgree loopFields (Env.setVar σ "vec.i" (Env.vars σ "copy.i")) w) (@Eq (String→ List Nat) (Env.arrs w) (Env.arrs (Env.setVar σ "vec.i" (Env.vars σ "copy.i")))))→ ∀ (w_1:Env),And (FractionOutput (@getElem (List Rat) Nat Rat (fun (as:List Rat) (i_1:Nat) => Nat.lt i_1 (@List.length Rat as)) (@List.instGetElemNatLtLength Rat) xs i hi) w_1) (And (FieldsAgree loopFields w w_1) (@Eq (String→ List Nat) (Env.arrs w_1) (Env.arrs w)))→ ∀ (w_2:Env),And (Represents b (@List.set Rat ys i (@getElem (List Rat) Nat Rat (fun (as:List Rat) (i_1:Nat) => Nat.lt i_1 (@List.length Rat as)) (@List.instGetElemNatLtLength Rat) xs i hi)) w_2) (And (FieldsAgree loopFields w_1 w_2) (∀ a_1∉ Com.warrs (storeReduced b), @Eq (List Nat) (Env.arrs w_2 a_1) (Env.arrs w_1 a_1)))→ And (Represents b (@List.set Rat ys i (@getElem (List Rat) Nat Rat (fun (as:List Rat) (i_1:Nat) => Nat.lt i_1 (@List.length Rat as)) (@List.instGetElemNatLtLength Rat) xs i hi)) w_2) (Represents a xs w_2):= ?_; let c0:Env→ Nat→ Prop:=Run B (loadLeft a) (Env.setVar σ "vec.i" (Env.vars σ "copy.i")); let c1:Rat:= @getElem (List Rat) Nat Rat (fun (as:List Rat) (i_1:Nat) => Nat.lt i_1 (@List.length Rat as)) (@List.instGetElemNatLtLength Rat) xs i hi; let c2:Env→ Prop:=LeftOutput c1; let c3:Env→ Prop:=FieldsAgree loopFields (Env.setVar σ "vec.i" (Env.vars σ "copy.i")); let c4:String→ List Nat:=Env.arrs (Env.setVar σ "vec.i" (Env.vars σ "copy.i")); let c5:Env→ Prop:=fun (σ':Env) => And (c0 σ' ((9:Nat))) (And (c2 σ') (And (c3 σ') (@Eq (String→ List Nat) (Env.arrs σ') c4))); let c6:Env→ Prop:=Represents b (@List.set Rat ys i c1); let c7:Env→ Prop:=(fun (x τ:Env) => And (c6 τ) (Represents a xs τ)) σ; let c8:Env→ Prop:=fun (σ':Env) => And (Run B (copyCoordinate a b) σ σ' ((30:Nat))) (c7 σ'); let c9:Prop:= @Exists Env c8; let c10:Env→ Prop:=FractionOutput c1; let c11:Nat→ Nat→ Nat:=Nat.add; let c12:Nat:=c11 ((1:Nat)) (Expr.size (Expr.var "copy.i")); let c13:Nat:=c11 ((6:Nat)) ((13:Nat)); let c14:Nat:=c11 ((9:Nat)) c13; @Exists.casesOn Env c5 (fun (x:@Exists Env c5) => c9) (RunStep.use B (fun (σ_1:Env) => And (Represents a xs σ_1) (@Eq Nat (Env.vars σ_1 "vec.i") i)) (loadLeft a) (fun (σ_1 τ:Env) => And (c2 τ) (And (FieldsAgree loopFields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) ((9:Nat)) hload (Env.setVar σ "vec.i" (Env.vars σ "copy.i")) vcgPost0) fun (w:Env) (h:And (c0 w ((9:Nat))) (And (c2 w) (And (c3 w) (@Eq (String→ List Nat) (Env.arrs w) c4)))) => let c0_1:Prop:=c0 w ((9:Nat)); let c1_1:Prop:=And (c2 w) (And (c3 w) (@Eq (String→ List Nat) (Env.arrs w) c4)); let c2_1:Env→ Prop:=fun (σ':Env) => And (Run B leftToResult w σ' ((6:Nat))) (And (c10 σ') (And (FieldsAgree loopFields w σ') (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs w)))); @And.casesOn c0_1 c1_1 (fun (x:And c0_1 c1_1) => c9) h fun (left:c0_1) (right:c1_1) => @Exists.casesOn Env c2_1 (fun (x:@Exists Env c2_1) => c9) (RunStep.use B c2 leftToResult (fun (σ_1 τ:Env) => And (c10 τ) (And (FieldsAgree loopFields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) ((6:Nat)) hresult w (vcgPost1 w right)) fun (w_1:Env) (h_1:And (Run B leftToResult w w_1 ((6:Nat))) (And (c10 w_1) (And (FieldsAgree loopFields w w_1) (@Eq (String→ List Nat) (Env.arrs w_1) (Env.arrs w))))) => let c0_2:Prop:=Run B leftToResult w w_1 ((6:Nat)); let c1_2:Prop:=And (c10 w_1) (And (FieldsAgree loopFields w w_1) (@Eq (String→ List Nat) (Env.arrs w_1) (Env.arrs w))); let c2_2:Env→ Prop:=fun (σ':Env) => And (Run B (storeReduced b) w_1 σ' ((13:Nat))) (And (c6 σ') (And (FieldsAgree loopFields w_1 σ') (∀ a_1∉ Com.warrs (storeReduced b), @Eq (List Nat) (Env.arrs σ' a_1) (Env.arrs w_1 a_1)))); @And.casesOn c0_2 c1_2 (fun (x:And c0_2 c1_2) => c9) h_1 fun (left_1:c0_2) (right_1:c1_2) => @Exists.casesOn Env c2_2 (fun (x:@Exists Env c2_2) => c9) (RunStep.use B (fun (σ_1:Env) => And (Represents b ys σ_1) (And (@Eq Nat (Env.vars σ_1 "vec.i") i) (c10 σ_1))) (storeReduced b) (fun (σ_1 τ:Env) => And (c6 τ) (And (FieldsAgree loopFields σ_1 τ) (∀ a_1∉ Com.warrs (storeReduced b), @Eq (List Nat) (Env.arrs τ a_1) (Env.arrs σ_1 a_1)))) ((13:Nat)) hstore w_1 (vcgPost2 w right w_1 right_1)) fun (w_2:Env) (h_2:And (Run B (storeReduced b) w_1 w_2 ((13:Nat))) (And (c6 w_2) (And (FieldsAgree loopFields w_1 w_2) (∀ a_1∉ Com.warrs (storeReduced b), @Eq (List Nat) (Env.arrs w_2 a_1) (Env.arrs w_1 a_1))))) => let c0_3:Prop:=Run B (storeReduced b) w_1 w_2 ((13:Nat)); let c1_3:Prop:=And (c6 w_2) (And (FieldsAgree loopFields w_1 w_2) (∀ a_1∉ Com.warrs (storeReduced b), @Eq (List Nat) (Env.arrs w_2 a_1) (Env.arrs w_1 a_1))); @And.casesOn c0_3 c1_3 (fun (x:And c0_3 c1_3) => c9) h_2 fun (left_2:c0_3) (right_2:c1_3) => @Exists.intro Env c8 w_2 (@And.intro (Run B (copyCoordinate a b) σ w_2 ((30:Nat))) (c7 w_2) (RunStep.mono B (copyCoordinate a b) σ w_2 (c11 c12 c14) ((30:Nat)) (RunStep.seq B (Com.assign "vec.i" (Expr.var "copy.i")) (Com.seq (loadLeft a) (Com.seq leftToResult (storeReduced b))) σ (Env.setVar σ "vec.i" (Env.vars σ "copy.i")) w_2 c12 c14 (RunStep.assign B σ "vec.i" (Expr.var "copy.i") (Env.vars σ "copy.i") (RunStep.eval_var B σ "copy.i" (?nAX_g4083_0_0_0))) (RunStep.seq B (loadLeft a) (Com.seq leftToResult (storeReduced b)) (Env.setVar σ "vec.i" (Env.vars σ "copy.i")) w w_2 ((9:Nat)) c13 left (RunStep.seq B leftToResult (storeReduced b) w w_1 w_2 ((6:Nat)) ((13:Nat)) left_1 left_2))) (?nAX_g4083_0_0_1)) (vcgPost3 w right w_1 right_1 w_2 right_2)) <;> try dsimp +zetaDelta at *); (all_goals try clear_value vcgPost0); (all_goals try clear_value vcgPost1); (all_goals try clear_value vcgPost2); (all_goals try clear_value vcgPost3); (all_goals try clear vcgPost3); (all_goals try clear vcgPost2); (all_goals try clear vcgPost1); (all_goals try clear vcgPost0); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4083_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4083_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals intros))
  all_goals clear hload hresult hstore
  all_goals simp_all [Disjoint,suffixes,LeftOutput,FractionOutput,Represents,FieldsAgree,loopFields,
    storeReduced,Com.warrs]
  all_goals aesop

def CopyInvariant {n:ℕ} (a b:String) (v:Fin n→ ℚ) (σ:Env):Prop:=
  Represents a (List.ofFn v) σ∧
    Represents b (RamCenterUpdate.filled v (σ.vars "copy.i")) σ∧
    σ.vars "copy.i" ≤ n∧ σ.vars "vec.n"=n

theorem copyStep_spec (B n M:ℕ) (a b:String) (v:Fin n→ ℚ)
    (h1:1 < B) (hnB:n < B) (hMB:M < B) (hv:∀ i,Height (v i) M) (hab:Disjoint a b):
    Spec B (fun σ => CopyInvariant a b v σ∧ σ.vars "copy.i" < n) (copyStep a b)
      (fun σ τ => CopyInvariant a b v τ∧ τ.vars "copy.i"=σ.vars "copy.i" + 1) 34:=by
  rintro σ ⟨⟨hσa,hσb,hσiN,hσn⟩,hσi⟩
  let i:Fin n:= ⟨σ.vars "copy.i",hσi⟩
  have hvi:Height (List.ofFn v)[i.val] M:=by simpa using hv i
  obtain ⟨τ,hr₁,hτb,hτa⟩:=copyCoordinate_spec B M i.val a b (List.ofFn v)
    (RamCenterUpdate.filled v i.val) (by simp) (by simp [RamCenterUpdate.filled])
    (i.isLt.trans hnB) h1 hMB hvi hab σ ⟨hσa,hσb,rfl⟩
  have hτi:τ.vars "copy.i"=i.val:=hr₁.frame_var _ (by
    simp [copyCoordinate,leftToResult,loadLeft,storeReduced,Com.wvars])
  have hτn:τ.vars "vec.n"=n:=(hr₁.frame_var "vec.n" (by
    simp [copyCoordinate,leftToResult,loadLeft,storeReduced,Com.wvars])).trans hσn
  have hτiB:τ.vars "copy.i" < B:=hτi ▸ i.isLt.trans hnB
  have hsumB:Bop.add.apply (τ.vars "copy.i") 1 < B:=by
    simpa [Bop.apply,hτi] using lt_of_le_of_lt i.isLt hnB
  have hr₂:Run B (.assign "copy.i" (.add (.var "copy.i") (.lit 1))) τ
      (τ.setVar "copy.i" (i.val + 1)) 4:=by
    exact Run.assign (by simpa [Bop.apply,hτi] using
      (evalB_bin (evalB_var hτiB) (evalB_lit h1) hsumB))
  have hnext:Represents b (RamCenterUpdate.filled v (i.val + 1)) τ:=by
    rw [← RamCenterUpdate.filled_step]
    simpa only [List.getElem_ofFn,Fin.eta] using hτb
  refine ⟨_,hr₁.seq hr₂, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [Represents,arrs_setVar] using hτa
  · simpa only [Represents,arrs_setVar,vars_setVar,ite_true] using hnext
  · change i.val + 1≤ n
    exact i.isLt
  · simpa using hτn
  · simp [i]

theorem copyLoop_spec (B n M:ℕ) (a b:String) (v:Fin n→ ℚ)
    (h1:1 < B) (hnB:n < B) (hMB:M < B) (hv:∀ i,Height (v i) M) (hab:Disjoint a b):
    Spec B (fun σ => Represents a (List.ofFn v) σ∧ Represents b (List.replicate n 0) σ∧ σ.vars "vec.n"=n)
      (copyLoop a b)
      (fun _ τ => Represents b (List.ofFn v) τ∧ Represents a (List.ofFn v) τ∧ τ.vars "vec.n"=n)
      (38 * n + 6):=by
  have hlo:=Spec.forRangeZero "copy.i" "vec.n" (CopyInvariant a b v) n 34 hnB
    (fun _ h => h.2.2.1) (fun _ h => h.2.2.2) (copyStep_spec B n M a b v h1 hnB hMB hv hab)
  refine (hlo.pre ?_).post ?_
  · rintro σ ⟨hσa,hσb,hσn⟩
    simp_all [CopyInvariant,Represents,RamCenterUpdate.filled_zero]
  · rintro σ τ _ ⟨hτ,hcounter⟩
    refine ⟨?_,hτ.1,hτ.2.2.2⟩
    simpa only [hcounter,RamCenterUpdate.filled_done] using hτ.2.1

theorem copyRationalArray_spec (B n M:ℕ) (a b:String) (v:Fin n→ ℚ)
    (h1:1 < B) (hnB:n < B) (hMB:M < B) (hv:∀ i,Height (v i) M) (hab:Disjoint a b):
    Spec B (fun σ => Represents a (List.ofFn v) σ∧ (σ.arrs (b ++ ".s")).length=n∧
        (σ.arrs (b ++ ".n")).length=n∧ (σ.arrs (b ++ ".d")).length=n∧ σ.vars "vec.n"=n)
      (copyRationalArray a b)
      (fun _ τ => Represents b (List.ofFn v) τ∧ Represents a (List.ofFn v) τ∧ τ.vars "vec.n"=n)
      (71 * n + 24):=by
  rintro σ ⟨hσa,hσs,hσn,hσd,hσN⟩
  obtain ⟨τ,hr₁,hτb,hτN,hτarr⟩:=RamZeroArray.zeroRationalArray_spec B n b hnB h1 σ ⟨hσs,hσn,hσd,hσN⟩
  have hτa:Represents a (List.ofFn v) τ:=by
    simpa only [Represents,hτarr (a ++ ".s") (disjoint_not_mem a b _ hab (by simp [suffixes])),
      hτarr (a ++ ".n") (disjoint_not_mem a b _ hab (by simp [suffixes])),
      hτarr (a ++ ".d") (disjoint_not_mem a b _ hab (by simp [suffixes]))] using hσa
  obtain ⟨υ,hr₂,hυ⟩:=copyLoop_spec B n M a b v h1 hnB hMB hv hab τ ⟨hτa,hτb,hτN⟩
  exact ⟨υ, (hr₁.seq hr₂).mono (by omega),hυ⟩

end Lax109476Proofs.RamCopy

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RamAdvanceState

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RationalArithmeticBounds RamEllipsoidStep RamCommitState
open RamEllipsoidCoefficients RamMatrixStorage

theorem array_length_of_bigStep {c:Com} {σ τ:Env} {K:ℕ}
    (hr:BigStep c σ τ K) (b:String):(τ.arrs b).length=(σ.arrs b).length:=by
  induction hr with
  | skip => rfl
  | assign _ => rfl
  | store _ _ _ => exact length_arrs_setArr _ _ _ _ _
  | seq _ _ ih ih' => exact ih'.trans ih
  | ite_true _ _ ih => exact ih
  | ite_false _ _ ih => exact ih
  | while_true _ _ _ ih ih' => exact ih'.trans ih
  | while_false _ => rfl
  | read _ => rfl
  | write _ => rfl

theorem extents_of_run {B K:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ K)
    (b:String) (n:ℕ) (hσ:Extents b n σ):Extents b n τ:=by
  obtain ⟨_,_,hstep⟩:=hr.bigStep
  intro s hs
  rw [array_length_of_bigStep hstep]
  exact hσ s hs

end Lax109476Proofs.RamAdvanceState

end

section

namespace Lax109476Proofs.RamReadBody

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamReadArray RamReadBlock RamRationalArrays RamFrame RamEllipsoidStep RamAdvanceState

theorem represents_frame {B K:ℕ} {c:Com} {σ τ:Env} (a:String) (qs:List ℚ)
    (hσ:Represents a qs σ) (hr:Run B c σ τ K)
    (ha:∀ s∈ [".s", ".n", ".d"],a ++ s∉ c.warrs):Represents a qs τ:=by
  simpa only [Represents,hr.frame_arr (a ++ ".s") (ha ".s" (by simp)),
    hr.frame_arr (a ++ ".n") (ha ".n" (by simp)),
    hr.frame_arr (a ++ ".d") (ha ".d" (by simp))] using hσ

end Lax109476Proofs.RamReadBody

end

section

namespace Lax109476Proofs.RamCopyBlock

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamCopy RamRationalArrays RamEllipsoidStep RationalArithmeticBounds

theorem copyBlock_wvars (a b field:String):
    (copyBlock a b field).wvars=(copyBlock "" "" "").wvars:=by rfl

theorem copyBlock_warrs (a b field:String):
    (copyBlock a b field).warrs =
      [b ++ ".s",b ++ ".n",b ++ ".d",b ++ ".s",b ++ ".s",b ++ ".n",b ++ ".d"]:=by rfl

theorem copyBlock_spec (B M n:ℕ) (a b field:String) (v:Fin n→ ℚ)
    (h1:1 < B) (hnB:n < B) (hMB:M < B) (hv:∀ i,Height (v i) M)
    (hab:Disjoint a b):
    Spec B (fun σ => Represents a (List.ofFn v) σ∧ Extents b n σ∧ σ.vars field=n)
      (copyBlock a b field)
      (fun _ τ => Represents b (List.ofFn v) τ∧ Represents a (List.ofFn v) τ)
      (71 * n + 26):=by
  rintro σ ⟨hσa,hσb,hσn⟩
  have hr₁:Run B (.assign "vec.n" (.var field)) σ (σ.setVar "vec.n" n) 2:=
    Run.assign (by simpa only [hσn] using evalB_var (B:=B) (σ:=σ) (x:=field) (hσn ▸ hnB))
  obtain ⟨τ,hr₂,hτ⟩:=copyRationalArray_spec B n M a b v h1 hnB hMB hv hab
    (σ.setVar "vec.n" n)
    ⟨hσa,hσb ".s" (by simp),hσb ".n" (by simp),hσb ".d" (by simp),by simp⟩
  exact ⟨τ, (hr₁.seq hr₂).mono (by omega),hτ.1,hτ.2.1⟩

end Lax109476Proofs.RamCopyBlock

end

section

open scoped BigOperators

namespace Lax109476Proofs.RecoveryArithmeticBounds

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open RationalArithmeticBounds
open LexicographicMinima EncodingSize

theorem program_height_size {m n:ℕ} (P:Program ℚ m n) (B:ℕ)
    (hA:∀ i j,Height (P.A i j) B) (hb:∀ i,Height (P.b i) B)
    (hc:∀ j,Height (P.c j) B):
    bitSize (encodeProgram P)≤ m + n + 2 + (m * n + m + n) * (4 + 2 * B.size):=by
  have hsA:(∑ i, ∑ j,bitSize (encodeRational (P.A i j)))≤ m * n * (4 + 2 * B.size):=by
    calc
      _≤ ∑ _i:Fin m, ∑ _j:Fin n, (4 + 2 * B.size):=by
        exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => height_encoding _ B (hA i j)))
      _=_:=by simp; ring
  have hsb:=bounded_vector_size P.b B hb
  have hsc:=bounded_vector_size P.c B hc
  have hm:=RationalSizeBounds.size_le_self m
  have hn:=RationalSizeBounds.size_le_self n
  rw [program_size]
  rw [vector_size] at hsb hsc
  nlinarith

end Lax109476Proofs.RecoveryArithmeticBounds

end

section

namespace Lax109476Proofs.RamIntegerFeasibility

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NormalizedFeasibility IntegerCertificates EllipsoidSequence EllipsoidSearch RamNormalizedBounds

def instructionBound (m n S:ℕ):ℕ:=RamFeasibilitySetup.instructionBound S +
  RamSearchBounds.instructionBound (m + n) n
    (thresholdSteps n (ballExponent m n (2 ^ (2 * S))) + 1) (coefficientBits S)

end Lax109476Proofs.RamIntegerFeasibility

end

section

namespace Lax109476Proofs.RamStoredFeasibilityBounds

theorem wordWidth_monotone {L S:ℕ} (h:L≤ S):
    RamStoredFeasibility.wordWidth L≤ RamStoredFeasibility.wordWidth S:=by
  unfold RamStoredFeasibility.wordWidth RamRationalFeasibility.wordWidth
    RamPaddedFeasibility.wordWidth RamIntegerFeasibility.wordWidth RamFeasibilitySetup.wordWidth
    RamFeasibilityScaleBounds.wordWidth RamSearchBounds.wordWidth RamEllipsoidBitBounds.wordWidth
    RamEllipsoidBitBounds.magnitudeExponent RamEllipsoidBitBounds.formExponent
    RamTrajectoryBounds.stateBits RamNormalizedBounds.coefficientBits
    RamIntegerFeasibility.iterationBound RamDecoder.wordWidth
  gcongr

set_option maxRecDepth 30000 in
theorem instructionBound_monotone {L S:ℕ} (h:L≤ S):
    RamStoredFeasibility.instructionBound L≤ RamStoredFeasibility.instructionBound S:=by
  unfold RamStoredFeasibility.instructionBound RamRationalFeasibility.instructionBound
    RamPaddedFeasibility.instructionBound RamIntegerFeasibility.uniformInstructionBound
    RamFeasibilitySetup.instructionBound RamFeasibilityParameters.instructionBound
    RamSearchBounds.instructionBound RamSearchBounds.stepBound RamSearchBounds.rowBound
    RamTrajectoryBounds.instructionBound RamTrajectoryBounds.stateBits
    RamEllipsoidBitBounds.magnitudeExponent RamEllipsoidBitBounds.formExponent
    RamNormalizedBounds.coefficientBits RamIntegerFeasibility.iterationBound
  dsimp only
  gcongr

end Lax109476Proofs.RamStoredFeasibilityBounds

end

section

namespace Lax109476Proofs.RamFamilyQueryCopy

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamFrame RamEllipsoidStep RationalArithmeticBounds RamCopy

def Input {r s:ℕ} (F:Program ℚ r s) (sourceA sourceB targetA targetB targetC:String) (σ:Env):Prop:=
  Represents sourceA (RamMatrixStorage.flatten F.A) σ∧ Represents sourceB (List.ofFn F.b) σ∧
    σ.vars "system.m"=r∧ σ.vars "system.n"=s∧
    Extents targetA (r * s) σ∧ Extents targetB r σ∧ Extents targetC s σ

def Output {r s:ℕ} (F:Program ℚ r s) (targetA targetB targetC:String) (σ:Env):Prop:=
  Represents targetA (RamMatrixStorage.flatten F.A) σ∧ Represents targetB (List.ofFn F.b) σ∧
    Represents targetC (List.ofFn F.c) σ∧ σ.vars "lp.m"=r∧ σ.vars "lp.n"=s∧
    σ.vars "decode.count"=r * s

theorem zeroObjective_spec (B s:ℕ) (a:String) (h1:1 < B) (hs:s < B):
    Spec B (fun σ => Extents a s σ∧ σ.vars "system.n"=s) (zeroObjective a)
      (fun _ τ => Represents a (List.replicate s 0) τ) (33 * s + 20):=by
  rintro σ ⟨hσa,hσs⟩
  have hr₁:Run B (.assign "vec.n" (.var "system.n")) σ (σ.setVar "vec.n" s) 2:=
    Run.assign (by simpa only [hσs] using evalB_var (B:=B) (σ:=σ) (x:= "system.n") (hσs ▸ hs))
  obtain ⟨τ,hr₂,hτa,_⟩:=RamZeroArray.zeroRationalArray_spec B s a hs h1 (σ.setVar "vec.n" s)
    ⟨hσa ".s" (by simp),hσa ".n" (by simp),hσa ".d" (by simp),by simp⟩
  exact ⟨τ, (hr₁.seq hr₂).mono (by omega),hτa⟩

theorem metadata_spec (B r s:ℕ) (hr:r < B) (hs:s < B):
    Spec B (fun σ => σ.vars "system.m"=r∧ σ.vars "system.n"=s) metadata
      (fun _ τ => τ.vars "lp.m"=r∧ τ.vars "lp.n"=s) 4:=by
  rintro σ ⟨hσr,hσs⟩
  (expose_names;
    (refine let vcgPost0:And (@Eq Nat (Env.vars (Env.setVar (Env.setVar σ "lp.m" (Env.vars σ "system.m")) "lp.n" (Env.vars (Env.setVar σ "lp.m" (Env.vars σ "system.m")) "system.n")) "lp.m") r) (@Eq Nat (Env.vars (Env.setVar (Env.setVar σ "lp.m" (Env.vars σ "system.m")) "lp.n" (Env.vars (Env.setVar σ "lp.m" (Env.vars σ "system.m")) "system.n")) "lp.n") s):= ?_; let c0:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "lp.m") r) (@Eq Nat (Env.vars τ "lp.n") s)) σ; let c1:Nat:=Env.vars (Env.setVar σ "lp.m" (Env.vars σ "system.m")) "system.n"; let c2:Env:=Env.setVar (Env.setVar σ "lp.m" (Env.vars σ "system.m")) "lp.n" c1; let c3:Nat→ Nat→ Nat:=Nat.add; let c4:Nat→ Nat:=c3 ((1:Nat)); let c5:Nat:=c4 (Expr.size (Expr.var "system.m")); let c6:Nat:=c4 (Expr.size (Expr.var "system.n")); @Exists.intro Env (fun (σ':Env) => And (Run B metadata σ σ' ((4:Nat))) (c0 σ')) c2 (@And.intro (Run B metadata σ c2 ((4:Nat))) (c0 c2) (RunStep.mono B metadata σ c2 (c3 c5 c6) ((4:Nat)) (RunStep.seq B (Com.assign "lp.m" (Expr.var "system.m")) (Com.assign "lp.n" (Expr.var "system.n")) σ (Env.setVar σ "lp.m" (Env.vars σ "system.m")) c2 c5 c6 (RunStep.assign B σ "lp.m" (Expr.var "system.m") (Env.vars σ "system.m") (RunStep.eval_var B σ "system.m" (?nAX_g5079_0_0_0))) (RunStep.assign B (Env.setVar σ "lp.m" (Env.vars σ "system.m")) "lp.n" (Expr.var "system.n") c1 (RunStep.eval_var B (Env.setVar σ "lp.m" (Env.vars σ "system.m")) "system.n" (?nAX_g5079_0_0_1)))) (?nAX_g5079_0_0_2)) vcgPost0) <;> try dsimp +zetaDelta at *); (all_goals try clear_value vcgPost0); (all_goals try clear vcgPost0); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5079_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5079_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5079_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals intros))
  all_goals simp_all

theorem count_spec (B r s:ℕ) (hr:r < B) (hs:s < B) (hcount:r * s < B):
    Spec B (fun σ => σ.vars "system.m"=r∧ σ.vars "system.n"=s) count
      (fun _ τ => τ.vars "decode.count"=r * s) 4:=by
  rintro σ ⟨hσr,hσs⟩
  (expose_names;
    (refine let vcgPost0:Nat.lt (Nat.mul (Env.vars σ "system.m") (Env.vars σ "system.n")) B:= ?_; let vcgPost1:@Eq Nat (Env.vars (Env.setVar σ "decode.count" (Nat.mul (Env.vars σ "system.m") (Env.vars σ "system.n"))) "decode.count") (Nat.mul r s):= ?_; let c0:Nat→ Nat→ Nat:=Nat.mul; let c1:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "decode.count") (c0 r s)) σ; let c2:Nat:=c0 (Env.vars σ "system.m") (Env.vars σ "system.n"); let c3:Env:=Env.setVar σ "decode.count" c2; @Exists.intro Env (fun (σ':Env) => And (Run B count σ σ' ((4:Nat))) (c1 σ')) c3 (@And.intro (Run B count σ c3 ((4:Nat))) (c1 c3) (RunStep.mono B count σ c3 (Nat.add ((1:Nat)) (Expr.size (Expr.mul (Expr.var "system.m") (Expr.var "system.n")))) ((4:Nat)) (RunStep.assign B σ "decode.count" (Expr.mul (Expr.var "system.m") (Expr.var "system.n")) c2 (RunStep.eval_mul B σ (Expr.var "system.m") (Expr.var "system.n") (Env.vars σ "system.m") (Env.vars σ "system.n") (RunStep.eval_var B σ "system.m" (?nAX_g5080_0_0_0)) (RunStep.eval_var B σ "system.n" (?nAX_g5080_0_0_1)) vcgPost0)) (?nAX_g5080_0_0_2)) vcgPost1) <;> try dsimp +zetaDelta at *); (all_goals try clear_value vcgPost0); (all_goals try clear_value vcgPost1); (all_goals try clear vcgPost1); (all_goals try clear vcgPost0); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5080_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5080_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5080_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals intros))
  all_goals simp_all

theorem copy_wvars (sourceA sourceB targetA targetB targetC:String):
    (copy sourceA sourceB targetA targetB targetC).wvars=(copy "" "" "" "" "").wvars:=by rfl

set_option maxHeartbeats 0 in
theorem copy_spec (B M r s:ℕ) (F:Program ℚ r s) (sourceA sourceB targetA targetB targetC:String)
    (h1:1 < B) (hMB:M < B) (hB:r * s + r + s + 4 < B)
    (hA:∀ i j,Height (F.A i j) M) (hb:∀ i,Height (F.b i) M) (hc:∀ j,F.c j=0)
    (hAA:Disjoint sourceA targetA) (hBA:Disjoint sourceB targetA) (hBB:Disjoint sourceB targetB)
    (hAB:Disjoint targetA targetB) (hAC:Disjoint targetA targetC) (hBC:Disjoint targetB targetC):
    Spec B (Input F sourceA sourceB targetA targetB targetC) (copy sourceA sourceB targetA targetB targetC)
      (fun _ τ => Output F targetA targetB targetC τ)
      (71 * (r * s + r) + 33 * s + 80):=by
  have hrB:r < B:=by omega
  have hsB:s < B:=by omega
  have hcountB:r * s < B:=by omega
  have hAcopy:=RamCopyBlock.copyBlock_spec B M (r * s) sourceA targetA "decode.count"
    (fun i => F.A i.divNat i.modNat) h1 hcountB hMB (fun i => hA i.divNat i.modNat) hAA
  have hbcopy:=RamCopyBlock.copyBlock_spec B M r sourceB targetB "system.m" F.b h1 hrB hMB hb hBB
  rintro σ ⟨hσA,hσb,hσr,hσs,hσtargetA,hσtargetB,hσtargetC⟩
  obtain ⟨τ,hr₀,hτcount⟩:=count_spec B r s hrB hsB hcountB σ ⟨hσr,hσs⟩
  have hτA:Represents sourceA (RamMatrixStorage.flatten F.A) τ:=
    RamReadBody.represents_frame _ _ hσA hr₀ (by intro t ht; simp [count,Com.warrs])
  obtain ⟨υ,hr₁,hυA,_⟩:=hAcopy τ
    ⟨hτA,RamAdvanceState.extents_of_run hr₀ targetA (r * s) hσtargetA,hτcount⟩
  have hυb:=RamReadBody.represents_frame _ _ hσb (hr₀.seq hr₁)
    (by
      intro t ht
      simp only [Com.warrs,count,RamCopyBlock.copyBlock_warrs,List.mem_append,List.not_mem_nil,false_or]
      simp only [List.mem_cons,List.mem_singleton]
      have h₁:=hBA t (by simpa [suffixes] using ht) ".s" (by simp [suffixes])
      have h₂:=hBA t (by simpa [suffixes] using ht) ".n" (by simp [suffixes])
      have h₃:=hBA t (by simpa [suffixes] using ht) ".d" (by simp [suffixes])
      simp_all [Ne.symm])
  have hυr:=((hr₀.seq hr₁).frame_var "system.m" (by
    simp only [Com.wvars,count,RamCopyBlock.copyBlock_wvars]; decide)).trans hσr
  obtain ⟨ξ,hr₂,hξb,_⟩:=hbcopy υ
    ⟨hυb,RamAdvanceState.extents_of_run (hr₀.seq hr₁) targetB r hσtargetB,hυr⟩
  have hrCopy:=hr₀.seq (hr₁.seq hr₂)
  have hξs:=(hrCopy.frame_var "system.n" (by
    simp only [Com.wvars,count,RamCopyBlock.copyBlock_wvars]; decide)).trans hσs
  obtain ⟨ρ,hr₃,hρc⟩:=zeroObjective_spec B s targetC h1 hsB ξ
    ⟨RamAdvanceState.extents_of_run hrCopy targetC s hσtargetC,hξs⟩
  have hrBuild:=hr₀.seq (hr₁.seq (hr₂.seq hr₃))
  have hρr:=(hrBuild.frame_var "system.m" (by
    change "system.m" ∉ (Com.seq count (Com.seq (RamCopyBlock.copyBlock "" "" "")
      (Com.seq (RamCopyBlock.copyBlock "" "" "") (zeroObjective "")))).wvars
    decide)).trans hσr
  have hρs:=(hrBuild.frame_var "system.n" (by
    change "system.n" ∉ (Com.seq count (Com.seq (RamCopyBlock.copyBlock "" "" "")
      (Com.seq (RamCopyBlock.copyBlock "" "" "") (zeroObjective "")))).wvars
    decide)).trans hσs
  obtain ⟨ω,hr₄,hωr,hωs⟩:=metadata_spec B r s hrB hsB ρ ⟨hρr,hρs⟩
  have hωcount:=((hr₁.seq (hr₂.seq (hr₃.seq hr₄))).frame_var "decode.count" (by
    change "decode.count" ∉ (Com.seq (RamCopyBlock.copyBlock "" "" "")
      (Com.seq (RamCopyBlock.copyBlock "" "" "") (Com.seq (zeroObjective "") metadata))).wvars
    decide)).trans hτcount
  have hωA:=RamReadBody.represents_frame _ _ hυA (hr₂.seq (hr₃.seq hr₄))
    (by
      intro t ht
      simp [suffixes] at ht
      rcases ht with rfl | rfl | rfl
      all_goals simp [RamCopyBlock.copyBlock_warrs,zeroObjective,metadata,Com.warrs,
        RamZeroArray.zeroRationalArray,RamZeroArray.fillConstant,Lib.Fill.put]
      all_goals simp_all [RamCopy.Disjoint,suffixes])
  have hωb:=RamReadBody.represents_frame _ _ hξb (hr₃.seq hr₄)
    (by
      intro t ht
      simp [suffixes] at ht
      rcases ht with rfl | rfl | rfl
      all_goals simp [zeroObjective,metadata,Com.warrs,RamZeroArray.zeroRationalArray,
        RamZeroArray.fillConstant,Lib.Fill.put]
      all_goals simp_all [RamCopy.Disjoint,suffixes])
  have hωc:=RamReadBody.represents_frame _ _ hρc hr₄ (by intro t ht; simp [metadata,Com.warrs])
  have hcList:List.ofFn F.c=List.replicate s 0:=by simp [funext hc]
  refine ⟨ω, (hr₀.seq (hr₁.seq (hr₂.seq (hr₃.seq hr₄)))).mono ?_,hωA,hωb, ?_,hωr,hωs,hωcount⟩
  · simp only [Nat.mul_add]; omega
  · simpa only [hcList] using hωc

end Lax109476Proofs.RamFamilyQueryCopy

end

section

namespace Lax109476Proofs.RamArrayRelabel

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

@[simp] theorem expression_size (f:String→ String) (e:Expr):
    (expression f e).size=e.size:=by
  induction e <;> simp_all [expression,Expr.size]

@[simp] theorem condition_size (f:String→ String) (b:Cond):
    (condition f b).size=b.size:=by
  cases b <;> simp [condition,Cond.size]

@[simp] theorem expression_eval (f:String→ String) (e:Expr) (B:ℕ) (σ:Env):
    (expression f e).evalB B σ=e.evalB B (view f σ):=by
  induction e <;> simp_all [expression,Expr.evalB,view]

@[simp] theorem condition_eval (f:String→ String) (b:Cond) (B:ℕ) (σ:Env):
    (condition f b).evalB B σ=b.evalB B (view f σ):=by
  cases b <;> simp [condition,Cond.evalB]

@[simp] theorem view_setVar (f:String→ String) (σ:Env) (x:String) (v:ℕ):
    view f (σ.setVar x v)=(view f σ).setVar x v:=rfl

@[simp] theorem view_setArr (f:String→ String) (hf:Function.Injective f)
    (σ:Env) (a:String) (k v:ℕ):
    view f (σ.setArr (f a) k v)=(view f σ).setArr a k v:=by
  cases σ
  simp only [view,Env.setArr]
  congr 1
  funext x
  by_cases hx:x=a
  · subst x; simp
  · have hfx:f x ≠ f a:=fun h => hx (hf h)
    simp [hx,hfx]

theorem run_relabel {B k:ℕ} {c:Com} {σ τ:Env} (f:String→ String)
    (hf:Function.Injective f) (h:BigStepB B c σ τ k):
    ∀ β,view f β=σ→ ∃ γ,BigStepB B (command f c) β γ k∧ view f γ=τ:=by
  induction h with
  | skip => intro β hβ; exact ⟨β, .skip,hβ⟩
  | @assign σ x e v he =>
    intro β hβ
    refine ⟨β.setVar x v, ?_,by simp [hβ]⟩
    simpa only [command,expression_size] using
      (BigStepB.assign (B:=B) (σ:=β) (x:=x) (e:=expression f e) (by simpa only [expression_eval,hβ] using he))
  | @store σ a i e k v hi he hk =>
    intro β hβ
    have hlen:k < (β.arrs (f a)).length:=by simpa only [← hβ,view] using hk
    refine ⟨β.setArr (f a) k v, ?_,by simp [hf,hβ]⟩
    simpa only [command,expression_size] using BigStepB.store (B:=B) (σ:=β) (a:=f a) (i:=expression f i) (e:=expression f e)
      (by simpa only [expression_eval,hβ] using hi)
      (by simpa only [expression_eval,hβ] using he) hlen
  | seq hc hd ihc ihd =>
    intro β hβ
    obtain ⟨γ,hγ,heγ⟩:=ihc β hβ
    obtain ⟨δ,hδ,heδ⟩:=ihd γ heγ
    exact ⟨δ,hγ.seq hδ,heδ⟩
  | @ite_true b c d σ σ' k hb hc ih =>
    intro β hβ
    obtain ⟨γ,hγ,heγ⟩:=ih β hβ
    exact ⟨γ,by simpa only [command,condition_size] using
      BigStepB.ite_true (B:=B) (σ:=β) (b:=condition f b) (d:=command f d) (by simpa only [condition_eval,hβ] using hb) hγ,heγ⟩
  | @ite_false b c d σ σ' k hb hd ih =>
    intro β hβ
    obtain ⟨γ,hγ,heγ⟩:=ih β hβ
    exact ⟨γ,by simpa only [command,condition_size] using
      BigStepB.ite_false (B:=B) (σ:=β) (b:=condition f b) (c:=command f c) (by simpa only [condition_eval,hβ] using hb) hγ,heγ⟩
  | @while_true b c σ σ' σ'' k k' hb hc hw ihc ihw =>
    intro β hβ
    obtain ⟨γ,hγ,heγ⟩:=ihc β hβ
    obtain ⟨δ,hδ,heδ⟩:=ihw γ heγ
    exact ⟨δ,by simpa only [command,condition_size] using
      BigStepB.while_true (B:=B) (σ:=β) (b:=condition f b) (by simpa only [condition_eval,hβ] using hb) hγ hδ,heδ⟩
  | @while_false b c σ hb =>
    intro β hβ
    exact ⟨β,by simpa only [command,condition_size] using
      BigStepB.while_false (B:=B) (σ:=β) (b:=condition f b) (c:=command f c) (by simpa only [condition_eval,hβ] using hb),hβ⟩
  | @read σ x v rest hi =>
    intro β hβ
    refine ⟨{β.setVar x v with inp:=rest}, ?_, ?_⟩
    · exact BigStepB.read (by simpa only [← hβ,view] using hi)
    · change {view f (β.setVar x v) with inp:=rest}=_
      simp only [view_setVar,hβ]
  | @write σ e v he =>
    intro β hβ
    refine ⟨{β with out:=β.out ++ [v]}, ?_, ?_⟩
    · simpa only [command,expression_size] using BigStepB.write (B:=B) (σ:=β) (e:=expression f e)
        (by simpa only [expression_eval,hβ] using he)
    · change {view f β with out:=(view f β).out ++ [v]}=_
      rw [hβ]

theorem spec_relabel {B K:ℕ} {P:Env→ Prop} {Q:Env→ Env→ Prop} {c:Com}
    (f:String→ String) (hf:Function.Injective f) (h:Spec B P c Q K):
    Spec B (fun σ => P (view f σ)) (command f c)
      (fun σ τ => Q (view f σ) (view f τ)) K:=by
  intro β hβ
  obtain ⟨τ, ⟨k,hk,hr⟩,hτ⟩:=h (view f β) hβ
  obtain ⟨γ,hγ,heγ⟩:=run_relabel f hf hr β rfl
  exact ⟨γ, ⟨k,hk,hγ⟩,by change Q (view f β) (view f γ); rw [heγ]; exact hτ⟩

theorem prefix_injective (name:String):Function.Injective (fun a => name ++ a):=
  fun _ _ h => (String.append_right_inj name).mp h

theorem spec_prefixed {B K:ℕ} {P:Env→ Prop} {Q:Env→ Env→ Prop} {c:Com}
    (name:String) (h:Spec B P c Q K):
    Spec B (fun σ => P (view (fun a => name ++ a) σ)) (prefixed name c)
      (fun σ τ => Q (view (fun a => name ++ a) σ) (view (fun a => name ++ a) τ)) K:=
  spec_relabel _ (prefix_injective name) h

end Lax109476Proofs.RamArrayRelabel

end

section

namespace Lax109476Proofs.RamCertificateArrayRelabel

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

@[simp] theorem command_wvars (f:String→ String) (c:Com):
    (RamArrayRelabel.command f c).wvars=c.wvars:=by
  induction c <;> simp_all [RamArrayRelabel.command,Com.wvars]

end Lax109476Proofs.RamCertificateArrayRelabel

end

section

namespace Lax109476Proofs.RamCertificateDecision

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep RationalArithmeticBounds IntegerEncoding

theorem workspace_view_of_run {B k:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ k)
    (name:String) (r s:ℕ) (hσ:RamFeasibilityQuery.Workspace r s (prefixedView name σ)):
    RamFeasibilityQuery.Workspace r s (prefixedView name τ):=by
  obtain ⟨_,_,hstep⟩:=hr.bigStep
  have hlen:=RamAdvanceState.array_length_of_bigStep hstep
  simpa only [RamFeasibilityQuery.Workspace,RamEllipsoidStep.Workspace,Extents,
    prefixedView,RamArrayRelabel.view,hlen] using hσ

theorem family_size {r s:ℕ} (F:Program ℤ r s) (S:ℕ)
    (hA:∀ i j, (F.A i j).natAbs≤ 2 ^ (2 * S)) (hb:∀ i, (F.b i).natAbs≤ 2 ^ (2 * S))
    (hc:∀ j,F.c j=0):bitSize (encodeProgram (rationalProgram F))≤ sizeBound r s S:=by
  have hH:1≤ 2 ^ (2 * S):=Nat.one_le_pow _ _ (by decide)
  simpa only [sizeBound,Nat.size_pow] using RecoveryArithmeticBounds.program_height_size (rationalProgram F)
    (2 ^ (2 * S)) (fun i j => ⟨by simpa [rationalProgram] using hA i j,by simpa [rationalProgram] using hH⟩)
    (fun i => ⟨by simpa [rationalProgram] using hb i,by simpa [rationalProgram] using hH⟩)
    (fun j => by simpa [rationalProgram,hc j,Height] using hH)

theorem decide_wvars (source target:String):
    (decideFeasible source target).wvars=(decideFeasible "" "").wvars:=by
  simp [decideFeasible,prepare,RamFamilyQueryCopy.copy_wvars,RamArrayRelabel.prefixed,
    RamCertificateArrayRelabel.command_wvars,Com.wvars]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem decideFeasible_spec (r s S w:ℕ) (F:Program ℤ r s) (source target:String)
    (hMB:2 ^ (2 * S) < 2 ^ w) (hB:r * s + r + s + 4 < 2 ^ w)
    (hw:RamStoredFeasibility.wordWidth (sizeBound r s S)≤ w)
    (hA:∀ i j, (F.A i j).natAbs≤ 2 ^ (2 * S)) (hb:∀ i, (F.b i).natAbs≤ 2 ^ (2 * S))
    (hc:∀ j,F.c j=0)
    (hAA:RamCopy.Disjoint (source ++ "system.A") (target ++ "lp.A"))
    (hBA:RamCopy.Disjoint (source ++ "system.b") (target ++ "lp.A"))
    (hBB:RamCopy.Disjoint (source ++ "system.b") (target ++ "lp.b"))
    (hFrameA:∀ t∈ RamCopy.suffixes,source ++ ("system.A" ++ t)∉ (decideFeasible source target).warrs)
    (hFrameB:∀ t∈ RamCopy.suffixes,source ++ ("system.b" ++ t)∉ (decideFeasible source target).warrs):
    Spec (2 ^ w) (Input F source target) (decideFeasible source target)
      (fun _ τ => RamEquationData.Data F (prefixedView source τ)∧
        RamBisectionCommit.condition.evalB (2 ^ w) τ=some (RationalFeasibilityDecision.feasible (rationalProgram F)))
      (instructionBound r s S):=by
  have hH:1≤ 2 ^ (2 * S):=Nat.one_le_pow _ _ (by decide)
  have h1:1 < 2 ^ w:=hH.trans_lt hMB
  have hsize:=family_size F S hA hb hc
  have hwidth:=(RamStoredFeasibilityBounds.wordWidth_monotone hsize).trans hw
  have hcopy:=RamFamilyQueryCopy.copy_spec (2 ^ w) (2 ^ (2 * S)) r s (rationalProgram F)
    (source ++ "system.A") (source ++ "system.b") (target ++ "lp.A") (target ++ "lp.b") (target ++ "lp.c")
    h1 hMB hB
    (fun i j => ⟨by simpa [rationalProgram] using hA i j,by simpa [rationalProgram] using hH⟩)
    (fun i => ⟨by simpa [rationalProgram] using hb i,by simpa [rationalProgram] using hH⟩)
    (fun j => by simp [rationalProgram,hc j]) hAA hBA hBB
    (by simp [RamCopy.Disjoint,RamCopy.suffixes,List.mem_cons,List.mem_singleton,String.append_assoc])
    (by simp [RamCopy.Disjoint,RamCopy.suffixes,List.mem_cons,List.mem_singleton,String.append_assoc])
    (by simp [RamCopy.Disjoint,RamCopy.suffixes,List.mem_cons,List.mem_singleton,String.append_assoc])
  rintro σ ⟨hσData,hσlpA,hσlpb,hσlpc,hσintA,hσintb,hσintc,hσWork⟩
  have hσcopy:RamFamilyQueryCopy.Input (rationalProgram F)
      (source ++ "system.A") (source ++ "system.b") (target ++ "lp.A") (target ++ "lp.b") (target ++ "lp.c") σ:=by
    rcases hσData with ⟨hσA,hσb,hσm,hσn⟩
    exact ⟨by simpa [prefixedView,RamArrayRelabel.view,Represents,String.append_assoc] using hσA,
      by simpa [prefixedView,RamArrayRelabel.view,Represents,String.append_assoc] using hσb,
      hσm,hσn,hσlpA,hσlpb,hσlpc⟩
  obtain ⟨τ,hr₁,hτcopy⟩:=hcopy σ hσcopy
  have hτP:RamStoredProgram.RepresentsProgram (rationalProgram F) (prefixedView target τ):=by
    simpa [RamFamilyQueryCopy.Output,RamStoredProgram.RepresentsProgram,prefixedView,
      RamArrayRelabel.view,Represents,String.append_assoc] using hτcopy
  have hτintA:=RamAdvanceState.extents_of_run hr₁ _ _ hσintA
  have hτintb:=RamAdvanceState.extents_of_run hr₁ _ _ hσintb
  have hτintc:=RamAdvanceState.extents_of_run hr₁ _ _ hσintc
  have hτWork:=workspace_view_of_run hr₁ target r s hσWork
  have hfeas:=RamArrayRelabel.spec_prefixed target
    (RamStoredFeasibility.decideFeasible_condition_spec r s (rationalProgram F) w hwidth)
  obtain ⟨υ,hr₂,hυbool⟩:=hfeas τ ⟨hτP,
    by simpa [Extents,prefixedView,RamArrayRelabel.view,String.append_assoc] using hτintA,
    by simpa [Extents,prefixedView,RamArrayRelabel.view,String.append_assoc] using hτintb,
    by simpa [Extents,prefixedView,RamArrayRelabel.view,String.append_assoc] using hτintc,hτWork⟩
  have hr:=hr₁.seq hr₂
  have hυm:=(hr.frame_var "system.m" (by change "system.m" ∉ (decideFeasible source target).wvars; rw [decide_wvars]; decide)).trans hσData.2.2.1
  have hυn:=(hr.frame_var "system.n" (by change "system.n" ∉ (decideFeasible source target).wvars; rw [decide_wvars]; decide)).trans hσData.2.2.2
  have hυA:=RamReadBody.represents_frame (source ++ "system.A") _ hσcopy.1 hr
    (by intro t ht; change (source ++ "system.A") ++ t∉ (decideFeasible source target).warrs; simpa [String.append_assoc] using hFrameA t (by simpa [RamCopy.suffixes] using ht))
  have hυb:=RamReadBody.represents_frame (source ++ "system.b") _ hσcopy.2.1 hr
    (by intro t ht; change (source ++ "system.b") ++ t∉ (decideFeasible source target).warrs; simpa [String.append_assoc] using hFrameB t (by simpa [RamCopy.suffixes] using ht))
  refine ⟨υ,hr.mono (Nat.add_le_add_left (RamStoredFeasibilityBounds.instructionBound_monotone hsize) _),
    ⟨?_, ?_,hυm,hυn⟩, ?_⟩
  · simpa [prefixedView,RamArrayRelabel.view,Represents,String.append_assoc] using hυA
  · simpa [prefixedView,RamArrayRelabel.view,Represents,String.append_assoc] using hυb
  · simpa [RamBisectionCommit.condition,prefixedView,RamArrayRelabel.view,Cond.evalB,Expr.evalB] using hυbool

end Lax109476Proofs.RamCertificateDecision

end

theorem solution:∀ (r s S w:ℕ) (F:Lax109476.LinearProgram.Program ℤ r s) (source target:String),
  2 ^ (2 * S) < 2 ^ w→
    r * s + r + s + 4 < 2 ^ w→
      Lax109476Proofs.RamStoredFeasibility.wordWidth (Lax109476Proofs.RamCertificateDecision.sizeBound r s S)≤ w→
        (∀ (i:Fin r) (j:Fin s), (F.A i j).natAbs≤ 2 ^ (2 * S))→
          (∀ (i:Fin r), (F.b i).natAbs≤ 2 ^ (2 * S))→
            (∀ (j:Fin s),F.c j=0)→
              Lax109476Proofs.RamCopy.Disjoint (source ++ "system.A") (target ++ "lp.A")→
                Lax109476Proofs.RamCopy.Disjoint (source ++ "system.b") (target ++ "lp.A")→
                  Lax109476Proofs.RamCopy.Disjoint (source ++ "system.b") (target ++ "lp.b")→
                    (∀ t∈ Lax109476Proofs.RamCopy.suffixes,
                        source ++ ("system.A" ++ t)∉
                          (Lax109476Proofs.RamCertificateDecision.decideFeasible source target).warrs)→
                      (∀ t∈ Lax109476Proofs.RamCopy.suffixes,
                          source ++ ("system.b" ++ t)∉
                            (Lax109476Proofs.RamCertificateDecision.decideFeasible source target).warrs)→
                        Lax808846Proofs.Reasoning.Spec (2 ^ w)
                          (Lax109476Proofs.RamCertificateDecision.Input F source target)
                          (Lax109476Proofs.RamCertificateDecision.decideFeasible source target)
                          (fun (x τ:Lax808846Proofs.Imp.Env) =>
                            Lax109476Proofs.RamEquationData.Data F
                                (Lax109476Proofs.RamCertificateDecision.prefixedView source τ)∧
                              Lax808846Proofs.Imp.Cond.evalB (2 ^ w) Lax109476Proofs.RamBisectionCommit.condition τ =
                                Option.some
                                  (Lax109476Proofs.RationalFeasibilityDecision.feasible
                                    (Lax109476Proofs.IntegerEncoding.rationalProgram F)))
                          (Lax109476Proofs.RamCertificateDecision.instructionBound r s S):= @Lax109476Proofs.RamCertificateDecision.decideFeasible_spec
