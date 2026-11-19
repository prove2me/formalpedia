-- Prove2me | solution 1 for Lax109476Proofs.RamSolverFinish.finish_spec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T11:22:22.13121+00:00
-- url     : https://prove2.me/submissions/4614ee30-651c-4e7c-a689-4618431d8aa8

import Mathlib.Tactic
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Size
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Nat.Cast.Field
import Definitions.Def_EdgeSublinearMWIS_Main_NativeSchemeInterfaces
import Theorems.Thm_Lax109476Proofs_RamSolverChooseCertificate_choose_spec

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

namespace Lax109476Proofs.RationalRounding

def roundDown (q:ℚ) (D:ℕ):ℚ:=(Int.floor (q * D):ℚ) / D

def sqrtUpper (q:ℚ) (D:ℕ):ℚ:=
  ((Nat.sqrt (Nat.ceil (q * (D:ℚ) ^ 2)) + 1:ℕ):ℚ) / D

end Lax109476Proofs.RationalRounding

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RationalSizeBounds

variable {ι:Type*} [Fintype ι]

theorem commonDenominator_pos (q:ι→ ℚ):0 < commonDenominator q:=by
  exact Finset.prod_pos (fun i _ => (q i).den_pos)

theorem denominator_dvd (q:ι→ ℚ) (i:ι):(q i).den ∣ commonDenominator q:=by
  classical
  exact Finset.dvd_prod_of_mem (fun i => (q i).den) (Finset.mem_univ i)

theorem clearedNumerator_cast (q:ι→ ℚ) (i:ι):
    (clearedNumerator q i:ℚ)=(commonDenominator q:ℚ) * q i:=by
  have hdiv:(commonDenominator q:ℚ) =
      (commonDenominator q / (q i).den:ℕ) * ((q i).den:ℚ):=by
    exact_mod_cast (Nat.div_mul_cancel (denominator_dvd q i)).symm
  rw [clearedNumerator,Int.cast_mul,Int.cast_natCast]
  conv_rhs => rw [← (q i).num_div_den,hdiv]
  have hd:((q i).den:ℚ) ≠ 0:=by exact_mod_cast (q i).den_ne_zero
  field_simp

theorem clearedNumerator_bound (q:ι→ ℚ) (i:ι):
    (clearedNumerator q i).natAbs≤ (q i).num.natAbs * commonDenominator q:=by
  simp only [clearedNumerator,Int.natAbs_mul,Int.natAbs_natCast]
  exact Nat.mul_le_mul_left _ (Nat.div_le_self _ _)

theorem product_le_two_pow_sum_size (s:Finset ι) (f:ι→ ℕ):
    (∏ i∈ s,f i)≤ 2 ^ (∑ i∈ s,Nat.size (f i)):=by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi,Finset.sum_insert hi,pow_add]
    exact Nat.mul_le_mul (Nat.lt_size_self (f i)).le ih

theorem commonDenominator_bound (q:ι→ ℚ):
    commonDenominator q≤ 2 ^ (∑ i,Nat.size (q i).den):=
  product_le_two_pow_sum_size Finset.univ (fun i => (q i).den)

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

theorem rational_size_bounds (q:ℚ):
    3≤ bitSize (encodeRational q)∧
      Nat.size q.num.natAbs + Nat.size q.den≤ bitSize (encodeRational q):=by
  unfold encodeRational
  rw [bitSize_cons,bitSize_cons,bitSize_cons,bitSize_nil]
  omega

theorem vector_size {n:ℕ} (x:Fin n→ ℚ):
    bitSize (encodeVector x)=∑ j,bitSize (encodeRational (x j)):=by
  rw [encodeVector,bitSize_flatMap,List.map_ofFn,List.sum_ofFn]
  rfl

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

theorem data_size_sum {m n:ℕ} (P:Program ℚ m n):
    (∑ i,bitSize (encodeRational (programData P i)))≤ bitSize (encodeProgram P):=by
  rw [program_size]
  simp only [programData,Fintype.sum_sum_type,Fintype.sum_prod_type,
    Sum.elim_inl,Sum.elim_inr]
  omega

theorem denominator_size_sum {m n:ℕ} (P:Program ℚ m n):
    (∑ i,Nat.size (programData P i).den)≤ bitSize (encodeProgram P):=by
  apply le_trans _ (data_size_sum P)
  apply Finset.sum_le_sum
  intro i _
  have h:=(rational_size_bounds (programData P i)).2
  omega

theorem datum_numerator_size {m n:ℕ} (P:Program ℚ m n) (i):
    Nat.size (programData P i).num.natAbs≤ bitSize (encodeProgram P):=by
  have h:=(rational_size_bounds (programData P i)).2
  have hs:=Finset.single_le_sum (fun j _ => Nat.zero_le
    (bitSize (encodeRational (programData P j)))) (Finset.mem_univ i)
  have hb:=data_size_sum P
  omega

end Lax109476Proofs.EncodingSize

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.IntegerEncoding

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax109476.RationalEncoding Lax759944.BinaryWordEncoding
open RationalSizeBounds EncodingSize

def scaledProgram {m n:ℕ} (P:Program ℚ m n) (s:ℚ):Program ℚ m n where
  A i j:=s * P.A i j
  b i:=s * P.b i
  c j:=s * P.c j

theorem integerProgram_eq_scaled {m n:ℕ} (P:Program ℚ m n):
    rationalProgram (integerProgram P)=scaledProgram P (programDenominator P):=by
  unfold rationalProgram integerProgram scaledProgram
  congr 1
  · funext i j
    exact clearedNumerator_cast (programData P) (.inl (i,j))
  · funext i
    exact clearedNumerator_cast (programData P) (.inr (.inl i))
  · funext j
    exact clearedNumerator_cast (programData P) (.inr (.inr j))

theorem programDenominator_bound {m n:ℕ} (P:Program ℚ m n):
    programDenominator P≤ 2 ^ bitSize (encodeProgram P):=
  (commonDenominator_bound (programData P)).trans
    (Nat.pow_le_pow_right (by decide) (denominator_size_sum P))

theorem cleared_datum_bound {m n:ℕ} (P:Program ℚ m n) (i):
    (clearedNumerator (programData P) i).natAbs≤
      2 ^ (2 * bitSize (encodeProgram P)):=by
  have hn:(programData P i).num.natAbs≤ 2 ^ bitSize (encodeProgram P):=
    (Nat.lt_size_self _).le.trans
      (Nat.pow_le_pow_right (by decide) (datum_numerator_size P i))
  calc
    _≤ (programData P i).num.natAbs * programDenominator P:=
      clearedNumerator_bound _ i
    _≤ 2 ^ bitSize (encodeProgram P) * 2 ^ bitSize (encodeProgram P):=
      Nat.mul_le_mul hn (programDenominator_bound P)
    _=_:=by rw [← pow_add]; congr 1; omega

theorem integerProgram_bounds {m n:ℕ} (P:Program ℚ m n):
    (∀ i j, ((integerProgram P).A i j).natAbs≤ 2 ^ (2 * bitSize (encodeProgram P)))∧
    (∀ i, ((integerProgram P).b i).natAbs≤ 2 ^ (2 * bitSize (encodeProgram P)))∧
    (∀ j, ((integerProgram P).c j).natAbs≤ 2 ^ (2 * bitSize (encodeProgram P))):=
  ⟨fun i j => cleared_datum_bound P (.inl (i,j)),
    fun i => cleared_datum_bound P (.inr (.inl i)),
    fun j => cleared_datum_bound P (.inr (.inr j))⟩

theorem row_scaled {m n:ℕ} (P:Program ℚ m n) (s:ℚ) (x:Fin n→ ℚ) (i):
    rowValue (scaledProgram P s) x i=s * rowValue P x i:=by
  simp only [rowValue,scaledProgram,Finset.mul_sum,mul_assoc]

theorem column_scaled {m n:ℕ} (P:Program ℚ m n) (s:ℚ) (y:Fin m→ ℚ) (j):
    columnValue (scaledProgram P s) y j=s * columnValue P y j:=by
  simp only [columnValue,scaledProgram,Finset.mul_sum,mul_assoc]

theorem primalValue_scaled {m n:ℕ} (P:Program ℚ m n) (s:ℚ) (x:Fin n→ ℚ):
    primalValue (scaledProgram P s) x=s * primalValue P x:=by
  simp only [primalValue,scaledProgram,Finset.mul_sum,mul_assoc]

theorem dualValue_scaled {m n:ℕ} (P:Program ℚ m n) (s:ℚ) (y:Fin m→ ℚ):
    dualValue (scaledProgram P s) y=s * dualValue P y:=by
  simp only [dualValue,scaledProgram,Finset.mul_sum,mul_assoc]

theorem primal_feasible_scaled {m n:ℕ} (P:Program ℚ m n) (s:ℚ)
    (hs:0 < s) (x:Fin n→ ℚ):
    PrimalFeasible (scaledProgram P s) x↔ PrimalFeasible P x:=by
  simp only [PrimalFeasible,row_scaled]
  change ((∀ j,0≤ x j)∧ ∀ i,s * rowValue P x i≤ s * P.b i)↔ _
  simp only [mul_le_mul_iff_of_pos_left hs]

theorem dual_feasible_scaled {m n:ℕ} (P:Program ℚ m n) (s:ℚ)
    (hs:0 < s) (y:Fin m→ ℚ):
    DualFeasible (scaledProgram P s) y↔ DualFeasible P y:=by
  simp only [DualFeasible,column_scaled]
  change ((∀ i,0≤ y i)∧ ∀ j,s * P.c j≤ s * columnValue P y j)↔ _
  simp only [mul_le_mul_iff_of_pos_left hs]

theorem farkas_scaled {m n:ℕ} (P:Program ℚ m n) (s:ℚ)
    (hs:0 < s) (y:Fin m→ ℚ):
    Lax109476.FarkasCertificate.IsInfeasibilityCertificate (scaledProgram P s) y↔
      Lax109476.FarkasCertificate.IsInfeasibilityCertificate P y:=by
  simp only [Lax109476.FarkasCertificate.IsInfeasibilityCertificate,
    column_scaled,dualValue_scaled]
  constructor <;> rintro ⟨hpos,hcol,hval⟩ <;> refine ⟨hpos, ?_, ?_⟩
  · intro j
    exact (mul_le_mul_iff_of_pos_left hs).mp (by simpa using hcol j)
  · exact (mul_lt_mul_iff_of_pos_left hs).mp (by simpa using hval)
  · intro j
    simpa using (mul_le_mul_iff_of_pos_left hs).mpr (hcol j)
  · simpa using (mul_lt_mul_iff_of_pos_left hs).mpr hval

theorem recession_scaled {m n:ℕ} (P:Program ℚ m n) (s:ℚ)
    (hs:0 < s) (d:Fin n→ ℚ):
    Lax109476.RecessionDirection.IsImprovingDirection (scaledProgram P s) d↔
      Lax109476.RecessionDirection.IsImprovingDirection P d:=by
  simp only [Lax109476.RecessionDirection.IsImprovingDirection,
    row_scaled,primalValue_scaled]
  constructor <;> rintro ⟨hpos,hrow,hval⟩ <;> refine ⟨hpos, ?_, ?_⟩
  · intro i
    exact (mul_le_mul_iff_of_pos_left hs).mp (by simpa using hrow i)
  · exact (mul_lt_mul_iff_of_pos_left hs).mp (by simpa using hval)
  · intro i
    simpa using (mul_le_mul_iff_of_pos_left hs).mpr (hrow i)
  · simpa using (mul_lt_mul_iff_of_pos_left hs).mpr hval

theorem certificate_scaled {m n:ℕ} (P:Program ℚ m n) (s:ℚ)
    (hs:0 < s) (certificate:Certificate m n):
    IsValidCertificate (scaledProgram P s) certificate↔
      IsValidCertificate P certificate:=by
  cases certificate with
  | optimal x y =>
    simp only [IsValidCertificate,primal_feasible_scaled P s hs,
      dual_feasible_scaled P s hs,primalValue_scaled,dualValue_scaled,
      mul_right_inj' (ne_of_gt hs)]
  | infeasible y => exact farkas_scaled P s hs y
  | unbounded x d =>
    simp only [IsValidCertificate,primal_feasible_scaled P s hs,
      recession_scaled P s hs]

end Lax109476Proofs.IntegerEncoding

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.IntegerCertificates

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax109476.FarkasCertificate Lax109476.RecessionDirection
open IntegerEncoding

def coordinateCap (m n H:ℕ):ℕ:=
  (2 * (m + n) + 2).factorial *
    ((2 * (m + n) + 2) * H ^ 2 + 1) ^ (2 * (m + n) + 2)

def pairMatrix {m n:ℕ} (P:Program ℤ m n):
    Matrix (Fin m ⊕ (Fin n ⊕ Bool)) (Fin n ⊕ Fin m) ℤ
  | .inl i => Sum.elim (P.A i) (fun _ => 0)
  | .inr (.inl j) => Sum.elim (fun _ => 0) (fun i => -P.A i j)
  | .inr (.inr false) => Sum.elim P.c (fun i => -P.b i)
  | .inr (.inr true) => Sum.elim (fun j => -P.c j) P.b

def pairBound {m n:ℕ} (P:Program ℤ m n):
    (Fin m ⊕ (Fin n ⊕ Bool))→ ℤ
  | .inl i => P.b i
  | .inr (.inl j) => -P.c j
  | .inr (.inr _) => 0

def rayMatrix {m n:ℕ} (P:Program ℤ m n):
    Matrix (Fin m ⊕ (Fin m ⊕ Unit)) (Fin n ⊕ Fin n) ℤ
  | .inl i => Sum.elim (P.A i) (fun _ => 0)
  | .inr (.inl i) => Sum.elim (fun _ => 0) (P.A i)
  | .inr (.inr _) => Sum.elim (fun _ => 0) (fun j => -P.c j)

def rayBound {m n:ℕ} (P:Program ℤ m n):
    (Fin m ⊕ (Fin m ⊕ Unit))→ ℤ
  | .inl i => P.b i
  | .inr (.inl _) => 0
  | .inr (.inr _) => -1

end Lax109476Proofs.IntegerCertificates

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.Relaxation

open Lax109476.LinearProgram Lax109476.FarkasCertificate
open Lax109476.RationalCertificates
open IntegerEncoding IntegerCertificates

def relaxationDenominator (m n H B:ℕ):ℕ:=
  2 * (m * B + n * m * H * B + 1)

end Lax109476Proofs.Relaxation

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RationalSeparation

open Lax109476.RationalCertificates

def rowValue {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ) (c:Fin n→ ℚ) (i:Fin m):ℚ:=
  ∑ j, (A i j:ℚ) * c j

def firstViolation {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ) (b:Fin m→ ℚ)
    (c:Fin n→ ℚ):Option (Fin m):=
  (List.finRange m).find? (fun i => decide (b i < rowValue A c i))

def rationalRow {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ) (i:Fin m):Fin n→ ℚ:=
  fun j => A i j

end Lax109476Proofs.RationalSeparation

end

section

namespace Lax109476Proofs.EllipsoidRounding

open Matrix

def roundedShape {n:ℕ} (A:Matrix (Fin n) (Fin n) ℚ) (D:ℕ):
    Matrix (Fin n) (Fin n) ℚ:=
  (of fun i j => RationalRounding.roundDown (A i j) D) + ((n:ℚ) / D) • 1

end Lax109476Proofs.EllipsoidRounding

end

section

namespace Lax109476Proofs.EllipsoidBounds

open Matrix EllipsoidRounding

def cutShape (n:ℕ) (A:Matrix (Fin n) (Fin n) ℚ) (a:Fin n→ ℚ):
    Matrix (Fin n) (Fin n) ℚ:=
  ((n:ℚ) ^ 2 / ((n:ℚ) ^ 2 - 1)) •
    (A - (2 / (((n:ℚ) + 1) * (a ⬝ᵥ (A *ᵥ a)))) •
      Matrix.vecMulVec (A *ᵥ a) (A *ᵥ a))

end Lax109476Proofs.EllipsoidBounds

end

section

namespace Lax109476Proofs.EllipsoidCenter

open Matrix EllipsoidRounding EllipsoidBounds
open Lax109476.RationalCertificates

def approximateCenter (n:ℕ) (A:Matrix (Fin n) (Fin n) ℚ)
    (a c:Fin n→ ℚ) (D:ℕ):Fin n→ ℚ:=
  c - (1 / (((n:ℚ) + 1) * RationalRounding.sqrtUpper (a ⬝ᵥ (A *ᵥ a)) D)) •
    (A *ᵥ a)

def roundedCenter (n:ℕ) (A:Matrix (Fin n) (Fin n) ℚ)
    (a c:Fin n→ ℚ) (D:ℕ):Fin n→ ℚ:=
  fun i => RationalRounding.roundDown (approximateCenter n A a c D i) D

def roundedStepShape (n:ℕ) (A:Matrix (Fin n) (Fin n) ℚ)
    (a:Fin n→ ℚ) (D:ℕ) (η:ℚ):Matrix (Fin n) (Fin n) ℚ:=
  ((1 + η) ^ 2) • roundedShape (cutShape n A a) D

end Lax109476Proofs.EllipsoidCenter

end

section

namespace Lax109476Proofs.EllipsoidPrecision

open Matrix EllipsoidRounding EllipsoidBounds EllipsoidCenter
open Lax109476.RationalCertificates

def gridDenominator (l s n:ℕ):ℕ:=2 ^ (l + s + n + 3)

end Lax109476Proofs.EllipsoidPrecision

end

section

namespace Lax109476Proofs.EllipsoidIteration

open Matrix EllipsoidRounding EllipsoidBounds EllipsoidCenter EllipsoidPrecision
open Lax109476.RationalCertificates

def stepAccuracy (n:ℕ):ℚ:=1 / (2:ℚ) ^ (2 * n + 4)

end Lax109476Proofs.EllipsoidIteration

end

section

namespace Lax109476Proofs.EllipsoidSequence

open Matrix EllipsoidRounding EllipsoidBounds EllipsoidCenter EllipsoidPrecision EllipsoidIteration
open Lax109476.RationalCertificates

def thresholdSteps (n B:ℕ):ℕ:=4 * (n + 1) * (B * n + 1)

end Lax109476Proofs.EllipsoidSequence

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.EllipsoidSearch

open Lax109476.RationalCertificates
open RationalSeparation EllipsoidRounding EllipsoidCenter EllipsoidPrecision
open EllipsoidIteration EllipsoidSequence

def cacheState {n:ℕ} (state:Matrix (Fin n) (Fin n) ℚ × (Fin n→ ℚ)):
    Matrix (Fin n) (Fin n) ℚ × (Fin n→ ℚ):=
  let rows:Vector (Vector ℚ n) n:=Vector.ofFn (fun i => Vector.ofFn (state.1 i))
  let center:Vector ℚ n:=Vector.ofFn state.2
  ((fun i j => (rows.get i).get j),fun i => center.get i)

def fallbackNormal (n:ℕ):Fin n→ ℚ:=fun j => if j.val=0 then 1 else 0

def selectedNormal {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ) (b:Fin m→ ℚ)
    (c:Fin n→ ℚ):Fin n→ ℚ:=
  match firstViolation A b c with
  | none => fallbackNormal n
  | some i => if A i=0 then fallbackNormal n else rationalRow A i

def nextState {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ) (b:Fin m→ ℚ)
    (k:ℕ) (old:Matrix (Fin n) (Fin n) ℚ × (Fin n→ ℚ)):
    Matrix (Fin n) (Fin n) ℚ × (Fin n→ ℚ):=
    let a:=selectedNormal A b old.2
    let D:=gridDenominator (2 * k + 2) (2 * n + 4) n
    cacheState
      (roundedStepShape n old.1 a D (stepAccuracy n),roundedCenter n old.1 a old.2 D)

def trajectory {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ) (b:Fin m→ ℚ):
    ℕ→ Matrix (Fin n) (Fin n) ℚ × (Fin n→ ℚ)
  | 0 => (1,0)
  | k + 1 => nextState A b k (trajectory A b k)

def scanStates {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ) (b:Fin m→ ℚ):
    ℕ→ ℕ→ (Matrix (Fin n) (Fin n) ℚ × (Fin n→ ℚ))→ Option ℕ
  | _,0,_ => none
  | start,count + 1,state =>
    if firstViolation A b state.2=none then some start
    else scanStates A b (start + 1) count (nextState A b start state)

def findIteration {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ) (b:Fin m→ ℚ)
    (K:ℕ):Option ℕ:=
  scanStates A b 0 (K + 1) (1,0)

def search {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ) (b:Fin m→ ℚ)
    (K:ℕ):Option (Fin n→ ℚ):=
  (findIteration A b K).map (fun k => (trajectory A b k).2)

end Lax109476Proofs.EllipsoidSearch

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.NormalizedFeasibility

open Lax109476.LinearProgram Lax109476.RationalCertificates
open IntegerEncoding IntegerCertificates Relaxation

def outerScale (n B:ℕ):ℕ:=4 * (n + 1) * (B + 1)

def normalizedMatrix {m n:ℕ} (P:Program ℤ m n) (R:ℕ):
    Matrix (Fin (m + n)) (Fin n) ℤ:=
  Fin.addCases (fun i j => (R:ℤ) * P.A i j)
    (fun k j => if k=j then -(R:ℤ) else 0)

def normalizedBound {m n:ℕ} (P:Program ℤ m n) (ε:ℚ):Fin (m + n)→ ℚ:=
  Fin.addCases (fun i => (P.b i:ℚ) + ε) (fun _ => ε)

def precisionDenominator (m n H:ℕ):ℕ:=
  relaxationDenominator m n H (coordinateCap m n H)

def ballDenominator (m n H:ℕ):ℕ:=
  precisionDenominator m n H * (n * H + 1) * outerScale n (coordinateCap m n H)

def ballExponent (m n H:ℕ):ℕ:=Nat.size (ballDenominator m n H)

end Lax109476Proofs.NormalizedFeasibility

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.IntegerFeasibilityDecision

open Lax109476.LinearProgram Lax109476.RationalCertificates
open IntegerEncoding IntegerCertificates Relaxation NormalizedFeasibility
open EllipsoidSearch EllipsoidSequence

def iterationResult {m n:ℕ} (P:Program ℤ m n) (H:ℕ):Option ℕ:=
  findIteration (normalizedMatrix P (outerScale n (coordinateCap m n H)))
    (normalizedBound P (1 / (precisionDenominator m n H:ℚ)))
    (thresholdSteps n (ballExponent m n H))

def feasible {m n:ℕ} (P:Program ℤ m n) (H:ℕ):Bool:=(iterationResult P H).isSome

end Lax109476Proofs.IntegerFeasibilityDecision

end

section

open scoped BigOperators

namespace Lax109476Proofs.FeasibilityPadding

open Lax109476.LinearProgram Lax109476.RationalCertificates
open IntegerEncoding

def pad {K:Type} [Zero K] [One K] {m n:ℕ} (P:Program K m n):
    Program K (m + 2) (n + 2) where
  A:=Fin.addCases (fun i => Fin.addCases (P.A i) (fun _ => 0))
    (fun k => Fin.addCases (fun _ => 0) (fun j => if k=j then 1 else 0))
  b:=Fin.addCases P.b (fun _ => 0)
  c:=Fin.addCases P.c (fun _ => 0)

def feasible {m n:ℕ} (P:Program ℤ m n) (H:ℕ):Bool:=
  IntegerFeasibilityDecision.feasible (pad P) H

end Lax109476Proofs.FeasibilityPadding

end

section

open scoped BigOperators

namespace Lax109476Proofs.RationalFeasibilityDecision

open Lax109476.LinearProgram Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open IntegerEncoding EncodingSize NormalizedFeasibility EllipsoidSequence

def sizeParameter {m n:ℕ} (P:Program ℚ m n):ℕ:=bitSize (encodeProgram P) + 4

def feasible {m n:ℕ} (P:Program ℚ m n):Bool:=
  FeasibilityPadding.feasible (integerProgram P) (2 ^ (2 * sizeParameter P))

end Lax109476Proofs.RationalFeasibilityDecision

end

section

namespace Lax109476Proofs.RationalReconstruction

def convergent:ℚ→ ℕ→ ℚ
  | a,0 => Int.floor a
  | a,k + 1 => Int.floor a + (convergent (Int.fract a)⁻¹ k)⁻¹

def reconstruct (l u:ℚ) (B:ℕ):Option ℚ:=
  ((List.range (2 * u.den.size + 1)).map (convergent u)).find?
    (fun q => decide (q.den≤ B∧ l≤ q∧ q≤ u))

end Lax109476Proofs.RationalReconstruction

end

section

namespace Lax109476Proofs.BinaryOptimization

open RationalReconstruction

def bisect (query:ℚ→ Bool):ℚ→ ℚ→ ℕ→ ℚ × ℚ
  | l,u,0 => (l,u)
  | l,u,k + 1 =>
    let old:=bisect query l u k
    let mid:=(old.1 + old.2) / 2
    if query mid then (old.1,mid) else (mid,old.2)

def steps (B:ℕ):ℕ:=3 * B.size + 2

def minimum (query:ℚ→ Bool) (B:ℕ):Option ℚ:=
  let interval:=bisect query 0 B (steps B)
  reconstruct interval.1 interval.2 B

end Lax109476Proofs.BinaryOptimization

end

section

open scoped BigOperators

namespace Lax109476Proofs.CoordinateOptimization

open Lax109476.LinearProgram Lax109476.RationalCertificates

def coordinateCut {m n:ℕ} (P:Program ℚ m n) (j:Fin n) (t:ℚ):
    Program ℚ (m + 1) n where
  A:=Fin.addCases P.A (fun _ k => if k=j then 1 else 0)
  b:=Fin.addCases P.b (fun _ => t)
  c:=P.c

def coordinateMinimum {m n:ℕ} (P:Program ℚ m n) (j:Fin n) (B:ℕ):Option ℚ:=
  BinaryOptimization.minimum (fun t => RationalFeasibilityDecision.feasible (coordinateCut P j t)) B

end Lax109476Proofs.CoordinateOptimization

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.LexicographicMinima

open Lax109476.LinearProgram Lax109476.RationalCertificates

def fixedPrefix {m n:ℕ} (P:Program ℚ m n) (x:Fin n→ ℚ) (k:ℕ):
    Program ℚ (m + (n + n)) n where
  A:=Fin.addCases P.A (Fin.addCases
    (fun i j => if i.val < k then if j=i then 1 else 0 else 0)
    (fun i j => if i.val < k then if j=i then -1 else 0 else 0))
  b:=Fin.addCases P.b (Fin.addCases
    (fun i => if i.val < k then x i else 0)
    (fun i => if i.val < k then -x i else 0))
  c:=P.c

end Lax109476Proofs.LexicographicMinima

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.PointRecovery

open Lax109476.LinearProgram Lax109476.RationalCertificates
open LexicographicMinima CoordinateOptimization

def recoverPrefix {m n:ℕ} (P:Program ℚ m n) (B:ℕ):
    ℕ→ Option (Fin n→ ℚ)
  | 0 => some 0
  | k + 1 =>
    (recoverPrefix P B k).bind (fun old =>
      if h:k < n then
        (coordinateMinimum (fixedPrefix P old k) ⟨k,h⟩ B).map
          (fun v => Function.update old ⟨k,h⟩ v)
      else some old)

def recover {m n:ℕ} (P:Program ℚ m n) (B:ℕ):Option (Fin n→ ℚ):=
  recoverPrefix P B n

end Lax109476Proofs.PointRecovery

end

section

open scoped BigOperators

namespace Lax109476Proofs.IndexedPointRecovery

open Lax109476.LinearProgram IntegerEncoding

def reindexProgram {κ ι:Type*} {r n:ℕ} (A:κ→ ι→ ℤ) (b:κ→ ℤ)
    (er:κ ≃ Fin r) (ec:ι ≃ Fin n):Program ℤ r n where
  A i j:=A (er.symm i) (ec.symm j)
  b i:=b (er.symm i)
  c:=0

end Lax109476Proofs.IndexedPointRecovery

end

section

open scoped BigOperators

namespace Lax109476Proofs.CertificateSystems

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax109476.FarkasCertificate Lax109476.RecessionDirection
open IntegerEncoding IntegerCertificates

def farkasMatrix {m n:ℕ} (P:Program ℤ m n):(Fin n ⊕ Unit)→ Fin m→ ℤ:=
  Sum.elim (fun j i => -P.A i j) (fun _ => P.b)

def farkasBound {n:ℕ}:(Fin n ⊕ Unit)→ ℤ:=
  Sum.elim (fun _ => 0) (fun _ => -1)

end Lax109476Proofs.CertificateSystems

end

section

open scoped BigOperators

namespace Lax109476Proofs.CertificateSearch

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax109476.FarkasCertificate Lax109476.RecessionDirection
open IntegerEncoding IntegerCertificates CertificateSystems

def unitFin:Unit ≃ Fin 1 where
  toFun _:=0
  invFun _:=()
  left_inv _:=rfl
  right_inv _:=Subsingleton.elim _ _

def pairRows (m n:ℕ):(Fin m ⊕ (Fin n ⊕ Bool)) ≃ Fin (m + (n + 2)):=
  (Equiv.sumCongr (Equiv.refl _) ((Equiv.sumCongr (Equiv.refl _) finTwoEquiv.symm).trans
    finSumFinEquiv)).trans finSumFinEquiv

def rayRows (m:ℕ):(Fin m ⊕ (Fin m ⊕ Unit)) ≃ Fin (m + (m + 1)):=
  (Equiv.sumCongr (Equiv.refl _) ((Equiv.sumCongr (Equiv.refl _) unitFin).trans
    finSumFinEquiv)).trans finSumFinEquiv

def farkasRows (n:ℕ):(Fin n ⊕ Unit) ≃ Fin (n + 1):=
  (Equiv.sumCongr (Equiv.refl _) unitFin).trans finSumFinEquiv

end Lax109476Proofs.CertificateSearch

end

section

namespace Lax109476Proofs.CertificateFamilyPrograms

open Lax109476.LinearProgram Lax109476.RationalCertificates
open IntegerEncoding IntegerCertificates CertificateSystems IndexedPointRecovery CertificateSearch

def optimal {m n:ℕ} (P:Program ℤ m n):Program ℤ (m + (n + 2)) (n + m):=
  reindexProgram (pairMatrix P) (pairBound P) (pairRows m n) finSumFinEquiv

def infeasible {m n:ℕ} (P:Program ℤ m n):Program ℤ (n + 1) m:=
  reindexProgram (farkasMatrix P) farkasBound (farkasRows n) (Equiv.refl _)

def unbounded {m n:ℕ} (P:Program ℤ m n):Program ℤ (m + (m + 1)) (n + n):=
  reindexProgram (rayMatrix P) (rayBound P) (rayRows m) finSumFinEquiv

end Lax109476Proofs.CertificateFamilyPrograms

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

def Com.decNoWrite:(c:Com)→ Decidable c.NoWrite
  | .skip => decidable_of_iff True (by rw [Com.NoWrite])
  | .assign _ _ => decidable_of_iff True (by rw [Com.NoWrite])
  | .store _ _ _ => decidable_of_iff True (by rw [Com.NoWrite])
  | .seq c d =>
      have:=c.decNoWrite
      have:=d.decNoWrite
      decidable_of_iff (c.NoWrite∧ d.NoWrite) (by rw [Com.NoWrite])
  | .ite _ c d =>
      have:=c.decNoWrite
      have:=d.decNoWrite
      decidable_of_iff (c.NoWrite∧ d.NoWrite) (by rw [Com.NoWrite])
  | .while _ c =>
      have:=c.decNoWrite
      decidable_of_iff c.NoWrite (by rw [Com.NoWrite])
  | .read _ => decidable_of_iff True (by rw [Com.NoWrite])
  | .write _ => decidable_of_iff False (by rw [Com.NoWrite])

instance:DecidablePred Com.NoWrite:=Com.decNoWrite

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

theorem eval_sub (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:m - n < B):
    (Expr.bin .sub e f).evalB B σ=some (m - n):=evalB_bin he hf h

theorem eval_mul (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:m * n < B):
    (Expr.bin .mul e f).evalB B σ=some (m * n):=evalB_bin he hf h

theorem eval_div (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:m / n < B):
    (Expr.bin .div e f).evalB B σ=some (m / n):=evalB_bin he hf h

theorem eval_and (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:Nat.land m n < B):
    (Expr.bin .and e f).evalB B σ=some (Nat.land m n):=evalB_bin he hf h

theorem eval_or (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:Nat.lor m n < B):
    (Expr.bin .or e f).evalB B σ=some (Nat.lor m n):=evalB_bin he hf h

theorem eval_xor (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:Nat.xor m n < B):
    (Expr.bin .xor e f).evalB B σ=some (Nat.xor m n):=evalB_bin he hf h

theorem eval_shiftl (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:m * 2 ^ n < B):
    (Expr.bin .shiftl e f).evalB B σ=some (m * 2 ^ n):=evalB_bin he hf h

theorem eval_shiftr (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:m / 2 ^ n < B):
    (Expr.bin .shiftr e f).evalB B σ=some (m / 2 ^ n):=evalB_bin he hf h

theorem cond_eq_true (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:m=n):
    (Cond.eq e f).evalB B σ=some true:=by
  rw [evalB_condEq he hf,h]; simp

theorem cond_eq_false (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:¬ m=n):
    (Cond.eq e f).evalB B σ=some false:=by
  rw [evalB_condEq he hf]; simp [h]

theorem cond_lt_true (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:m < n):
    (Cond.lt e f).evalB B σ=some true:=by
  rw [evalB_condLt he hf]; simp [h]

theorem cond_lt_false (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:¬ m < n):
    (Cond.lt e f).evalB B σ=some false:=by
  rw [evalB_condLt he hf]; simp [h]

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

theorem seq_inv (B:ℕ) (c d:Com) (σ σ'':Env) (K:ℕ) (h:Run B (.seq c d) σ σ'' K):
    ∃ σ' K₁ K₂,Run B c σ σ' K₁∧ Run B d σ' σ'' K₂∧ K₁ + K₂≤ K:=by
  obtain ⟨k,hk,hbs⟩:=h
  cases hbs with
  | seq h₁ h₂ => exact ⟨_,_,_, ⟨_,le_rfl,h₁⟩, ⟨_,le_rfl,h₂⟩,hk⟩

theorem seq_split (B:ℕ) (p r w:Com) (hs:SeqSplit p r w):
    ∀ (σ σ₁ σ₂:Env) (K₁ K₂:ℕ),Run B p σ σ₁ K₁→ Run B r σ₁ σ₂ K₂→
      Run B w σ σ₂ (K₁ + K₂):=by
  induction hs with
  | one a r => intro σ σ₁ σ₂ K₁ K₂ h₁ h₂; exact h₁.seq h₂
  | cons a p r w _ ih =>
      intro σ σ₁ σ₂ K₁ K₂ h₁ h₂
      obtain ⟨σ',Ka,Kb,ha,hb,hk⟩:=seq_inv B a p σ σ₁ K₁ h₁
      exact (ha.seq (ih σ' σ₁ σ₂ Kb K₂ hb h₂)).mono (by omega)

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

def fractionValue (s n d:ℕ):ℚ:=if s=1 then -(n:ℚ) / d else (n:ℚ) / d

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

def Height (q:ℚ) (B:ℕ):Prop:=q.num.natAbs≤ B∧ q.den≤ B

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

noncomputable abbrev _root_.AXr3955_0:= @Lax109476Proofs.RamRationalArrays.loadLeft
noncomputable abbrev _root_.AXr3955_1:= @Lax808846Proofs.Reasoning.RunStep.eval_get
noncomputable abbrev _root_.AXr3955_2:= @Lax808846Proofs.Reasoning.RunStep.eval_var
noncomputable abbrev _root_.AXr3955_3:= @Lax808846Proofs.Reasoning.RunStep.assign
noncomputable abbrev _root_.AXr3955_4:= @Lax808846Proofs.Imp.Com.assign
noncomputable abbrev _root_.AXr3955_5:= @Lax808846Proofs.Imp.Env.setVar
noncomputable abbrev _root_.AXr3955_6:= @Lax808846Proofs.Imp.Expr.size
noncomputable abbrev _root_.AXr3955_7:= @Lax808846Proofs.Imp.Env.arrs
noncomputable abbrev _root_.AXr3955_8:= @Lax808846Proofs.Imp.Env.vars
noncomputable abbrev _root_.AXr3955_9:= @Lax808846Proofs.Imp.Expr.get
noncomputable abbrev _root_.AXr3955_10:= @Lax808846Proofs.Imp.Expr.var
noncomputable abbrev _root_.AXr3955_11:= @Lax808846Proofs.Imp.Env
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
  (first
   | (expose_names;
       refine
         let c0:AXr3955_11→ Prop:=
           Lax109476Proofs.RamRationalArrays.LeftOutput
             (@GetElem.getElem (List Rat) Nat Rat
               (fun (as:List Rat) (i:Nat) => @LT.lt Nat instLTNat i (@List.length Rat as))
               (@List.instGetElemNatLtLength Rat) qs i hi);
         let c1:AXr3955_11→ Prop:=(fun (x τ:AXr3955_11) => c0 τ) σ;
         let c2:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a;
         let c3:String:=c2 ".s";
         let c4:Nat:=
           @List.getD Nat (AXr3955_7 σ c3) (AXr3955_8 σ "vec.i")
             (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)));
         let c5:AXr3955_11:=AXr3955_5 σ "left.s" c4;
         let c6:String:=c2 ".n";
         let c7:Nat:=AXr3955_8 c5 "vec.i";
         let c8:Nat:=
           @List.getD Nat (AXr3955_7 c5 c6) c7 (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)));
         let c9:AXr3955_11:=AXr3955_5 c5 "left.n" c8;
         let c10:String:=c2 ".d";
         let c11:Nat:=AXr3955_8 c9 "vec.i";
         let c12:Nat:=
           @List.getD Nat (AXr3955_7 c9 c10) c11
             (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)));
         let c13:AXr3955_11:=AXr3955_5 c9 "left.d" c12;
         let c14:Nat→ Nat→ Nat:= @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat);
         let c15:Nat→ Nat:=c14 (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)));
         let c16:Lax808846Proofs.Imp.Expr:=AXr3955_9 c3 (AXr3955_10 "vec.i");
         let c17:Nat:=c15 (AXr3955_6 c16);
         let c18:Lax808846Proofs.Imp.Expr:=AXr3955_9 c6 (AXr3955_10 "vec.i");
         let c19:Nat:=c15 (AXr3955_6 c18);
         let c20:Lax808846Proofs.Imp.Expr:=AXr3955_9 c10 (AXr3955_10 "vec.i");
         let c21:Nat:=c15 (AXr3955_6 c20);
         let c22:Nat:=c14 c19 c21;
         let c23:Lax808846Proofs.Imp.Com:=AXr3955_4 "left.n" c18;
         let c24:Lax808846Proofs.Imp.Com:=AXr3955_4 "left.d" c20;
         @Exists.intro AXr3955_11
           (fun (σ':AXr3955_11) =>
             And
               (Lax808846Proofs.Reasoning.Run B (AXr3955_0 a) σ σ'
                 (@OfNat.ofNat Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
               (c1 σ'))
           c13
           (@And.intro
             (Lax808846Proofs.Reasoning.Run B (AXr3955_0 a) σ c13
               (@OfNat.ofNat Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
             (c1 c13)
             (Lax808846Proofs.Reasoning.RunStep.mono B (AXr3955_0 a) σ c13 (c14 c17 c22)
               (@OfNat.ofNat Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
               (Lax808846Proofs.Reasoning.RunStep.seq B (AXr3955_4 "left.s" c16)
                 (Lax808846Proofs.Imp.Com.seq c23 c24) σ c5 c13 c17 c22
                 (AXr3955_3 B σ "left.s" c16 c4
                   (AXr3955_1 B σ c3 (AXr3955_10 "vec.i")
                     (AXr3955_8 σ "vec.i")
                     (AXr3955_2 B σ "vec.i"
                       (?nAX_g3955_0_0_0))
                     (?nAX_g3955_0_0_1)
                     (?nAX_g3955_0_0_2)))
                 (Lax808846Proofs.Reasoning.RunStep.seq B c23 c24 c5 c9 c13 c19 c21
                   (AXr3955_3 B c5 "left.n" c18 c8
                     (AXr3955_1 B c5 c6 (AXr3955_10 "vec.i") c7
                       (AXr3955_2 B c5 "vec.i"
                         (?nAX_g3955_0_0_3))
                       (?nAX_g3955_0_0_4)
                       (?nAX_g3955_0_0_5)))
                   (AXr3955_3 B c9 "left.d" c20 c12
                     (AXr3955_1 B c9 c10 (AXr3955_10 "vec.i") c11
                       (AXr3955_2 B c9 "vec.i"
                         (?nAX_g3955_0_0_6))
                       (?nAX_g3955_0_0_7)
                       (?nAX_g3955_0_0_8)))))
               (?nAX_g3955_0_0_9))
             ?_)
      all_goals try dsimp +zetaDelta at *
      try case nAX_g3955_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3955_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3955_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3955_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3955_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3955_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3955_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3955_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3955_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3955_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all
     )
   | (expose_names;
       refine
           let c0:AXr3955_11→ Prop:=
             Lax109476Proofs.RamRationalArrays.LeftOutput
               (@GetElem.getElem (List Rat) Nat Rat
                 (fun (as:List Rat) (i:Nat) => @LT.lt Nat instLTNat i (@List.length Rat as))
                 (@List.instGetElemNatLtLength Rat) qs i hi);
           let c1:AXr3955_11→ Prop:=(fun (x τ:AXr3955_11) => c0 τ) σ;
           let c2:String→ String:=
             @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a;
           let c3:String:=c2 ".s";
           let c4:Nat:=
             @List.getD Nat (AXr3955_7 σ c3) (AXr3955_8 σ "vec.i")
               (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)));
           let c5:AXr3955_11:=AXr3955_5 σ "left.s" c4;
           let c6:String:=c2 ".n";
           let c7:Nat:=AXr3955_8 c5 "vec.i";
           let c8:Nat:=
             @List.getD Nat (AXr3955_7 c5 c6) c7
               (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)));
           let c9:AXr3955_11:=AXr3955_5 c5 "left.n" c8;
           let c10:String:=c2 ".d";
           let c11:Nat:=AXr3955_8 c9 "vec.i";
           let c12:Nat:=
             @List.getD Nat (AXr3955_7 c9 c10) c11
               (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)));
           let c13:AXr3955_11:=AXr3955_5 c9 "left.d" c12;
           let c14:Nat→ Nat→ Nat:= @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat);
           let c15:Nat→ Nat:=c14 (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)));
           let c16:Lax808846Proofs.Imp.Expr:=AXr3955_9 c3 (AXr3955_10 "vec.i");
           let c17:Nat:=c15 (AXr3955_6 c16);
           let c18:Lax808846Proofs.Imp.Expr:=AXr3955_9 c6 (AXr3955_10 "vec.i");
           let c19:Nat:=c15 (AXr3955_6 c18);
           let c20:Lax808846Proofs.Imp.Expr:=AXr3955_9 c10 (AXr3955_10 "vec.i");
           let c21:Nat:=c15 (AXr3955_6 c20);
           let c22:Nat:=c14 c19 c21;
           let c23:Lax808846Proofs.Imp.Com:=AXr3955_4 "left.n" c18;
           let c24:Lax808846Proofs.Imp.Com:=AXr3955_4 "left.d" c20;
           @Exists.intro AXr3955_11
             (fun (σ':AXr3955_11) =>
               And
                 (Lax808846Proofs.Reasoning.Run B (AXr3955_0 a) σ σ'
                   (@OfNat.ofNat Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
                 (c1 σ'))
             c13
             (@And.intro
               (Lax808846Proofs.Reasoning.Run B (AXr3955_0 a) σ c13
                 (@OfNat.ofNat Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
               (c1 c13)
               (Lax808846Proofs.Reasoning.RunStep.mono B (AXr3955_0 a) σ c13 (c14 c17 c22)
                 (@OfNat.ofNat Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
                 (Lax808846Proofs.Reasoning.RunStep.seq B (AXr3955_4 "left.s" c16)
                   (Lax808846Proofs.Imp.Com.seq c23 c24) σ c5 c13 c17 c22
                   (AXr3955_3 B σ "left.s" c16 c4
                     (AXr3955_1 B σ c3 (AXr3955_10 "vec.i")
                       (AXr3955_8 σ "vec.i")
                       (AXr3955_2 B σ "vec.i"
                         (?nAX_g3955_0_1_0))
                       (?nAX_g3955_0_1_1)
                       ?_))
                   (Lax808846Proofs.Reasoning.RunStep.seq B c23 c24 c5 c9 c13 c19 c21
                     (AXr3955_3 B c5 "left.n" c18 c8
                       (AXr3955_1 B c5 c6 (AXr3955_10 "vec.i") c7
                         (AXr3955_2 B c5 "vec.i"
                           (?nAX_g3955_0_1_2))
                         (?nAX_g3955_0_1_3)
                         ?_))
                     (AXr3955_3 B c9 "left.d" c20 c12
                       (AXr3955_1 B c9 c10 (AXr3955_10 "vec.i") c11
                         (AXr3955_2 B c9 "vec.i"
                           (?nAX_g3955_0_1_4))
                         (?nAX_g3955_0_1_5)
                         ?_))))
                 (?nAX_g3955_0_1_6))
               ?_) <;> try dsimp +zetaDelta at *
      all_goals try dsimp +zetaDelta at *
      try case nAX_g3955_0_1_0 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3955_0_1_1 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3955_0_1_2 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3955_0_1_3 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3955_0_1_4 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3955_0_1_5 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3955_0_1_6 => solve | omega | (simp <;> omega) | assumption | simp_all
     )
  )
  all_goals simp_all [LeftOutput]

noncomputable abbrev _root_.AXr3962_0:= @Lax109476Proofs.RamRationalArrays.storeReduced
noncomputable abbrev _root_.AXr3962_1:= @Lax808846Proofs.Reasoning.RunStep.eval_var
noncomputable abbrev _root_.AXr3962_2:= @Lax808846Proofs.Reasoning.RunStep.store
noncomputable abbrev _root_.AXr3962_3:= @Lax808846Proofs.Imp.Env.setArr
noncomputable abbrev _root_.AXr3962_4:= @Lax808846Proofs.Imp.Expr.evalB
noncomputable abbrev _root_.AXr3962_5:= @Lax808846Proofs.Imp.Com.store
noncomputable abbrev _root_.AXr3962_6:= @Lax808846Proofs.Imp.Expr.size
noncomputable abbrev _root_.AXr3962_7:= @Lax808846Proofs.Reasoning.Run
noncomputable abbrev _root_.AXr3962_8:= @Lax808846Proofs.Imp.Env.vars
noncomputable abbrev _root_.AXr3962_9:= @Lax808846Proofs.Imp.Expr.lit
noncomputable abbrev _root_.AXr3962_10:= @Lax808846Proofs.Imp.Expr.var
noncomputable abbrev _root_.AXr3962_11:= @Lax808846Proofs.Imp.Com.seq
noncomputable abbrev _root_.AXr3962_12:= @Lax808846Proofs.Imp.Com
noncomputable abbrev _root_.AXr3962_13:= @Lax808846Proofs.Imp.Env
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
  (first
   | (expose_names;
       refine
         let c0:Prop:=
           @Eq Nat (AXr3962_8 σ "rat.n") (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)));
         let c1:Prop:=Not c0;
         let c2:AXr3962_13→ Prop:=Lax109476Proofs.RamRationalArrays.Represents a (@List.set Rat qs i q);
         let c3:AXr3962_13→ Prop:=(fun (x τ:AXr3962_13) => c2 τ) σ;
         let c4:AXr3962_13→ Prop:=fun (σ':AXr3962_13) =>
           And
             (AXr3962_7 B (AXr3962_0 a) σ σ'
               (@OfNat.ofNat Nat (nat_lit 13) (instOfNatNat (nat_lit 13))))
             (c3 σ');
         let c5:∀ (w:AXr3962_13),c4 w→ @Exists AXr3962_13 c4:=
           @Exists.intro AXr3962_13 c4;
         let c6:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a;
         let c7:String:=c6 ".s";
         let c8:Nat→ AXr3962_13:=
           AXr3962_3 σ c7 (AXr3962_8 σ "vec.i");
         let c9:AXr3962_13:=c8 (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)));
         let c10:String:=c6 ".n";
         let c11:String→ Nat:=AXr3962_8 c9;
         let c12:Nat:=c11 "vec.i";
         let c13:Nat:=c11 "rat.n";
         let c14:AXr3962_13:=AXr3962_3 c9 c10 c12 c13;
         let c15:String:=c6 ".d";
         let c16:String→ Nat:=AXr3962_8 c14;
         let c17:Nat:=c16 "vec.i";
         let c18:Nat:=c16 "rat.d";
         let c19:AXr3962_13:=AXr3962_3 c14 c15 c17 c18;
         let c20:Nat→ Nat→ Nat:= @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat);
         let c21:Nat→ Nat:=c20 (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)));
         let c22:Lax808846Proofs.Imp.Cond:=
           Lax808846Proofs.Imp.Cond.eq (AXr3962_10 "rat.n")
             (AXr3962_9 (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))));
         let c23:Nat→ Nat:=c20 (c21 (Lax808846Proofs.Imp.Cond.size c22));
         let c24:Nat→ Nat:=c20 (c21 (AXr3962_6 (AXr3962_10 "vec.i")));
         let c25:Nat:=
           c24
             (AXr3962_6
               (AXr3962_9 (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))));
         let c26:Nat:=c23 c25;
         let c27:Nat:=c24 (AXr3962_6 (AXr3962_10 "rat.n"));
         let c28:Nat:=c24 (AXr3962_6 (AXr3962_10 "rat.d"));
         let c29:Nat:=c20 c27 c28;
         let c30:Lax808846Proofs.Imp.Expr→ AXr3962_12:=
           AXr3962_5 c7 (AXr3962_10 "vec.i");
         let c31:AXr3962_12:=
           c30 (AXr3962_9 (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))));
         let c32:AXr3962_12:=c30 (AXr3962_10 "rat.s");
         let c33:AXr3962_12:=
           AXr3962_5 c10 (AXr3962_10 "vec.i") (AXr3962_10 "rat.n");
         let c34:AXr3962_12:=
           AXr3962_5 c15 (AXr3962_10 "vec.i") (AXr3962_10 "rat.d");
         let c35:
           ∀ (σ' σ'':AXr3962_13) (K K':Nat),
             AXr3962_7 B (Lax808846Proofs.Imp.Com.ite c22 c31 c32) σ σ' K→
               AXr3962_7 B (AXr3962_11 c33 c34) σ' σ'' K'→
                 AXr3962_7 B
                   (AXr3962_11 (Lax808846Proofs.Imp.Com.ite c22 c31 c32)
                     (AXr3962_11 c33 c34))
                   σ σ'' (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) K K'):=
           Lax808846Proofs.Reasoning.RunStep.seq B (Lax808846Proofs.Imp.Com.ite c22 c31 c32)
             (AXr3962_11 c33 c34) σ;
         let c36:
           @Eq (Option Nat)
             (AXr3962_4 B
               (AXr3962_9 (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) σ)
             (@Option.some Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))):=
           Lax808846Proofs.Reasoning.RunStep.eval_lit B (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) σ
             (?nAX_g3962_0_0_0);
         let c37:
           ∀ (e:Lax808846Proofs.Imp.Expr) (idx v:Nat),
             @Eq (Option Nat) (AXr3962_4 B (AXr3962_10 "vec.i") σ)
                 (@Option.some Nat idx)→
               @Eq (Option Nat) (AXr3962_4 B e σ) (@Option.some Nat v)→
                 @LT.lt Nat instLTNat idx (@List.length Nat (Lax808846Proofs.Imp.Env.arrs σ c7))→
                   AXr3962_7 B
                     (AXr3962_5 c7 (AXr3962_10 "vec.i") e) σ
                     (AXr3962_3 σ c7 idx v)
                     (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                       (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                         (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                         (AXr3962_6 (AXr3962_10 "vec.i")))
                       (AXr3962_6 e)):=
           AXr3962_2 B σ c7 (AXr3962_10 "vec.i");
         let c38:
           ∀ (σ σ' σ'':AXr3962_13) (K K':Nat),
             AXr3962_7 B c33 σ σ' K→
               AXr3962_7 B c34 σ' σ'' K'→
                 AXr3962_7 B (AXr3962_11 c33 c34) σ σ''
                   (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) K K'):=
           Lax808846Proofs.Reasoning.RunStep.seq B c33 c34;
         let c39:
           ∀ (x:String),
             @LT.lt Nat instLTNat (AXr3962_8 c9 x) B→
               @Eq (Option Nat) (AXr3962_4 B (AXr3962_10 x) c9)
                 (@Option.some Nat (AXr3962_8 c9 x)):=
           AXr3962_1 B c9;
         let c40:
           ∀ (x:String),
             @LT.lt Nat instLTNat (AXr3962_8 c14 x) B→
               @Eq (Option Nat) (AXr3962_4 B (AXr3962_10 x) c14)
                 (@Option.some Nat (AXr3962_8 c14 x)):=
           AXr3962_1 B c14;
         let c41:AXr3962_13:=c8 (AXr3962_8 σ "rat.s");
         let c42:String→ Nat:=AXr3962_8 c41;
         let c43:Nat:=c42 "vec.i";
         let c44:Nat:=c42 "rat.n";
         let c45:AXr3962_13:=AXr3962_3 c41 c10 c43 c44;
         let c46:String→ Nat:=AXr3962_8 c45;
         let c47:Nat:=c46 "vec.i";
         let c48:Nat:=c46 "rat.d";
         let c49:AXr3962_13:=AXr3962_3 c45 c15 c47 c48;
         let c50:Nat:=c24 (AXr3962_6 (AXr3962_10 "rat.s"));
         let c51:Nat:=c23 c50;
         let c52:
           ∀ (x:String),
             @LT.lt Nat instLTNat (AXr3962_8 c41 x) B→
               @Eq (Option Nat) (AXr3962_4 B (AXr3962_10 x) c41)
                 (@Option.some Nat (AXr3962_8 c41 x)):=
           AXr3962_1 B c41;
         let c53:
           ∀ (x:String),
             @LT.lt Nat instLTNat (AXr3962_8 c45 x) B→
               @Eq (Option Nat) (AXr3962_4 B (AXr3962_10 x) c45)
                 (@Option.some Nat (AXr3962_8 c45 x)):=
           AXr3962_1 B c45;
         @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists AXr3962_13 c4) (Classical.em c0)
           (fun (hcase:c0) =>
             c5 c19
               (@And.intro
                 (AXr3962_7 B (AXr3962_0 a) σ c19
                   (@OfNat.ofNat Nat (nat_lit 13) (instOfNatNat (nat_lit 13))))
                 (c3 c19)
                 (Lax808846Proofs.Reasoning.RunStep.mono B (AXr3962_0 a) σ c19
                   (c20 c26 c29) (@OfNat.ofNat Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                   (c35 c9 c19 c26 c29
                     (Lax808846Proofs.Reasoning.RunStep.ite_true B c22 c31 c32 σ c9 c25
                       (Lax808846Proofs.Reasoning.RunStep.cond_eq_true B σ (AXr3962_10 "rat.n")
                         (AXr3962_9 (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                         (AXr3962_8 σ "rat.n") (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                         (AXr3962_1 B σ "rat.n" hnB) c36 hcase)
                       (c37 (AXr3962_9 (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                         (AXr3962_8 σ "vec.i") (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                         (AXr3962_1 B σ "vec.i"
                           (?nAX_g3962_0_0_1))
                         c36
                         (?nAX_g3962_0_0_2)))
                     (c38 c9 c14 c19 c27 c28
                       (AXr3962_2 B c9 c10 (AXr3962_10 "vec.i")
                         (AXr3962_10 "rat.n") c12 c13
                         (c39 "vec.i"
                           (?nAX_g3962_0_0_3))
                         (c39 "rat.n"
                           (?nAX_g3962_0_0_4))
                         (?nAX_g3962_0_0_5))
                       (AXr3962_2 B c14 c15 (AXr3962_10 "vec.i")
                         (AXr3962_10 "rat.d") c17 c18
                         (c40 "vec.i"
                           (?nAX_g3962_0_0_6))
                         (c40 "rat.d"
                           (?nAX_g3962_0_0_7))
                         (?nAX_g3962_0_0_8))))
                   (?nAX_g3962_0_0_9))
                 ?_))
           fun (hcase:c1) =>
           c5 c49
             (@And.intro
               (AXr3962_7 B (AXr3962_0 a) σ c49
                 (@OfNat.ofNat Nat (nat_lit 13) (instOfNatNat (nat_lit 13))))
               (c3 c49)
               (Lax808846Proofs.Reasoning.RunStep.mono B (AXr3962_0 a) σ c49
                 (c20 c51 c29) (@OfNat.ofNat Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                 (c35 c41 c49 c51 c29
                   (Lax808846Proofs.Reasoning.RunStep.ite_false B c22 c31 c32 σ c41 c50
                     (Lax808846Proofs.Reasoning.RunStep.cond_eq_false B σ (AXr3962_10 "rat.n")
                       (AXr3962_9 (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                       (AXr3962_8 σ "rat.n") (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                       (AXr3962_1 B σ "rat.n" hnB) c36 hcase)
                     (c37 (AXr3962_10 "rat.s") (AXr3962_8 σ "vec.i")
                       (AXr3962_8 σ "rat.s")
                       (AXr3962_1 B σ "vec.i"
                         (?nAX_g3962_0_0_10))
                       (AXr3962_1 B σ "rat.s" hsB)
                       (?nAX_g3962_0_0_11)))
                   (c38 c41 c45 c49 c27 c28
                     (AXr3962_2 B c41 c10 (AXr3962_10 "vec.i")
                       (AXr3962_10 "rat.n") c43 c44
                       (c52 "vec.i"
                         (?nAX_g3962_0_0_12))
                       (c52 "rat.n"
                         (?nAX_g3962_0_0_13))
                       (?nAX_g3962_0_0_14))
                     (AXr3962_2 B c45 c15 (AXr3962_10 "vec.i")
                       (AXr3962_10 "rat.d") c47 c48
                       (c53 "vec.i"
                         (?nAX_g3962_0_0_15))
                       (c53 "rat.d"
                         (?nAX_g3962_0_0_16))
                       (?nAX_g3962_0_0_17))))
                 (?nAX_g3962_0_0_18))
               ?_)
      all_goals try dsimp +zetaDelta at *
      try case nAX_g3962_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3962_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3962_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3962_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3962_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3962_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3962_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3962_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3962_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3962_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3962_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3962_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3962_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3962_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3962_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3962_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3962_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3962_0_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3962_0_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all
     )
   | (expose_names;
       refine
           let c0:Prop:=
             @Eq Nat (AXr3962_8 σ "rat.n") (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)));
           let c1:Prop:=Not c0;
           let c2:AXr3962_13→ Prop:=Lax109476Proofs.RamRationalArrays.Represents a (@List.set Rat qs i q);
           let c3:AXr3962_13→ Prop:=(fun (x τ:AXr3962_13) => c2 τ) σ;
           let c4:AXr3962_13→ Prop:=fun (σ':AXr3962_13) =>
             And
               (AXr3962_7 B (AXr3962_0 a) σ σ'
                 (@OfNat.ofNat Nat (nat_lit 13) (instOfNatNat (nat_lit 13))))
               (c3 σ');
           let c5:∀ (w:AXr3962_13),c4 w→ @Exists AXr3962_13 c4:=
             @Exists.intro AXr3962_13 c4;
           let c6:String→ String:=
             @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a;
           let c7:String:=c6 ".s";
           let c8:Nat→ AXr3962_13:=
             AXr3962_3 σ c7 (AXr3962_8 σ "vec.i");
           let c9:AXr3962_13:=c8 (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)));
           let c10:String:=c6 ".n";
           let c11:String→ Nat:=AXr3962_8 c9;
           let c12:Nat:=c11 "vec.i";
           let c13:Nat:=c11 "rat.n";
           let c14:AXr3962_13:=AXr3962_3 c9 c10 c12 c13;
           let c15:String:=c6 ".d";
           let c16:String→ Nat:=AXr3962_8 c14;
           let c17:Nat:=c16 "vec.i";
           let c18:Nat:=c16 "rat.d";
           let c19:AXr3962_13:=AXr3962_3 c14 c15 c17 c18;
           let c20:Nat→ Nat→ Nat:= @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat);
           let c21:Nat→ Nat:=c20 (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)));
           let c22:Lax808846Proofs.Imp.Cond:=
             Lax808846Proofs.Imp.Cond.eq (AXr3962_10 "rat.n")
               (AXr3962_9 (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))));
           let c23:Nat→ Nat:=c20 (c21 (Lax808846Proofs.Imp.Cond.size c22));
           let c24:Nat→ Nat:=c20 (c21 (AXr3962_6 (AXr3962_10 "vec.i")));
           let c25:Nat:=
             c24
               (AXr3962_6
                 (AXr3962_9 (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))));
           let c26:Nat:=c23 c25;
           let c27:Nat:=c24 (AXr3962_6 (AXr3962_10 "rat.n"));
           let c28:Nat:=c24 (AXr3962_6 (AXr3962_10 "rat.d"));
           let c29:Nat:=c20 c27 c28;
           let c30:Lax808846Proofs.Imp.Expr→ AXr3962_12:=
             AXr3962_5 c7 (AXr3962_10 "vec.i");
           let c31:AXr3962_12:=
             c30 (AXr3962_9 (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))));
           let c32:AXr3962_12:=c30 (AXr3962_10 "rat.s");
           let c33:AXr3962_12:=
             AXr3962_5 c10 (AXr3962_10 "vec.i") (AXr3962_10 "rat.n");
           let c34:AXr3962_12:=
             AXr3962_5 c15 (AXr3962_10 "vec.i") (AXr3962_10 "rat.d");
           let c35:
             ∀ (σ' σ'':AXr3962_13) (K K':Nat),
               AXr3962_7 B (Lax808846Proofs.Imp.Com.ite c22 c31 c32) σ σ' K→
                 AXr3962_7 B (AXr3962_11 c33 c34) σ' σ'' K'→
                   AXr3962_7 B
                     (AXr3962_11 (Lax808846Proofs.Imp.Com.ite c22 c31 c32)
                       (AXr3962_11 c33 c34))
                     σ σ'' (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) K K'):=
             Lax808846Proofs.Reasoning.RunStep.seq B (Lax808846Proofs.Imp.Com.ite c22 c31 c32)
               (AXr3962_11 c33 c34) σ;
           let c36:
             @Eq (Option Nat)
               (AXr3962_4 B
                 (AXr3962_9 (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) σ)
               (@Option.some Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))):=
             Lax808846Proofs.Reasoning.RunStep.eval_lit B (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) σ
               (?nAX_g3962_0_1_0);
           let c37:
             ∀ (e:Lax808846Proofs.Imp.Expr) (idx v:Nat),
               @Eq (Option Nat) (AXr3962_4 B (AXr3962_10 "vec.i") σ)
                   (@Option.some Nat idx)→
                 @Eq (Option Nat) (AXr3962_4 B e σ) (@Option.some Nat v)→
                   @LT.lt Nat instLTNat idx (@List.length Nat (Lax808846Proofs.Imp.Env.arrs σ c7))→
                     AXr3962_7 B
                       (AXr3962_5 c7 (AXr3962_10 "vec.i") e) σ
                       (AXr3962_3 σ c7 idx v)
                       (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                         (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                           (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                           (AXr3962_6 (AXr3962_10 "vec.i")))
                         (AXr3962_6 e)):=
             AXr3962_2 B σ c7 (AXr3962_10 "vec.i");
           let c38:
             ∀ (σ σ' σ'':AXr3962_13) (K K':Nat),
               AXr3962_7 B c33 σ σ' K→
                 AXr3962_7 B c34 σ' σ'' K'→
                   AXr3962_7 B (AXr3962_11 c33 c34) σ σ''
                     (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) K K'):=
             Lax808846Proofs.Reasoning.RunStep.seq B c33 c34;
           let c39:
             ∀ (x:String),
               @LT.lt Nat instLTNat (AXr3962_8 c9 x) B→
                 @Eq (Option Nat) (AXr3962_4 B (AXr3962_10 x) c9)
                   (@Option.some Nat (AXr3962_8 c9 x)):=
             AXr3962_1 B c9;
           let c40:
             ∀ (x:String),
               @LT.lt Nat instLTNat (AXr3962_8 c14 x) B→
                 @Eq (Option Nat) (AXr3962_4 B (AXr3962_10 x) c14)
                   (@Option.some Nat (AXr3962_8 c14 x)):=
             AXr3962_1 B c14;
           let c41:AXr3962_13:=c8 (AXr3962_8 σ "rat.s");
           let c42:String→ Nat:=AXr3962_8 c41;
           let c43:Nat:=c42 "vec.i";
           let c44:Nat:=c42 "rat.n";
           let c45:AXr3962_13:=AXr3962_3 c41 c10 c43 c44;
           let c46:String→ Nat:=AXr3962_8 c45;
           let c47:Nat:=c46 "vec.i";
           let c48:Nat:=c46 "rat.d";
           let c49:AXr3962_13:=AXr3962_3 c45 c15 c47 c48;
           let c50:Nat:=c24 (AXr3962_6 (AXr3962_10 "rat.s"));
           let c51:Nat:=c23 c50;
           let c52:
             ∀ (x:String),
               @LT.lt Nat instLTNat (AXr3962_8 c41 x) B→
                 @Eq (Option Nat) (AXr3962_4 B (AXr3962_10 x) c41)
                   (@Option.some Nat (AXr3962_8 c41 x)):=
             AXr3962_1 B c41;
           let c53:
             ∀ (x:String),
               @LT.lt Nat instLTNat (AXr3962_8 c45 x) B→
                 @Eq (Option Nat) (AXr3962_4 B (AXr3962_10 x) c45)
                   (@Option.some Nat (AXr3962_8 c45 x)):=
             AXr3962_1 B c45;
           @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists AXr3962_13 c4) (Classical.em c0)
             (fun (hcase:c0) =>
               c5 c19
                 (@And.intro
                   (AXr3962_7 B (AXr3962_0 a) σ c19
                     (@OfNat.ofNat Nat (nat_lit 13) (instOfNatNat (nat_lit 13))))
                   (c3 c19)
                   (Lax808846Proofs.Reasoning.RunStep.mono B (AXr3962_0 a) σ c19
                     (c20 c26 c29) (@OfNat.ofNat Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                     (c35 c9 c19 c26 c29
                       (Lax808846Proofs.Reasoning.RunStep.ite_true B c22 c31 c32 σ c9 c25
                         (Lax808846Proofs.Reasoning.RunStep.cond_eq_true B σ (AXr3962_10 "rat.n")
                           (AXr3962_9 (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                           (AXr3962_8 σ "rat.n") (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                           (AXr3962_1 B σ "rat.n" hnB) c36 hcase)
                         (c37 (AXr3962_9 (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                           (AXr3962_8 σ "vec.i") (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                           (AXr3962_1 B σ "vec.i"
                             (?nAX_g3962_0_1_1))
                           c36
                           (?nAX_g3962_0_1_2)))
                       (c38 c9 c14 c19 c27 c28
                         (AXr3962_2 B c9 c10 (AXr3962_10 "vec.i")
                           (AXr3962_10 "rat.n") c12 c13
                           (c39 "vec.i"
                             (?nAX_g3962_0_1_3))
                           (c39 "rat.n"
                             (?nAX_g3962_0_1_4))
                           (?nAX_g3962_0_1_5))
                         (AXr3962_2 B c14 c15 (AXr3962_10 "vec.i")
                           (AXr3962_10 "rat.d") c17 c18
                           (c40 "vec.i"
                             (?nAX_g3962_0_1_6))
                           (c40 "rat.d"
                             (?nAX_g3962_0_1_7))
                           (?nAX_g3962_0_1_8))))
                     (?nAX_g3962_0_1_9))
                   ?_))
             fun (hcase:c1) =>
             c5 c49
               (@And.intro
                 (AXr3962_7 B (AXr3962_0 a) σ c49
                   (@OfNat.ofNat Nat (nat_lit 13) (instOfNatNat (nat_lit 13))))
                 (c3 c49)
                 (Lax808846Proofs.Reasoning.RunStep.mono B (AXr3962_0 a) σ c49
                   (c20 c51 c29) (@OfNat.ofNat Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                   (c35 c41 c49 c51 c29
                     (Lax808846Proofs.Reasoning.RunStep.ite_false B c22 c31 c32 σ c41 c50
                       (Lax808846Proofs.Reasoning.RunStep.cond_eq_false B σ (AXr3962_10 "rat.n")
                         (AXr3962_9 (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                         (AXr3962_8 σ "rat.n") (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                         (AXr3962_1 B σ "rat.n" hnB) c36 hcase)
                       (c37 (AXr3962_10 "rat.s") (AXr3962_8 σ "vec.i")
                         (AXr3962_8 σ "rat.s")
                         (AXr3962_1 B σ "vec.i"
                           (?nAX_g3962_0_1_10))
                         (AXr3962_1 B σ "rat.s" hsB)
                         (?nAX_g3962_0_1_11)))
                     (c38 c41 c45 c49 c27 c28
                       (AXr3962_2 B c41 c10 (AXr3962_10 "vec.i")
                         (AXr3962_10 "rat.n") c43 c44
                         (c52 "vec.i"
                           (?nAX_g3962_0_1_12))
                         (c52 "rat.n"
                           (?nAX_g3962_0_1_13))
                         (?nAX_g3962_0_1_14))
                       (AXr3962_2 B c45 c15 (AXr3962_10 "vec.i")
                         (AXr3962_10 "rat.d") c47 c48
                         (c53 "vec.i"
                           (?nAX_g3962_0_1_15))
                         (c53 "rat.d"
                           (?nAX_g3962_0_1_16))
                         (?nAX_g3962_0_1_17))))
                   (?nAX_g3962_0_1_18))
                 ?_) <;> try dsimp +zetaDelta at *
      all_goals try dsimp +zetaDelta at *
      try case nAX_g3962_0_1_0 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3962_0_1_1 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3962_0_1_2 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3962_0_1_3 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3962_0_1_4 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3962_0_1_5 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3962_0_1_6 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3962_0_1_7 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3962_0_1_8 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3962_0_1_9 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3962_0_1_10 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3962_0_1_11 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3962_0_1_12 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3962_0_1_13 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3962_0_1_14 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3962_0_1_15 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3962_0_1_16 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3962_0_1_17 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g3962_0_1_18 => solve | omega | (simp <;> omega) | assumption | simp_all
     )
  )
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

def suffixes:List String:= [".s", ".n", ".d"]
def Disjoint (a b:String):Prop:= ∀ s∈ suffixes, ∀ t∈ suffixes,a ++ s ≠ b ++ t

theorem disjoint_not_mem (a b s:String) (hab:Disjoint a b) (hs:s∈ suffixes):
    a ++ s∉ [b ++ ".s",b ++ ".n",b ++ ".d"]:=by
  intro h
  simp at h
  rcases h with h | h | h
  · exact hab s hs ".s" (by simp [suffixes]) h
  · exact hab s hs ".n" (by simp [suffixes]) h
  · exact hab s hs ".d" (by simp [suffixes]) h

def loopFields:List String:= ["copy.i", "vec.i", "vec.n"]

noncomputable abbrev _root_.AXr4081_0:= @Lax109476Proofs.RamRational.FractionOutput
noncomputable abbrev _root_.AXr4081_1:= @Lax808846Proofs.Reasoning.RunStep.eval_var
noncomputable abbrev _root_.AXr4081_2:= @Lax808846Proofs.Reasoning.RunStep.assign
noncomputable abbrev _root_.AXr4081_3:= @Lax109476Proofs.RamCopy.leftToResult
noncomputable abbrev _root_.AXr4081_4:= @Lax808846Proofs.Imp.Com.assign
noncomputable abbrev _root_.AXr4081_5:= @Lax808846Proofs.Imp.Env.setVar
noncomputable abbrev _root_.AXr4081_6:= @Lax808846Proofs.Imp.Expr.size
noncomputable abbrev _root_.AXr4081_7:= @Lax808846Proofs.Imp.Env.vars
noncomputable abbrev _root_.AXr4081_8:= @Lax808846Proofs.Imp.Expr.var
noncomputable abbrev _root_.AXr4081_9:= @Lax808846Proofs.Imp.Env
theorem leftToResult_spec (B:ℕ) (q:ℚ) (h1:1 < B)
    (hn:q.num.natAbs < B) (hd:q.den < B):
    Spec B (LeftOutput q) leftToResult (fun _ τ => FractionOutput q τ) 6:=by
  rintro σ ⟨hσs,hσn,hσd⟩
  have hs:σ.vars "left.s" < B:=hσs ▸ (rationalSign_le_one q).trans_lt h1
  (first
   | (expose_names;
       refine
         let c0:Nat:=
           AXr4081_7 (AXr4081_5 σ "rat.s" (AXr4081_7 σ "left.s"))
             "left.n";
         let c1:AXr4081_9:=
           AXr4081_5
             (AXr4081_5 σ "rat.s" (AXr4081_7 σ "left.s")) "rat.n" c0;
         let c2:Nat:=AXr4081_7 c1 "left.d";
         let c3:AXr4081_9:=AXr4081_5 c1 "rat.d" c2;
         let c4:Nat→ Nat→ Nat:= @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat);
         let c5:Nat→ Nat:=c4 (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)));
         let c6:Nat:=c5 (AXr4081_6 (AXr4081_8 "left.s"));
         let c7:Nat:=c5 (AXr4081_6 (AXr4081_8 "left.n"));
         let c8:Nat:=c5 (AXr4081_6 (AXr4081_8 "left.d"));
         let c9:Nat:=c4 c7 c8;
         @Exists.intro AXr4081_9
           (fun (σ':AXr4081_9) =>
             And
               (Lax808846Proofs.Reasoning.Run B AXr4081_3 σ σ'
                 (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
               ((fun (x τ:AXr4081_9) => AXr4081_0 q τ) σ σ'))
           c3
           (@And.intro
             (Lax808846Proofs.Reasoning.Run B AXr4081_3 σ c3
               (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
             ((fun (x τ:AXr4081_9) => AXr4081_0 q τ) σ c3)
             (Lax808846Proofs.Reasoning.RunStep.mono B AXr4081_3 σ c3 (c4 c6 c9)
               (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
               (Lax808846Proofs.Reasoning.RunStep.seq B
                 (AXr4081_4 "rat.s" (AXr4081_8 "left.s"))
                 (Lax808846Proofs.Imp.Com.seq
                   (AXr4081_4 "rat.n" (AXr4081_8 "left.n"))
                   (AXr4081_4 "rat.d" (AXr4081_8 "left.d")))
                 σ (AXr4081_5 σ "rat.s" (AXr4081_7 σ "left.s")) c3 c6 c9
                 (AXr4081_2 B σ "rat.s" (AXr4081_8 "left.s")
                   (AXr4081_7 σ "left.s") (AXr4081_1 B σ "left.s" hs))
                 (Lax808846Proofs.Reasoning.RunStep.seq B
                   (AXr4081_4 "rat.n" (AXr4081_8 "left.n"))
                   (AXr4081_4 "rat.d" (AXr4081_8 "left.d"))
                   (AXr4081_5 σ "rat.s" (AXr4081_7 σ "left.s")) c1 c3 c7 c8
                   (AXr4081_2 B
                     (AXr4081_5 σ "rat.s" (AXr4081_7 σ "left.s")) "rat.n"
                     (AXr4081_8 "left.n") c0
                     (AXr4081_1 B
                       (AXr4081_5 σ "rat.s" (AXr4081_7 σ "left.s")) "left.n"
                       (?nAX_g4081_0_0_0)))
                   (AXr4081_2 B c1 "rat.d" (AXr4081_8 "left.d") c2
                     (AXr4081_1 B c1 "left.d"
                       (?nAX_g4081_0_0_1)))))
               (?nAX_g4081_0_0_2))
             ?_)
      all_goals try dsimp +zetaDelta at *
      try case nAX_g4081_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g4081_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g4081_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all
     )
   | (expose_names;
       refine
           let c0:Nat:=
             AXr4081_7
               (AXr4081_5 σ "rat.s" (AXr4081_7 σ "left.s")) "left.n";
           let c1:AXr4081_9:=
             AXr4081_5
               (AXr4081_5 σ "rat.s" (AXr4081_7 σ "left.s")) "rat.n" c0;
           let c2:Nat:=AXr4081_7 c1 "left.d";
           let c3:AXr4081_9:=AXr4081_5 c1 "rat.d" c2;
           let c4:Nat→ Nat→ Nat:= @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat);
           let c5:Nat→ Nat:=c4 (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)));
           let c6:Nat:=c5 (AXr4081_6 (AXr4081_8 "left.s"));
           let c7:Nat:=c5 (AXr4081_6 (AXr4081_8 "left.n"));
           let c8:Nat:=c5 (AXr4081_6 (AXr4081_8 "left.d"));
           let c9:Nat:=c4 c7 c8;
           @Exists.intro AXr4081_9
             (fun (σ':AXr4081_9) =>
               And
                 (Lax808846Proofs.Reasoning.Run B AXr4081_3 σ σ'
                   (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                 ((fun (x τ:AXr4081_9) => AXr4081_0 q τ) σ σ'))
             c3
             (@And.intro
               (Lax808846Proofs.Reasoning.Run B AXr4081_3 σ c3
                 (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
               ((fun (x τ:AXr4081_9) => AXr4081_0 q τ) σ c3)
               (Lax808846Proofs.Reasoning.RunStep.mono B AXr4081_3 σ c3 (c4 c6 c9)
                 (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                 (Lax808846Proofs.Reasoning.RunStep.seq B
                   (AXr4081_4 "rat.s" (AXr4081_8 "left.s"))
                   (Lax808846Proofs.Imp.Com.seq
                     (AXr4081_4 "rat.n" (AXr4081_8 "left.n"))
                     (AXr4081_4 "rat.d" (AXr4081_8 "left.d")))
                   σ (AXr4081_5 σ "rat.s" (AXr4081_7 σ "left.s")) c3 c6 c9
                   (AXr4081_2 B σ "rat.s" (AXr4081_8 "left.s")
                     (AXr4081_7 σ "left.s") (AXr4081_1 B σ "left.s" hs))
                   (Lax808846Proofs.Reasoning.RunStep.seq B
                     (AXr4081_4 "rat.n" (AXr4081_8 "left.n"))
                     (AXr4081_4 "rat.d" (AXr4081_8 "left.d"))
                     (AXr4081_5 σ "rat.s" (AXr4081_7 σ "left.s")) c1 c3 c7 c8
                     (AXr4081_2 B
                       (AXr4081_5 σ "rat.s" (AXr4081_7 σ "left.s")) "rat.n"
                       (AXr4081_8 "left.n") c0
                       (AXr4081_1 B
                         (AXr4081_5 σ "rat.s" (AXr4081_7 σ "left.s")) "left.n"
                         (?nAX_g4081_0_1_0)))
                     (AXr4081_2 B c1 "rat.d" (AXr4081_8 "left.d") c2
                       (AXr4081_1 B c1 "left.d"
                         (?nAX_g4081_0_1_1)))))
                 (?nAX_g4081_0_1_2))
               ?_) <;> try dsimp +zetaDelta at *
      all_goals try dsimp +zetaDelta at *
      try case nAX_g4081_0_1_0 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g4081_0_1_1 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g4081_0_1_2 => solve | omega | (simp <;> omega) | assumption | simp_all
     )
  )
  all_goals simp_all [FractionOutput,canonical_fractionValue,rationalSign_le_one]

set_option maxHeartbeats 500000 in
noncomputable abbrev _root_.AXr4083_0:= @Lax109476Proofs.RamRationalArrays.storeReduced
noncomputable abbrev _root_.AXr4083_1:= @Lax109476Proofs.RamRationalArrays.Represents
noncomputable abbrev _root_.AXr4083_2:= @Lax109476Proofs.RamRationalArrays.loadLeft
noncomputable abbrev _root_.AXr4083_3:= @Lax109476Proofs.RamCopy.copyCoordinate
noncomputable abbrev _root_.AXr4083_4:= @Lax808846Proofs.Reasoning.RunStep.seq
noncomputable abbrev _root_.AXr4083_5:= @Lax808846Proofs.Reasoning.RunStep.use
noncomputable abbrev _root_.AXr4083_6:= @Lax109476Proofs.RamCopy.leftToResult
noncomputable abbrev _root_.AXr4083_7:= @Lax109476Proofs.RamFrame.FieldsAgree
noncomputable abbrev _root_.AXr4083_8:= @Lax109476Proofs.RamCopy.loopFields
noncomputable abbrev _root_.AXr4083_9:= @Lax808846Proofs.Imp.Env.setVar
noncomputable abbrev _root_.AXr4083_10:= @Lax808846Proofs.Imp.Com.warrs
noncomputable abbrev _root_.AXr4083_11:= @Lax808846Proofs.Reasoning.Run
noncomputable abbrev _root_.AXr4083_12:= @Lax808846Proofs.Imp.Env.arrs
noncomputable abbrev _root_.AXr4083_13:= @Lax808846Proofs.Imp.Env.vars
noncomputable abbrev _root_.AXr4083_14:= @Lax808846Proofs.Imp.Env
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
  (first
   | (expose_names;
       refine
         let c0:AXr4083_14→ Nat→ Prop:=
           AXr4083_11 B (AXr4083_2 a)
             (AXr4083_9 σ "vec.i" (AXr4083_13 σ "copy.i"));
         let c1:Rat:=
           @GetElem.getElem (List Rat) Nat Rat
             (fun (as:List Rat) (i:Nat) => @LT.lt Nat instLTNat i (@List.length Rat as))
             (@List.instGetElemNatLtLength Rat) xs i hi;
         let c2:AXr4083_14→ Prop:=Lax109476Proofs.RamRationalArrays.LeftOutput c1;
         let c3:AXr4083_14→ Prop:=
           AXr4083_7 AXr4083_8
             (AXr4083_9 σ "vec.i" (AXr4083_13 σ "copy.i"));
         let c4:String→ List Nat:=
           AXr4083_12 (AXr4083_9 σ "vec.i" (AXr4083_13 σ "copy.i"));
         let c5:AXr4083_14→ Prop:=fun (σ':AXr4083_14) =>
           And (c0 σ' (@OfNat.ofNat Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
             (And (c2 σ') (And (c3 σ') (@Eq (String→ List Nat) (AXr4083_12 σ') c4)));
         let c6:AXr4083_14→ Prop:=AXr4083_1 b (@List.set Rat ys i c1);
         let c7:AXr4083_14→ Prop:=
           (fun (x τ:AXr4083_14) => And (c6 τ) (AXr4083_1 a xs τ)) σ;
         let c8:AXr4083_14→ Prop:=fun (σ':AXr4083_14) =>
           And
             (AXr4083_11 B (AXr4083_3 a b) σ σ'
               (@OfNat.ofNat Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
             (c7 σ');
         let c9:Prop:= @Exists AXr4083_14 c8;
         let c10:AXr4083_14→ Prop:=Lax109476Proofs.RamRational.FractionOutput c1;
         let c11:Nat→ Nat→ Nat:= @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat);
         let c12:Nat:=
           c11 (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
             (Lax808846Proofs.Imp.Expr.size (Lax808846Proofs.Imp.Expr.var "copy.i"));
         let c13:Nat:=
           c11 (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
             (@OfNat.ofNat Nat (nat_lit 13) (instOfNatNat (nat_lit 13)));
         let c14:Nat:=c11 (@OfNat.ofNat Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) c13;
         @Exists.casesOn AXr4083_14 c5 (fun (x:@Exists AXr4083_14 c5) => c9)
           (AXr4083_5 B
             (fun (σ:AXr4083_14) =>
               And (AXr4083_1 a xs σ)
                 (@Eq Nat (AXr4083_13 σ "vec.i") i))
             (AXr4083_2 a)
             (fun (σ τ:AXr4083_14) =>
               And (c2 τ)
                 (And (AXr4083_7 AXr4083_8 σ τ)
                   (@Eq (String→ List Nat) (AXr4083_12 τ) (AXr4083_12 σ))))
             (@OfNat.ofNat Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) hload
             (AXr4083_9 σ "vec.i" (AXr4083_13 σ "copy.i")) ?_)
           fun (w:AXr4083_14)
             (h:
               And (c0 w (@OfNat.ofNat Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
                 (And (c2 w) (And (c3 w) (@Eq (String→ List Nat) (AXr4083_12 w) c4)))) =>
           let c0:Prop:=c0 w (@OfNat.ofNat Nat (nat_lit 9) (instOfNatNat (nat_lit 9)));
           let c1:Prop:=And (c2 w) (And (c3 w) (@Eq (String→ List Nat) (AXr4083_12 w) c4));
           let c2_1:AXr4083_14→ Prop:=fun (σ':AXr4083_14) =>
             And
               (AXr4083_11 B AXr4083_6 w σ'
                 (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
               (And (c10 σ')
                 (And (AXr4083_7 AXr4083_8 w σ')
                   (@Eq (String→ List Nat) (AXr4083_12 σ') (AXr4083_12 w))));
           @And.casesOn c0 c1 (fun (x:And c0 c1) => c9) h fun (left:c0) (right:c1) =>
             @Exists.casesOn AXr4083_14 c2_1 (fun (x:@Exists AXr4083_14 c2_1) => c9)
               (AXr4083_5 B c2 AXr4083_6
                 (fun (σ τ:AXr4083_14) =>
                   And (c10 τ)
                     (And (AXr4083_7 AXr4083_8 σ τ)
                       (@Eq (String→ List Nat) (AXr4083_12 τ) (AXr4083_12 σ))))
                 (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) hresult w ?_)
               fun (w_1:AXr4083_14)
                 (h:
                   And
                     (AXr4083_11 B AXr4083_6 w w_1
                       (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                     (And (c10 w_1)
                       (And (AXr4083_7 AXr4083_8 w w_1)
                         (@Eq (String→ List Nat) (AXr4083_12 w_1) (AXr4083_12 w))))) =>
               let c0:Prop:=
                 AXr4083_11 B AXr4083_6 w w_1
                   (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6)));
               let c1:Prop:=
                 And (c10 w_1)
                   (And (AXr4083_7 AXr4083_8 w w_1)
                     (@Eq (String→ List Nat) (AXr4083_12 w_1) (AXr4083_12 w)));
               let c2:AXr4083_14→ Prop:=fun (σ':AXr4083_14) =>
                 And
                   (AXr4083_11 B (AXr4083_0 b) w_1 σ'
                     (@OfNat.ofNat Nat (nat_lit 13) (instOfNatNat (nat_lit 13))))
                   (And (c6 σ')
                     (And (AXr4083_7 AXr4083_8 w_1 σ')
                       (∀ a∉ AXr4083_10 (AXr4083_0 b),
                         @Eq (List Nat) (AXr4083_12 σ' a) (AXr4083_12 w_1 a))));
               @And.casesOn c0 c1 (fun (x:And c0 c1) => c9) h fun (left_1:c0) (right:c1) =>
                 @Exists.casesOn AXr4083_14 c2 (fun (x:@Exists AXr4083_14 c2) => c9)
                   (AXr4083_5 B
                     (fun (σ:AXr4083_14) =>
                       And (AXr4083_1 b ys σ)
                         (And (@Eq Nat (AXr4083_13 σ "vec.i") i) (c10 σ)))
                     (AXr4083_0 b)
                     (fun (σ τ:AXr4083_14) =>
                       And (c6 τ)
                         (And (AXr4083_7 AXr4083_8 σ τ)
                           (∀ a∉ AXr4083_10 (AXr4083_0 b),
                             @Eq (List Nat) (AXr4083_12 τ a) (AXr4083_12 σ a))))
                     (@OfNat.ofNat Nat (nat_lit 13) (instOfNatNat (nat_lit 13))) hstore w_1 ?_)
                   fun (w_2:AXr4083_14)
                     (h:
                       And
                         (AXr4083_11 B (AXr4083_0 b) w_1 w_2
                           (@OfNat.ofNat Nat (nat_lit 13) (instOfNatNat (nat_lit 13))))
                         (And (c6 w_2)
                           (And (AXr4083_7 AXr4083_8 w_1 w_2)
                             (∀ a∉ AXr4083_10 (AXr4083_0 b),
                               @Eq (List Nat) (AXr4083_12 w_2 a)
                                 (AXr4083_12 w_1 a))))) =>
                   let c0:Prop:=
                     AXr4083_11 B (AXr4083_0 b) w_1 w_2
                       (@OfNat.ofNat Nat (nat_lit 13) (instOfNatNat (nat_lit 13)));
                   let c1:Prop:=
                     And (c6 w_2)
                       (And (AXr4083_7 AXr4083_8 w_1 w_2)
                         (∀ a∉ AXr4083_10 (AXr4083_0 b),
                           @Eq (List Nat) (AXr4083_12 w_2 a) (AXr4083_12 w_1 a)));
                   @And.casesOn c0 c1 (fun (x:And c0 c1) => c9) h fun (left_2:c0) (right:c1) =>
                     @Exists.intro AXr4083_14 c8 w_2
                       (@And.intro
                         (AXr4083_11 B (AXr4083_3 a b) σ w_2
                           (@OfNat.ofNat Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
                         (c7 w_2)
                         (Lax808846Proofs.Reasoning.RunStep.mono B (AXr4083_3 a b) σ w_2
                           (c11 c12 c14) (@OfNat.ofNat Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))
                           (AXr4083_4 B
                             (Lax808846Proofs.Imp.Com.assign "vec.i" (Lax808846Proofs.Imp.Expr.var "copy.i"))
                             (Lax808846Proofs.Imp.Com.seq (AXr4083_2 a)
                               (Lax808846Proofs.Imp.Com.seq AXr4083_6
                                 (AXr4083_0 b)))
                             σ (AXr4083_9 σ "vec.i" (AXr4083_13 σ "copy.i")) w_2 c12
                             c14
                             (Lax808846Proofs.Reasoning.RunStep.assign B σ "vec.i" (Lax808846Proofs.Imp.Expr.var "copy.i")
                               (AXr4083_13 σ "copy.i")
                               (Lax808846Proofs.Reasoning.RunStep.eval_var B σ "copy.i"
                                 (?nAX_g4083_0_0_0)))
                             (AXr4083_4 B (AXr4083_2 a)
                               (Lax808846Proofs.Imp.Com.seq AXr4083_6
                                 (AXr4083_0 b))
                               (AXr4083_9 σ "vec.i" (AXr4083_13 σ "copy.i")) w w_2
                               (@OfNat.ofNat Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) c13 left
                               (AXr4083_4 B AXr4083_6
                                 (AXr4083_0 b) w w_1 w_2
                                 (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                                 (@OfNat.ofNat Nat (nat_lit 13) (instOfNatNat (nat_lit 13))) left_1 left_2)))
                           (?nAX_g4083_0_0_1))
                         ?_)
      all_goals try dsimp +zetaDelta at *
      try case nAX_g4083_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g4083_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all
     )
   | (expose_names;
       refine
           let c0:AXr4083_14→ Nat→ Prop:=
             AXr4083_11 B (AXr4083_2 a)
               (AXr4083_9 σ "vec.i" (AXr4083_13 σ "copy.i"));
           let c1:Rat:=
             @GetElem.getElem (List Rat) Nat Rat
               (fun (as:List Rat) (i:Nat) => @LT.lt Nat instLTNat i (@List.length Rat as))
               (@List.instGetElemNatLtLength Rat) xs i hi;
           let c2:AXr4083_14→ Prop:=Lax109476Proofs.RamRationalArrays.LeftOutput c1;
           let c3:AXr4083_14→ Prop:=
             AXr4083_7 AXr4083_8
               (AXr4083_9 σ "vec.i" (AXr4083_13 σ "copy.i"));
           let c4:String→ List Nat:=
             AXr4083_12
               (AXr4083_9 σ "vec.i" (AXr4083_13 σ "copy.i"));
           let c5:AXr4083_14→ Prop:=fun (σ':AXr4083_14) =>
             And (c0 σ' (@OfNat.ofNat Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
               (And (c2 σ') (And (c3 σ') (@Eq (String→ List Nat) (AXr4083_12 σ') c4)));
           let c6:AXr4083_14→ Prop:=AXr4083_1 b (@List.set Rat ys i c1);
           let c7:AXr4083_14→ Prop:=
             (fun (x τ:AXr4083_14) => And (c6 τ) (AXr4083_1 a xs τ)) σ;
           let c8:AXr4083_14→ Prop:=fun (σ':AXr4083_14) =>
             And
               (AXr4083_11 B (AXr4083_3 a b) σ σ'
                 (@OfNat.ofNat Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
               (c7 σ');
           let c9:Prop:= @Exists AXr4083_14 c8;
           let c10:AXr4083_14→ Prop:=Lax109476Proofs.RamRational.FractionOutput c1;
           let c11:Nat→ Nat→ Nat:= @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat);
           let c12:Nat:=
             c11 (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
               (Lax808846Proofs.Imp.Expr.size (Lax808846Proofs.Imp.Expr.var "copy.i"));
           let c13:Nat:=
             c11 (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
               (@OfNat.ofNat Nat (nat_lit 13) (instOfNatNat (nat_lit 13)));
           let c14:Nat:=c11 (@OfNat.ofNat Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) c13;
           @Exists.casesOn AXr4083_14 c5 (fun (x:@Exists AXr4083_14 c5) => c9)
             (AXr4083_5 B
               (fun (σ:AXr4083_14) =>
                 And (AXr4083_1 a xs σ)
                   (@Eq Nat (AXr4083_13 σ "vec.i") i))
               (AXr4083_2 a)
               (fun (σ τ:AXr4083_14) =>
                 And (c2 τ)
                   (And (AXr4083_7 AXr4083_8 σ τ)
                     (@Eq (String→ List Nat) (AXr4083_12 τ) (AXr4083_12 σ))))
               (@OfNat.ofNat Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) hload
               (AXr4083_9 σ "vec.i" (AXr4083_13 σ "copy.i")) ?_)
             fun (w:AXr4083_14)
               (h:
                 And (c0 w (@OfNat.ofNat Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
                   (And (c2 w) (And (c3 w) (@Eq (String→ List Nat) (AXr4083_12 w) c4)))) =>
             let c0:Prop:=c0 w (@OfNat.ofNat Nat (nat_lit 9) (instOfNatNat (nat_lit 9)));
             let c1:Prop:=And (c2 w) (And (c3 w) (@Eq (String→ List Nat) (AXr4083_12 w) c4));
             let c2_1:AXr4083_14→ Prop:=fun (σ':AXr4083_14) =>
               And
                 (AXr4083_11 B AXr4083_6 w σ'
                   (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                 (And (c10 σ')
                   (And (AXr4083_7 AXr4083_8 w σ')
                     (@Eq (String→ List Nat) (AXr4083_12 σ') (AXr4083_12 w))));
             @And.casesOn c0 c1 (fun (x:And c0 c1) => c9) h fun (left:c0) (right:c1) =>
               @Exists.casesOn AXr4083_14 c2_1 (fun (x:@Exists AXr4083_14 c2_1) => c9)
                 (AXr4083_5 B c2 AXr4083_6
                   (fun (σ τ:AXr4083_14) =>
                     And (c10 τ)
                       (And (AXr4083_7 AXr4083_8 σ τ)
                         (@Eq (String→ List Nat) (AXr4083_12 τ) (AXr4083_12 σ))))
                   (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) hresult w ?_)
                 fun (w_1:AXr4083_14)
                   (h:
                     And
                       (AXr4083_11 B AXr4083_6 w w_1
                         (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                       (And (c10 w_1)
                         (And (AXr4083_7 AXr4083_8 w w_1)
                           (@Eq (String→ List Nat) (AXr4083_12 w_1)
                             (AXr4083_12 w))))) =>
                 let c0:Prop:=
                   AXr4083_11 B AXr4083_6 w w_1
                     (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6)));
                 let c1:Prop:=
                   And (c10 w_1)
                     (And (AXr4083_7 AXr4083_8 w w_1)
                       (@Eq (String→ List Nat) (AXr4083_12 w_1) (AXr4083_12 w)));
                 let c2:AXr4083_14→ Prop:=fun (σ':AXr4083_14) =>
                   And
                     (AXr4083_11 B (AXr4083_0 b) w_1 σ'
                       (@OfNat.ofNat Nat (nat_lit 13) (instOfNatNat (nat_lit 13))))
                     (And (c6 σ')
                       (And (AXr4083_7 AXr4083_8 w_1 σ')
                         (∀ a∉ AXr4083_10 (AXr4083_0 b),
                           @Eq (List Nat) (AXr4083_12 σ' a) (AXr4083_12 w_1 a))));
                 @And.casesOn c0 c1 (fun (x:And c0 c1) => c9) h fun (left_1:c0) (right:c1) =>
                   @Exists.casesOn AXr4083_14 c2 (fun (x:@Exists AXr4083_14 c2) => c9)
                     (AXr4083_5 B
                       (fun (σ:AXr4083_14) =>
                         And (AXr4083_1 b ys σ)
                           (And (@Eq Nat (AXr4083_13 σ "vec.i") i) (c10 σ)))
                       (AXr4083_0 b)
                       (fun (σ τ:AXr4083_14) =>
                         And (c6 τ)
                           (And (AXr4083_7 AXr4083_8 σ τ)
                             (∀ a∉ AXr4083_10 (AXr4083_0 b),
                               @Eq (List Nat) (AXr4083_12 τ a) (AXr4083_12 σ a))))
                       (@OfNat.ofNat Nat (nat_lit 13) (instOfNatNat (nat_lit 13))) hstore w_1 ?_)
                     fun (w_2:AXr4083_14)
                       (h:
                         And
                           (AXr4083_11 B (AXr4083_0 b) w_1 w_2
                             (@OfNat.ofNat Nat (nat_lit 13) (instOfNatNat (nat_lit 13))))
                           (And (c6 w_2)
                             (And (AXr4083_7 AXr4083_8 w_1 w_2)
                               (∀ a∉ AXr4083_10 (AXr4083_0 b),
                                 @Eq (List Nat) (AXr4083_12 w_2 a)
                                   (AXr4083_12 w_1 a))))) =>
                     let c0:Prop:=
                       AXr4083_11 B (AXr4083_0 b) w_1 w_2
                         (@OfNat.ofNat Nat (nat_lit 13) (instOfNatNat (nat_lit 13)));
                     let c1:Prop:=
                       And (c6 w_2)
                         (And (AXr4083_7 AXr4083_8 w_1 w_2)
                           (∀ a∉ AXr4083_10 (AXr4083_0 b),
                             @Eq (List Nat) (AXr4083_12 w_2 a) (AXr4083_12 w_1 a)));
                     @And.casesOn c0 c1 (fun (x:And c0 c1) => c9) h fun (left_2:c0) (right:c1) =>
                       @Exists.intro AXr4083_14 c8 w_2
                         (@And.intro
                           (AXr4083_11 B (AXr4083_3 a b) σ w_2
                             (@OfNat.ofNat Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
                           (c7 w_2)
                           (Lax808846Proofs.Reasoning.RunStep.mono B (AXr4083_3 a b) σ w_2
                             (c11 c12 c14) (@OfNat.ofNat Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))
                             (AXr4083_4 B
                               (Lax808846Proofs.Imp.Com.assign "vec.i" (Lax808846Proofs.Imp.Expr.var "copy.i"))
                               (Lax808846Proofs.Imp.Com.seq (AXr4083_2 a)
                                 (Lax808846Proofs.Imp.Com.seq AXr4083_6
                                   (AXr4083_0 b)))
                               σ (AXr4083_9 σ "vec.i" (AXr4083_13 σ "copy.i")) w_2 c12
                               c14
                               (Lax808846Proofs.Reasoning.RunStep.assign B σ "vec.i" (Lax808846Proofs.Imp.Expr.var "copy.i")
                                 (AXr4083_13 σ "copy.i")
                                 (Lax808846Proofs.Reasoning.RunStep.eval_var B σ "copy.i"
                                   (?nAX_g4083_0_1_0)))
                               (AXr4083_4 B (AXr4083_2 a)
                                 (Lax808846Proofs.Imp.Com.seq AXr4083_6
                                   (AXr4083_0 b))
                                 (AXr4083_9 σ "vec.i" (AXr4083_13 σ "copy.i")) w w_2
                                 (@OfNat.ofNat Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) c13 left
                                 (AXr4083_4 B AXr4083_6
                                   (AXr4083_0 b) w w_1 w_2
                                   (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                                   (@OfNat.ofNat Nat (nat_lit 13) (instOfNatNat (nat_lit 13))) left_1 left_2)))
                             (?nAX_g4083_0_1_1))
                           ?_) <;> try dsimp +zetaDelta at *
      all_goals try dsimp +zetaDelta at *
      try case nAX_g4083_0_1_0 => solve | omega | (simp <;> omega) | assumption | simp_all
      try case nAX_g4083_0_1_1 => solve | omega | (simp <;> omega) | assumption | simp_all
     )
  )
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

namespace Lax109476Proofs.WordDecoding

open Lax109476.LinearProgram Lax109476.RationalEncoding

theorem encodeVector_cons (n:ℕ) (q:ℚ) (x:Fin n→ ℚ):
    encodeVector (Fin.cons q x)=encodeRational q ++ encodeVector x:=by
  simp [encodeVector,List.ofFn_succ]

def encodeRows {m n:ℕ} (A:Fin m→ Fin n→ ℚ):List ℕ:=
  (List.ofFn fun i => encodeVector (A i)).flatten

theorem encodeRows_cons {m n:ℕ} (row:Fin n→ ℚ) (rows:Fin m→ Fin n→ ℚ):
    encodeRows (Fin.cons row rows)=encodeVector row ++ encodeRows rows:=by
  simp [encodeRows,List.ofFn_succ]

theorem encodeVector_length (n:ℕ) (x:Fin n→ ℚ):(encodeVector x).length=3 * n:=by
  induction n with
  | zero => simp [encodeVector]
  | succ n ih =>
    rw [← Fin.cons_self_tail x,encodeVector_cons,List.length_append]
    simp only [encodeRational,List.length_cons,List.length_nil]
    rw [ih]
    omega

theorem encodeRows_length (m n:ℕ) (A:Fin m→ Fin n→ ℚ):
    (encodeRows A).length=3 * m * n:=by
  induction m with
  | zero => simp [encodeRows]
  | succ m ih =>
    rw [← Fin.cons_self_tail A,encodeRows_cons,List.length_append,encodeVector_length,ih]
    ring

theorem encodeProgram_rows {m n:ℕ} (P:Program ℚ m n):
    encodeProgram P=m::n::(encodeRows P.A ++ encodeVector P.b ++ encodeVector P.c):=by
  have hrows:(List.ofFn fun i => List.ofFn (P.A i)).flatten.flatMap encodeRational =
      encodeRows P.A:=by
    unfold encodeRows encodeVector
    rw [List.flatten_eq_flatMap,List.flatMap_assoc,List.flatMap_def,List.map_ofFn]
    rfl
  simp only [encodeProgram,hrows]
  rfl

structure PackedProgram where
  m:ℕ
  n:ℕ
  program:Program ℚ m n

end Lax109476Proofs.WordDecoding

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

namespace Lax109476Proofs.WordSolverSize

open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax109476.RationalEncoding EncodingSize

theorem length_le_bitSize (xs:List ℕ):xs.length≤ bitSize xs:=by
  induction xs with
  | nil => rfl
  | cons a xs ih => rw [List.length_cons,bitSize_cons]; omega

end Lax109476Proofs.WordSolverSize

end

section

open scoped BigOperators

namespace Lax109476Proofs.RamSolverInitialization

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamStoredProgram RationalArithmeticBounds EncodingSize IntegerEncoding

theorem cells_bound {m n:ℕ} (P:Program ℚ m n):m * n + m + n≤ bitSize (encodeProgram P):=by
  have hlen:(encodeProgram P).length=2 + 3 * (m * n + m + n):=by
    rw [WordDecoding.encodeProgram_rows]
    simp only [List.length_cons,List.length_append,WordDecoding.encodeRows_length,
      WordDecoding.encodeVector_length,Nat.mul_assoc]
    omega
  have hl:=WordSolverSize.length_le_bitSize (encodeProgram P)
  rw [hlen] at hl
  omega

end Lax109476Proofs.RamSolverInitialization

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

namespace Lax109476Proofs.RamRecoveryThreshold

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamRationalScalars RamEllipsoidStep RationalArithmeticBounds

def sizeBound (m n M:ℕ):ℕ:=
  ((m + (n + n)) + 1) + n + 2 +
    ((((m + (n + n)) + 1) * n) + ((m + (n + n)) + 1) + n) * (4 + 2 * M.size)

def instructionBound (m n M:ℕ):ℕ:=
  142 * (((m + (n + n)) + 1) * n) + 138 * ((m + (n + n)) + 1) + 33 * n + 106 +
    RamStoredFeasibility.instructionBound (sizeBound m n M)

end Lax109476Proofs.RamRecoveryThreshold

end

section

namespace Lax109476Proofs.RamArrayRelabel

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

@[simp] theorem view_setVar (f:String→ String) (σ:Env) (x:String) (v:ℕ):
    view f (σ.setVar x v)=(view f σ).setVar x v:=rfl

end Lax109476Proofs.RamArrayRelabel

end

section

namespace Lax109476Proofs.RamCertificateSetup

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamFrame RamEllipsoidStep IntegerEncoding RationalArithmeticBounds

noncomputable abbrev _root_.AXr5194_0:= @Lax808846Proofs.Reasoning.RunStep.eval_var
noncomputable abbrev _root_.AXr5194_1:= @Lax808846Proofs.Reasoning.RunStep.assign
noncomputable abbrev _root_.AXr5194_2:= @Lax808846Proofs.Reasoning.RunStep.seq
noncomputable abbrev _root_.AXr5194_3:= @Lax808846Proofs.Imp.Com.assign
noncomputable abbrev _root_.AXr5194_4:= @Lax808846Proofs.Imp.Env.setVar
noncomputable abbrev _root_.AXr5194_5:= @Lax808846Proofs.Imp.Env.vars
noncomputable abbrev _root_.AXr5194_6:= @Lax808846Proofs.Imp.Expr.lit
noncomputable abbrev _root_.AXr5194_7:= @Lax808846Proofs.Imp.Expr.var
noncomputable abbrev _root_.AXr5194_8:= @Lax808846Proofs.Imp.Env
theorem metadata_spec (B m n L:ℕ) (hB:2 * parameter L + L + m + n + 8 < B)
    (hH:2 ^ (2 * parameter L) < B):
    Spec B (fun σ => σ.vars "lp.m"=m∧ σ.vars "lp.n"=n∧ σ.vars "input.bits"=L) metadata
      (fun _ τ => Saved m n L τ∧ τ.vars "system.H"=2 ^ (2 * parameter L)∧
        τ.vars "source.m"=m∧ τ.vars "source.n"=n) 22:=by
  have h1:1 < B:=by omega
  have h2:2 < B:=by omega
  have h4:4 < B:=by omega
  have hm:m < B:=by omega
  have hn:n < B:=by omega
  have hL:L < B:=by omega
  have hL4:L + 4 < B:=by omega
  have hp:parameter L < B:=by omega
  have hp2:2 * parameter L < B:=by omega
  rintro σ ⟨hσm,hσn,hσbits⟩
  (expose_names;
    refine
        let c0:Nat→ Nat:=
          @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)));
        let c1:Nat→ Nat→ Nat:= @HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat);
        let c2:Nat→ Nat:=c1 (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)));
        let c3:Nat:=c0 (c2 (Lax109476Proofs.RamCertificateSetup.parameter L));
        let c4:AXr5194_8→ Prop:=
          (fun (x τ:AXr5194_8) =>
              And (Lax109476Proofs.RamCertificateSetup.Saved m n L τ)
                (And (@Eq Nat (AXr5194_5 τ "system.H") c3)
                  (And (@Eq Nat (AXr5194_5 τ "source.m") m)
                    (@Eq Nat (AXr5194_5 τ "source.n") n))))
            σ;
        let c5:Nat:=
          AXr5194_5
            (AXr5194_4 σ "certificate.m" (AXr5194_5 σ "lp.m")) "lp.n";
        let c6:AXr5194_8:=
          AXr5194_4
            (AXr5194_4 σ "certificate.m" (AXr5194_5 σ "lp.m")) "certificate.n" c5;
        let c7:Nat:=AXr5194_5 c6 "input.bits";
        let c8:AXr5194_8:=AXr5194_4 c6 "certificate.bits" c7;
        let c9:Nat→ Nat→ Nat:= @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat);
        let c10:Nat:=AXr5194_5 c8 "input.bits";
        let c11:Nat:=c9 c10 (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)));
        let c12:Nat:=c2 c11;
        let c13:AXr5194_8:=AXr5194_4 c8 "certificate.parameter" c12;
        let c14:Nat:=AXr5194_5 c13 "certificate.parameter";
        let c15:Nat:=c2 c14;
        let c16:Nat:=c1 (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (c0 c15);
        let c17:AXr5194_8:=AXr5194_4 c13 "system.H" c16;
        let c18:Nat:=AXr5194_5 c17 "lp.m";
        let c19:AXr5194_8:=AXr5194_4 c17 "source.m" c18;
        let c20:Nat:=AXr5194_5 c19 "lp.n";
        let c21:AXr5194_8:=AXr5194_4 c19 "source.n" c20;
        let c22:Nat→ Nat:=c9 (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)));
        let c23:Nat:=c22 (Lax808846Proofs.Imp.Expr.size (AXr5194_7 "lp.m"));
        let c24:Nat→ Nat:=c9 c23;
        let c25:Nat:=c22 (Lax808846Proofs.Imp.Expr.size (AXr5194_7 "lp.n"));
        let c26:Nat:=c22 (Lax808846Proofs.Imp.Expr.size (AXr5194_7 "input.bits"));
        let c27:Lax808846Proofs.Imp.Expr→ Lax808846Proofs.Imp.Expr:=
          Lax808846Proofs.Imp.Expr.mul
            (AXr5194_6 (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))));
        let c28:Lax808846Proofs.Imp.Expr:=
          Lax808846Proofs.Imp.Expr.add (AXr5194_7 "input.bits")
            (AXr5194_6 (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))));
        let c29:Lax808846Proofs.Imp.Expr:=c27 c28;
        let c30:Nat:=c22 (Lax808846Proofs.Imp.Expr.size c29);
        let c31:Lax808846Proofs.Imp.Expr:=c27 (AXr5194_7 "certificate.parameter");
        let c32:Lax808846Proofs.Imp.Expr:=
          Lax808846Proofs.Imp.Expr.shiftl
            (AXr5194_6 (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) c31;
        let c33:Nat:=c22 (Lax808846Proofs.Imp.Expr.size c32);
        let c34:Nat:=c24 c25;
        let c35:Nat:=c9 c33 c34;
        let c36:Nat:=c9 c30 c35;
        let c37:Nat:=c9 c26 c36;
        let c38:Nat:=c9 c25 c37;
        let c39:Lax808846Proofs.Imp.Com:=AXr5194_3 "certificate.parameter" c29;
        let c40:Lax808846Proofs.Imp.Com:=AXr5194_3 "system.H" c32;
        let c41:Lax808846Proofs.Imp.Com:=
          Lax808846Proofs.Imp.Com.seq (AXr5194_3 "source.m" (AXr5194_7 "lp.m"))
            (AXr5194_3 "source.n" (AXr5194_7 "lp.n"));
        let c42:Lax808846Proofs.Imp.Com:=Lax808846Proofs.Imp.Com.seq c40 c41;
        let c43:Lax808846Proofs.Imp.Com:=Lax808846Proofs.Imp.Com.seq c39 c42;
        let c44:Lax808846Proofs.Imp.Com:=
          Lax808846Proofs.Imp.Com.seq
            (AXr5194_3 "certificate.bits" (AXr5194_7 "input.bits")) c43;
        let c45:
          ∀ (σ:AXr5194_8),
            @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) B→
              @Eq (Option Nat)
                (Lax808846Proofs.Imp.Expr.evalB B
                  (AXr5194_6 (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) σ)
                (@Option.some Nat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))):=
          Lax808846Proofs.Reasoning.RunStep.eval_lit B (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)));
        let c46:String→ Nat:=AXr5194_5 c21;
        @Exists.intro AXr5194_8
          (fun (σ':AXr5194_8) =>
            And
              (Lax808846Proofs.Reasoning.Run B Lax109476Proofs.RamCertificateSetup.metadata σ σ'
                (@OfNat.ofNat Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
              (c4 σ'))
          c21
          (@And.intro
            (Lax808846Proofs.Reasoning.Run B Lax109476Proofs.RamCertificateSetup.metadata σ c21
              (@OfNat.ofNat Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
            (c4 c21)
            (Lax808846Proofs.Reasoning.RunStep.mono B Lax109476Proofs.RamCertificateSetup.metadata σ c21 (c24 c38)
              (@OfNat.ofNat Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))
              (AXr5194_2 B
                (AXr5194_3 "certificate.m" (AXr5194_7 "lp.m"))
                (Lax808846Proofs.Imp.Com.seq
                  (AXr5194_3 "certificate.n" (AXr5194_7 "lp.n")) c44)
                σ (AXr5194_4 σ "certificate.m" (AXr5194_5 σ "lp.m")) c21 c23 c38
                (AXr5194_1 B σ "certificate.m" (AXr5194_7 "lp.m")
                  (AXr5194_5 σ "lp.m")
                  (AXr5194_0 B σ "lp.m"
                    (?nAX_g5194_0_0_0)))
                (AXr5194_2 B
                  (AXr5194_3 "certificate.n" (AXr5194_7 "lp.n")) c44
                  (AXr5194_4 σ "certificate.m" (AXr5194_5 σ "lp.m")) c6 c21 c25
                  c37
                  (AXr5194_1 B
                    (AXr5194_4 σ "certificate.m" (AXr5194_5 σ "lp.m"))
                    "certificate.n" (AXr5194_7 "lp.n") c5
                    (AXr5194_0 B
                      (AXr5194_4 σ "certificate.m" (AXr5194_5 σ "lp.m")) "lp.n"
                      (?nAX_g5194_0_0_1)))
                  (AXr5194_2 B
                    (AXr5194_3 "certificate.bits" (AXr5194_7 "input.bits")) c43 c6
                    c8 c21 c26 c36
                    (AXr5194_1 B c6 "certificate.bits"
                      (AXr5194_7 "input.bits") c7
                      (AXr5194_0 B c6 "input.bits"
                        (?nAX_g5194_0_0_2)))
                    (AXr5194_2 B c39 c42 c8 c13 c21 c30 c35
                      (AXr5194_1 B c8 "certificate.parameter" c29 c12
                        (Lax808846Proofs.Reasoning.RunStep.eval_mul B c8
                          (AXr5194_6 (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) c28
                          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) c11 (c45 c8 h2)
                          (Lax808846Proofs.Reasoning.RunStep.eval_add B c8 (AXr5194_7 "input.bits")
                            (AXr5194_6 (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) c10
                            (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                            (AXr5194_0 B c8 "input.bits"
                              (?nAX_g5194_0_0_3))
                            (Lax808846Proofs.Reasoning.RunStep.eval_lit B
                              (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) c8 h4)
                            (?nAX_g5194_0_0_4))
                          ?_))
                      (AXr5194_2 B c40 c41 c13 c17 c21 c33 c34
                        (AXr5194_1 B c13 "system.H" c32 c16
                          (Lax808846Proofs.Reasoning.RunStep.eval_shiftl B c13
                            (AXr5194_6 (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) c31
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) c15
                            (Lax808846Proofs.Reasoning.RunStep.eval_lit B
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) c13 h1)
                            (Lax808846Proofs.Reasoning.RunStep.eval_mul B c13
                              (AXr5194_6 (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (AXr5194_7 "certificate.parameter")
                              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) c14 (c45 c13 h2)
                              (AXr5194_0 B c13 "certificate.parameter" ?_) ?_)
                            ?_))
                        (AXr5194_2 B
                          (AXr5194_3 "source.m" (AXr5194_7 "lp.m"))
                          (AXr5194_3 "source.n" (AXr5194_7 "lp.n")) c17 c19 c21
                          c23 c25
                          (AXr5194_1 B c17 "source.m" (AXr5194_7 "lp.m")
                            c18
                            (AXr5194_0 B c17 "lp.m"
                              (?nAX_g5194_0_0_5)))
                          (AXr5194_1 B c19 "source.n" (AXr5194_7 "lp.n")
                            c20
                            (AXr5194_0 B c19 "lp.n"
                              (?nAX_g5194_0_0_6)))))))))
              (?nAX_g5194_0_0_7))
            ?_) <;> try dsimp +zetaDelta at *
   all_goals try dsimp +zetaDelta at *
   try case nAX_g5194_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g5194_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g5194_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g5194_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g5194_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g5194_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g5194_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g5194_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all
  )
  all_goals simp_all [Saved,parameter,Bop.apply_shiftl]

def Input {m n:ℕ} (P:Program ℤ m n) (L:ℕ) (σ:Env):Prop:=
  Represents "int.A" (RamMatrixStorage.flatten (rationalProgram P).A) σ∧
    Represents "int.b" (List.ofFn (rationalProgram P).b) σ∧
    Represents "int.c" (List.ofFn (rationalProgram P).c) σ∧
    σ.vars "lp.m"=m∧ σ.vars "lp.n"=n∧ σ.vars "decode.count"=m * n∧ σ.vars "input.bits"=L∧
    Extents "source.A" (m * n) σ∧ Extents "source.b" m σ∧ Extents "source.c" n σ

set_option maxHeartbeats 1000000 in
theorem save_spec (B M m n L:ℕ) (P:Program ℤ m n) (hM:1≤ M) (hMB:M < B)
    (hB:m * n + 2 * parameter L + L + m + n + 8 < B) (hH:2 ^ (2 * parameter L) < B)
    (hA:∀ i j, (P.A i j).natAbs≤ M) (hb:∀ i, (P.b i).natAbs≤ M)
    (hc:∀ j, (P.c j).natAbs≤ M):
    Spec B (Input P L) save
      (fun _ τ => RamCertificateSource.Data P τ∧ Saved m n L τ∧ τ.vars "system.H"=2 ^ (2 * parameter L))
      (71 * (m * n + m + n) + 100):=by
  have h1:1 < B:=by omega
  have hAcopy:=RamCopyBlock.copyBlock_spec B M (m * n) "int.A" "source.A" "decode.count"
    (fun i => (rationalProgram P).A i.divNat i.modNat) h1 (by omega) hMB
    (fun i => ⟨by simpa [rationalProgram] using hA i.divNat i.modNat,by simpa [rationalProgram] using hM⟩)
    (by simp [RamCopy.Disjoint,RamCopy.suffixes])
  have hbcopy:=RamCopyBlock.copyBlock_spec B M m "int.b" "source.b" "lp.m"
    (rationalProgram P).b h1 (by omega) hMB
    (fun i => ⟨by simpa [rationalProgram] using hb i,by simpa [rationalProgram] using hM⟩) (by simp [RamCopy.Disjoint,RamCopy.suffixes])
  have hccopy:=RamCopyBlock.copyBlock_spec B M n "int.c" "source.c" "lp.n"
    (rationalProgram P).c h1 (by omega) hMB
    (fun i => ⟨by simpa [rationalProgram] using hc i,by simpa [rationalProgram] using hM⟩) (by simp [RamCopy.Disjoint,RamCopy.suffixes])
  have hmeta:=metadata_spec B m n L (by omega) hH
  rintro σ ⟨hσA,hσb,hσc,hσm,hσn,hσcount,hσbits,hσSA,hσSb,hσSc⟩
  obtain ⟨τ,hr₁,hτA,_⟩:=hAcopy σ ⟨hσA,hσSA,hσcount⟩
  have hτb:=RamReadBody.represents_frame _ _ hσb hr₁ (by decide)
  have hτc:=RamReadBody.represents_frame _ _ hσc hr₁ (by decide)
  have hτm:=(hr₁.frame_var "lp.m" (by decide)).trans hσm
  obtain ⟨υ,hr₂,hυb,_⟩:=hbcopy τ
    ⟨hτb,RamAdvanceState.extents_of_run hr₁ "source.b" m hσSb,hτm⟩
  have hυc:=RamReadBody.represents_frame _ _ hτc hr₂ (by decide)
  have hυn:=((hr₁.seq hr₂).frame_var "lp.n" (by decide)).trans hσn
  obtain ⟨ξ,hr₃,hξc,_⟩:=hccopy υ
    ⟨hυc,RamAdvanceState.extents_of_run (hr₁.seq hr₂) "source.c" n hσSc,hυn⟩
  have hrCopy:=hr₁.seq (hr₂.seq hr₃)
  have hξm:=(hrCopy.frame_var "lp.m" (by decide)).trans hσm
  have hξn:=(hrCopy.frame_var "lp.n" (by decide)).trans hσn
  have hξbits:=(hrCopy.frame_var "input.bits" (by decide)).trans hσbits
  obtain ⟨ρ,hr₄,hρSaved,hρH,hρm,hρn⟩:=hmeta ξ ⟨hξm,hξn,hξbits⟩
  have hρA:=RamReadBody.represents_frame _ _ hτA (hr₂.seq (hr₃.seq hr₄)) (by decide)
  have hρb:=RamReadBody.represents_frame _ _ hυb (hr₃.seq hr₄) (by decide)
  have hρc:=RamReadBody.represents_frame _ _ hξc hr₄ (by decide)
  refine ⟨ρ, (hrCopy.seq hr₄).mono ?_, ⟨hρA,hρb,hρc,hρm,hρn⟩,hρSaved,hρH⟩
  simp only [Nat.mul_add]
  omega

end Lax109476Proofs.RamCertificateSetup

end

section

namespace Lax109476Proofs.RamSolverWorkspace

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep RamCertificateArrayRelabel

theorem recovery_of_run {B k:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ k)
    (name:String) (r s N:ℕ) (hσ:Recovery name r s N σ):Recovery name r s N τ:=by
  obtain ⟨_,_,hstep⟩:=hr.bigStep
  have hlen:=RamAdvanceState.array_length_of_bigStep hstep
  simpa only [Recovery,recoveryView,RamArrayRelabel.view,Extents,
    RamRecoveryThreshold.Workspace,RamRecoveryQuery.Extent,RamFeasibilityQuery.Workspace,
    RamEllipsoidStep.Workspace,hlen] using hσ

theorem decision_of_run {B k:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ k)
    (name:String) (r s:ℕ) (hσ:Decision name r s σ):Decision name r s τ:=by
  obtain ⟨_,_,hstep⟩:=hr.bigStep
  have hlen:=RamAdvanceState.array_length_of_bigStep hstep
  simpa only [Decision,RamCertificateDecision.prefixedView,RamArrayRelabel.view,Extents,
    RamFeasibilityQuery.Workspace,RamEllipsoidStep.Workspace,hlen] using hσ

theorem all_of_run {B k:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ k)
    (m n N:ℕ) (hσ:All m n N σ):All m n N τ:=
  ⟨recovery_of_run hr _ _ _ _ hσ.1,decision_of_run hr _ _ _ hσ.2.1,
    recovery_of_run hr _ _ _ _ hσ.2.2.1,decision_of_run hr _ _ _ hσ.2.2.2.1,
    recovery_of_run hr _ _ _ _ hσ.2.2.2.2⟩

end Lax109476Proofs.RamSolverWorkspace

end

section

namespace Lax109476Proofs.RamSolverOriginalContext

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays IntegerEncoding

theorem of_source {m n L:ℕ} (P:Program ℤ m n) (σ:Env)
    (hData:RamCertificateSource.Data P σ) (hSaved:RamCertificateSetup.Saved m n L σ)
    (hH:σ.vars "system.H"=2 ^ (2 * RamCertificateSetup.parameter L)):Context P L σ:=
  ⟨⟨hData.1,hData.2.1,hData.2.2.1⟩,hSaved,hH⟩

end Lax109476Proofs.RamSolverOriginalContext

end

section

namespace Lax109476Proofs.RamSolverBranchBounds

theorem guards (S w:ℕ) (hw:wordWidth S≤ w):
    2 ^ (2 * S) < 2 ^ w∧ S * S + 2 * S + 8 < 2 ^ w:=by
  have hh:RamRecoverFeasibleSystem.wordWidth S S S≤ w:=by unfold wordWidth at hw; omega
  have hguard:S * S + 2 * S + 8≤ w:=by
    unfold RamRecoverFeasibleSystem.wordWidth RamCoordinateCapBounds.wordWidth at hh
    nlinarith
  have hexp:2 * S < w:=by
    unfold RamRecoverFeasibleSystem.wordWidth RamCoordinateCapBounds.wordWidth at hh
    nlinarith
  exact ⟨Nat.pow_lt_pow_right (by decide) hexp,hguard.trans_lt (Nat.lt_two_pow_self (n:=w))⟩

end Lax109476Proofs.RamSolverBranchBounds

end

section

namespace Lax109476Proofs.RamSolverFinish

open Lax109476.LinearProgram Lax109476.RationalEncoding Lax109476.RationalCertificates
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep IntegerEncoding RamSolverWorkspace EncodingSize

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1800000 in
theorem save_noWrite:RamCertificateSetup.save.NoWrite:=by decide

theorem finish_spec (m n N w:ℕ) (P:Program ℚ m n)
    (hw:RamSolverBranchBounds.wordWidth (RamCertificateSetup.parameter (bitSize (encodeProgram P)))≤ w)
    (hN:RamRationalReconstruction.depthBound (RamRecoverFeasibleSystem.recoveryBits
      (RamCertificateSetup.parameter (bitSize (encodeProgram P)))) + 1≤ N):
    Spec (2 ^ w) (Input P N) (.seq RamCertificateSetup.save RamExactSolverProgram.chooseCertificate)
      (Result P) (instructionBound (bitSize (encodeProgram P))):=by
  let L:=bitSize (encodeProgram P)
  let S:=RamCertificateSetup.parameter L
  let H:=2 ^ (2 * S)
  have hcells:=RamSolverInitialization.cells_bound P
  have hdim:m + n≤ L:=by dsimp only [L]; omega
  have hAraw:=(integerProgram_bounds P).1
  have hbraw:=(integerProgram_bounds P).2.1
  have hcraw:=(integerProgram_bounds P).2.2
  have hLS:L≤ S:=by dsimp only [S,RamCertificateSetup.parameter]; omega
  have hp:2 ^ (2 * L)≤ H:=Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 2 hLS)
  have hA:∀ i j, ((integerProgram P).A i j).natAbs≤ H:=fun i j => (hAraw i j).trans hp
  have hb:∀ i, ((integerProgram P).b i).natAbs≤ H:=fun i => (hbraw i).trans hp
  have hc:∀ j, ((integerProgram P).c j).natAbs≤ H:=fun j => (hcraw j).trans hp
  have hH:1≤ H:=Nat.one_le_pow _ _ (by decide)
  have hguards:=RamSolverBranchBounds.guards S w hw
  have hSaveGuard:m * n + 2 * S + L + m + n + 8 < 2 ^ w:=by
    have hL2:2 * L≤ S:=by dsimp only [S,RamCertificateSetup.parameter]; omega
    have hS1:1≤ S:=by dsimp only [S,RamCertificateSetup.parameter]; omega
    have hSS:S≤ S * S:=Nat.le_mul_of_pos_right S (by omega)
    dsimp only [L] at *
    omega
  rintro σ ⟨hσFront,hσA,hσb,hσc,hσAll⟩
  rcases hσFront with ⟨hσP,hσInt,hσvalid,hσbits,hσden,hσinp⟩
  have hσSave:RamCertificateSetup.Input (integerProgram P) L σ:=
    ⟨hσInt.1,hσInt.2.1,hσInt.2.2,hσP.2.2.2.1,hσP.2.2.2.2.1,
      hσP.2.2.2.2.2,hσbits,hσA,hσb,hσc⟩
  obtain ⟨τ,hrSave,hτSource,hτSaved,hτH⟩:=RamCertificateSetup.save_spec (2 ^ w) H m n L
    (integerProgram P) hH hguards.1 hSaveGuard hguards.1 hA hb hc σ hσSave
  have hτContext:=RamSolverOriginalContext.of_source (integerProgram P) τ hτSource hτSaved hτH
  have hτAll:=all_of_run hrSave m n N hσAll
  obtain ⟨υ,hrChoose,cert,hυout,hvalid⟩:=RamSolverChooseCertificate.choose_spec m n L N w
    (integerProgram P) hdim hw hN hA hb hc τ ⟨hτSource,hτContext,hτAll⟩
  have hvalidOriginal:IsValidCertificate P cert:=by
    have hh:=hvalid
    rw [integerProgram_eq_scaled] at hh
    exact (certificate_scaled P (programDenominator P) (by
      exact_mod_cast RationalSizeBounds.commonDenominator_pos (programData P)) cert).mp hh
  refine ⟨υ, (hrSave.seq hrChoose).mono ?_,cert, ?_,hvalidOriginal⟩
  · have hcost:=Nat.mul_le_mul_left 71 hcells
    dsimp only [instructionBound,L]
    omega
  · simpa only [hrSave.out_eq save_noWrite] using hυout

end Lax109476Proofs.RamSolverFinish

end

theorem solution:∀ (m n N w:ℕ) (P:Lax109476.LinearProgram.Program ℚ m n),
  Lax109476Proofs.RamSolverBranchBounds.wordWidth
        (Lax109476Proofs.RamCertificateSetup.parameter
          (Lax759944.BinaryWordEncoding.bitSize (Lax109476.RationalEncoding.encodeProgram P)))≤
      w→
    Lax109476Proofs.RamRationalReconstruction.depthBound
            (Lax109476Proofs.RamRecoverFeasibleSystem.recoveryBits
              (Lax109476Proofs.RamCertificateSetup.parameter
                (Lax759944.BinaryWordEncoding.bitSize (Lax109476.RationalEncoding.encodeProgram P)))) +
          1≤
        N→
      Lax808846Proofs.Reasoning.Spec (2 ^ w) (Lax109476Proofs.RamSolverFinish.Input P N)
        (Lax109476Proofs.RamCertificateSetup.save.seq Lax109476Proofs.RamExactSolverProgram.chooseCertificate)
        (Lax109476Proofs.RamSolverFinish.Result P)
        (Lax109476Proofs.RamSolverFinish.instructionBound
          (Lax759944.BinaryWordEncoding.bitSize (Lax109476.RationalEncoding.encodeProgram P))):= @Lax109476Proofs.RamSolverFinish.finish_spec
