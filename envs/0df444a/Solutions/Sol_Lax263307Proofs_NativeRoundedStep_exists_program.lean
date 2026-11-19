-- Prove2me | solution 1 for Lax263307Proofs.NativeRoundedStep.exists_program
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T11:40:02.377552+00:00
-- url     : https://prove2.me/submissions/3c82dcc2-1c31-47cf-98e1-5f540e3414b2

import Mathlib.Tactic
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Size
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.Polynomial.Eval.Defs
import Definitions.Def_EdgeSublinearMWIS_Main_NativeOperationalInterfaces
import Theorems.Thm_Lax808846Proofs_Simulation_compileProgram_runsTo
import Theorems.Thm_Lax109476Proofs_RamEllipsoidStep_ellipsoidStep_spec

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

@[simp] theorem evalB_condEq_iff {B:ℕ} {e f:Expr} {σ:Env} {r:Bool}:
    (Cond.eq e f).evalB B σ=some r↔
      ∃ m n,e.evalB B σ=some m∧ f.evalB B σ=some n∧ r=(m == n):=by
  rw [Cond.evalB]
  simp only [Option.bind_eq_some_iff,Option.map_eq_some_iff]
  constructor
  · rintro ⟨m,hm,n,hn,rfl⟩; exact ⟨m,n,hm,hn,rfl⟩
  · rintro ⟨m,n,hm,hn,rfl⟩; exact ⟨m,hm,n,hn,rfl⟩

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

theorem Run.inpBounded {B:ℕ} {c:Com} {σ σ':Env} {K:ℕ} (h:Run B c σ σ' K)
    (hσ:σ.InpBounded B):σ'.InpBounded B:=by
  obtain ⟨_,_,hbs⟩:=h; exact hbs.inpBounded hσ

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

namespace Lax808846Proofs.Transfer

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Compile
open Lax808846Proofs.Simulation Lax808846Proofs.Reasoning

theorem fitsWords_of_max_le {L:Layout} {B w:ℕ} (h1:1 < B)
    (h:max B (L.span B)≤ 2 ^ w):L.FitsWords B w:=
  ⟨h1,le_trans (le_max_left _ _) h,le_trans (le_max_right _ _) h⟩

end Lax808846Proofs.Transfer

end

section

namespace Lax109476Proofs.RationalRounding

theorem grid_num_den_bound (k:ℤ) (D:ℕ) (hD:0 < D):
    ((k:ℚ) / D).num.natAbs≤ k.natAbs∧ ((k:ℚ) / D).den≤ D:=by
  obtain ⟨c,hnum,hden⟩:=Rat.exists_eq_mul_div_num_and_eq_mul_div_den k
    (d:=(D:ℤ)) (by exact_mod_cast ne_of_gt hD)
  have hc:c ≠ 0:=by
    intro h
    rw [h,zero_mul] at hden
    have hDn:(D:ℤ) ≠ 0:=by exact_mod_cast ne_of_gt hD
    exact hDn hden
  have hcpos:0 < c.natAbs:=Int.natAbs_pos.mpr hc
  have hnumAbs:k.natAbs=c.natAbs * ((k:ℚ) / D).num.natAbs:=by
    simpa only [Int.natAbs_mul,Int.cast_natCast] using congrArg Int.natAbs hnum
  have hdenAbs:D=c.natAbs * ((k:ℚ) / D).den:=by
    simpa only [Int.natAbs_mul,Int.natAbs_natCast,Int.cast_natCast] using
      congrArg Int.natAbs hden
  constructor
  · calc
      _≤ c.natAbs * ((k:ℚ) / D).num.natAbs:=Nat.le_mul_of_pos_left _ hcpos
      _=_:=hnumAbs.symm
  · calc
      _≤ c.natAbs * ((k:ℚ) / D).den:=Nat.le_mul_of_pos_left _ hcpos
      _=_:=hdenAbs.symm

private theorem abs_le_num (q:ℚ):|q|≤ (q.num.natAbs:ℚ):=by
  have hden:(0:ℚ) < q.den:=by exact_mod_cast q.den_pos
  have hden₁:(1:ℚ)≤ q.den:=by exact_mod_cast q.den_pos
  have hnum:(q.num.natAbs:ℚ)=|(q.num:ℚ)|:=by
    rw [Nat.cast_natAbs,Int.cast_abs]
  conv_lhs => rw [← q.num_div_den]
  rw [abs_div,abs_of_nonneg (le_of_lt hden), ← hnum]
  apply (div_le_iff₀ hden).mpr
  simpa using mul_le_mul_of_nonneg_left hden₁ (Nat.cast_nonneg q.num.natAbs)

theorem roundDown_floor_magnitude_bound (q:ℚ) (M D:ℕ) (hq:|q|≤ M):
    (Int.floor (q * D)).natAbs≤ M * D + 1:=by
  let k:=Int.floor (q * D)
  have hab:=abs_le.mp hq
  have hD:(0:ℚ)≤ D:=Nat.cast_nonneg _
  have hupper:=mul_le_mul_of_nonneg_right hab.2 hD
  have hlower:=mul_le_mul_of_nonneg_right hab.1 hD
  have hfloor:(k:ℚ)≤ q * D:=Int.floor_le _
  have hfloor':q * D < (k:ℚ) + 1:=Int.lt_floor_add_one _
  have hk:|(k:ℚ)|≤ (M:ℚ) * D + 1:=by
    apply abs_le.mpr
    constructor <;> linarith
  have hk':(k.natAbs:ℚ)≤ ((M * D + 1:ℕ):ℚ):=by
    simpa only [Nat.cast_natAbs,Int.cast_abs,Nat.cast_add,Nat.cast_mul,
      Nat.cast_one] using hk
  exact Nat.cast_le.mp hk'

theorem roundDown_floor_bound (q:ℚ) (D:ℕ):
    (Int.floor (q * D)).natAbs≤ q.num.natAbs * D + 1:=
  roundDown_floor_magnitude_bound q q.num.natAbs D (abs_le_num q)

end Lax109476Proofs.RationalRounding

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.DeterminantBounds

theorem integer_ratio_num_den_bound (a b:ℤ) (hb:b ≠ 0):
    ((a:ℚ) / b).num.natAbs≤ a.natAbs∧
      ((a:ℚ) / b).den≤ b.natAbs:=by
  obtain ⟨c,hn,hd⟩:=Rat.exists_eq_mul_div_num_and_eq_mul_div_den a (d:=b) hb
  have hc:c ≠ 0:=by
    intro h
    rw [h,zero_mul] at hd
    exact hb hd
  have hcpos:=Int.natAbs_pos.mpr hc
  have hna:a.natAbs=c.natAbs * ((a:ℚ) / b).num.natAbs:=by
    simpa only [Int.natAbs_mul] using congrArg Int.natAbs hn
  have hda:b.natAbs=c.natAbs * ((a:ℚ) / b).den:=by
    simpa only [Int.natAbs_mul,Int.natAbs_natCast] using congrArg Int.natAbs hd
  constructor
  · rw [hna]
    exact Nat.le_mul_of_pos_left _ hcpos
  · rw [hda]
    exact Nat.le_mul_of_pos_left _ hcpos

end Lax109476Proofs.DeterminantBounds

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RationalSizeBounds

variable {ι:Type*} [Fintype ι]

theorem size_mul_le (a b:ℕ):Nat.size (a * b)≤ Nat.size a + Nat.size b:=by
  apply Nat.size_le.mpr
  rw [pow_add]
  exact (Nat.mul_le_mul_right b (Nat.lt_size_self a).le).trans_lt
    (Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self b) (by positivity))

theorem size_pow_le (a k:ℕ):Nat.size (a ^ k)≤ k * Nat.size a + 1:=by
  induction k with
  | zero => simp
  | succ k ih =>
    have h:=size_mul_le (a ^ k) a
    rw [pow_succ,Nat.succ_mul]
    omega

theorem size_add_one_le (a:ℕ):Nat.size (a + 1)≤ Nat.size a + 1:=by
  apply Nat.size_le.mpr
  rw [pow_succ]
  have h:=Nat.lt_size_self a
  have hp:0 < 2 ^ Nat.size a:=by positivity
  omega

theorem size_add_le (a b:ℕ):Nat.size (a + b)≤ Nat.size a + Nat.size b + 1:=by
  apply Nat.size_le.mpr
  rw [pow_succ,pow_add]
  have ha:=Nat.lt_size_self a
  have hb:=Nat.lt_size_self b
  have hpa:0 < 2 ^ Nat.size a:=by positivity
  have hpb:0 < 2 ^ Nat.size b:=by positivity
  have h₁:=Nat.le_mul_of_pos_right (2 ^ Nat.size a) hpb
  have h₂:=Nat.le_mul_of_pos_left (2 ^ Nat.size b) hpa
  omega

end Lax109476Proofs.RationalSizeBounds

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

def Com.decReads:(c:Com)→ Decidable c.reads
  | .skip => decidable_of_iff False (by rw [Com.reads])
  | .assign _ _ => decidable_of_iff False (by rw [Com.reads])
  | .store _ _ _ => decidable_of_iff False (by rw [Com.reads])
  | .seq c d =>
      have:=c.decReads
      have:=d.decReads
      decidable_of_iff (c.reads∨ d.reads) (by rw [Com.reads])
  | .ite _ c d =>
      have:=c.decReads
      have:=d.decReads
      decidable_of_iff (c.reads∨ d.reads) (by rw [Com.reads])
  | .while _ c =>
      have:=c.decReads
      decidable_of_iff c.reads (by rw [Com.reads])
  | .read _ => decidable_of_iff True (by rw [Com.reads])
  | .write _ => decidable_of_iff False (by rw [Com.reads])

instance:DecidablePred Com.reads:=Com.decReads

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

theorem Spec.while_count {b:Cond} (I:Env→ Prop) (V:Env→ ℕ) (Kb:ℕ)
    (hdef:∀ σ,I σ→ ∃ v,b.evalB B σ=some v)
    (hbody:Spec B (fun σ => I σ∧ b.evalB B σ=some true) c
      (fun σ σ' => I σ'∧ V σ' < V σ) Kb)
    (hPI:∀ σ,P σ→ I σ) (hK:∀ σ,P σ→ (1 + b.size + Kb) * V σ + 1 + b.size≤ K):
    Spec B P (.while b c) (fun _ σ' => I σ'∧ b.evalB B σ'=some false) K:=by
  refine Spec.while_potential I (fun σ => (1 + b.size + Kb) * V σ) hdef ?_ hPI hK
  intro σ hI hv
  obtain ⟨σ',hr,hI',hV⟩:=hbody σ ⟨hI,hv⟩
  refine ⟨σ',Kb,hr,hI', ?_⟩
  calc 1 + b.size + Kb + (1 + b.size + Kb) * V σ'
     =(1 + b.size + Kb) * (V σ' + 1):=by ring
    _≤ (1 + b.size + Kb) * V σ:=Nat.mul_le_mul_left _ hV

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

namespace Lax109476Proofs.RamArithmetic

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem gcdStep_spec (B a b:ℕ) (ha:a < B) (hb:b < B):
    Spec B (fun σ => σ.vars "gcd.a"=a∧ σ.vars "gcd.b"=b) gcdStep
      (fun _ σ' => σ'.vars "gcd.a"=b∧ σ'.vars "gcd.b"=a % b) 12:=by
  rintro σ ⟨hsa,hsb⟩
  have hdiv:a / b < B:=(Nat.div_le_self a b).trans_lt ha
  have hmul:a / b * b < B:=(Nat.div_mul_le_self a b).trans_lt ha
  have hsub:a - a / b * b < B:=(Nat.sub_le _ _).trans_lt ha
  (expose_names;
    refine
        let c0:Nat:= @HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a b;
        let c1:Env→ Prop:=
          (fun (x σ':Env) => And (@Eq Nat (Env.vars σ' "gcd.a") b) (@Eq Nat (Env.vars σ' "gcd.b") c0)) σ;
        let c2:Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) (Env.vars σ "gcd.a") (Env.vars σ "gcd.b");
        let c3:Nat:=Nat.mul c2 (Env.vars σ "gcd.b");
        let c4:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (Env.vars σ "gcd.a") c3;
        let c5:Env:=Env.setVar σ "gcd.t" c4;
        let c6:Nat:=Env.vars c5 "gcd.b";
        let c7:Env:=Env.setVar c5 "gcd.a" c6;
        let c8:Nat:=Env.vars c7 "gcd.t";
        let c9:Env:=Env.setVar c7 "gcd.b" c8;
        let c10:Nat→ Nat→ Nat:=Nat.add;
        let c11:Nat→ Nat:=c10 ((1:Nat));
        let c12:Expr:=Expr.mul (Expr.div (Expr.var "gcd.a") (Expr.var "gcd.b")) (Expr.var "gcd.b");
        let c13:Expr:=Expr.sub (Expr.var "gcd.a") c12;
        let c14:Nat:=c11 (Expr.size c13);
        let c15:Nat:=c11 (Expr.size (Expr.var "gcd.b"));
        let c16:Nat:=c11 (Expr.size (Expr.var "gcd.t"));
        let c17:Nat:=c10 c15 c16;
        let c18:String→ Nat:=Env.vars c9;
        @Exists.intro Env
          (fun (σ':Env) => And (Run B gcdStep σ σ' ((12:Nat))) (c1 σ'))
          c9
          (@And.intro (Run B gcdStep σ c9 ((12:Nat))) (c1 c9)
            (RunStep.mono B gcdStep σ c9 (c10 c14 c17) ((12:Nat))
              (RunStep.seq B (Com.assign "gcd.t" c13)
                (Com.seq (Com.assign "gcd.a" (Expr.var "gcd.b")) (Com.assign "gcd.b" (Expr.var "gcd.t"))) σ c5 c9 c14 c17
                (RunStep.assign B σ "gcd.t" c13 c4
                  (RunStep.eval_sub B σ (Expr.var "gcd.a") c12 (Env.vars σ "gcd.a") c3
                    (RunStep.eval_var B σ "gcd.a"
                      (?nAX_g3873_0_0_0))
                    (RunStep.eval_mul B σ (Expr.div (Expr.var "gcd.a") (Expr.var "gcd.b")) (Expr.var "gcd.b") c2
                      (Env.vars σ "gcd.b")
                      (RunStep.eval_div B σ (Expr.var "gcd.a") (Expr.var "gcd.b") (Env.vars σ "gcd.a")
                        (Env.vars σ "gcd.b")
                        (RunStep.eval_var B σ "gcd.a"
                          (?nAX_g3873_0_0_1))
                        (RunStep.eval_var B σ "gcd.b"
                          (?nAX_g3873_0_0_2))
                        ?_)
                      (RunStep.eval_var B σ "gcd.b"
                        (?nAX_g3873_0_0_3))
                      ?_)
                    (?nAX_g3873_0_0_4)))
                (RunStep.seq B (Com.assign "gcd.a" (Expr.var "gcd.b")) (Com.assign "gcd.b" (Expr.var "gcd.t")) c5 c7 c9
                  c15 c16
                  (RunStep.assign B c5 "gcd.a" (Expr.var "gcd.b") c6
                    (RunStep.eval_var B c5 "gcd.b"
                      (?nAX_g3873_0_0_5)))
                  (RunStep.assign B c7 "gcd.b" (Expr.var "gcd.t") c8
                    (RunStep.eval_var B c7 "gcd.t"
                      (?nAX_g3873_0_0_6)))))
              (?nAX_g3873_0_0_7))
            ?_) <;> try dsimp +zetaDelta at *
   all_goals try dsimp +zetaDelta at *
   try case nAX_g3873_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g3873_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g3873_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g3873_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g3873_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g3873_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g3873_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g3873_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all
  )
  all_goals simp_all [Nat.mod_def,Nat.mul_comm]

theorem remainder_half (d r:ℕ) (hr:0 < r) (hrd:r < d):d % r≤ d / 2:=by
  by_cases h:r≤ d / 2
  · exact (Nat.mod_lt d hr).le.trans h
  · rw [Nat.mod_eq_sub_mod hrd.le,Nat.mod_eq_of_lt (by omega)]
    omega

theorem size_half_lt (b:ℕ) (hb:0 < b):(b / 2).size < b.size:=by
  have hs:0 < b.size:=Nat.size_pos.mpr hb
  have hp:b < 2 ^ b.size:=Nat.lt_size_self b
  have he:2 ^ b.size=2 * 2 ^ (b.size - 1):=by
    calc
      _=2 ^ ((b.size - 1) + 1):=congrArg (fun k => 2 ^ k) (by omega)
      _=_:=by rw [pow_succ]; omega
  have hhalf:b / 2 < 2 ^ (b.size - 1):=by omega
  have h:=Nat.size_le.mpr hhalf
  omega

theorem gcd_swap_mod (a b:ℕ):Nat.gcd b (a % b)=Nat.gcd a b:=by
  rw [Nat.gcd_comm b _, ← Nat.gcd_rec,Nat.gcd_comm]

theorem gcdDoubleStep_spec (B M a b:ℕ) (hM:M < B)
    (ha:a≤ M) (hb:b≤ M) (hbpos:0 < b):
    Spec B (fun σ => σ.vars "gcd.a"=a∧ σ.vars "gcd.b"=b) gcdDoubleStep
      (fun _ σ' => σ'.vars "gcd.a" ≤ M∧ σ'.vars "gcd.b" ≤ M∧
        Nat.gcd (σ'.vars "gcd.a") (σ'.vars "gcd.b")=Nat.gcd a b∧
        (σ'.vars "gcd.b").size < b.size) 32:=by
  intro σ hσ
  obtain ⟨τ,hrun,hτa,hτb⟩:=(gcdStep_spec B a b (ha.trans_lt hM) (hb.trans_lt hM)) σ hσ
  have hrlt:a % b < b:=Nat.mod_lt a hbpos
  have hrB:a % b < B:=hrlt.trans (hb.trans_lt hM)
  have h0B:0 < B:=(Nat.zero_le M).trans_lt hM
  by_cases hr0:a % b=0
  · have hc:(Cond.lt (.lit 0) (.var "gcd.b")).evalB B τ=some false:=by
      rw [evalB_condLt (evalB_lit h0B) (evalB_var (hτb ▸ hrB)),hτb,hr0]
      rfl
    refine ⟨τ, (hrun.seq (Run.ite_false hc Run.skip)).mono (by norm_num), ?_⟩
    dsimp only
    rw [hτa,hτb]
    refine ⟨hb,hrlt.le.trans hb,gcd_swap_mod a b, ?_⟩
    rw [hr0]
    exact Nat.size_pos.mpr hbpos
  · have hrpos:0 < a % b:=Nat.pos_of_ne_zero hr0
    have hc:(Cond.lt (.lit 0) (.var "gcd.b")).evalB B τ=some true:=by
      rw [evalB_condLt (evalB_lit h0B) (evalB_var (hτb ▸ hrB)),hτb]
      simp [hrpos]
    obtain ⟨ν,hrν,hνa,hνb⟩:=
      (gcdStep_spec B b (a % b) (hb.trans_lt hM) hrB) τ ⟨hτa,hτb⟩
    refine ⟨ν, (hrun.seq (Run.ite_true hc hrν)).mono (by norm_num), ?_⟩
    dsimp only
    rw [hνa,hνb]
    refine ⟨hrlt.le.trans hb, (Nat.mod_lt b hrpos).le.trans (hrlt.le.trans hb),
      (gcd_swap_mod b (a % b)).trans (gcd_swap_mod a b), ?_⟩
    exact (Nat.size_le_size (remainder_half b (a % b) hrpos hrlt)).trans_lt
      (size_half_lt b hbpos)

theorem gcdLoop_spec (B M a b:ℕ) (hM:M < B) (ha:a≤ M) (hb:b≤ M):
    Spec B (fun σ => σ.vars "gcd.a"=a∧ σ.vars "gcd.b"=b) gcdLoop
      (fun _ σ' => σ'.vars "gcd.a"=Nat.gcd a b∧ σ'.vars "gcd.b"=0)
      (36 * b.size + 4):=by
  let I:=fun σ:Env => σ.vars "gcd.a" ≤ M∧ σ.vars "gcd.b" ≤ M∧
    Nat.gcd (σ.vars "gcd.a") (σ.vars "gcd.b")=Nat.gcd a b
  have hloop:Spec B (fun σ => σ.vars "gcd.a"=a∧ σ.vars "gcd.b"=b) gcdLoop
      (fun _ σ' => I σ'∧
        (Cond.lt (.lit 0) (.var "gcd.b")).evalB B σ'=some false)
      (36 * b.size + 4):=by
    apply Spec.while_count I (fun σ => (σ.vars "gcd.b").size) 32
    · intro σ hI
      exact ⟨_,evalB_condLt (evalB_lit ((Nat.zero_le M).trans_lt hM))
        (evalB_var (hI.2.1.trans_lt hM))⟩
    · rintro σ ⟨hI,hc⟩
      have hbpos:0 < σ.vars "gcd.b" :=by
        rw [evalB_condLt (evalB_lit ((Nat.zero_le M).trans_lt hM))
          (evalB_var (hI.2.1.trans_lt hM))] at hc
        simpa using hc
      obtain ⟨τ,hr,hτa,hτb,hτg,hτs⟩:=
        gcdDoubleStep_spec B M _ _ hM hI.1 hI.2.1 hbpos σ ⟨rfl,rfl⟩
      exact ⟨τ,hr, ⟨hτa,hτb,hτg.trans hI.2.2⟩,hτs⟩
    · rintro σ ⟨hσa,hσb⟩
      exact ⟨hσa ▸ ha,hσb ▸ hb,by rw [hσa,hσb]⟩
    · rintro σ ⟨_,hσb⟩
      simp [hσb]
  apply hloop.post
  rintro σ τ _ ⟨hI,hc⟩
  have hb0:τ.vars "gcd.b"=0:=by
    rw [evalB_condLt (evalB_lit ((Nat.zero_le M).trans_lt hM))
      (evalB_var (hI.2.1.trans_lt hM))] at hc
    simpa using hc
  exact ⟨by simpa [hb0] using hI.2.2,hb0⟩

theorem normalizeFraction_spec (B n d:ℕ) (hn:n < B) (hd:d < B) (hdpos:0 < d):
    Spec B (fun σ => σ.vars "rat.n"=n∧ σ.vars "rat.d"=d) normalizeFraction
      (fun _ σ' => σ'.vars "rat.n"=n / Nat.gcd n d∧
        σ'.vars "rat.d"=d / Nat.gcd n d) (36 * d.size + 16):=by
  have hM:max n d < B:=max_lt hn hd
  have hg:Nat.gcd n d < B:=(Nat.gcd_le_right n hdpos).trans_lt hd
  have hnDiv:n / Nat.gcd n d < B:=(Nat.div_le_self _ _).trans_lt hn
  have hdDiv:d / Nat.gcd n d < B:=(Nat.div_le_self _ _).trans_lt hd
  have hs:=(gcdLoop_spec B (max n d) n d hM (le_max_left _ _) (le_max_right _ _)).frame
  rintro σ ⟨hσn,hσd⟩
  (expose_names;
    refine
        let c0:Nat:=Env.vars (Env.setVar σ "gcd.a" (Env.vars σ "rat.n")) "rat.d";
        let c1:Env:=Env.setVar (Env.setVar σ "gcd.a" (Env.vars σ "rat.n")) "gcd.b" c0;
        let c2:Env→ Nat→ Prop:=Run B gcdLoop c1;
        let c3:Nat→ Nat→ Nat:=Nat.add;
        let c4:Nat→ Nat:=
          c3
            (Nat.mul ((36:Nat))
              (Nat.size d));
        let c5:Nat:=c4 ((4:Nat));
        let c6:String→ Nat:=Env.vars c1;
        let c7:List Nat:=Env.inp c1;
        let c8:List Nat:=Env.out c1;
        let c9:Env→ Prop:=fun (σ':Env) =>
          And (c2 σ' c5)
            (And
              (And (@Eq Nat (Env.vars σ' "gcd.a") (Nat.gcd n d))
                (@Eq Nat (Env.vars σ' "gcd.b") ((0:Nat))))
              (And (∀ y∉ Com.wvars gcdLoop, @Eq Nat (Env.vars σ' y) (c6 y))
                (And (∀ a∉ Com.warrs gcdLoop, @Eq (List Nat) (Env.arrs σ' a) (Env.arrs c1 a))
                  (And (Not (Com.reads gcdLoop)→ @Eq (List Nat) (Env.inp σ') c7)
                    (Com.NoWrite gcdLoop→ @Eq (List Nat) (Env.out σ') c8)))));
        let c10:Nat:=c4 ((16:Nat));
        let c11:Nat→ Nat→ Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv);
        let c12:Nat:=c11 n (Nat.gcd n d);
        let c13:Nat:=c11 d (Nat.gcd n d);
        let c14:Env→ Prop:=
          (fun (x σ':Env) => And (@Eq Nat (Env.vars σ' "rat.n") c12) (@Eq Nat (Env.vars σ' "rat.d") c13)) σ;
        let c15:Env→ Prop:=fun (σ':Env) => And (Run B normalizeFraction σ σ' c10) (c14 σ');
        let c16:Prop:= @Exists Env c15;
        let c17:Nat→ Nat:=c3 ((1:Nat));
        let c18:Nat:=c17 (Expr.size (Expr.var "rat.n"));
        let c19:Nat:=c17 (Expr.size (Expr.var "rat.d"));
        let c20:Nat:=c17 (Expr.size (Expr.div (Expr.var "rat.n") (Expr.var "gcd.a")));
        let c21:Nat:=c17 (Expr.size (Expr.div (Expr.var "rat.d") (Expr.var "gcd.a")));
        let c22:Nat:=c3 c20 c21;
        let c23:Nat:=c3 c5 c22;
        let c24:Nat:=c3 c19 c23;
        let c25:Com:=Com.assign "rat.n" (Expr.div (Expr.var "rat.n") (Expr.var "gcd.a"));
        let c26:Com:=Com.assign "rat.d" (Expr.div (Expr.var "rat.d") (Expr.var "gcd.a"));
        let c27:Com:=Com.seq c25 c26;
        let c28:Com:=Com.seq gcdLoop c27;
        @Exists.casesOn Env c9 (fun (x:@Exists Env c9) => c16)
          (RunStep.use B (fun (σ:Env) => And (@Eq Nat (Env.vars σ "gcd.a") n) (@Eq Nat (Env.vars σ "gcd.b") d)) gcdLoop
            (fun (σ σ':Env) =>
              And
                (And (@Eq Nat (Env.vars σ' "gcd.a") (Nat.gcd n d))
                  (@Eq Nat (Env.vars σ' "gcd.b") ((0:Nat))))
                (And (∀ y∉ Com.wvars gcdLoop, @Eq Nat (Env.vars σ' y) (Env.vars σ y))
                  (And (∀ a∉ Com.warrs gcdLoop, @Eq (List Nat) (Env.arrs σ' a) (Env.arrs σ a))
                    (And (Not (Com.reads gcdLoop)→ @Eq (List Nat) (Env.inp σ') (Env.inp σ))
                      (Com.NoWrite gcdLoop→ @Eq (List Nat) (Env.out σ') (Env.out σ))))))
            c5 hs c1 ?_)
          fun (w:Env)
            (h:
              And (c2 w c5)
                (And
                  (And (@Eq Nat (Env.vars w "gcd.a") (Nat.gcd n d))
                    (@Eq Nat (Env.vars w "gcd.b") ((0:Nat))))
                  (And (∀ y∉ Com.wvars gcdLoop, @Eq Nat (Env.vars w y) (c6 y))
                    (And (∀ a∉ Com.warrs gcdLoop, @Eq (List Nat) (Env.arrs w a) (Env.arrs c1 a))
                      (And (Not (Com.reads gcdLoop)→ @Eq (List Nat) (Env.inp w) c7)
                        (Com.NoWrite gcdLoop→ @Eq (List Nat) (Env.out w) c8)))))) =>
          let c0_1:Prop:=
            And
              (And (@Eq Nat (Env.vars w "gcd.a") (Nat.gcd n d))
                (@Eq Nat (Env.vars w "gcd.b") ((0:Nat))))
              (And (∀ y∉ Com.wvars gcdLoop, @Eq Nat (Env.vars w y) (c6 y))
                (And (∀ a∉ Com.warrs gcdLoop, @Eq (List Nat) (Env.arrs w a) (Env.arrs c1 a))
                  (And (Not (Com.reads gcdLoop)→ @Eq (List Nat) (Env.inp w) c7)
                    (Com.NoWrite gcdLoop→ @Eq (List Nat) (Env.out w) c8))));
          let c1_1:Nat:=c11 (Env.vars w "rat.n") (Env.vars w "gcd.a");
          let c2_1:Env:=Env.setVar w "rat.n" c1_1;
          let c3_1:String→ Nat:=Env.vars c2_1;
          let c4:Nat:=c3_1 "rat.d";
          let c5_1:Nat:=c3_1 "gcd.a";
          let c6:Nat:=c11 c4 c5_1;
          let c7:Env:=Env.setVar c2_1 "rat.d" c6;
          let c8:
            ∀ (x:String),
              Nat.lt (Env.vars c2_1 x) B→
                @Eq (Option Nat) (Expr.evalB B (Expr.var x) c2_1) (@some Nat (Env.vars c2_1 x)):=
            RunStep.eval_var B c2_1;
          let c9:String→ Nat:=Env.vars c7;
          @And.casesOn (c2 w c5) c0_1 (fun (x:And (c2 w c5) c0_1) => c16) h fun (left:c2 w c5) (right:c0_1) =>
            @Exists.intro Env c15 c7
              (@And.intro (Run B normalizeFraction σ c7 c10) (c14 c7)
                (RunStep.mono B normalizeFraction σ c7 (c3 c18 c24) c10
                  (RunStep.seq B (Com.assign "gcd.a" (Expr.var "rat.n"))
                    (Com.seq (Com.assign "gcd.b" (Expr.var "rat.d")) c28) σ (Env.setVar σ "gcd.a" (Env.vars σ "rat.n")) c7
                    c18 c24
                    (RunStep.assign B σ "gcd.a" (Expr.var "rat.n") (Env.vars σ "rat.n")
                      (RunStep.eval_var B σ "rat.n"
                        (?nAX_g3882_0_0_0)))
                    (RunStep.seq B (Com.assign "gcd.b" (Expr.var "rat.d")) c28 (Env.setVar σ "gcd.a" (Env.vars σ "rat.n"))
                      c1 c7 c19 c23
                      (RunStep.assign B (Env.setVar σ "gcd.a" (Env.vars σ "rat.n")) "gcd.b" (Expr.var "rat.d") c0
                        (RunStep.eval_var B (Env.setVar σ "gcd.a" (Env.vars σ "rat.n")) "rat.d"
                          (?nAX_g3882_0_0_1)))
                      (RunStep.seq B gcdLoop c27 c1 w c7 c5 c22 left
                        (RunStep.seq B c25 c26 w c2_1 c7 c20 c21
                          (RunStep.assign B w "rat.n" (Expr.div (Expr.var "rat.n") (Expr.var "gcd.a")) c1_1
                            (RunStep.eval_div B w (Expr.var "rat.n") (Expr.var "gcd.a") (Env.vars w "rat.n")
                              (Env.vars w "gcd.a") (RunStep.eval_var B w "rat.n" ?_)
                              (RunStep.eval_var B w "gcd.a"
                                (?nAX_g3882_0_0_2))
                              ?_))
                          (RunStep.assign B c2_1 "rat.d" (Expr.div (Expr.var "rat.d") (Expr.var "gcd.a")) c6
                            (RunStep.eval_div B c2_1 (Expr.var "rat.d") (Expr.var "gcd.a") c4 c5_1 (c8 "rat.d" ?_)
                              (c8 "gcd.a"
                                (?nAX_g3882_0_0_3))
                              ?_))))))
                  (?nAX_g3882_0_0_4))
                ?_) <;> try dsimp +zetaDelta at *
   all_goals try dsimp +zetaDelta at *
   try case nAX_g3882_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g3882_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g3882_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g3882_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g3882_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all
  )
  all_goals simp_all [gcdLoop,gcdDoubleStep,gcdStep,Com.wvars]

end Lax109476Proofs.RamArithmetic

end

section

namespace Lax109476Proofs.RamRational

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamArithmetic

theorem fractionValue_reduce (s n d:ℕ):
    fractionValue s (n / Nat.gcd n d) (d / Nat.gcd n d)=fractionValue s n d:=by
  have h:((n / Nat.gcd n d:ℕ):ℚ) / ((d / Nat.gcd n d:ℕ):ℚ)=(n:ℚ) / d:=
    Nat.cast_div_div_div_cancel_right (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)
  unfold fractionValue
  split_ifs
  · simpa only [neg_div] using congrArg Neg.neg h
  · exact h

theorem normalizeFraction_signed_spec (B s n d:ℕ) (hn:n < B) (hd:d < B) (hdpos:0 < d):
    Spec B (fun σ => σ.vars "rat.n"=n∧ σ.vars "rat.d"=d∧ σ.vars "rat.s"=s)
      normalizeFraction (fun _ σ' => σ'.vars "rat.n"=n / Nat.gcd n d∧
        σ'.vars "rat.d"=d / Nat.gcd n d∧ σ'.vars "rat.s"=s) (36 * d.size + 16):=by
  rintro σ ⟨hσn,hσd,hσs⟩
  obtain ⟨τ,hr,hτn,hτd⟩:=normalizeFraction_spec B n d hn hd hdpos σ ⟨hσn,hσd⟩
  have hτs:=hr.frame_var "rat.s" (by decide)
  exact ⟨τ,hr,hτn,hτd,hτs.trans hσs⟩

theorem fractionValue_num_den (s n d:ℕ) (hd:0 < d):
    (fractionValue s n d).num.natAbs=n / Nat.gcd n d∧
      (fractionValue s n d).den=d / Nat.gcd n d:=by
  have h:(((n:ℚ) / d).num.natAbs=n / Nat.gcd n d)∧
      ((n:ℚ) / d).den=d / Nat.gcd n d:=by
    have he:(n:ℚ) / d=mkRat (n:ℤ) d:=by simp [Rat.mkRat_eq_div]
    rw [he]
    simp [Rat.num_mkRat,Rat.den_mkRat,ne_of_gt hd,
      Int.natAbs_ediv_of_nonneg (by positivity:(0:ℤ)≤ n),Nat.gcd_comm]
  unfold fractionValue
  split_ifs
  · simpa only [neg_div,Rat.neg_num,Rat.neg_den,Int.natAbs_neg] using h
  · exact h

def FractionOutput (q:ℚ) (σ:Env):Prop:=
  fractionValue (σ.vars "rat.s") (σ.vars "rat.n") (σ.vars "rat.d")=q∧
    σ.vars "rat.n"=q.num.natAbs∧ σ.vars "rat.d"=q.den∧ σ.vars "rat.s" ≤ 1

theorem normalizeFraction_output_spec (B s n d:ℕ) (hs:s≤ 1)
    (hn:n < B) (hd:d < B) (hdpos:0 < d):
    Spec B (fun σ => σ.vars "rat.n"=n∧ σ.vars "rat.d"=d∧ σ.vars "rat.s"=s)
      normalizeFraction (fun _ σ' => FractionOutput (fractionValue s n d) σ')
      (36 * d.size + 16):=by
  apply (normalizeFraction_signed_spec B s n d hn hd hdpos).post
  rintro σ τ _ ⟨hτn,hτd,hτs⟩
  obtain ⟨hnum,hden⟩:=fractionValue_num_den s n d hdpos
  exact ⟨by rw [hτs,hτn,hτd]; exact fractionValue_reduce s n d,
    hτn.trans hnum.symm,hτd.trans hden.symm,hτs ▸ hs⟩

end Lax109476Proofs.RamRational

end

section

open scoped BigOperators

namespace Lax109476Proofs.RationalArithmeticBounds

open DeterminantBounds RationalSizeBounds
open Lax109476.RationalEncoding Lax759944.BinaryWordEncoding

theorem height_zero:Height 0 1:=by simp [Height]

theorem height_mono (q:ℚ) {B C:ℕ} (hq:Height q B) (hBC:B≤ C):Height q C:=
  ⟨hq.1.trans hBC,hq.2.trans hBC⟩

theorem height_mul (q r:ℚ) (B C:ℕ) (hq:Height q B) (hr:Height r C):
    Height (q * r) (B * C):=by
  have hd:(q.den:ℤ) * r.den ≠ 0:=by positivity
  have he:q * r=((q.num * r.num:ℤ):ℚ) / ((q.den:ℤ) * r.den):=by
    conv_lhs => rw [← q.num_div_den, ← r.num_div_den]
    push_cast
    ring
  rw [he]
  simp only [Int.cast_mul,Int.cast_natCast]
  obtain ⟨hn,hd'⟩:=integer_ratio_num_den_bound (q.num * r.num) _ hd
  simp only [Int.cast_mul,Int.cast_natCast] at hn hd'
  simp only [Int.natAbs_mul,Int.natAbs_natCast] at hn hd'
  exact ⟨hn.trans (Nat.mul_le_mul hq.1 hr.1),hd'.trans (Nat.mul_le_mul hq.2 hr.2)⟩

theorem height_add (q r:ℚ) (B C:ℕ) (hq:Height q B) (hr:Height r C):
    Height (q + r) (2 * B * C):=by
  have hd:(q.den:ℤ) * r.den ≠ 0:=by positivity
  have he:q + r=((q.num * r.den + r.num * q.den:ℤ):ℚ) /
      ((q.den:ℤ) * r.den):=by
    conv_lhs => rw [← q.num_div_den, ← r.num_div_den]
    push_cast
    field_simp
  rw [he]
  obtain ⟨hn,hd'⟩:=integer_ratio_num_den_bound (q.num * r.den + r.num * q.den) _ hd
  simp only [Int.cast_mul,Int.cast_natCast] at hn hd'
  have hb:(q.num * r.den + r.num * q.den:ℤ).natAbs≤ 2 * B * C:=by
    calc
      _≤ (q.num * r.den:ℤ).natAbs + (r.num * q.den:ℤ).natAbs:=Int.natAbs_add_le _ _
      _=q.num.natAbs * r.den + r.num.natAbs * q.den:=by simp [Int.natAbs_mul]
      _≤ B * C + C * B:=Nat.add_le_add (Nat.mul_le_mul hq.1 hr.2) (Nat.mul_le_mul hr.1 hq.2)
      _=_:=by ring
  refine ⟨hn.trans hb, ?_⟩
  simp only [Int.natAbs_mul,Int.natAbs_natCast] at hd'
  exact hd'.trans ((Nat.mul_le_mul hq.2 hr.2).trans (by nlinarith))

theorem height_neg (q:ℚ) (B:ℕ) (hq:Height q B):Height (-q) B:=by
  simpa only [Height,Rat.neg_num,Rat.neg_den,Int.natAbs_neg] using hq

theorem height_inv (q:ℚ) (B:ℕ) (hq:Height q B):Height q⁻¹ B:=by
  have hB:1≤ B:=le_trans q.den_pos hq.2
  by_cases hz:q=0
  · subst q
    simpa using height_mono 0 height_zero hB
  · have hnum:(q⁻¹).num.natAbs≤ q.den:=by
      rw [Rat.num_inv,Int.natAbs_mul]
      have hs:q.num.sign.natAbs≤ 1:=by
        have hsign:=Int.sign_trichotomy q.num
        rcases hsign with h | h | h <;> rw [h] <;> norm_num
      simpa using Nat.mul_le_mul_right q.den hs
    exact ⟨hnum.trans hq.2,by rw [Rat.den_inv_of_ne_zero hz]; exact hq.1⟩

theorem height_nat (v B:ℕ) (hv:v≤ B) (hB:1≤ B):Height (v:ℚ) B:=by
  simpa [Height] using And.intro hv hB

theorem height_sub (q r:ℚ) (B C:ℕ) (hq:Height q B) (hr:Height r C):
    Height (q - r) (2 * B * C):=by
  simpa only [sub_eq_add_neg] using height_add q (-r) B C hq (height_neg r C hr)

theorem height_div (q r:ℚ) (B C:ℕ) (hq:Height q B) (hr:Height r C):
    Height (q / r) (B * C):=by
  simpa only [div_eq_mul_inv] using height_mul q r⁻¹ B C hq (height_inv r C hr)

theorem height_pow (q:ℚ) (B k:ℕ) (hq:Height q B):Height (q ^ k) (B ^ k):=by
  induction k with
  | zero => simp [Height]
  | succ k ih => simpa only [pow_succ] using height_mul (q ^ k) q (B ^ k) B ih hq

theorem height_sum {ι:Type*} (s:Finset ι) (f:ι→ ℚ) (B:ℕ)
    (hf:∀ i∈ s,Height (f i) B):
    Height (∑ i∈ s,f i) ((2 * B) ^ s.card):=by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using height_zero
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.card_insert_of_notMem hi,pow_succ]
    have h:=height_add (f i) (∑ j∈ s,f j) B ((2 * B) ^ s.card)
      (hf i (Finset.mem_insert_self _ _)) (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
    convert h using 1
    ring

end Lax109476Proofs.RationalArithmeticBounds

end

section

namespace Lax109476Proofs.RamPrimitiveBounds

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRounding RationalSizeBounds RationalArithmeticBounds

theorem fractionValue_height (s n d M:ℕ) (hn:n≤ M) (hd:d≤ M) (hdpos:0 < d):
    Height (fractionValue s n d) M:=by
  obtain ⟨hnum,hden⟩:=fractionValue_num_den s n d hdpos
  exact ⟨by rw [hnum]; exact (Nat.div_le_self _ _).trans hn,
    by rw [hden]; exact (Nat.div_le_self _ _).trans hd⟩

end Lax109476Proofs.RamPrimitiveBounds

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

theorem writeReducedFraction_spec (B:ℕ) (q:ℚ) (hB:1 < B)
    (hn:q.num.natAbs < B) (hd:q.den < B):
    Spec B (FractionOutput q) writeReducedFraction
      (fun σ τ => τ.out=σ.out ++ encodeRational q) 10:=by
  intro σ hσ
  obtain ⟨hv,hσn,hσd,hσs⟩:=hσ
  have hnB:σ.vars "rat.n" < B:=hσn ▸ hn
  have hdB:σ.vars "rat.d" < B:=hσd ▸ hd
  have hsB:σ.vars "rat.s" < B:=hσs.trans_lt hB
  have hsign:=fractionValue_sign (σ.vars "rat.s") (σ.vars "rat.n")
    (σ.vars "rat.d") hσs (hσd ▸ q.den_pos)
  rw [hv] at hsign
  (expose_names;
    refine
        let c0:Prop:= @Eq Nat (Env.vars σ "rat.n") ((0:Nat));
        let c1:Prop:=Not c0;
        let c2:List Nat→ List Nat→ List Nat:=
          @HAppend.hAppend (List Nat) (List Nat) (List Nat) (@instHAppendOfAppend (List Nat) (@List.instAppend Nat));
        let c3:Env→ Prop:=(fun (σ τ:Env) => @Eq (List Nat) (Env.out τ) (c2 (Env.out σ) (encodeRational q))) σ;
        let c4:Env→ Prop:=fun (σ':Env) =>
          And (Run B writeReducedFraction σ σ' ((10:Nat))) (c3 σ');
        let c5:∀ (w:Env),c4 w→ @Exists Env c4:= @Exists.intro Env c4;
        let c6:List Nat→ Env:=Env.mk (Env.vars σ) (Env.arrs σ) (Env.inp σ);
        let c7:List Nat→ List Nat:=c2 (Env.out σ);
        let c8:Env:=
          c6 (c7 (@List.cons Nat ((0:Nat)) (@List.nil Nat)));
        let c9:String→ Nat:=Env.vars c8;
        let c10:Nat:=c9 "rat.n";
        let c11:Env:=Env.mk c9 (Env.arrs c8) (Env.inp c8) (c2 (Env.out c8) (@List.cons Nat c10 (@List.nil Nat)));
        let c12:String→ Nat:=Env.vars c11;
        let c13:Nat:=c12 "rat.d";
        let c14:Env:=Env.mk c12 (Env.arrs c11) (Env.inp c11) (c2 (Env.out c11) (@List.cons Nat c13 (@List.nil Nat)));
        let c15:Nat→ Nat→ Nat:=Nat.add;
        let c16:Nat→ Nat:=c15 ((1:Nat));
        let c17:Cond:=Cond.eq (Expr.var "rat.n") (Expr.lit ((0:Nat)));
        let c18:Nat→ Nat:=c15 (c16 (Cond.size c17));
        let c19:Nat:=c16 (Expr.size (Expr.lit ((0:Nat))));
        let c20:Nat:=c18 c19;
        let c21:Nat:=c16 (Expr.size (Expr.var "rat.n"));
        let c22:Nat:=c16 (Expr.size (Expr.var "rat.d"));
        let c23:Nat:=c15 c21 c22;
        let c24:Com:=Com.write (Expr.lit ((0:Nat)));
        let c25:
          ∀ (σ' σ'':Env) (K K':Nat),
            Run B (Com.ite c17 c24 (Com.write (Expr.var "rat.s"))) σ σ' K→
              Run B (Com.seq (Com.write (Expr.var "rat.n")) (Com.write (Expr.var "rat.d"))) σ' σ'' K'→
                Run B
                  (Com.seq (Com.ite c17 c24 (Com.write (Expr.var "rat.s")))
                    (Com.seq (Com.write (Expr.var "rat.n")) (Com.write (Expr.var "rat.d"))))
                  σ σ'' (Nat.add K K'):=
          RunStep.seq B (Com.ite c17 c24 (Com.write (Expr.var "rat.s")))
            (Com.seq (Com.write (Expr.var "rat.n")) (Com.write (Expr.var "rat.d"))) σ;
        let c26:
          @Eq (Option Nat) (Expr.evalB B (Expr.lit ((0:Nat))) σ)
            (@some Nat ((0:Nat))):=
          RunStep.eval_lit B ((0:Nat)) σ
            (?nAX_g3947_0_0_0);
        let c27:
          ∀ (σ σ' σ'':Env) (K K':Nat),
            Run B (Com.write (Expr.var "rat.n")) σ σ' K→
              Run B (Com.write (Expr.var "rat.d")) σ' σ'' K'→
                Run B (Com.seq (Com.write (Expr.var "rat.n")) (Com.write (Expr.var "rat.d"))) σ σ''
                  (Nat.add K K'):=
          RunStep.seq B (Com.write (Expr.var "rat.n")) (Com.write (Expr.var "rat.d"));
        let c28:List Nat:=c7 (encodeRational q);
        let c29:Env:=c6 (c7 (@List.cons Nat (Env.vars σ "rat.s") (@List.nil Nat)));
        let c30:String→ Nat:=Env.vars c29;
        let c31:Nat:=c30 "rat.n";
        let c32:Env:=Env.mk c30 (Env.arrs c29) (Env.inp c29) (c2 (Env.out c29) (@List.cons Nat c31 (@List.nil Nat)));
        let c33:String→ Nat:=Env.vars c32;
        let c34:Nat:=c33 "rat.d";
        let c35:Env:=Env.mk c33 (Env.arrs c32) (Env.inp c32) (c2 (Env.out c32) (@List.cons Nat c34 (@List.nil Nat)));
        let c36:Nat:=c16 (Expr.size (Expr.var "rat.s"));
        let c37:Nat:=c18 c36;
        @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c4) (Classical.em c0)
          (fun (hcase:c0) =>
            c5 c14
              (@And.intro (Run B writeReducedFraction σ c14 ((10:Nat)))
                (c3 c14)
                (RunStep.mono B writeReducedFraction σ c14 (c15 c20 c23)
                  ((10:Nat))
                  (c25 c8 c14 c20 c23
                    (RunStep.ite_true B c17 c24 (Com.write (Expr.var "rat.s")) σ c8 c19
                      (RunStep.cond_eq_true B σ (Expr.var "rat.n")
                        (Expr.lit ((0:Nat))) (Env.vars σ "rat.n")
                        ((0:Nat)) (RunStep.eval_var B σ "rat.n" hnB) c26
                        hcase)
                      (RunStep.write B σ (Expr.lit ((0:Nat)))
                        ((0:Nat)) c26))
                    (c27 c8 c11 c14 c21 c22
                      (RunStep.write B c8 (Expr.var "rat.n") c10 (RunStep.eval_var B c8 "rat.n" hnB))
                      (RunStep.write B c11 (Expr.var "rat.d") c13 (RunStep.eval_var B c11 "rat.d" hdB))))
                  (?nAX_g3947_0_0_1))
                ?_))
          fun (hcase:c1) =>
          c5 c35
            (@And.intro (Run B writeReducedFraction σ c35 ((10:Nat)))
              (c3 c35)
              (RunStep.mono B writeReducedFraction σ c35 (c15 c37 c23)
                ((10:Nat))
                (c25 c29 c35 c37 c23
                  (RunStep.ite_false B c17 c24 (Com.write (Expr.var "rat.s")) σ c29 c36
                    (RunStep.cond_eq_false B σ (Expr.var "rat.n")
                      (Expr.lit ((0:Nat))) (Env.vars σ "rat.n")
                      ((0:Nat)) (RunStep.eval_var B σ "rat.n" hnB) c26
                      hcase)
                    (RunStep.write B σ (Expr.var "rat.s") (Env.vars σ "rat.s") (RunStep.eval_var B σ "rat.s" hsB)))
                  (c27 c29 c32 c35 c21 c22
                    (RunStep.write B c29 (Expr.var "rat.n") c31 (RunStep.eval_var B c29 "rat.n" hnB))
                    (RunStep.write B c32 (Expr.var "rat.d") c34 (RunStep.eval_var B c32 "rat.d" hdB))))
                (?nAX_g3947_0_0_2))
              ?_) <;> try dsimp +zetaDelta at *
   all_goals try dsimp +zetaDelta at *
   try case nAX_g3947_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g3947_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g3947_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all
  )
  all_goals simp_all [encodeRational,List.append_assoc]

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
    refine
        let c0:Env→ Prop:=
          LeftOutput
            (@getElem (List Rat) Nat Rat (fun (as:List Rat) (i:Nat) => Nat.lt i (@List.length Rat as))
              (@List.instGetElemNatLtLength Rat) qs i hi);
        let c1:Env→ Prop:=(fun (x τ:Env) => c0 τ) σ;
        let c2:String→ String:=
          @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a;
        let c3:String:=c2 ".s";
        let c4:Nat:=
          @List.getD Nat (Env.arrs σ c3) (Env.vars σ "vec.i") ((0:Nat));
        let c5:Env:=Env.setVar σ "left.s" c4;
        let c6:String:=c2 ".n";
        let c7:Nat:=Env.vars c5 "vec.i";
        let c8:Nat:= @List.getD Nat (Env.arrs c5 c6) c7 ((0:Nat));
        let c9:Env:=Env.setVar c5 "left.n" c8;
        let c10:String:=c2 ".d";
        let c11:Nat:=Env.vars c9 "vec.i";
        let c12:Nat:= @List.getD Nat (Env.arrs c9 c10) c11 ((0:Nat));
        let c13:Env:=Env.setVar c9 "left.d" c12;
        let c14:Nat→ Nat→ Nat:=Nat.add;
        let c15:Nat→ Nat:=c14 ((1:Nat));
        let c16:Expr:=Expr.get c3 (Expr.var "vec.i");
        let c17:Nat:=c15 (Expr.size c16);
        let c18:Expr:=Expr.get c6 (Expr.var "vec.i");
        let c19:Nat:=c15 (Expr.size c18);
        let c20:Expr:=Expr.get c10 (Expr.var "vec.i");
        let c21:Nat:=c15 (Expr.size c20);
        let c22:Nat:=c14 c19 c21;
        let c23:Com:=Com.assign "left.n" c18;
        let c24:Com:=Com.assign "left.d" c20;
        @Exists.intro Env
          (fun (σ':Env) =>
            And (Run B (loadLeft a) σ σ' ((9:Nat))) (c1 σ'))
          c13
          (@And.intro (Run B (loadLeft a) σ c13 ((9:Nat))) (c1 c13)
            (RunStep.mono B (loadLeft a) σ c13 (c14 c17 c22) ((9:Nat))
              (RunStep.seq B (Com.assign "left.s" c16) (Com.seq c23 c24) σ c5 c13 c17 c22
                (RunStep.assign B σ "left.s" c16 c4
                  (RunStep.eval_get B σ c3 (Expr.var "vec.i") (Env.vars σ "vec.i")
                    (RunStep.eval_var B σ "vec.i"
                      (?nAX_g3955_0_0_0))
                    (?nAX_g3955_0_0_1)
                    ?_))
                (RunStep.seq B c23 c24 c5 c9 c13 c19 c21
                  (RunStep.assign B c5 "left.n" c18 c8
                    (RunStep.eval_get B c5 c6 (Expr.var "vec.i") c7
                      (RunStep.eval_var B c5 "vec.i"
                        (?nAX_g3955_0_0_2))
                      (?nAX_g3955_0_0_3)
                      ?_))
                  (RunStep.assign B c9 "left.d" c20 c12
                    (RunStep.eval_get B c9 c10 (Expr.var "vec.i") c11
                      (RunStep.eval_var B c9 "vec.i"
                        (?nAX_g3955_0_0_4))
                      (?nAX_g3955_0_0_5)
                      ?_))))
              (?nAX_g3955_0_0_6))
            ?_) <;> try dsimp +zetaDelta at *
   all_goals try dsimp +zetaDelta at *
   try case nAX_g3955_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g3955_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g3955_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g3955_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g3955_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g3955_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g3955_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all
  )
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
    refine
        let c0:Prop:= @Eq Nat (Env.vars σ "rat.n") ((0:Nat));
        let c1:Prop:=Not c0;
        let c2:Env→ Prop:=Represents a (@List.set Rat qs i q);
        let c3:Env→ Prop:=(fun (x τ:Env) => c2 τ) σ;
        let c4:Env→ Prop:=fun (σ':Env) =>
          And (Run B (storeReduced a) σ σ' ((13:Nat))) (c3 σ');
        let c5:∀ (w:Env),c4 w→ @Exists Env c4:= @Exists.intro Env c4;
        let c6:String→ String:=
          @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a;
        let c7:String:=c6 ".s";
        let c8:Nat→ Env:=Env.setArr σ c7 (Env.vars σ "vec.i");
        let c9:Env:=c8 ((0:Nat));
        let c10:String:=c6 ".n";
        let c11:String→ Nat:=Env.vars c9;
        let c12:Nat:=c11 "vec.i";
        let c13:Nat:=c11 "rat.n";
        let c14:Env:=Env.setArr c9 c10 c12 c13;
        let c15:String:=c6 ".d";
        let c16:String→ Nat:=Env.vars c14;
        let c17:Nat:=c16 "vec.i";
        let c18:Nat:=c16 "rat.d";
        let c19:Env:=Env.setArr c14 c15 c17 c18;
        let c20:Nat→ Nat→ Nat:=Nat.add;
        let c21:Nat→ Nat:=c20 ((1:Nat));
        let c22:Cond:=Cond.eq (Expr.var "rat.n") (Expr.lit ((0:Nat)));
        let c23:Nat→ Nat:=c20 (c21 (Cond.size c22));
        let c24:Nat→ Nat:=c20 (c21 (Expr.size (Expr.var "vec.i")));
        let c25:Nat:=c24 (Expr.size (Expr.lit ((0:Nat))));
        let c26:Nat:=c23 c25;
        let c27:Nat:=c24 (Expr.size (Expr.var "rat.n"));
        let c28:Nat:=c24 (Expr.size (Expr.var "rat.d"));
        let c29:Nat:=c20 c27 c28;
        let c30:Expr→ Com:=Com.store c7 (Expr.var "vec.i");
        let c31:Com:=c30 (Expr.lit ((0:Nat)));
        let c32:Com:=c30 (Expr.var "rat.s");
        let c33:Com:=Com.store c10 (Expr.var "vec.i") (Expr.var "rat.n");
        let c34:Com:=Com.store c15 (Expr.var "vec.i") (Expr.var "rat.d");
        let c35:
          ∀ (σ' σ'':Env) (K K':Nat),
            Run B (Com.ite c22 c31 c32) σ σ' K→
              Run B (Com.seq c33 c34) σ' σ'' K'→
                Run B (Com.seq (Com.ite c22 c31 c32) (Com.seq c33 c34)) σ σ''
                  (Nat.add K K'):=
          RunStep.seq B (Com.ite c22 c31 c32) (Com.seq c33 c34) σ;
        let c36:
          @Eq (Option Nat) (Expr.evalB B (Expr.lit ((0:Nat))) σ)
            (@some Nat ((0:Nat))):=
          RunStep.eval_lit B ((0:Nat)) σ
            (?nAX_g3962_0_0_0);
        let c37:
          ∀ (e:Expr) (idx v:Nat),
            @Eq (Option Nat) (Expr.evalB B (Expr.var "vec.i") σ) (@some Nat idx)→
              @Eq (Option Nat) (Expr.evalB B e σ) (@some Nat v)→
                Nat.lt idx (@List.length Nat (Env.arrs σ c7))→
                  Run B (Com.store c7 (Expr.var "vec.i") e) σ (Env.setArr σ c7 idx v)
                    (Nat.add
                      (Nat.add
                        ((1:Nat)) (Expr.size (Expr.var "vec.i")))
                      (Expr.size e)):=
          RunStep.store B σ c7 (Expr.var "vec.i");
        let c38:
          ∀ (σ σ' σ'':Env) (K K':Nat),
            Run B c33 σ σ' K→
              Run B c34 σ' σ'' K'→
                Run B (Com.seq c33 c34) σ σ'' (Nat.add K K'):=
          RunStep.seq B c33 c34;
        let c39:
          ∀ (x:String),
            Nat.lt (Env.vars c9 x) B→
              @Eq (Option Nat) (Expr.evalB B (Expr.var x) c9) (@some Nat (Env.vars c9 x)):=
          RunStep.eval_var B c9;
        let c40:
          ∀ (x:String),
            Nat.lt (Env.vars c14 x) B→
              @Eq (Option Nat) (Expr.evalB B (Expr.var x) c14) (@some Nat (Env.vars c14 x)):=
          RunStep.eval_var B c14;
        let c41:Env:=c8 (Env.vars σ "rat.s");
        let c42:String→ Nat:=Env.vars c41;
        let c43:Nat:=c42 "vec.i";
        let c44:Nat:=c42 "rat.n";
        let c45:Env:=Env.setArr c41 c10 c43 c44;
        let c46:String→ Nat:=Env.vars c45;
        let c47:Nat:=c46 "vec.i";
        let c48:Nat:=c46 "rat.d";
        let c49:Env:=Env.setArr c45 c15 c47 c48;
        let c50:Nat:=c24 (Expr.size (Expr.var "rat.s"));
        let c51:Nat:=c23 c50;
        let c52:
          ∀ (x:String),
            Nat.lt (Env.vars c41 x) B→
              @Eq (Option Nat) (Expr.evalB B (Expr.var x) c41) (@some Nat (Env.vars c41 x)):=
          RunStep.eval_var B c41;
        let c53:
          ∀ (x:String),
            Nat.lt (Env.vars c45 x) B→
              @Eq (Option Nat) (Expr.evalB B (Expr.var x) c45) (@some Nat (Env.vars c45 x)):=
          RunStep.eval_var B c45;
        @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c4) (Classical.em c0)
          (fun (hcase:c0) =>
            c5 c19
              (@And.intro (Run B (storeReduced a) σ c19 ((13:Nat)))
                (c3 c19)
                (RunStep.mono B (storeReduced a) σ c19 (c20 c26 c29)
                  ((13:Nat))
                  (c35 c9 c19 c26 c29
                    (RunStep.ite_true B c22 c31 c32 σ c9 c25
                      (RunStep.cond_eq_true B σ (Expr.var "rat.n")
                        (Expr.lit ((0:Nat))) (Env.vars σ "rat.n")
                        ((0:Nat)) (RunStep.eval_var B σ "rat.n" hnB) c36
                        hcase)
                      (c37 (Expr.lit ((0:Nat))) (Env.vars σ "vec.i")
                        ((0:Nat))
                        (RunStep.eval_var B σ "vec.i"
                          (?nAX_g3962_0_0_1))
                        c36
                        (?nAX_g3962_0_0_2)))
                    (c38 c9 c14 c19 c27 c28
                      (RunStep.store B c9 c10 (Expr.var "vec.i") (Expr.var "rat.n") c12 c13
                        (c39 "vec.i"
                          (?nAX_g3962_0_0_3))
                        (c39 "rat.n"
                          (?nAX_g3962_0_0_4))
                        (?nAX_g3962_0_0_5))
                      (RunStep.store B c14 c15 (Expr.var "vec.i") (Expr.var "rat.d") c17 c18
                        (c40 "vec.i"
                          (?nAX_g3962_0_0_6))
                        (c40 "rat.d"
                          (?nAX_g3962_0_0_7))
                        (?nAX_g3962_0_0_8))))
                  (?nAX_g3962_0_0_9))
                ?_))
          fun (hcase:c1) =>
          c5 c49
            (@And.intro (Run B (storeReduced a) σ c49 ((13:Nat)))
              (c3 c49)
              (RunStep.mono B (storeReduced a) σ c49 (c20 c51 c29)
                ((13:Nat))
                (c35 c41 c49 c51 c29
                  (RunStep.ite_false B c22 c31 c32 σ c41 c50
                    (RunStep.cond_eq_false B σ (Expr.var "rat.n")
                      (Expr.lit ((0:Nat))) (Env.vars σ "rat.n")
                      ((0:Nat)) (RunStep.eval_var B σ "rat.n" hnB) c36
                      hcase)
                    (c37 (Expr.var "rat.s") (Env.vars σ "vec.i") (Env.vars σ "rat.s")
                      (RunStep.eval_var B σ "vec.i"
                        (?nAX_g3962_0_0_10))
                      (RunStep.eval_var B σ "rat.s" hsB)
                      (?nAX_g3962_0_0_11)))
                  (c38 c41 c45 c49 c27 c28
                    (RunStep.store B c41 c10 (Expr.var "vec.i") (Expr.var "rat.n") c43 c44
                      (c52 "vec.i"
                        (?nAX_g3962_0_0_12))
                      (c52 "rat.n"
                        (?nAX_g3962_0_0_13))
                      (?nAX_g3962_0_0_14))
                    (RunStep.store B c45 c15 (Expr.var "vec.i") (Expr.var "rat.d") c47 c48
                      (c53 "vec.i"
                        (?nAX_g3962_0_0_15))
                      (c53 "rat.d"
                        (?nAX_g3962_0_0_16))
                      (?nAX_g3962_0_0_17))))
                (?nAX_g3962_0_0_18))
              ?_) <;> try dsimp +zetaDelta at *
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
  all_goals simp_all [Represents,Env.setArr,List.map_set]

end Lax109476Proofs.RamRationalArrays

end

section

namespace Lax109476Proofs.RamFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def FieldsAgree (fields:List String) (σ τ:Env):Prop:=
  ∀ x∈ fields,τ.vars x=σ.vars x

theorem fieldsAgree_trans (fields:List String) (σ τ υ:Env)
    (hστ:FieldsAgree fields σ τ) (hτυ:FieldsAgree fields τ υ):FieldsAgree fields σ υ:=
  fun x hx => (hτυ x hx).trans (hστ x hx)

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

open scoped BigOperators Matrix

namespace Lax109476Proofs.EllipsoidArithmeticBounds

open RationalArithmeticBounds RationalRounding Matrix
open EllipsoidBounds EllipsoidCenter

theorem height_roundDown (q:ℚ) (B D:ℕ) (hq:Height q B) (hD:0 < D):
    Height (roundDown q D) (B * D + 1):=by
  have hb:1≤ B:=q.den_pos.trans_le hq.2
  have hg:=grid_num_den_bound (Int.floor (q * D)) D hD
  have hn:=roundDown_floor_bound q D
  exact ⟨hg.1.trans (hn.trans (Nat.add_le_add_right (Nat.mul_le_mul_right D hq.1) 1)),
    hg.2.trans (by nlinarith)⟩

theorem height_sqrtUpper (q:ℚ) (B D:ℕ) (hq:Height q B) (hD:0 < D):
    Height (sqrtUpper q D) (B * D ^ 2 + 1):=by
  have hb:1≤ B:=q.den_pos.trans_le hq.2
  have hqB:q≤ (B:ℚ):=by
    have hden:(0:ℚ) < q.den:=by positivity
    have hden1:(1:ℚ)≤ q.den:=by exact_mod_cast q.den_pos
    have hn:(q.num:ℚ)≤ B:=by
      have hnabs:q.num≤ (q.num.natAbs:ℤ):=Int.le_natAbs
      have hc':(q.num:ℚ)≤ ((q.num.natAbs:ℤ):ℚ):=Int.cast_le.mpr hnabs
      have hc:(q.num:ℚ)≤ (q.num.natAbs:ℚ):=by simpa only [Int.cast_natCast] using hc'
      exact hc.trans (by exact_mod_cast hq.1)
    rw [← q.num_div_den]
    apply (div_le_iff₀ hden).mpr
    exact hn.trans (by nlinarith)
  have hc:Nat.ceil (q * (D:ℚ) ^ 2)≤ B * D ^ 2:=by
    apply Nat.ceil_le.mpr
    exact_mod_cast mul_le_mul_of_nonneg_right hqB (sq_nonneg (D:ℚ))
  have hs:Nat.sqrt (Nat.ceil (q * (D:ℚ) ^ 2))≤ B * D ^ 2:=
    (Nat.sqrt_le_self _).trans hc
  have hg:=grid_num_den_bound
    ((Nat.sqrt (Nat.ceil (q * (D:ℚ) ^ 2)) + 1:ℕ):ℤ) D hD
  simp only [Int.cast_natCast,Int.natAbs_natCast] at hg
  exact ⟨hg.1.trans (Nat.add_le_add_right hs 1),hg.2.trans (by nlinarith)⟩

end Lax109476Proofs.EllipsoidArithmeticBounds

end

section

namespace Lax109476Proofs.RamCenterCoordinate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFractionInterface RamFrame RationalArithmeticBounds

theorem centerCap_bounds (M:ℕ) (hM:1≤ M):
    M≤ centerCap M∧ M ^ 2≤ centerCap M∧ 2 * M ^ 3≤ centerCap M∧
      2 * M ^ 4 + 1≤ centerCap M:=by
  have hbase:1≤ M + 1:=by omega
  have h₂:=(Nat.pow_le_pow_left (by omega:M≤ M + 1) 2).trans
    (Nat.pow_le_pow_right hbase (by omega:2≤ 4))
  have h₃:=(Nat.pow_le_pow_left (by omega:M≤ M + 1) 3).trans
    (Nat.pow_le_pow_right hbase (by omega:3≤ 4))
  have h₄:=Nat.pow_le_pow_left (by omega:M≤ M + 1) 4
  have hm:=le_self_pow hM (by decide:(2:ℕ) ≠ 0)
  unfold centerCap
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

end Lax109476Proofs.RamCenterCoordinate

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

def centerValues {n:ℕ} (u c:Fin n→ ℚ) (gamma:ℚ) (D:ℕ):Fin n→ ℚ:=
  fun j => RationalRounding.roundDown (c j - u j * gamma) D

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

theorem centerCap_size (M:ℕ):(centerCap M).size≤ 4 * M.size + 8:=by
  have hb:=RationalSizeBounds.size_add_one_le M
  have hp:=RationalSizeBounds.size_pow_le (M + 1) 4
  have hm:=RationalSizeBounds.size_mul_le 2 ((M + 1) ^ 4)
  have ha:=RationalSizeBounds.size_add_one_le (2 * (M + 1) ^ 4)
  have htwo:Nat.size 2=2:=by decide
  unfold centerCap
  omega

theorem updateCenter_cost_polynomial (n M:ℕ):
    33 * n + 18 + ((180 * (centerCap M).size + 318 + 4 + 4) * n + 6)≤
      (720 * M.size + 1799) * n + 24:=by
  have hm:=Nat.mul_le_mul_left 180 (centerCap_size M)
  have hn:=Nat.mul_le_mul_right n (Nat.add_le_add_right hm 359)
  convert Nat.add_le_add_right hn 24 using 1 <;> ring

theorem centerValues_eq_roundedCenter {n:ℕ} (A:Matrix (Fin n) (Fin n) ℚ)
    (a c:Fin n→ ℚ) (D:ℕ):
    centerValues (A *ᵥ a) c (1 / (((n:ℚ) + 1) * RationalRounding.sqrtUpper (a ⬝ᵥ (A *ᵥ a)) D)) D =
      EllipsoidCenter.roundedCenter n A a c D:=by
  funext i
  simp only [centerValues,EllipsoidCenter.roundedCenter,EllipsoidCenter.approximateCenter,
    Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  rw [mul_comm]

end Lax109476Proofs.RamCenterUpdate

end

section

namespace Lax109476Proofs.RamCopy

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds

theorem leftToResult_spec (B:ℕ) (q:ℚ) (h1:1 < B)
    (hn:q.num.natAbs < B) (hd:q.den < B):
    Spec B (LeftOutput q) leftToResult (fun _ τ => FractionOutput q τ) 6:=by
  rintro σ ⟨hσs,hσn,hσd⟩
  have hs:σ.vars "left.s" < B:=hσs ▸ (rationalSign_le_one q).trans_lt h1
  (expose_names;
    refine
        let c0:Nat:=Env.vars (Env.setVar σ "rat.s" (Env.vars σ "left.s")) "left.n";
        let c1:Env:=Env.setVar (Env.setVar σ "rat.s" (Env.vars σ "left.s")) "rat.n" c0;
        let c2:Nat:=Env.vars c1 "left.d";
        let c3:Env:=Env.setVar c1 "rat.d" c2;
        let c4:Nat→ Nat→ Nat:=Nat.add;
        let c5:Nat→ Nat:=c4 ((1:Nat));
        let c6:Nat:=c5 (Expr.size (Expr.var "left.s"));
        let c7:Nat:=c5 (Expr.size (Expr.var "left.n"));
        let c8:Nat:=c5 (Expr.size (Expr.var "left.d"));
        let c9:Nat:=c4 c7 c8;
        @Exists.intro Env
          (fun (σ':Env) =>
            And (Run B leftToResult σ σ' ((6:Nat)))
              ((fun (x τ:Env) => FractionOutput q τ) σ σ'))
          c3
          (@And.intro (Run B leftToResult σ c3 ((6:Nat)))
            ((fun (x τ:Env) => FractionOutput q τ) σ c3)
            (RunStep.mono B leftToResult σ c3 (c4 c6 c9) ((6:Nat))
              (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s"))
                (Com.seq (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d"))) σ
                (Env.setVar σ "rat.s" (Env.vars σ "left.s")) c3 c6 c9
                (RunStep.assign B σ "rat.s" (Expr.var "left.s") (Env.vars σ "left.s") (RunStep.eval_var B σ "left.s" hs))
                (RunStep.seq B (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d"))
                  (Env.setVar σ "rat.s" (Env.vars σ "left.s")) c1 c3 c7 c8
                  (RunStep.assign B (Env.setVar σ "rat.s" (Env.vars σ "left.s")) "rat.n" (Expr.var "left.n") c0
                    (RunStep.eval_var B (Env.setVar σ "rat.s" (Env.vars σ "left.s")) "left.n"
                      (?nAX_g4081_0_0_0)))
                  (RunStep.assign B c1 "rat.d" (Expr.var "left.d") c2
                    (RunStep.eval_var B c1 "left.d"
                      (?nAX_g4081_0_0_1)))))
              (?nAX_g4081_0_0_2))
            ?_) <;> try dsimp +zetaDelta at *
   all_goals try dsimp +zetaDelta at *
   try case nAX_g4081_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g4081_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g4081_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all
  )
  all_goals simp_all [FractionOutput,canonical_fractionValue,rationalSign_le_one]

end Lax109476Proofs.RamCopy

end

section

namespace Lax109476Proofs.RamArrayResult

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamRationalScalars

theorem load_spec (B:ℕ) (a:String) (xs:List ℚ) (i:ℕ) (hi:i < xs.length)
    (h1:1 < B) (hiB:i < B) (hn:xs[i].num.natAbs < B) (hd:xs[i].den < B):
    Spec B (fun σ => Represents a xs σ∧ σ.vars "vec.i"=i) (load a)
      (fun _ τ => FractionOutput xs[i] τ) 15:=by
  intro σ hσ
  obtain ⟨τ,hr₁,hτ⟩:=loadLeft_spec B a xs i hi h1 hiB hn hd σ hσ
  obtain ⟨υ,hr₂,hυ⟩:=RamCopy.leftToResult_spec B xs[i] h1 hn hd τ hτ
  exact ⟨υ,hr₁.seq hr₂,hυ⟩

end Lax109476Proofs.RamArrayResult

end

section

namespace Lax109476Proofs.RamInput

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem safeRead_spec (B:ℕ) (x:String) (xs:List ℕ) (v:ℕ)
    (h1:1 < B) (hxsB:xs.length < B) (hv:v≤ 1)
    (hxv:x ≠ "input.valid") (hxr:x ≠ "input.remaining"):
    Spec B (fun σ => σ.inp=xs∧ σ.vars "input.remaining"=xs.length∧
        σ.vars "input.valid"=v∧ σ.InpBounded B)
      (safeRead x)
      (fun _ τ => τ.vars x=xs.headD 0∧ τ.inp=xs.tail∧
        τ.vars "input.remaining"=xs.length - 1∧
        τ.vars "input.valid"=if xs=[] then 0 else v) 9:=by
  rintro σ ⟨hσinp,hσlen,hσvalid,hσbound⟩
  have hrv:"input.remaining" ≠ x:=Ne.symm hxr
  have hvx:"input.valid" ≠ x:=Ne.symm hxv
  cases xs with
  | nil =>
    have hb:(Cond.lt (.lit 0) (.var "input.remaining")).evalB B σ=some false:=by
      simpa [hσlen] using (evalB_condLt (evalB_lit (by omega:0 < B))
        (evalB_var (B:=B) (σ:=σ) (x:= "input.remaining") (by simpa [hσlen] using hxsB)))
    have hr₁:Run B (.assign "input.valid" (.lit 0)) σ (σ.setVar "input.valid" 0) 2:=
      Run.assign (evalB_lit (by omega))
    have hr₂:Run B (.assign x (.lit 0)) (σ.setVar "input.valid" 0)
        ((σ.setVar "input.valid" 0).setVar x 0) 2:=Run.assign (evalB_lit (by omega))
    refine ⟨_, (Run.ite_false hb (hr₁.seq hr₂)).mono (by simp only [Cond.size,Expr.size]; omega), ?_⟩
    simp_all [hxv,hxr,Env.setVar]
  | cons a rest =>
    have hrestB:rest.length < B:=by simp only [List.length_cons] at hxsB; omega
    have haB:a < B:=by
      apply hσbound a
      rw [hσinp]
      simp
    have hb:(Cond.lt (.lit 0) (.var "input.remaining")).evalB B σ=some true:=by
      simpa [hσlen] using (evalB_condLt (evalB_lit (by omega:0 < B))
        (evalB_var (B:=B) (σ:=σ) (x:= "input.remaining") (by simpa [hσlen] using hxsB)))
    have hr₁:Run B (.read x) σ {σ.setVar x a with inp:=rest} 1:=Run.read hσinp
    have he:(Expr.sub (.var "input.remaining") (.lit 1)).evalB B {σ.setVar x a with inp:=rest} =
        some rest.length:=by
      have hvar:({σ.setVar x a with inp:=rest}:Env).vars "input.remaining"=rest.length + 1:=by
        simp [Env.setVar,hrv,hσlen]
      apply evalB_bin_iff.mpr
      refine ⟨rest.length + 1,1, ?_,evalB_lit h1,by simp [Bop.apply],hrestB⟩
      apply evalB_var_iff.mpr
      exact ⟨hvar.symm,by rw [hvar]; exact hxsB⟩
    have hr₂:=Run.assign (x:= "input.remaining") he
    refine ⟨_, (Run.ite_true hb (hr₁.seq hr₂)).mono (by simp only [Cond.size,Expr.size]; omega), ?_⟩
    simp_all [hxv,hxr,Env.setVar]

end Lax109476Proofs.RamInput

end

section

namespace Lax109476Proofs.WordDecoding

open Lax109476.LinearProgram Lax109476.RationalEncoding

def signedNumerator (sign magnitude:ℕ):ℤ:=
  if sign=1 then -(magnitude:ℤ) else magnitude

def readRational:List ℕ→ Option (ℚ × List ℕ)
  | sign::magnitude::denominator::rest =>
    if sign≤ 1∧ 0 < denominator then
      some ((signedNumerator sign magnitude:ℚ) / denominator,rest)
    else none
  | _ => none

theorem signedNumerator_encode (q:ℚ):
    signedNumerator (if q.num < 0 then 1 else 0) q.num.natAbs=q.num:=by
  unfold signedNumerator
  by_cases h:q.num < 0
  · simp [h,abs_of_neg h]
  · simp [h,abs_of_nonneg (le_of_not_gt h)]

theorem readRational_encode (q:ℚ) (rest:List ℕ):
    readRational (encodeRational q ++ rest)=some (q,rest):=by
  have hs:(if q.num < 0 then 1 else 0:ℕ)≤ 1:=by split_ifs <;> omega
  simp only [encodeRational,List.cons_append,List.nil_append,readRational,
    if_pos (And.intro hs q.den_pos),signedNumerator_encode,Rat.num_div_den]

def readVector:(n:ℕ)→ List ℕ→ Option ((Fin n→ ℚ) × List ℕ)
  | 0,xs => some (0,xs)
  | n + 1,xs => do
    let (q,rest) ← readRational xs
    let (x,tail) ← readVector n rest
    pure (Fin.cons q x,tail)

theorem encodeVector_cons (n:ℕ) (q:ℚ) (x:Fin n→ ℚ):
    encodeVector (Fin.cons q x)=encodeRational q ++ encodeVector x:=by
  simp [encodeVector,List.ofFn_succ]

theorem readVector_encode (n:ℕ) (x:Fin n→ ℚ) (rest:List ℕ):
    readVector n (encodeVector x ++ rest)=some (x,rest):=by
  induction n generalizing rest with
  | zero =>
    have hx:x=0:=by funext j; exact Fin.elim0 j
    simp [readVector,encodeVector,hx]
  | succ n ih =>
    have hx:x=Fin.cons (x 0) (Fin.tail x):=(Fin.cons_self_tail x).symm
    rw [hx,encodeVector_cons,List.append_assoc]
    simp [readVector,readRational_encode,ih]

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

structure PackedProgram where
  m:ℕ
  n:ℕ
  program:Program ℚ m n

end Lax109476Proofs.WordDecoding

end

section

namespace Lax109476Proofs.RamReadFraction

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamInput RamRational RamArithmetic RamFrame

theorem readRawFraction_spec (B:ℕ) (xs:List ℕ) (v:ℕ)
    (h1:1 < B) (hxsB:xs.length < B) (hv:v≤ 1):
    Spec B (fun σ => σ.inp=xs∧ σ.vars "input.remaining"=xs.length∧
        σ.vars "input.valid"=v∧ σ.InpBounded B)
      readRawFraction
      (fun _ τ => τ.vars "rat.s"=xs.headD 0∧ τ.vars "rat.n"=xs.tail.headD 0∧
        τ.vars "rat.d"=xs.tail.tail.headD 0∧ τ.inp=xs.drop 3∧
        τ.vars "input.remaining"=xs.length - 3∧
        τ.vars "input.valid"=(if xs.length < 3 then 0 else v)∧ τ.InpBounded B) 27:=by
  rintro σ ⟨hσinp,hσrem,hσvalid,hσbound⟩
  obtain ⟨τ,hr₁,hτs,hτinp,hτrem,hτvalid⟩:=
    safeRead_spec B "rat.s" xs v h1 hxsB hv (by decide) (by decide)
      σ ⟨hσinp,hσrem,hσvalid,hσbound⟩
  have hτvle:(if xs=[] then 0 else v)≤ 1:=by split_ifs <;> omega
  have htailB:xs.tail.length < B:=by simp only [List.length_tail]; omega
  obtain ⟨υ,hr₂,hυn,hυinp,hυrem,hυvalid⟩:=
    safeRead_spec B "rat.n" xs.tail (if xs=[] then 0 else v) h1 htailB hτvle (by decide) (by decide)
      τ ⟨hτinp,by simpa using hτrem,hτvalid,hr₁.inpBounded hσbound⟩
  have hυs:υ.vars "rat.s"=xs.headD 0:=(hr₂.frame_var _ (by decide)).trans hτs
  have hυvle:(if xs.tail=[] then 0 else if xs=[] then 0 else v)≤ 1:=by split_ifs <;> omega
  have htailtailB:xs.tail.tail.length < B:=by simp only [List.length_tail]; omega
  obtain ⟨ξ,hr₃,hξd,hξinp,hξrem,hξvalid⟩:=
    safeRead_spec B "rat.d" xs.tail.tail (if xs.tail=[] then 0 else if xs=[] then 0 else v)
      h1 htailtailB hυvle (by decide) (by decide) υ
      ⟨hυinp,by simpa using hυrem,hυvalid, (hr₁.seq hr₂).inpBounded hσbound⟩
  have hξs:=(hr₃.frame_var "rat.s" (by decide)).trans hυs
  have hξn:=(hr₃.frame_var "rat.n" (by decide)).trans hυn
  have hrun:=hr₁.seq (hr₂.seq hr₃)
  refine ⟨ξ,hrun,hξs,hξn,hξd, ?_, ?_, ?_,hrun.inpBounded hσbound⟩
  · simpa only [← List.drop_one,List.drop_drop] using hξinp
  · simp only [List.length_tail] at hξrem
    omega
  · cases xs with
    | nil => simpa using hξvalid
    | cons s ys => cases ys with
      | nil => simpa using hξvalid
      | cons n zs => cases zs with
        | nil => simpa using hξvalid
        | cons d rest =>
          have hn:¬rest.length + 1 + 1 + 1 < 3:=by omega
          simpa [hn] using hξvalid

theorem decoded_fractionValue (s n d:ℕ):
    (WordDecoding.signedNumerator s n:ℚ) / d=fractionValue s n d:=by
  simp only [WordDecoding.signedNumerator,fractionValue,Int.cast_ite,Int.cast_neg,Int.cast_natCast]
  split_ifs <;> rfl

theorem validateFraction_valid_spec (B s n d remaining v:ℕ) (h2:2 < B) (hs:s≤ 1)
    (hn:n < B) (hd:d < B) (hdpos:0 < d):
    Spec B (fun σ => σ.vars "rat.s"=s∧ σ.vars "rat.n"=n∧ σ.vars "rat.d"=d∧
        σ.vars "input.remaining"=remaining∧ σ.vars "input.valid"=v)
      validateFraction
      (fun _ τ => FractionOutput (fractionValue s n d) τ∧
        τ.vars "input.remaining"=remaining∧ τ.vars "input.valid"=v)
      (36 * d.size + 24):=by
  have hsB:s < B:=by omega
  have hnrm:=spec_with_fields ["input.remaining", "input.valid"]
    (normalizeFraction_output_spec B s n d hs hn hd hdpos)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> decide)
    (by decide)
  rintro σ ⟨hσs,hσn,hσd,hσr,hσv⟩
  (expose_names;
    refine
        let c0:Prop:=
          Nat.lt (Env.vars σ "rat.s") ((2:Nat));
        let c1:Prop:=Not c0;
        let c2:Nat→ Nat→ Nat:=Nat.add;
        let c3:Nat→ Nat:=
          c2
            (Nat.mul ((36:Nat))
              (Nat.size d));
        let c4:Nat:=c3 ((24:Nat));
        let c5:Env→ Prop:=
          (fun (x τ:Env) =>
              And (FractionOutput (fractionValue s n d) τ)
                (And (@Eq Nat (Env.vars τ "input.remaining") remaining) (@Eq Nat (Env.vars τ "input.valid") v)))
            σ;
        let c6:Env→ Prop:=fun (σ':Env) => And (Run B validateFraction σ σ' c4) (c5 σ');
        let c7:Prop:= @Exists Env c6;
        let c8:Prop:=
          Nat.lt ((0:Nat)) (Env.vars σ "rat.d");
        let c9:Prop:=Not c8;
        let c10:Nat:=c3 ((16:Nat));
        let c11:Env→ Env→ Prop:=
          FieldsAgree (@List.cons String "input.remaining" (@List.cons String "input.valid" (@List.nil String)));
        let c12:Env→ Prop:=c11 σ;
        let c13:Env→ Prop:=fun (σ':Env) =>
          And (Run B normalizeFraction σ σ' c10)
            (And (FractionOutput (fractionValue s n d) σ')
              (And (c12 σ') (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs σ))));
        let c14:∀ (w:Env),c6 w→ @Exists Env c6:= @Exists.intro Env c6;
        let c15:Nat→ Nat:=c2 ((1:Nat));
        let c16:Cond:=Cond.lt (Expr.var "rat.s") (Expr.lit ((2:Nat)));
        let c17:Nat→ Nat:=c2 (c15 (Cond.size c16));
        let c18:Cond:=Cond.lt (Expr.lit ((0:Nat))) (Expr.var "rat.d");
        let c19:Nat→ Nat:=c2 (c15 (Cond.size c18));
        let c20:Nat:=c19 c10;
        let c21:Com:=Com.assign "input.valid" (Expr.lit ((0:Nat)));
        let c22:Com:=Com.ite c18 normalizeFraction c21;
        let c23:
          ∀ (σ':Env) (K:Nat),
            @Eq (Option Bool) (Cond.evalB B c16 σ) (@some Bool true)→
              Run B c22 σ σ' K→
                Run B (Com.ite c16 c22 c21) σ σ'
                  (Nat.add
                    (Nat.add
                      ((1:Nat)) (Cond.size c16))
                    K):=
          RunStep.ite_true B c16 c22 c21 σ;
        let c24:
          @Eq (Option Nat) (Expr.evalB B (Expr.lit ((2:Nat))) σ)
            (@some Nat ((2:Nat))):=
          RunStep.eval_lit B ((2:Nat)) σ h2;
        let c25:
          Nat.lt (Env.vars σ "rat.s") ((2:Nat))→
            @Eq (Option Bool)
              (Cond.evalB B
                (Cond.lt (Expr.var "rat.s") (Expr.lit ((2:Nat)))) σ)
              (@some Bool true):=
          RunStep.cond_lt_true B σ (Expr.var "rat.s") (Expr.lit ((2:Nat)))
            (Env.vars σ "rat.s") ((2:Nat))
            (RunStep.eval_var B σ "rat.s"
              (?nAX_g4133_0_0_0))
            c24;
        let c26:
          Nat.lt ((0:Nat)) B→
            @Eq (Option Nat) (Expr.evalB B (Expr.lit ((0:Nat))) σ)
              (@some Nat ((0:Nat))):=
          RunStep.eval_lit B ((0:Nat)) σ;
        let c27:
          @Eq (Option Nat) (Expr.evalB B (Expr.lit ((0:Nat))) σ)
            (@some Nat ((0:Nat))):=
          c26
            (?nAX_g4133_0_0_1);
        let c28:Env:=Env.setVar σ "input.valid" ((0:Nat));
        let c29:c6 c28→ @Exists Env c6:=c14 c28;
        let c30:Run B validateFraction σ c28 c4→ c5 c28→ And (Run B validateFraction σ c28 c4) (c5 c28):=
          @And.intro (Run B validateFraction σ c28 c4) (c5 c28);
        let c31:
          ∀ (K K':Nat),Run B validateFraction σ c28 K→ Nat.le K K'→ Run B validateFraction σ c28 K':=
          RunStep.mono B validateFraction σ c28;
        let c32:Nat:=c15 (Expr.size (Expr.lit ((0:Nat))));
        let c33:Nat:=c19 c32;
        let c34:
          @Eq (Option Nat) (Expr.evalB B (Expr.lit ((0:Nat))) σ)
              (@some Nat ((0:Nat)))→
            Run B (Com.assign "input.valid" (Expr.lit ((0:Nat)))) σ
              (Env.setVar σ "input.valid" ((0:Nat)))
              (Nat.add ((1:Nat))
                (Expr.size (Expr.lit ((0:Nat))))):=
          RunStep.assign B σ "input.valid" (Expr.lit ((0:Nat)))
            ((0:Nat));
        let c35:String→ Nat:=Env.vars c28;
        @Or.casesOn c0 c1 (fun (x:Or c0 c1) => c7) (Classical.em c0)
          (fun (hcase:c0) =>
            @Or.casesOn c8 c9 (fun (x:Or c8 c9) => c7) (Classical.em c8)
              (fun (hcase_1:c8) =>
                @Exists.casesOn Env c13 (fun (x:@Exists Env c13) => c7)
                  (RunStep.use B
                    (fun (σ:Env) =>
                      And (@Eq Nat (Env.vars σ "rat.n") n)
                        (And (@Eq Nat (Env.vars σ "rat.d") d) (@Eq Nat (Env.vars σ "rat.s") s)))
                    normalizeFraction
                    (fun (σ τ:Env) =>
                      And (FractionOutput (fractionValue s n d) τ)
                        (And (c11 σ τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ))))
                    c10 hnrm σ ?_)
                  fun (w:Env)
                    (h:
                      And (Run B normalizeFraction σ w c10)
                        (And (FractionOutput (fractionValue s n d) w)
                          (And (c12 w) (@Eq (String→ List Nat) (Env.arrs w) (Env.arrs σ))))) =>
                  let c0:Prop→ Prop:=And (FractionOutput (fractionValue s n d) w);
                  let c1:Prop:=c0 (And (c12 w) (@Eq (String→ List Nat) (Env.arrs w) (Env.arrs σ)));
                  @And.casesOn (Run B normalizeFraction σ w c10) c1
                    (fun (x:And (Run B normalizeFraction σ w c10) c1) => c7) h
                    fun (left:Run B normalizeFraction σ w c10) (right:c1) =>
                    c14 w
                      (@And.intro (Run B validateFraction σ w c4) (c5 w)
                        (RunStep.mono B validateFraction σ w (c17 c20) c4
                          (c23 w c20 (c25 hcase)
                            (RunStep.ite_true B c18 normalizeFraction c21 σ w c10
                              (RunStep.cond_lt_true B σ
                                (Expr.lit ((0:Nat))) (Expr.var "rat.d")
                                ((0:Nat)) (Env.vars σ "rat.d") c27
                                (RunStep.eval_var B σ "rat.d"
                                  (?nAX_g4133_0_0_2))
                                hcase_1)
                              left))
                          (?nAX_g4133_0_0_3))
                        ?_))
              fun (hcase_1:c9) =>
              c29
                (c30
                  (c31 (c17 c33) c4
                    (c23 c28 c33 (c25 hcase)
                      (RunStep.ite_false B c18 normalizeFraction c21 σ c28 c32
                        (RunStep.cond_lt_false B σ (Expr.lit ((0:Nat)))
                          (Expr.var "rat.d") ((0:Nat))
                          (Env.vars σ "rat.d") c27
                          (RunStep.eval_var B σ "rat.d"
                            (?nAX_g4133_0_0_4))
                          hcase_1)
                        (c34
                          (c26
                            (?nAX_g4133_0_0_5)))))
                    (?nAX_g4133_0_0_6))
                  ?_))
          fun (hcase:c1) =>
          c29
            (c30
              (c31 (c17 c32) c4
                (RunStep.ite_false B c16 c22 c21 σ c28 c32
                  (RunStep.cond_lt_false B σ (Expr.var "rat.s")
                    (Expr.lit ((2:Nat))) (Env.vars σ "rat.s")
                    ((2:Nat))
                    (RunStep.eval_var B σ "rat.s"
                      (?nAX_g4133_0_0_7))
                    c24 hcase)
                  (c34
                    (c26
                      (?nAX_g4133_0_0_8))))
                (?nAX_g4133_0_0_9))
              ?_) <;> try dsimp +zetaDelta at *
   all_goals try dsimp +zetaDelta at *
   try case nAX_g4133_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g4133_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g4133_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g4133_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g4133_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g4133_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g4133_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g4133_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g4133_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g4133_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all
  )
  all_goals clear hnrm
  all_goals simp_all [FieldsAgree]
  all_goals first | omega | (exfalso; omega)

theorem validateFraction_spec (B s n d remaining v:ℕ) (h2:2 < B)
    (hsB:s < B) (hnB:n < B) (hdB:d < B):
    Spec B (fun σ => σ.vars "rat.s"=s∧ σ.vars "rat.n"=n∧ σ.vars "rat.d"=d∧
        σ.vars "input.remaining"=remaining∧ σ.vars "input.valid"=v)
      validateFraction
      (fun _ τ => (s≤ 1∧ 0 < d→ FractionOutput (fractionValue s n d) τ)∧
        τ.vars "input.remaining"=remaining∧
        τ.vars "input.valid"=if s≤ 1∧ 0 < d then v else 0)
      (36 * d.size + 24):=by
  by_cases hgood:s≤ 1∧ 0 < d
  · apply (validateFraction_valid_spec B s n d remaining v h2 hgood.1 hnB hdB hgood.2).post
    intro σ τ hσ hτ
    exact ⟨fun _ => hτ.1,hτ.2.1,by simpa only [if_pos hgood] using hτ.2.2⟩
  · rintro σ ⟨hσs,hσn,hσd,hσr,hσv⟩
    have h0:0 < B:=by omega
    have hz:Run B (.assign "input.valid" (.lit 0)) σ (σ.setVar "input.valid" 0) 2:=
      Run.assign (evalB_lit h0)
    by_cases hs:s≤ 1
    · have hd:d=0:=by omega
      have ho:(Cond.lt (.var "rat.s") (.lit 2)).evalB B σ=some true:=by
        simpa [hσs,hs] using evalB_condLt
          (evalB_var (B:=B) (σ:=σ) (x:= "rat.s") (by rw [hσs]; exact hsB)) (evalB_lit h2)
      have hi:(Cond.lt (.lit 0) (.var "rat.d")).evalB B σ=some false:=by
        simpa [hσd,hd] using evalB_condLt (evalB_lit h0)
          (evalB_var (B:=B) (σ:=σ) (x:= "rat.d") (by rw [hσd]; exact hdB))
      have hr:=Run.ite_true (d:=Com.assign "input.valid" (.lit 0)) ho
        (Run.ite_false (c:=normalizeFraction) hi hz)
      refine ⟨_,hr.mono (by simp only [Cond.size,Expr.size]; omega), ?_⟩
      simp [hgood,Env.setVar,hσr]
    · have ho:(Cond.lt (.var "rat.s") (.lit 2)).evalB B σ=some false:=by
        simpa [hσs,show ¬s < 2 by omega] using evalB_condLt
          (evalB_var (B:=B) (σ:=σ) (x:= "rat.s") (by rw [hσs]; exact hsB)) (evalB_lit h2)
      have hr:=Run.ite_false (c:=.ite (.lt (.lit 0) (.var "rat.d"))
        normalizeFraction (.assign "input.valid" (.lit 0))) ho hz
      refine ⟨_,hr.mono (by simp only [Cond.size,Expr.size]; omega), ?_⟩
      simp [hgood,Env.setVar,hσr]

theorem readRational_raw (xs:List ℕ):
    WordDecoding.readRational xs =
      if xs.headD 0≤ 1∧ 0 < xs.tail.tail.headD 0 then
        some (fractionValue (xs.headD 0) (xs.tail.headD 0) (xs.tail.tail.headD 0),xs.drop 3)
      else none:=by
  cases xs with
  | nil => simp [WordDecoding.readRational]
  | cons s ys => cases ys with
    | nil => simp [WordDecoding.readRational]
    | cons n zs => cases zs with
      | nil => simp [WordDecoding.readRational]
      | cons d rest => simp [WordDecoding.readRational,decoded_fractionValue]

theorem raw_den_positive_length (xs:List ℕ) (hd:0 < xs.tail.tail.headD 0):
    3≤ xs.length:=by
  cases xs with
  | nil => simp at hd
  | cons s ys => cases ys with
    | nil => simp at hd
    | cons n zs => cases zs with
      | nil => simp at hd
      | cons d rest => simp only [List.length_cons]; omega

theorem headD_le (xs:List ℕ) (M:ℕ) (h:∀ a∈ xs,a≤ M):xs.headD 0≤ M:=by
  cases xs with
  | nil => simp
  | cons a rest => exact h a (by simp)

theorem readFraction_spec (B M:ℕ) (xs:List ℕ) (v:ℕ)
    (h2:2 < B) (hlen:xs.length < B) (hv:v≤ 1)
    (hM:M < B) (hwords:∀ a∈ xs,a≤ M):
    Spec B (fun σ => σ.inp=xs∧ σ.vars "input.remaining"=xs.length∧
        σ.vars "input.valid"=v∧ σ.InpBounded B)
      readFraction
      (fun _ τ => τ.inp=xs.drop 3∧ τ.vars "input.remaining"=xs.length - 3∧
        τ.vars "input.valid"=(if WordDecoding.readRational xs=none then 0 else v)∧
        (∀ q rest,WordDecoding.readRational xs=some (q,rest)→
          FractionOutput q τ∧ τ.inp=rest)∧ τ.InpBounded B)
      (36 * M.size + 51):=by
  have hsM:=headD_le xs M hwords
  have hnM:=headD_le xs.tail M (fun a ha => hwords a (List.mem_of_mem_tail ha))
  have hdM:=headD_le xs.tail.tail M
    (fun a ha => hwords a (List.mem_of_mem_tail (List.mem_of_mem_tail ha)))
  rintro σ ⟨hinp,hrem,hvalid,hbound⟩
  obtain ⟨τ,hr₁,hτs,hτn,hτd,hτinp,hτrem,hτvalid,hτbound⟩:=
    readRawFraction_spec B xs v (by omega) hlen hv σ ⟨hinp,hrem,hvalid,hbound⟩
  obtain ⟨υ,hr₂,hυq,hυrem,hυvalid⟩:=validateFraction_spec B (xs.headD 0)
    (xs.tail.headD 0) (xs.tail.tail.headD 0) (xs.length - 3) (if xs.length < 3 then 0 else v)
    h2 (hsM.trans_lt hM) (hnM.trans_lt hM) (hdM.trans_lt hM)
    τ ⟨hτs,hτn,hτd,hτrem,hτvalid⟩
  have hυinp:=(hr₂.frame_inp (by decide)).trans hτinp
  have hrun:=hr₁.seq hr₂
  have hds:(xs.tail.tail.headD 0).size≤ M.size:=Nat.size_le_size hdM
  refine ⟨υ,hrun.mono (by omega),hυinp,hυrem, ?_, ?_,hr₂.inpBounded hτbound⟩
  · rw [readRational_raw]
    by_cases hg:xs.headD 0≤ 1∧ 0 < xs.tail.tail.headD 0
    · have hlong:¬xs.length < 3:=by have:=raw_den_positive_length xs hg.2; omega
      simpa only [if_pos hg,if_neg hlong,reduceCtorEq,if_false] using hυvalid
    · simpa only [if_neg hg,if_true] using hυvalid
  · intro q rest hdecode
    rw [readRational_raw] at hdecode
    split_ifs at hdecode with hg
    · have he:=Option.some.inj hdecode
      have heq:=Prod.mk.inj he
      exact ⟨by rw [← heq.1]; exact hυq hg,hυinp.trans heq.2⟩

theorem zeroResult_spec (B:ℕ) (h1:1 < B):
    Spec B (fun _ => True) zeroResult (fun _ τ => FractionOutput 0 τ) 6:=by
  (expose_names;
    refine fun (σ:Env) (a:True) =>
        let c0:Env→ Prop:=
          (fun (x τ:Env) => FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) τ) σ;
        let c1:Env:=Env.setVar σ "rat.s" ((0:Nat));
        let c2:Env:=Env.setVar c1 "rat.n" ((0:Nat));
        let c3:Env:=Env.setVar c2 "rat.d" ((1:Nat));
        let c4:Nat→ Nat→ Nat:=Nat.add;
        let c5:Nat→ Nat:=c4 ((1:Nat));
        let c6:Nat:=c5 (Expr.size (Expr.lit ((0:Nat))));
        let c7:Nat→ Nat:=c4 c6;
        let c8:Nat:=c5 (Expr.size (Expr.lit ((1:Nat))));
        let c9:Nat:=c7 c8;
        let c10:Com:=Com.assign "rat.n" (Expr.lit ((0:Nat)));
        let c11:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat)));
        let c12:
          ∀ (σ:Env),
            Nat.lt ((0:Nat)) B→
              @Eq (Option Nat) (Expr.evalB B (Expr.lit ((0:Nat))) σ)
                (@some Nat ((0:Nat))):=
          RunStep.eval_lit B ((0:Nat));
        @Exists.intro Env
          (fun (σ':Env) =>
            And (Run B zeroResult σ σ' ((6:Nat))) (c0 σ'))
          c3
          (@And.intro (Run B zeroResult σ c3 ((6:Nat))) (c0 c3)
            (RunStep.mono B zeroResult σ c3 (c7 c9) ((6:Nat))
              (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat))))
                (Com.seq c10 c11) σ c1 c3 c6 c9
                (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat)))
                  ((0:Nat))
                  (c12 σ
                    (?nAX_g4141_0_0_0)))
                (RunStep.seq B c10 c11 c1 c2 c3 c6 c8
                  (RunStep.assign B c1 "rat.n" (Expr.lit ((0:Nat)))
                    ((0:Nat))
                    (c12 c1
                      (?nAX_g4141_0_0_1)))
                  (RunStep.assign B c2 "rat.d" (Expr.lit ((1:Nat)))
                    ((1:Nat))
                    (RunStep.eval_lit B ((1:Nat)) c2 h1))))
              (?nAX_g4141_0_0_2))
            ?_) <;> try dsimp +zetaDelta at *
   all_goals try dsimp +zetaDelta at *
   try case nAX_g4141_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g4141_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g4141_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all
  )
  all_goals simp [FractionOutput,fractionValue]

def safeValue (xs:List ℕ) (v:ℕ):ℚ:=
  if v=1 then (WordDecoding.readRational xs).map Prod.fst |>.getD 0 else 0

theorem safeFraction_spec (B M:ℕ) (xs:List ℕ) (v:ℕ)
    (h2:2 < B) (hlen:xs.length < B) (hv:v≤ 1)
    (hM:M < B) (hwords:∀ a∈ xs,a≤ M):
    Spec B (fun σ => σ.inp=xs∧ σ.vars "input.remaining"=xs.length∧
        σ.vars "input.valid"=v∧ σ.InpBounded B)
      safeFraction
      (fun _ τ => FractionOutput (safeValue xs v) τ∧ τ.inp=xs.drop 3∧
        τ.vars "input.remaining"=xs.length - 3∧
        τ.vars "input.valid"=(if WordDecoding.readRational xs=none then 0 else v)∧
        τ.InpBounded B)
      (36 * M.size + 61):=by
  intro σ hσ
  obtain ⟨τ,hr₁,hτinp,hτrem,hτvalid,hτq,hτbound⟩:=
    readFraction_spec B M xs v h2 hlen hv hM hwords σ hσ
  have hflag:τ.vars "input.valid" ≤ 1:=by rw [hτvalid]; split_ifs <;> omega
  have h1:1 < B:=by omega
  have hflagB:=hflag.trans_lt h1
  by_cases hgood:τ.vars "input.valid"=1
  · have hv1:v=1:=by rw [hτvalid] at hgood; split_ifs at hgood <;> omega
    have hdecode:WordDecoding.readRational xs ≠ none:=by
      intro hh; simp [hh] at hτvalid; omega
    obtain ⟨⟨q,rest⟩,hsome⟩:=Option.ne_none_iff_exists'.mp hdecode
    have hq:FractionOutput (safeValue xs v) τ:=by
      simpa [safeValue,hv1,hsome] using (hτq q rest hsome).1
    have hb:(Cond.eq (.var "input.valid") (.lit 1)).evalB B τ=some true:=by
      simpa [hgood] using evalB_condEq
        (evalB_var (B:=B) (σ:=τ) (x:= "input.valid") hflagB) (evalB_lit h1)
    exact ⟨τ, (hr₁.seq (Run.ite_true (d:=zeroResult) hb Run.skip)).mono
      (by simp only [Cond.size,Expr.size]; omega),hq,hτinp,hτrem,hτvalid,hτbound⟩
  · have hzero:safeValue xs v=0:=by
      by_cases hv1:v=1
      · have hnone:WordDecoding.readRational xs=none:=by
          by_contra hh; simp only [if_neg hh,hv1] at hτvalid; exact hgood hτvalid
        simp [safeValue,hv1,hnone]
      · simp [safeValue,hv1]
    have hb:(Cond.eq (.var "input.valid") (.lit 1)).evalB B τ=some false:=by
      simpa [hgood] using evalB_condEq
        (evalB_var (B:=B) (σ:=τ) (x:= "input.valid") hflagB) (evalB_lit h1)
    obtain ⟨υ,hr₂,hυq⟩:=zeroResult_spec B h1 τ True.intro
    have hυinp:=(hr₂.frame_inp (by decide)).trans hτinp
    have hυrem:=(hr₂.frame_var "input.remaining" (by decide)).trans hτrem
    have hυvalid:=(hr₂.frame_var "input.valid" (by decide)).trans hτvalid
    exact ⟨υ, (hr₁.seq (Run.ite_false (c:=.skip) hb hr₂)).mono
      (by simp only [Cond.size,Expr.size]; omega),hzero.symm ▸ hυq,
      hυinp,hυrem,hυvalid,hr₂.inpBounded hτbound⟩

end Lax109476Proofs.RamReadFraction

end

section

namespace Lax109476Proofs.RamReadArray

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamReadFraction RamRational RamRationalArrays RamFrame RamCenterUpdate
open RationalArithmeticBounds RamArithmetic

def flag (xs:List ℕ) (v:ℕ):ℕ→ ℕ
  | 0 => v
  | k + 1 => if WordDecoding.readRational (xs.drop (3 * k))=none then 0 else flag xs v k

def values (xs:List ℕ) (v n:ℕ):Fin n→ ℚ:=
  fun i => safeValue (xs.drop (3 * i.val)) (flag xs v i.val)

theorem flag_le_one (xs:List ℕ) (v k:ℕ) (hv:v≤ 1):flag xs v k≤ 1:=by
  induction k with
  | zero => exact hv
  | succ k ih => simp only [flag]; split_ifs <;> omega

theorem safeValue_height (xs:List ℕ) (v M:ℕ) (hM:1≤ M)
    (hwords:∀ a∈ xs,a≤ M):Height (safeValue xs v) M:=by
  unfold safeValue
  split_ifs with hv
  · rw [readRational_raw]
    split_ifs with hg
    · simp only [Option.map_some,Option.getD_some]
      exact RamPrimitiveBounds.fractionValue_height _ _ _ M
        (headD_le xs.tail M (fun a ha => hwords a (List.mem_of_mem_tail ha)))
        (headD_le xs.tail.tail M
          (fun a ha => hwords a (List.mem_of_mem_tail (List.mem_of_mem_tail ha)))) hg.2
    · simpa [Height] using hM
  · simpa [Height] using hM

def Invariant (B:ℕ) (a:String) (xs:List ℕ) (v n:ℕ) (σ:Env):Prop:=
  Represents a (filled (values xs v n) (σ.vars "vec.i")) σ∧
    σ.inp=xs.drop (3 * σ.vars "vec.i")∧
    σ.vars "input.remaining"=(xs.drop (3 * σ.vars "vec.i")).length∧
    σ.vars "input.valid"=flag xs v (σ.vars "vec.i")∧
    σ.InpBounded B∧ σ.vars "vec.i" ≤ n∧ σ.vars "vec.n"=n

theorem readStep_spec (B M n v:ℕ) (a:String) (xs:List ℕ)
    (h2:2 < B) (hMB:M < B) (hM:1≤ M) (hnB:n < B)
    (hxB:xs.length < B) (hv:v≤ 1) (hwords:∀ z∈ xs,z≤ M):
    Spec B (fun σ => Invariant B a xs v n σ∧ σ.vars "vec.i" < n) (readStep a)
      (fun σ τ => Invariant B a xs v n τ∧ τ.vars "vec.i"=σ.vars "vec.i" + 1)
      (36 * M.size + 78):=by
  rintro σ ⟨⟨hσa,hσinp,hσrem,hσvalid,hσbound,hσin,hσn⟩,hσi⟩
  let i:Fin n:= ⟨σ.vars "vec.i",hσi⟩
  let tail:=xs.drop (3 * i.val)
  have htailB:tail.length < B:=by dsimp [tail]; simp only [List.length_drop]; omega
  have htailwords:∀ z∈ tail,z≤ M:=by
    intro z hz; exact hwords z (List.mem_of_mem_drop hz)
  obtain ⟨τ,hr₁,hτq,hτinp,hτrem,hτvalid,hτbound⟩:=
    safeFraction_spec B M tail (flag xs v i.val) h2 htailB (flag_le_one xs v i.val hv)
      hMB htailwords σ ⟨hσinp,hσrem,hσvalid,hσbound⟩
  have hτi:τ.vars "vec.i"=i.val:=hr₁.frame_var _ (by decide)
  have hτn:τ.vars "vec.n"=n:=(hr₁.frame_var _ (by decide)).trans hσn
  have harr:τ.arrs=σ.arrs:=by
    funext b
    exact hr₁.frame_arr b (by
      simp [safeFraction,readFraction,readRawFraction,RamInput.safeRead,validateFraction,
        normalizeFraction,gcdLoop,gcdDoubleStep,gcdStep,zeroResult,Com.warrs])
  have hτa:Represents a (filled (values xs v n) i.val) τ:=by
    simpa only [Represents,harr,i] using hσa
  have hq:Height (values xs v n i) M:=safeValue_height tail (flag xs v i.val) M hM htailwords
  obtain ⟨υ,hr₂,hυa⟩:=storeReduced_spec B a (filled (values xs v n) i.val)
    (values xs v n i) i.val (by simpa [filled] using i.isLt) (by omega) (i.isLt.trans hnB)
    (hq.1.trans_lt hMB) (hq.2.trans_lt hMB) τ ⟨hτa,hτi,hτq⟩
  have hυi:υ.vars "vec.i"=i.val:=(hr₂.frame_var _ (by simp [storeReduced,Com.wvars])).trans hτi
  have hυn:υ.vars "vec.n"=n:=(hr₂.frame_var _ (by simp [storeReduced,Com.wvars])).trans hτn
  have hυinp:=(hr₂.frame_inp (by simp [storeReduced,Com.reads])).trans hτinp
  have hυrem:=(hr₂.frame_var "input.remaining" (by simp [storeReduced,Com.wvars])).trans hτrem
  have hυvalid:=(hr₂.frame_var "input.valid" (by simp [storeReduced,Com.wvars])).trans hτvalid
  have hdrop:tail.drop 3=xs.drop (3 * (i.val + 1)):=by
    dsimp [tail]; rw [List.drop_drop]; congr 1
  have hnext:Represents a (filled (values xs v n) (i.val + 1)) υ:=by
    simpa only [filled_step] using hυa
  have he:(Expr.add (.var "vec.i") (.lit 1)).evalB B υ=some (i.val + 1):=by
    simpa only [hυi,Bop.apply_add] using evalB_bin
      (evalB_var (B:=B) (σ:=υ) (x:= "vec.i") (by rw [hυi]; exact i.isLt.trans hnB))
      (evalB_lit (by omega:1 < B))
      (show Bop.add.apply (υ.vars "vec.i") 1 < B by rw [hυi]; simp only [Bop.apply_add]; omega)
  have hr₃:=Run.assign (x:= "vec.i") he
  have hrun:=hr₁.seq (hr₂.seq hr₃)
  refine ⟨_,hrun, ⟨?_, ?_, ?_, ?_,hrun.inpBounded hσbound, ?_, ?_⟩, ?_⟩
  · simpa only [Represents,arrs_setVar,vars_setVar,ite_true] using hnext
  · simpa only [Env.setVar,ite_true,hdrop] using hυinp
  · simp only [Env.setVar,ite_true]
    rw [← hdrop,List.length_drop]
    exact hυrem
  · simp only [Env.setVar,ite_true,flag]
    exact hυvalid
  · change i.val + 1≤ n; exact i.isLt
  · simpa [Env.setVar] using hυn
  · simp [i]

theorem readLoop_spec (B M n v:ℕ) (a:String) (xs:List ℕ)
    (h2:2 < B) (hMB:M < B) (hM:1≤ M) (hnB:n < B)
    (hxB:xs.length < B) (hv:v≤ 1) (hwords:∀ z∈ xs,z≤ M):
    Spec B (fun σ => Represents a (List.replicate n 0) σ∧ σ.inp=xs∧
        σ.vars "input.remaining"=xs.length∧ σ.vars "input.valid"=v∧
        σ.InpBounded B∧ σ.vars "vec.n"=n)
      (readLoop a)
      (fun _ τ => Represents a (List.ofFn (values xs v n)) τ∧ τ.inp=xs.drop (3 * n)∧
        τ.vars "input.remaining"=(xs.drop (3 * n)).length∧
        τ.vars "input.valid"=flag xs v n∧ τ.InpBounded B∧ τ.vars "vec.n"=n)
      ((36 * M.size + 82) * n + 6):=by
  have hlo:=Spec.forRangeZero "vec.i" "vec.n" (Invariant B a xs v n) n (36 * M.size + 78)
    hnB (fun _ h => h.2.2.2.2.2.1) (fun _ h => h.2.2.2.2.2.2)
    (readStep_spec B M n v a xs h2 hMB hM hnB hxB hv hwords)
  refine ((hlo.pre ?_).post ?_).mono (by simp only [Nat.add_assoc,Nat.reduceAdd]; omega)
  · rintro σ ⟨hσa,hσinp,hσrem,hσvalid,hσbound,hσn⟩
    clear hlo
    simp_all [Invariant,filled_zero,Represents,Env.setVar,flag,Env.InpBounded]
  · rintro σ τ _ ⟨hτ,hcounter⟩
    rcases hτ with ⟨hτa,hτinp,hτrem,hτvalid,hτbound,hτi,hτn⟩
    exact ⟨by simpa only [hcounter,filled_done] using hτa,
      by simpa only [hcounter] using hτinp,by simpa only [hcounter] using hτrem,
      by simpa only [hcounter] using hτvalid,hτbound,hτn⟩

theorem readArray_spec (B M n v:ℕ) (a:String) (xs:List ℕ)
    (h2:2 < B) (hMB:M < B) (hM:1≤ M) (hnB:n < B)
    (hxB:xs.length < B) (hv:v≤ 1) (hwords:∀ z∈ xs,z≤ M):
    Spec B (fun σ => (σ.arrs (a ++ ".s")).length=n∧
        (σ.arrs (a ++ ".n")).length=n∧ (σ.arrs (a ++ ".d")).length=n∧
        σ.inp=xs∧ σ.vars "input.remaining"=xs.length∧ σ.vars "input.valid"=v∧
        σ.InpBounded B∧ σ.vars "vec.n"=n)
      (readArray a)
      (fun _ τ => Represents a (List.ofFn (values xs v n)) τ∧ τ.inp=xs.drop (3 * n)∧
        τ.vars "input.remaining"=(xs.drop (3 * n)).length∧
        τ.vars "input.valid"=flag xs v n∧ τ.InpBounded B∧ τ.vars "vec.n"=n)
      ((36 * M.size + 115) * n + 24):=by
  rintro σ ⟨hσs,hσnum,hσd,hσinp,hσrem,hσvalid,hσbound,hσn⟩
  obtain ⟨τ,hr₁,hτa,hτn,_⟩:=RamZeroArray.zeroRationalArray_spec B n a hnB (by omega)
    σ ⟨hσs,hσnum,hσd,hσn⟩
  have hτinp:=(hr₁.frame_inp (by simp [RamZeroArray.zeroRationalArray,RamZeroArray.fillConstant,
    Lib.Fill.put,Com.reads])).trans hσinp
  have hτrem:=(hr₁.frame_var "input.remaining" (by simp [RamZeroArray.zeroRationalArray,
    RamZeroArray.fillConstant,Lib.Fill.put,Com.wvars])).trans hσrem
  have hτvalid:=(hr₁.frame_var "input.valid" (by simp [RamZeroArray.zeroRationalArray,
    RamZeroArray.fillConstant,Lib.Fill.put,Com.wvars])).trans hσvalid
  obtain ⟨υ,hr₂,hυ⟩:=readLoop_spec B M n v a xs h2 hMB hM hnB hxB hv hwords
    τ ⟨hτa,hτinp,hτrem,hτvalid,hr₁.inpBounded hσbound,hτn⟩
  exact ⟨υ, (hr₁.seq hr₂).mono (by simp only [Nat.add_mul]; omega),hυ⟩

theorem rational_drop (xs:List ℕ) (q:ℚ) (rest:List ℕ)
    (h:WordDecoding.readRational xs=some (q,rest)):xs.drop 3=rest:=by
  rw [readRational_raw] at h
  split_ifs at h with hg
  exact (Prod.mk.inj (Option.some.inj h)).2

theorem flag_shift (xs:List ℕ) (v k:ℕ) (h:WordDecoding.readRational xs ≠ none):
    flag (xs.drop 3) v k=flag xs v (k + 1):=by
  induction k with
  | zero => simp [flag,h]
  | succ k ih =>
    simp only [flag,List.drop_drop]
    have he:3 + 3 * k=3 * (k + 1):=by omega
    rw [he,ih]
    rfl

theorem readVector_correct (n:ℕ) (xs:List ℕ) (x:Fin n→ ℚ) (rest:List ℕ)
    (h:WordDecoding.readVector n xs=some (x,rest)):
    flag xs 1 n=1∧ values xs 1 n=x∧ xs.drop (3 * n)=rest:=by
  induction n generalizing xs rest with
  | zero =>
    simp only [WordDecoding.readVector,Option.some.injEq,Prod.mk.injEq] at h
    exact ⟨rfl,by funext j; exact Fin.elim0 j,by simpa using h.2⟩
  | succ n ih =>
    obtain ⟨⟨q,mid⟩,hq,hx⟩:=Option.bind_eq_some_iff.mp h
    obtain ⟨⟨y,tail⟩,hy,he⟩:=Option.bind_eq_some_iff.mp hx
    simp only [Option.pure_def,Option.some.injEq,Prod.mk.injEq] at he
    obtain ⟨rfl,rfl⟩:=he
    obtain ⟨hflag,hvals,hrest⟩:=ih mid y tail hy
    have hdrop:=rational_drop xs q mid hq
    have hne:WordDecoding.readRational xs ≠ none:=by rw [hq]; simp
    have hshift:=flag_shift xs 1 n hne
    rw [hdrop] at hshift
    refine ⟨hshift.symm.trans hflag, ?_, ?_⟩
    · funext j
      refine Fin.cases ?_ (fun k => ?_) j
      · simp [values,safeValue,flag,hq]
      · change safeValue (xs.drop (3 * (k.val + 1))) (flag xs 1 (k.val + 1))=y k
        have hd:xs.drop (3 * (k.val + 1))=mid.drop (3 * k.val):=by
          rw [← hdrop,List.drop_drop]
          congr 1 <;> omega
        have hf:=flag_shift xs 1 k.val hne
        rw [hdrop] at hf
        rw [hd, ← hf]
        exact congrFun hvals k
    · rw [← hrest, ← hdrop,List.drop_drop]
      congr 1 <;> omega

end Lax109476Proofs.RamReadArray

end

section

open scoped BigOperators

namespace Lax109476Proofs.RamDotProduct

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamPrimitiveBounds RamFrame RationalArithmeticBounds

def prefixValue (xs ys:List ℚ) (k:ℕ):ℚ:=
  ∑ i∈ Finset.range k,xs.getD i 0 * ys.getD i 0

theorem cap_ge (n H:ℕ) (hH:1≤ H):H * H≤ cap n H∧ H≤ cap n H:=by
  have hb:1≤ 2 * (H * H):=by nlinarith
  have hp:=le_self_pow hb (by omega:n + 1 ≠ 0)
  change H * H≤ (2 * (H * H)) ^ (n + 1)∧ H≤ (2 * (H * H)) ^ (n + 1)
  constructor <;> nlinarith

theorem prefix_height (xs ys:List ℚ) (n H k:ℕ) (hH:1≤ H)
    (hx:xs.length=n) (hy:ys.length=n) (hk:k≤ n)
    (hxs:∀ q∈ xs,Height q H) (hys:∀ q∈ ys,Height q H):
    Height (prefixValue xs ys k) (cap n H):=by
  have hf:∀ i∈ Finset.range k,Height (xs.getD i 0 * ys.getD i 0) (H * H):=by
    intro i hi
    have hix:i < xs.length:=by have h:=Finset.mem_range.mp hi; omega
    have hiy:i < ys.length:=by have h:=Finset.mem_range.mp hi; omega
    have hxq:xs.getD i 0=xs[i]:=by simp [List.getD_eq_getElem?_getD,hix]
    have hyq:ys.getD i 0=ys[i]:=by simp [List.getD_eq_getElem?_getD,hiy]
    rw [hxq,hyq]
    exact height_mul _ _ H H (hxs _ (List.getElem_mem hix)) (hys _ (List.getElem_mem hiy))
  have hs:=height_sum (Finset.range k) (fun i => xs.getD i 0 * ys.getD i 0) (H * H) hf
  simp only [Finset.card_range] at hs
  exact height_mono _ hs (Nat.pow_le_pow_right (by nlinarith) (by omega))

theorem cap_size (n H:ℕ):(cap n H).size≤ (n + 1) * (2 * H.size + 3) + 1:=by
  have hh:=RationalSizeBounds.size_mul_le H H
  have ht:=RationalSizeBounds.size_mul_le 2 (H * H)
  have hp:=RationalSizeBounds.size_pow_le (2 * (H * H)) (n + 1)
  have htwo:Nat.size 2=2:=by decide
  have hb:(2 * (H * H)).size≤ 2 * H.size + 3:=by omega
  have hm:=Nat.mul_le_mul_left (n + 1) hb
  dsimp [cap]
  omega

theorem prefix_ofFn (n:ℕ) (x y:Fin n→ ℚ):
    prefixValue (List.ofFn x) (List.ofFn y) n=∑ i,x i * y i:=by
  rw [Finset.sum_fin_eq_sum_range]
  unfold prefixValue
  apply Finset.sum_congr rfl
  intro i hi
  have hin:=Finset.mem_range.mp hi
  simp [List.getD_eq_getElem?_getD,hin]

end Lax109476Proofs.RamDotProduct

end

section

namespace Lax109476Proofs.RamMatrixStorage

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamMatrixRows

@[simp] theorem flatten_length {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℚ):
    (flatten A).length=m * n:=by simp [flatten]

theorem row_index_lt {m n:ℕ} (i:Fin m) (j:Fin n):i.val * n + j.val < m * n:=by
  have hmul:=Nat.mul_le_mul_right n i.isLt
  calc
    _ < i.val * n + n:=Nat.add_lt_add_left j.isLt _
    _=(i.val + 1) * n:=by ring
    _≤ _:=hmul

theorem flatten_entry {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℚ) (i:Fin m) (j:Fin n):
    (flatten A)[i.val * n + j.val]'(by simp; exact row_index_lt i j)=A i j:=by
  have hk:(⟨i.val * n + j.val,row_index_lt i j⟩:Fin (m * n))=finProdFinEquiv (i,j):=by
    apply Fin.ext
    simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
  simp only [flatten,List.getElem_ofFn]
  change A ((finProdFinEquiv.symm (⟨i.val * n + j.val,row_index_lt i j⟩:Fin (m * n))).1)
    ((finProdFinEquiv.symm (⟨i.val * n + j.val,row_index_lt i j⟩:Fin (m * n))).2)=_
  rw [hk,Equiv.symm_apply_apply]

end Lax109476Proofs.RamMatrixStorage

end

section

namespace Lax109476Proofs.RamReadMatrix

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamMatrixStorage WordDecoding

theorem flatten_rows {m n:ℕ} (A:Fin m→ Fin n→ ℚ):
    flatten A=(List.ofFn fun i => List.ofFn (A i)).flatten:=by
  unfold flatten
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  simpa only [flatten,List.getElem_ofFn] using flatten_entry A i j

theorem encodeRows_flat {m n:ℕ} (A:Fin m→ Fin n→ ℚ):
    encodeRows A=encodeVector (fun k:Fin (m * n) => A k.divNat k.modNat):=by
  change _=(flatten A).flatMap encodeRational
  rw [flatten_rows]
  unfold encodeRows encodeVector
  simp only [List.flatten_eq_flatMap,List.flatMap_assoc]
  simp only [List.flatMap_def,List.map_ofFn,Function.comp_def,id_eq]

end Lax109476Proofs.RamReadMatrix

end

section

namespace Lax109476Proofs.RamReadBlock

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamReadArray RamRationalArrays RamFrame

def fields:List String:= ["lp.m", "lp.n", "decode.count"]

theorem readArray_wvars (a:String):(readArray a).wvars=(readArray "").wvars:=by rfl

theorem readArray_warrs (a:String):(readArray a).warrs =
    [a ++ ".s",a ++ ".n",a ++ ".d",a ++ ".s",a ++ ".s",a ++ ".n",a ++ ".d"]:=by rfl

theorem readBlock_spec (B M n v:ℕ) (a field:String) (xs:List ℕ)
    (h2:2 < B) (hMB:M < B) (hM:1≤ M) (hnB:n < B)
    (hxB:xs.length < B) (hv:v≤ 1) (hwords:∀ z∈ xs,z≤ M)
    (hfield:field∈ fields):
    Spec B (fun σ => (σ.arrs (a ++ ".s")).length=n∧
        (σ.arrs (a ++ ".n")).length=n∧ (σ.arrs (a ++ ".d")).length=n∧
        σ.inp=xs∧ σ.vars "input.remaining"=xs.length∧ σ.vars "input.valid"=v∧
        σ.InpBounded B∧ σ.vars field=n)
      (readBlock a field)
      (fun σ τ => Represents a (List.ofFn (values xs v n)) τ∧ τ.inp=xs.drop (3 * n)∧
        τ.vars "input.remaining"=(xs.drop (3 * n)).length∧
        τ.vars "input.valid"=flag xs v n∧ τ.InpBounded B∧
        FieldsAgree fields σ τ∧ ∀ b∉ [a ++ ".s",a ++ ".n",a ++ ".d"],τ.arrs b=σ.arrs b)
      ((36 * M.size + 115) * n + 26):=by
  have hf:∀ x∈ fields,x∉ (readArray a).wvars:=by
    intro x hx; rw [readArray_wvars]
    simp [fields] at hx
    rcases hx with rfl | rfl | rfl <;> decide
  have harray:=spec_with_write_frame fields
    (readArray_spec B M n v a xs h2 hMB hM hnB hxB hv hwords) hf
  rintro σ ⟨hσs,hσnum,hσd,hσinp,hσrem,hσvalid,hσbound,hσn⟩
  have hr₁:Run B (.assign "vec.n" (.var field)) σ (σ.setVar "vec.n" n) 2:=
    Run.assign (by simpa only [hσn] using evalB_var (B:=B) (σ:=σ) (x:=field) (hσn ▸ hnB))
  obtain ⟨τ,hr₂,hτ,hfields,harrs⟩:=harray (σ.setVar "vec.n" n)
    ⟨hσs,hσnum,hσd,hσinp,hσrem,hσvalid,hr₁.inpBounded hσbound,by simp⟩
  refine ⟨τ, (hr₁.seq hr₂).mono (by omega),hτ.1,hτ.2.1,hτ.2.2.1,hτ.2.2.2.1,hτ.2.2.2.2.1, ?_, ?_⟩
  · intro x hx
    exact (hfields x hx).trans (by simp [fields] at hx; rcases hx with rfl | rfl | rfl <;> simp [Env.setVar])
  · intro b hb
    apply harrs b
    rw [readArray_warrs]
    simp at hb ⊢
    tauto

end Lax109476Proofs.RamReadBlock

end

section

namespace Lax109476Proofs.RamShapeCoordinate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFractionInterface RamFrame RationalArithmeticBounds

theorem shapeCap_pow (M k:ℕ) (hk:k≤ 8):M ^ k≤ (M + 1) ^ 8:=
  (Nat.pow_le_pow_left (by omega:M≤ M + 1) k).trans
    (Nat.pow_le_pow_right (by omega:1≤ M + 1) hk)

theorem shapeCap_bounds (M:ℕ):
    M≤ shapeCap M∧ M ^ 2≤ shapeCap M∧ M ^ 3≤ shapeCap M∧
      2 * M ^ 4≤ shapeCap M∧ 2 * M ^ 5≤ shapeCap M∧
      2 * M ^ 6 + 1≤ shapeCap M∧ 6 * M ^ 7≤ shapeCap M∧ 6 * M ^ 8≤ shapeCap M:=by
  have hp1:=shapeCap_pow M 1 (by omega)
  have hp2:=shapeCap_pow M 2 (by omega)
  have hp3:=shapeCap_pow M 3 (by omega)
  have hp4:=shapeCap_pow M 4 (by omega)
  have hp5:=shapeCap_pow M 5 (by omega)
  have hp6:=shapeCap_pow M 6 (by omega)
  have hp7:=shapeCap_pow M 7 (by omega)
  have hp8:=shapeCap_pow M 8 (by omega)
  have hbase:1≤ (M + 1) ^ 8:=Nat.one_le_pow _ _ (by omega)
  simp only [pow_one] at hp1
  unfold shapeCap
  exact ⟨by nlinarith,by nlinarith,by nlinarith,by nlinarith,
    by nlinarith,by nlinarith,by nlinarith,by nlinarith⟩

end Lax109476Proofs.RamShapeCoordinate

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RamShapeUpdate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFractionInterface RamFrame RationalArithmeticBounds
open RamShapeCoordinate RamZeroArray RamMatrixStorage

def shapeValues {n:ℕ} (u:Fin n→ ℚ) (A:Matrix (Fin n) (Fin n) ℚ)
    (gs:List ℚ) (hg:4 < gs.length) (D:ℕ):Matrix (Fin n) (Fin n) ℚ:=
  fun i j => gs[3] * (RationalRounding.roundDown
    (gs[0] * (A i j - gs[1] * (u i * u j))) D + if i=j then gs[4] else 0)

theorem shapeCap_size (M:ℕ):(shapeCap M).size≤ 8 * M.size + 13:=by
  have hb:=RationalSizeBounds.size_add_one_le M
  have hp:=RationalSizeBounds.size_pow_le (M + 1) 8
  have hm:=RationalSizeBounds.size_mul_le 8 ((M + 1) ^ 8)
  have h8:Nat.size 8=4:=by decide
  unfold shapeCap
  omega

theorem updateShape_cost_polynomial (n M:ℕ):
    33 * (n * n) + 26 + ((468 * (shapeCap M).size + 690 + 4 + 4) * (n * n) + 10)≤
      (3744 * M.size + 6815) * (n * n) + 36:=by
  have hm:=Nat.mul_le_mul_left 468 (shapeCap_size M)
  have hn:=Nat.mul_le_mul_right (n * n) (Nat.add_le_add_right hm 731)
  convert Nat.add_le_add_right hn 36 using 1 <;> ring

theorem shapeValues_eq_roundedStepShape {n:ℕ} (A:Matrix (Fin n) (Fin n) ℚ)
    (a:Fin n→ ℚ) (gs:List ℚ) (hg:4 < gs.length) (D:ℕ) (η:ℚ)
    (hα:gs[0]=(n:ℚ) ^ 2 / ((n:ℚ) ^ 2 - 1))
    (hβ:gs[1]=2 / (((n:ℚ) + 1) * (a ⬝ᵥ (A *ᵥ a))))
    (hρ:gs[3]=(1 + η) ^ 2) (hδ:gs[4]=(n:ℚ) / D):
    shapeValues (A *ᵥ a) A gs hg D=EllipsoidCenter.roundedStepShape n A a D η:=by
  ext i j
  simp only [shapeValues,hα,hβ,hρ,hδ,EllipsoidCenter.roundedStepShape,
    EllipsoidRounding.roundedShape,EllipsoidBounds.cutShape,Matrix.smul_apply,Matrix.add_apply,
    Matrix.sub_apply,Matrix.vecMulVec_apply,smul_eq_mul]
  by_cases hij:i=j <;> simp [Matrix.one_apply,hij]

end Lax109476Proofs.RamShapeUpdate

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RamMatrixVector

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamDotProduct RamMatrixRows RationalArithmeticBounds

theorem ellipsoidMulVec_cost_polynomial (n H:ℕ):
    33 * n + 18 + (((4 + ((144 * (cap n H).size + 216 + 4) * n + 12) + 21 + 4) + 4) * n + 8)≤
      (144 * ((n + 1) * (2 * H.size + 3) + 1) + 220) * n ^ 2 + 78 * n + 26:=by
  have hm:=Nat.mul_le_mul_right (n * n)
    (Nat.add_le_add_right (Nat.mul_le_mul_left 144 (cap_size n H)) 220)
  convert Nat.add_le_add_right hm (78 * n + 26) using 1 <;> ring

theorem mulVec_height (n H:ℕ) (A:Matrix (Fin n) (Fin n) ℚ) (c:Fin n→ ℚ)
    (hH:1≤ H) (hA:∀ k j,Height (A k j) H) (hc:∀ j,Height (c j) H) (i:Fin n):
    Height ((A *ᵥ c) i) (cap n H):=by
  change Height (∑ j,A i j * c j) (cap n H)
  rw [← prefix_ofFn]
  apply prefix_height _ _ n H n hH (by simp) (by simp) le_rfl
  · intro q hq; simp only [List.mem_ofFn] at hq; obtain ⟨j,rfl⟩:=hq; exact hA i j
  · intro q hq; simp only [List.mem_ofFn] at hq; obtain ⟨j,rfl⟩:=hq; exact hc j

end Lax109476Proofs.RamMatrixVector

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RamEllipsoidForm

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamDotProduct RamMatrixRows RamMatrixVector
open RationalArithmeticBounds

theorem formHeight_ge (n H:ℕ) (hH:1≤ H):cap n H≤ formHeight n H:=by
  have hcap:=(cap_ge n H hH).2
  exact (cap_ge n (cap n H) (hH.trans hcap)).2

theorem formHeight_size (n H:ℕ):
    (formHeight n H).size≤
      (n + 1) * (2 * ((n + 1) * (2 * H.size + 3) + 1) + 3) + 1:=by
  have hc:=cap_size n H
  have hf:=cap_size n (cap n H)
  have hm:=Nat.mul_le_mul_left (n + 1) (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hc) 3)
  unfold formHeight
  omega

theorem ellipsoidForm_cost_polynomial (n H:ℕ):
    33 * n + 18 + (((4 + ((144 * (cap n H).size + 216 + 4) * n + 12) + 21 + 4) + 4) * n + 8) +
      (((144 * (formHeight n H).size + 210 + 4) * n + 12) + 6)≤
    (144 * ((n + 1) * (2 * H.size + 3) + 1) + 220) * n ^ 2 +
      (144 * ((n + 1) * (2 * ((n + 1) * (2 * H.size + 3) + 1) + 3) + 1) + 292) * n + 44:=by
  have hd:=Nat.add_le_add_right
    (Nat.mul_le_mul_right n (Nat.add_le_add_right (Nat.mul_le_mul_left 144 (formHeight_size n H)) 214)) 18
  convert Nat.add_le_add (ellipsoidMulVec_cost_polynomial n H) hd using 1
  ring

end Lax109476Proofs.RamEllipsoidForm

end

section

namespace Lax109476Proofs.RamEllipsoidCoefficients

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamEllipsoidScalars RamEllipsoidForm
open RationalArithmeticBounds

theorem coefficients_height (n M D E:ℕ) (q:ℚ) (hq:Height q M)
    (hnM:n≤ M) (hDM:D≤ M) (hEM:E≤ M) (hDpos:0 < D):
    ∀ v∈ coefficients n q D E,Height v (coefficientCap M):=by
  have hM:1≤ M:=le_trans q.den_pos hq.2
  have hn:=height_nat n M hnM hM
  have hD:=height_nat D M hDM hM
  have hE:=height_nat E M hEM hM
  have hone:Height (1:ℚ) 1:=by simp [Height]
  have htwo:Height (2:ℚ) 2:=by simp [Height]
  have hnp:Height ((n:ℚ) + 1) (M + 1):=by
    simpa only [Nat.cast_add,Nat.cast_one] using height_nat (n + 1) (M + 1) (by omega) (by omega)
  have hpow:=height_pow _ M 2 hn
  have hsub:=height_sub _ _ (M ^ 2) 1 hpow hone
  have hα:=height_div _ _ (M ^ 2) (2 * M ^ 2 * 1) hpow hsub
  have hβ:=height_div _ _ 2 ((M + 1) * M) htwo (height_mul _ _ (M + 1) M hnp hq)
  have hroot:Height (RationalRounding.sqrtUpper q D) (M ^ 3 + 1):=by
    apply height_mono _ (EllipsoidArithmeticBounds.height_sqrtUpper q M D hq hDpos)
    calc
      M * D ^ 2 + 1≤ M * M ^ 2 + 1:=Nat.add_le_add_right
        (Nat.mul_le_mul_left M (Nat.pow_le_pow_left hDM 2)) 1
      _=M ^ 3 + 1:=by ring
  have hγ:=height_div _ _ 1 ((M + 1) * (M ^ 3 + 1)) hone
    (height_mul _ _ (M + 1) (M ^ 3 + 1) hnp hroot)
  have hρ:=height_pow _ (2 * M) 2
    (by simpa using height_add _ _ 1 M hone (by simpa only [one_mul] using height_div _ _ 1 M hone hE))
  have hδ:=height_div _ _ M M hn hD
  have hp1:=Nat.pow_le_pow_right (by omega:1≤ M + 1) (by decide:(1:ℕ)≤ 4)
  have hp2:=Nat.pow_le_pow_right (by omega:1≤ M + 1) (by decide:(2:ℕ)≤ 4)
  have hp4:=Nat.pow_le_pow_left (by omega:M≤ M + 1) 4
  have hrootpow:M ^ 3 + 1≤ (M + 1) ^ 3:=by nlinarith only [hM]
  have hγbound:1 * ((M + 1) * (M ^ 3 + 1))≤ coefficientCap M:=by
    calc
      1 * ((M + 1) * (M ^ 3 + 1))≤ (M + 1) * (M + 1) ^ 3:=by
        simpa using Nat.mul_le_mul_left (M + 1) hrootpow
      _=(M + 1) ^ 4:=by ring
      _≤ coefficientCap M:=by unfold coefficientCap; omega
  intro v hv
  simp only [coefficients,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl
  · apply height_mono _ hα
    calc
      M ^ 2 * (2 * M ^ 2 * 1)=2 * M ^ 4:=by ring
      _≤ coefficientCap M:=by unfold coefficientCap; omega
  · apply height_mono _ hβ
    calc
      2 * ((M + 1) * M)≤ 2 * (M + 1) ^ 2:=by nlinarith only [hM]
      _≤ coefficientCap M:=by unfold coefficientCap; omega
  · exact height_mono _ hγ hγbound
  · apply height_mono _ hρ
    have hp:=(Nat.pow_le_pow_left (by omega:M≤ M + 1) 2).trans hp2
    calc
      (2 * M) ^ 2=4 * M ^ 2:=by ring
      _≤ coefficientCap M:=by unfold coefficientCap; omega
  · apply height_mono _ hδ
    have hp:=(Nat.pow_le_pow_left (by omega:M≤ M + 1) 2).trans hp2
    calc
      M * M=M ^ 2:=by ring
      _≤ coefficientCap M:=by unfold coefficientCap; omega

end Lax109476Proofs.RamEllipsoidCoefficients

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RamEllipsoidUpdate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds
open RamCenterCoordinate RamCenterUpdate RamShapeCoordinate RamShapeUpdate
open RamEllipsoidCoefficients RamMatrixStorage

theorem roundedUpdate_cost_polynomial (n M:ℕ):
    ((33 * n + 18 + ((180 * (centerCap M).size + 318 + 4 + 4) * n + 6)) +
      (33 * (n * n) + 26 + ((468 * (shapeCap M).size + 690 + 4 + 4) * (n * n) + 10)))≤
      (720 * M.size + 1799) * n + (3744 * M.size + 6815) * (n * n) + 60:=by
  have h:=Nat.add_le_add (updateCenter_cost_polynomial n M) (updateShape_cost_polynomial n M)
  convert h using 1 <;> ring

theorem roundedUpdate_eq_ellipsoid {n:ℕ} (A:Matrix (Fin n) (Fin n) ℚ)
    (a c:Fin n→ ℚ) (D E:ℕ):
    centerValues (A *ᵥ a) c ((coefficients n (a ⬝ᵥ (A *ᵥ a)) D E)[2]'(by simp [coefficients])) D =
        EllipsoidCenter.roundedCenter n A a c D∧
      shapeValues (A *ᵥ a) A (coefficients n (a ⬝ᵥ (A *ᵥ a)) D E) (by simp [coefficients]) D =
        EllipsoidCenter.roundedStepShape n A a D (1 / (E:ℚ)):=by
  constructor
  · simpa [coefficients] using centerValues_eq_roundedCenter A a c D
  · exact shapeValues_eq_roundedStepShape A a _ (by simp [coefficients]) D (1 / (E:ℚ))
      (by simp [coefficients]) (by simp [coefficients]) (by simp [coefficients]) (by simp [coefficients])

end Lax109476Proofs.RamEllipsoidUpdate

end

section

namespace Lax109476Proofs.RamEllipsoidWordBounds

open RamEllipsoidCoefficients RamShapeCoordinate RamCenterCoordinate

theorem coefficientCap_bounds (M:ℕ):
    M≤ coefficientCap M∧ M ^ 3 + 2≤ coefficientCap M∧ 4 * (M + 1)≤ coefficientCap M:=by
  have hp1:M + 1≤ (M + 1) ^ 4:=
    le_self_pow (by omega) (by decide:(4:ℕ) ≠ 0)
  have hp3:=(Nat.pow_le_pow_left (by omega:M≤ M + 1) 3).trans
    (Nat.pow_le_pow_right (by omega:1≤ M + 1) (by decide:(3:ℕ)≤ 4))
  have hone:1≤ (M + 1) ^ 4:=Nat.one_le_pow _ _ (by omega)
  unfold coefficientCap
  omega

theorem shapeCap_linear (N:ℕ):8 * (N + 1)≤ shapeCap N:=by
  exact Nat.mul_le_mul_left 8 (le_self_pow (by omega) (by decide:(8:ℕ) ≠ 0))

theorem centerCap_le_shapeCap (N:ℕ):centerCap N≤ shapeCap N:=by
  have hp:=Nat.pow_le_pow_right (by omega:1≤ N + 1) (by decide:(4:ℕ)≤ 8)
  have hone:1≤ (N + 1) ^ 8:=Nat.one_le_pow _ _ (by omega)
  unfold centerCap shapeCap
  omega

theorem rootBound_le_shapeBound (M:ℕ):
    (2 * (M ^ 3 + 2) + 1) ^ 2 + M ^ 3 + 3≤ 2 * (shapeCap (coefficientCap M)) ^ 2 + 3:=by
  let N:=coefficientCap M
  let S:=shapeCap N
  have hM3:M ^ 3 + 2≤ N:=(coefficientCap_bounds M).2.1
  have hS:8 * (N + 1)≤ S:=shapeCap_linear N
  have hbase:2 * (M ^ 3 + 2) + 1≤ 2 * N + 1:=by omega
  have hsq:=Nat.pow_le_pow_left hbase 2
  calc
    (2 * (M ^ 3 + 2) + 1) ^ 2 + M ^ 3 + 3≤ (2 * N + 1) ^ 2 + N + 1:=by omega
    _≤ 2 * S ^ 2 + 3:=by nlinarith only [hS]

theorem dimensions_le_coefficientCap (n M:ℕ) (hn:2≤ n) (hnM:n * n≤ M):
    n + n + n * n + 1≤ coefficientCap M:=by
  have hnp:n≤ n * n:=by
    simpa only [pow_two] using le_self_pow (by omega:1≤ n) (by decide:(2:ℕ) ≠ 0)
  have hc:=(coefficientCap_bounds M).2.2
  omega

theorem unified_word_bounds (B M n:ℕ) (hn:2≤ n) (hnM:n * n≤ M)
    (hB:2 * (shapeCap (coefficientCap M)) ^ 2 + 3 < B):
    coefficientCap M < B∧ M < B∧ n ^ 2 < B∧ n < B∧ 5 < B∧
      n + n + n * n + 1 < B∧ 2 * M ^ 2 + 3 < B∧
      (2 * (M ^ 3 + 2) + 1) ^ 2 + M ^ 3 + 3 < B∧
      2 * (centerCap (coefficientCap M)) ^ 2 + 3 < B:=by
  have hN:=(coefficientCap_bounds M).1
  have hNS:=(shapeCap_bounds (coefficientCap M)).1
  have hSB:shapeCap (coefficientCap M) < B:=by nlinarith only [hB]
  have hNB:=hNS.trans_lt hSB
  have hMB:=hN.trans_lt hNB
  have hnB:n < B:=lt_of_le_of_lt (by nlinarith only [hn,hnM]) hMB
  have h5B:5 < B:=by
    have hlin:=shapeCap_linear (coefficientCap M)
    omega
  have hdimB:=(dimensions_le_coefficientCap n M hn hnM).trans_lt hNB
  have hMS:=hN.trans hNS
  have hpow:=Nat.pow_le_pow_left hMS 2
  have hprim:2 * M ^ 2 + 3 < B:=lt_of_le_of_lt (by omega) hB
  have hroot:=(rootBound_le_shapeBound M).trans_lt hB
  have hcenter:=Nat.pow_le_pow_left (centerCap_le_shapeCap (coefficientCap M)) 2
  refine ⟨hNB,hMB, ?_,hnB,h5B,hdimB,hprim,hroot, ?_⟩
  · simpa only [pow_two] using hnM.trans_lt hMB
  · exact lt_of_le_of_lt (by omega) hB

end Lax109476Proofs.RamEllipsoidWordBounds

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RamEllipsoidStep

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds
open RamEllipsoidUpdate RamEllipsoidWordBounds RamEllipsoidPrecision RamEllipsoidCoefficients
open RamEllipsoidScalars RamEllipsoidForm RamMatrixVector RamMatrixRows RamDotProduct RamMatrixStorage

theorem form_height (n H:ℕ) (A:Matrix (Fin n) (Fin n) ℚ) (a:Fin n→ ℚ)
    (hH:1≤ H) (hA:∀ i j,Height (A i j) H) (ha:∀ i,Height (a i) H):
    Height (a ⬝ᵥ (A *ᵥ a)) (formHeight n H):=by
  have hcap:=(cap_ge n H hH).2
  have hna:(List.ofFn a).length=n:=by simp
  have hnu:(List.ofFn (A *ᵥ a)).length=n:=by simp
  have han:∀ q∈ List.ofFn a,Height q (cap n H):=by
    intro q hq
    simp only [List.mem_ofFn] at hq
    obtain ⟨i,rfl⟩:=hq
    exact height_mono _ (ha i) hcap
  have hun:∀ q∈ List.ofFn (A *ᵥ a),Height q (cap n H):=by
    intro q hq
    simp only [List.mem_ofFn] at hq
    obtain ⟨i,rfl⟩:=hq
    exact mulVec_height n H A a hH hA ha i
  change Height (∑ j,a j * (A *ᵥ a) j) (formHeight n H)
  rw [← prefix_ofFn]
  exact prefix_height _ _ n (cap n H) n (hH.trans hcap) hna hnu le_rfl han hun

theorem coefficientCap_size (M:ℕ):(coefficientCap M).size≤ 4 * M.size + 8:=by
  have hb:=RationalSizeBounds.size_add_one_le M
  have hp:=RationalSizeBounds.size_pow_le (M + 1) 4
  have hm:=RationalSizeBounds.size_mul_le 4 ((M + 1) ^ 4)
  have hfour:Nat.size 4=3:=by decide
  unfold coefficientCap
  omega

theorem stepCost_polynomial (n H M:ℕ):
    stepCost n H M≤
      (144 * ((n + 1) * (2 * H.size + 3) + 1) + 220) * n ^ 2 +
      (144 * ((n + 1) * (2 * ((n + 1) * (2 * H.size + 3) + 1) + 3) + 1) + 292) * n +
      (2880 * M.size + 7559) * n + (14976 * M.size + 36767) * (n * n) + 582 * M.size + 1000:=by
  have hcap:=coefficientCap_size M
  have hlin:=Nat.mul_le_mul_right n (Nat.add_le_add_right (Nat.mul_le_mul_left 720 hcap) 1799)
  have hquad:=Nat.mul_le_mul_right (n * n) (Nat.add_le_add_right (Nat.mul_le_mul_left 3744 hcap) 6815)
  have hupdate:=roundedUpdate_cost_polynomial n (coefficientCap M)
  have hupdate':updateCost n (coefficientCap M)≤
      (2880 * M.size + 7559) * n + (14976 * M.size + 36767) * (n * n) + 60:=by
    have hp:=Nat.add_le_add_right (Nat.add_le_add hlin hquad) 60
    have hpay:=hupdate.trans hp
    convert hpay using 1 <;> first | rfl | ring | (simp only [updateCost] <;> ring)
  let P:=(144 * ((n + 1) * (2 * H.size + 3) + 1) + 220) * n ^ 2 +
    (144 * ((n + 1) * (2 * ((n + 1) * (2 * H.size + 3) + 1) + 3) + 1) + 292) * n + 44
  let R:=(2880 * M.size + 7559) * n + (14976 * M.size + 36767) * (n * n) + 60
  have hform:formCost n H≤ P:=ellipsoidForm_cost_polynomial n H
  have htotal:formCost n H + updateCost n (coefficientCap M)≤ P + R:=Nat.add_le_add hform hupdate'
  calc
    stepCost n H M=(formCost n H + updateCost n (coefficientCap M)) + (20 + (582 * M.size + 876)):=by
      unfold stepCost
      omega
    _≤ (P + R) + (20 + (582 * M.size + 876)):=Nat.add_le_add_right htotal _
    _=_:=by dsimp only [P,R]; ring

end Lax109476Proofs.RamEllipsoidStep

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RamEllipsoidStoredBounds

open RationalArithmeticBounds RamCenterCoordinate RamCenterUpdate RamShapeCoordinate RamShapeUpdate
open RamEllipsoidCoefficients RamEllipsoidWordBounds

theorem centerValues_height {n:ℕ} (M D:ℕ) (u c:Fin n→ ℚ) (γ:ℚ)
    (hM:1≤ M) (hD:D≤ M) (hDpos:0 < D)
    (hu:∀ i,Height (u i) M) (hc:∀ i,Height (c i) M) (hγ:Height γ M):
    ∀ i,Height (centerValues u c γ D i) (centerCap M):=by
  intro i
  have hp:Height (u i * γ) (M ^ 2):=by simpa [pow_two] using height_mul _ _ M M (hu i) hγ
  have hd:Height (c i - u i * γ) (2 * M ^ 3):=by
    have h:=height_sub _ _ M (M ^ 2) (hc i) hp
    convert h using 1
    ring
  have hr:=EllipsoidArithmeticBounds.height_roundDown _ (2 * M ^ 3) D hd hDpos
  apply height_mono _ hr
  calc
    2 * M ^ 3 * D + 1≤ 2 * M ^ 3 * M + 1:=Nat.add_le_add_right (Nat.mul_le_mul_left _ hD) 1
    _=2 * M ^ 4 + 1:=by ring
    _≤ centerCap M:=(centerCap_bounds M hM).2.2.2

set_option maxHeartbeats 500000 in
theorem shapeValues_height {n:ℕ} (M D:ℕ) (u:Fin n→ ℚ)
    (A:Matrix (Fin n) (Fin n) ℚ) (gs:List ℚ) (hg:4 < gs.length)
    (hM:1≤ M) (hD:D≤ M) (hDpos:0 < D)
    (hu:∀ i,Height (u i) M) (hA:∀ i j,Height (A i j) M)
    (hα:Height gs[0] M) (hβ:Height gs[1] M) (hρ:Height gs[3] M) (hδ:Height gs[4] M):
    ∀ i j,Height (shapeValues u A gs hg D i j) (shapeCap M):=by
  intro i j
  let p:=u i * u j
  let t:=gs[1] * p
  let d:=A i j - t
  let r:=RationalRounding.roundDown (gs[0] * d) D
  have hp:Height p (M ^ 2):=by simpa [p,pow_two] using height_mul _ _ M M (hu i) (hu j)
  have ht:Height t (M ^ 3):=by
    have h:=height_mul _ _ M (M ^ 2) hβ hp
    convert h using 1
    ring
  have hd:Height d (2 * M ^ 4):=by
    have h:=height_sub _ _ M (M ^ 3) (hA i j) ht
    convert h using 1
    ring
  have ha:Height (gs[0] * d) (2 * M ^ 5):=by
    have h:=height_mul _ _ M (2 * M ^ 4) hα hd
    convert h using 1
    ring
  have hr:Height r (2 * M ^ 6 + 1):=by
    apply height_mono _ (EllipsoidArithmeticBounds.height_roundDown _ (2 * M ^ 5) D ha hDpos)
    calc
      2 * M ^ 5 * D + 1≤ 2 * M ^ 5 * M + 1:=Nat.add_le_add_right (Nat.mul_le_mul_left _ hD) 1
      _=2 * M ^ 6 + 1:=by ring
  have hsum:Height (r + if i=j then gs[4] else 0) (6 * M ^ 7):=by
    by_cases hij:i=j
    · simp only [if_pos hij]
      apply height_mono _ (height_add _ _ (2 * M ^ 6 + 1) M hr hδ)
      have hpM:M≤ M ^ 7:=le_self_pow hM (by decide:(7:ℕ) ≠ 0)
      calc
        2 * (2 * M ^ 6 + 1) * M=4 * M ^ 7 + 2 * M:=by ring
        _≤ 6 * M ^ 7:=by omega
    · simp only [if_neg hij,add_zero]
      apply height_mono _ hr
      have hp67:=Nat.pow_le_pow_right hM (by decide:(6:ℕ)≤ 7)
      have hp1:1≤ M ^ 7:=Nat.one_le_pow _ _ hM
      omega
  have hresult:=height_mul _ _ M (6 * M ^ 7) hρ hsum
  apply height_mono _ hresult
  convert (shapeCap_bounds M).2.2.2.2.2.2.2 using 1
  ring

open RamEllipsoidStep RamEllipsoidForm RamMatrixVector RamDotProduct RamEllipsoidUpdate

theorem _root_.Lax109476Proofs.RamEllipsoidStoredBounds.step_stored_bounds (n H M k:ℕ) (A:Matrix (Fin n) (Fin n) ℚ) (a c:Fin n→ ℚ)
    (hH:1≤ H) (hA:∀ i j,Height (A i j) H) (ha:∀ i,Height (a i) H)
    (hc:∀ i,Height (c i) H) (hnM:n≤ M) (hFM:formHeight n H≤ M)
    (hDM:2 ^ (2 * k + 3 * n + 9)≤ M) (hEM:2 ^ (2 * n + 4)≤ M):
    (∀ i,Height (EllipsoidCenter.roundedCenter n A a c (2 ^ (2 * k + 3 * n + 9)) i)
        (shapeCap (coefficientCap M)))∧
      (∀ i j,Height (EllipsoidCenter.roundedStepShape n A a (2 ^ (2 * k + 3 * n + 9))
        (EllipsoidIteration.stepAccuracy n) i j) (shapeCap (coefficientCap M))):=by
  let D:=2 ^ (2 * k + 3 * n + 9)
  let E:=2 ^ (2 * n + 4)
  let q:=a ⬝ᵥ (A *ᵥ a)
  let N:=coefficientCap M
  let gs:=coefficients n q D E
  have hcapM:=(formHeight_ge n H hH).trans hFM
  have hHM:=(cap_ge n H hH).2.trans hcapM
  have hM:=hH.trans hHM
  have hMN:M≤ N:=(coefficientCap_bounds M).1
  have hN:1≤ N:=hM.trans hMN
  have hDpos:0 < D:=Nat.pow_pos (by decide)
  have hq:Height q M:=height_mono _ (form_height n H A a hH hA ha) hFM
  have hu:∀ i,Height ((A *ᵥ a) i) N:=fun i =>
    height_mono _ (mulVec_height n H A a hH hA ha i) (hcapM.trans hMN)
  have hAc:∀ i j,Height (A i j) N:=fun i j => height_mono _ (hA i j) (hHM.trans hMN)
  have hcc:∀ i,Height (c i) N:=fun i => height_mono _ (hc i) (hHM.trans hMN)
  have hgs:∀ v∈ gs,Height v N:=coefficients_height n M D E q hq hnM hDM hEM hDpos
  have hg:4 < gs.length:=by simp [gs,coefficients]
  have hα:=hgs gs[0] (by simp [gs,coefficients])
  have hβ:=hgs gs[1] (by simp [gs,coefficients])
  have hγ:=hgs gs[2] (by simp [gs,coefficients])
  have hρ:=hgs gs[3] (by simp [gs,coefficients])
  have hδ:=hgs gs[4] (by simp [gs,coefficients])
  have hcenter:=centerValues_height N D (A *ᵥ a) c gs[2] hN (hDM.trans hMN) hDpos hu hcc hγ
  have hshape:=shapeValues_height N D (A *ᵥ a) A gs hg hN (hDM.trans hMN) hDpos hu hAc hα hβ hρ hδ
  have heq:=roundedUpdate_eq_ellipsoid A a c D E
  have hη:(1 / (E:ℚ))=EllipsoidIteration.stepAccuracy n:=by simp [E,EllipsoidIteration.stepAccuracy]
  change (∀ i,Height (EllipsoidCenter.roundedCenter n A a c D i) (shapeCap N))∧
    (∀ i j,Height (EllipsoidCenter.roundedStepShape n A a D (EllipsoidIteration.stepAccuracy n) i j) (shapeCap N))
  constructor
  · intro i
    have h:=height_mono _ (hcenter i) (centerCap_le_shapeCap N)
    simpa only [gs,q,heq.1] using h
  · intro i j
    simpa only [gs,q,heq.2,hη] using hshape i j

end Lax109476Proofs.RamEllipsoidStoredBounds

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RamAdvanceState

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RationalArithmeticBounds RamEllipsoidStep RamCommitState
open RamEllipsoidCoefficients RamEllipsoidWordBounds RamEllipsoidStoredBounds RamMatrixStorage

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

theorem workspace_of_run {B K:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ K)
    (n:ℕ) (hσ:Workspace n σ):Workspace n τ:=
  ⟨extents_of_run hr _ _ hσ.1,extents_of_run hr _ _ hσ.2.1,
    extents_of_run hr _ _ hσ.2.2.1,extents_of_run hr _ _ hσ.2.2.2⟩

end Lax109476Proofs.RamAdvanceState

end

section

namespace Lax109476Proofs.RamReadBody

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamReadArray RamReadBlock RamRationalArrays RamFrame RamEllipsoidStep RamAdvanceState

theorem finishInput_spec (B r v:ℕ) (hrB:r < B):
    Spec B (fun σ => σ.vars "input.remaining"=r∧ σ.vars "input.valid"=v)
      finishInput (fun _ τ => τ.vars "input.remaining"=r∧
        τ.vars "input.valid"=if r=0 then v else 0) 6:=by
  have h0:0 < B:=by omega
  rintro σ ⟨hσr,hσv⟩
  (expose_names;
    refine
        let c0:Prop:= @Eq Nat (Env.vars σ "input.remaining") ((0:Nat));
        let c1:Prop:=Not c0;
        let c2:Nat:=
          @ite Nat (@Eq Nat r ((0:Nat)))
            (instDecidableEqNat r ((0:Nat))) v
            ((0:Nat));
        let c3:Env→ Prop:=
          (fun (x τ:Env) => And (@Eq Nat (Env.vars τ "input.remaining") r) (@Eq Nat (Env.vars τ "input.valid") c2)) σ;
        let c4:Env→ Prop:=fun (σ':Env) =>
          And (Run B finishInput σ σ' ((6:Nat))) (c3 σ');
        let c5:∀ (w:Env),c4 w→ @Exists Env c4:= @Exists.intro Env c4;
        let c6:Nat→ Nat→ Nat:=Nat.add;
        let c7:Nat→ Nat:=c6 ((1:Nat));
        let c8:Cond:=
          Cond.eq (Expr.var "input.remaining") (Expr.lit ((0:Nat)));
        let c9:Nat→ Nat:=c6 (c7 (Cond.size c8));
        let c10:Com:=Com.assign "input.valid" (Expr.lit ((0:Nat)));
        let c11:
          @Eq (Option Nat) (Expr.evalB B (Expr.lit ((0:Nat))) σ)
            (@some Nat ((0:Nat))):=
          RunStep.eval_lit B ((0:Nat)) σ h0;
        let c12:Env:=Env.setVar σ "input.valid" ((0:Nat));
        let c13:Nat:=c7 (Expr.size (Expr.lit ((0:Nat))));
        let c14:String→ Nat:=Env.vars c12;
        @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c4) (Classical.em c0)
          (fun (hcase:c0) =>
            c5 σ
              (@And.intro (Run B finishInput σ σ ((6:Nat))) (c3 σ)
                (RunStep.mono B finishInput σ σ (c9 ((1:Nat)))
                  ((6:Nat))
                  (RunStep.ite_true B c8 Com.skip c10 σ σ ((1:Nat))
                    (RunStep.cond_eq_true B σ (Expr.var "input.remaining")
                      (Expr.lit ((0:Nat))) (Env.vars σ "input.remaining")
                      ((0:Nat))
                      (RunStep.eval_var B σ "input.remaining"
                        (?nAX_g4367_0_0_0))
                      c11 hcase)
                    (RunStep.skip B σ))
                  (?nAX_g4367_0_0_1))
                ?_))
          fun (hcase:c1) =>
          c5 c12
            (@And.intro (Run B finishInput σ c12 ((6:Nat))) (c3 c12)
              (RunStep.mono B finishInput σ c12 (c9 c13) ((6:Nat))
                (RunStep.ite_false B c8 Com.skip c10 σ c12 c13
                  (RunStep.cond_eq_false B σ (Expr.var "input.remaining")
                    (Expr.lit ((0:Nat))) (Env.vars σ "input.remaining")
                    ((0:Nat))
                    (RunStep.eval_var B σ "input.remaining"
                      (?nAX_g4367_0_0_2))
                    c11 hcase)
                  (RunStep.assign B σ "input.valid" (Expr.lit ((0:Nat)))
                    ((0:Nat)) c11))
                (?nAX_g4367_0_0_3))
              ?_) <;> try dsimp +zetaDelta at *
   all_goals try dsimp +zetaDelta at *
   try case nAX_g4367_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g4367_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g4367_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g4367_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all
  )
  all_goals simp_all [Env.setVar]

def afterA (xs:List ℕ) (m n:ℕ):List ℕ:=xs.drop (3 * (m * n))
def flagA (xs:List ℕ) (v m n:ℕ):ℕ:=flag xs v (m * n)
def afterB (xs:List ℕ) (m n:ℕ):List ℕ:=(afterA xs m n).drop (3 * m)
def flagB (xs:List ℕ) (v m n:ℕ):ℕ:=flag (afterA xs m n) (flagA xs v m n) m
def afterC (xs:List ℕ) (m n:ℕ):List ℕ:=(afterB xs m n).drop (3 * n)
def flagC (xs:List ℕ) (v m n:ℕ):ℕ:=flag (afterB xs m n) (flagB xs v m n) n

def Result (B:ℕ) (xs:List ℕ) (v m n:ℕ) (σ:Env):Prop:=
  Represents "lp.A" (List.ofFn (values xs v (m * n))) σ∧
    Represents "lp.b" (List.ofFn (values (afterA xs m n) (flagA xs v m n) m)) σ∧
    Represents "lp.c" (List.ofFn (values (afterB xs m n) (flagB xs v m n) n)) σ∧
    σ.inp=afterC xs m n∧ σ.vars "input.remaining"=(afterC xs m n).length∧
    σ.vars "input.valid"=(if (afterC xs m n).length=0 then flagC xs v m n else 0)∧
    σ.InpBounded B∧ σ.vars "lp.m"=m∧ σ.vars "lp.n"=n∧ σ.vars "decode.count"=m * n

theorem represents_frame {B K:ℕ} {c:Com} {σ τ:Env} (a:String) (qs:List ℚ)
    (hσ:Represents a qs σ) (hr:Run B c σ τ K)
    (ha:∀ s∈ [".s", ".n", ".d"],a ++ s∉ c.warrs):Represents a qs τ:=by
  simpa only [Represents,hr.frame_arr (a ++ ".s") (ha ".s" (by simp)),
    hr.frame_arr (a ++ ".n") (ha ".n" (by simp)),
    hr.frame_arr (a ++ ".d") (ha ".d" (by simp))] using hσ

theorem readBody_spec (B M m n v:ℕ) (xs:List ℕ)
    (h2:2 < B) (hMB:M < B) (hM:1≤ M) (hmB:m < B) (hnB:n < B)
    (hmnB:m * n < B) (hxB:xs.length < B) (hv:v≤ 1)
    (hwords:∀ z∈ xs,z≤ M):
    Spec B (fun σ => Extents "lp.A" (m * n) σ∧ Extents "lp.b" m σ∧ Extents "lp.c" n σ∧
        σ.inp=xs∧ σ.vars "input.remaining"=xs.length∧ σ.vars "input.valid"=v∧
        σ.InpBounded B∧ σ.vars "lp.m"=m∧ σ.vars "lp.n"=n∧ σ.vars "decode.count"=m * n)
      readBody (fun _ τ => Result B xs v m n τ)
      ((36 * M.size + 115) * (m * n + m + n) + 84):=by
  rintro σ ⟨hσA,hσb,hσc,hσinp,hσrem,hσvalid,hσbound,hσm,hσn,hσcount⟩
  obtain ⟨τ,hr₁,hτA,hτinp,hτrem,hτvalid,hτbound,hτfields,_⟩:=
    readBlock_spec B M (m * n) v "lp.A" "decode.count" xs h2 hMB hM hmnB hxB hv hwords
      (by simp [fields]) σ
      ⟨hσA ".s" (by simp),hσA ".n" (by simp),
        hσA ".d" (by simp),hσinp,hσrem,hσvalid,hσbound,hσcount⟩
  have hτb:=extents_of_run hr₁ "lp.b" m hσb
  have hτc:=extents_of_run hr₁ "lp.c" n hσc
  have hxAB:(afterA xs m n).length < B:=by dsimp [afterA]; simp only [List.length_drop]; omega
  have hwordsA:∀ z∈ afterA xs m n,z≤ M:=
    fun z hz => hwords z (List.mem_of_mem_drop hz)
  have hvA:flagA xs v m n≤ 1:=flag_le_one xs v (m * n) hv
  obtain ⟨υ,hr₂,hυb,hυinp,hυrem,hυvalid,hυbound,hυfields,harr₂⟩:=
    readBlock_spec B M m (flagA xs v m n) "lp.b" "lp.m" (afterA xs m n)
      h2 hMB hM hmB hxAB hvA hwordsA (by simp [fields]) τ
      ⟨hτb ".s" (by simp),hτb ".n" (by simp),
        hτb ".d" (by simp),hτinp,hτrem,hτvalid,hτbound,
        (hτfields _ (by simp [fields])).trans hσm⟩
  have hυA:Represents "lp.A" (List.ofFn (values xs v (m * n))) υ:=by
    simpa [Represents,harr₂ "lp.A.s" (by decide),harr₂ "lp.A.n" (by decide),
      harr₂ "lp.A.d" (by decide)] using hτA
  have hυc:=extents_of_run hr₂ "lp.c" n hτc
  have hxBB:(afterB xs m n).length < B:=by dsimp [afterB]; simp only [List.length_drop]; omega
  have hwordsB:∀ z∈ afterB xs m n,z≤ M:=
    fun z hz => hwordsA z (List.mem_of_mem_drop hz)
  have hvB:flagB xs v m n≤ 1:=flag_le_one _ _ m hvA
  obtain ⟨ξ,hr₃,hξc,hξinp,hξrem,hξvalid,hξbound,hξfields,harr₃⟩:=
    readBlock_spec B M n (flagB xs v m n) "lp.c" "lp.n" (afterB xs m n)
      h2 hMB hM hnB hxBB hvB hwordsB (by simp [fields]) υ
      ⟨hυc ".s" (by simp),hυc ".n" (by simp),
        hυc ".d" (by simp),hυinp,hυrem,hυvalid,hυbound,
        (hυfields _ (by simp [fields])).trans ((hτfields _ (by simp [fields])).trans hσn)⟩
  have hξA:Represents "lp.A" (List.ofFn (values xs v (m * n))) ξ:=by
    simpa [Represents,harr₃ "lp.A.s" (by decide),harr₃ "lp.A.n" (by decide),
      harr₃ "lp.A.d" (by decide)] using hυA
  have hξb:Represents "lp.b" (List.ofFn (values (afterA xs m n) (flagA xs v m n) m)) ξ:=by
    simpa [Represents,harr₃ "lp.b.s" (by decide),harr₃ "lp.b.n" (by decide),
      harr₃ "lp.b.d" (by decide)] using hυb
  have hxCB:(afterC xs m n).length < B:=by dsimp [afterC]; simp only [List.length_drop]; omega
  obtain ⟨ρ,hr₄,hρrem,hρvalid⟩:=finishInput_spec B (afterC xs m n).length (flagC xs v m n)
    hxCB ξ ⟨hξrem,hξvalid⟩
  have hrun:=hr₁.seq (hr₂.seq (hr₃.seq hr₄))
  have hfields:=fieldsAgree_trans fields σ τ ξ hτfields
    (fieldsAgree_trans fields τ υ ξ hυfields hξfields)
  refine ⟨ρ,hrun.mono (by simp only [Nat.mul_add]; omega), ⟨?_, ?_, ?_, ?_,hρrem,
    hρvalid,hrun.inpBounded hσbound, ?_, ?_, ?_⟩⟩
  · exact represents_frame _ _ hξA hr₄ (by decide)
  · exact represents_frame _ _ hξb hr₄ (by decide)
  · exact represents_frame _ _ hξc hr₄ (by decide)
  · exact (hr₄.frame_inp (by decide)).trans hξinp
  · exact (hr₄.frame_var "lp.m" (by decide)).trans ((hfields _ (by simp [fields])).trans hσm)
  · exact (hr₄.frame_var "lp.n" (by decide)).trans ((hfields _ (by simp [fields])).trans hσn)
  · exact (hr₄.frame_var "decode.count" (by decide)).trans ((hfields _ (by simp [fields])).trans hσcount)

theorem encodedResult_correct (B m n:ℕ) (P:Lax109476.LinearProgram.Program ℚ m n) (τ:Env)
    (hτ:Result B (WordDecoding.encodeRows P.A ++ Lax109476.RationalEncoding.encodeVector P.b ++
      Lax109476.RationalEncoding.encodeVector P.c) 1 m n τ):
    Represents "lp.A" (RamMatrixStorage.flatten P.A) τ∧
      Represents "lp.b" (List.ofFn P.b) τ∧ Represents "lp.c" (List.ofFn P.c) τ∧
      τ.inp=[]∧ τ.vars "input.remaining"=0∧ τ.vars "input.valid"=1∧
      τ.InpBounded B∧ τ.vars "lp.m"=m∧ τ.vars "lp.n"=n∧ τ.vars "decode.count"=m * n:=by
  let xs:=WordDecoding.encodeRows P.A ++ Lax109476.RationalEncoding.encodeVector P.b ++
    Lax109476.RationalEncoding.encodeVector P.c
  have ha:WordDecoding.readVector (m * n) xs =
      some ((fun k:Fin (m * n) => P.A k.divNat k.modNat),
        Lax109476.RationalEncoding.encodeVector P.b ++ Lax109476.RationalEncoding.encodeVector P.c):=by
    dsimp [xs]
    rw [List.append_assoc,RamReadMatrix.encodeRows_flat]
    exact WordDecoding.readVector_encode _ _ _
  have hb:=WordDecoding.readVector_encode m P.b (Lax109476.RationalEncoding.encodeVector P.c)
  have hc:=WordDecoding.readVector_encode n P.c []
  simp only [List.append_nil] at hc
  have hA:=readVector_correct _ _ _ _ ha
  have hb':=readVector_correct _ _ _ _ hb
  have hc':=readVector_correct _ _ _ _ hc
  change Result B xs 1 m n τ at hτ
  dsimp only [Result,afterA,afterB,afterC,flagA,flagB,flagC] at hτ
  simp only [hA.1,hA.2.1,hA.2.2,hb'.1,hb'.2.1,hb'.2.2,
    hc'.1,hc'.2.1,hc'.2.2] at hτ
  simpa only [RamMatrixStorage.flatten,List.length_nil,if_true] using hτ

theorem readBody_valid_spec (B M m n:ℕ) (P:Lax109476.LinearProgram.Program ℚ m n)
    (h2:2 < B) (hMB:M < B) (hM:1≤ M) (hmB:m < B) (hnB:n < B)
    (hmnB:m * n < B)
    (hxB:(WordDecoding.encodeRows P.A ++ Lax109476.RationalEncoding.encodeVector P.b ++
      Lax109476.RationalEncoding.encodeVector P.c).length < B)
    (hwords:∀ z∈ WordDecoding.encodeRows P.A ++ Lax109476.RationalEncoding.encodeVector P.b ++
      Lax109476.RationalEncoding.encodeVector P.c,z≤ M):
    Spec B (fun σ => Extents "lp.A" (m * n) σ∧ Extents "lp.b" m σ∧ Extents "lp.c" n σ∧
        σ.inp=WordDecoding.encodeRows P.A ++ Lax109476.RationalEncoding.encodeVector P.b ++
          Lax109476.RationalEncoding.encodeVector P.c∧
        σ.vars "input.remaining"=(WordDecoding.encodeRows P.A ++
          Lax109476.RationalEncoding.encodeVector P.b ++ Lax109476.RationalEncoding.encodeVector P.c).length∧
        σ.vars "input.valid"=1∧ σ.InpBounded B∧
        σ.vars "lp.m"=m∧ σ.vars "lp.n"=n∧ σ.vars "decode.count"=m * n)
      readBody
      (fun _ τ => Represents "lp.A" (RamMatrixStorage.flatten P.A) τ∧
        Represents "lp.b" (List.ofFn P.b) τ∧ Represents "lp.c" (List.ofFn P.c) τ∧
        τ.inp=[]∧ τ.vars "input.remaining"=0∧ τ.vars "input.valid"=1∧
        τ.InpBounded B∧ τ.vars "lp.m"=m∧ τ.vars "lp.n"=n∧ τ.vars "decode.count"=m * n)
      ((36 * M.size + 115) * (m * n + m + n) + 84):=by
  apply (readBody_spec B M m n 1 _ h2 hMB hM hmB hnB hmnB hxB (by decide) hwords).post
  intro σ τ hσ hτ
  exact encodedResult_correct B m n P τ hτ

end Lax109476Proofs.RamReadBody

end

section

namespace Lax109476Proofs.RamEllipsoidBitBounds

open RamDotProduct RamEllipsoidForm RamEllipsoidStep RamEllipsoidCoefficients
open RamShapeCoordinate RamShapeUpdate RationalSizeBounds

theorem cap_two_pow (n h:ℕ):cap n (2 ^ h)=2 ^ ((2 * h + 1) * (n + 1)):=by
  simp only [cap, ← pow_two]
  change (2 ^ 1 * (2 ^ h) ^ 2) ^ (n + 1)=_
  rw [← pow_mul, ← pow_add, ← pow_mul]
  congr 1
  ring

theorem formHeight_two_pow (n h:ℕ):formHeight n (2 ^ h)=2 ^ formExponent n h:=by
  simp only [formHeight,cap_two_pow,formExponent]

theorem guard_size (M:ℕ):
    (2 * (shapeCap (coefficientCap M)) ^ 2 + 3).size≤ 64 * M.size + 160:=by
  have hc:=coefficientCap_size M
  have hs:=shapeCap_size (coefficientCap M)
  have hp:=size_pow_le (shapeCap (coefficientCap M)) 2
  have hm:=size_mul_le 2 ((shapeCap (coefficientCap M)) ^ 2)
  have ha:=size_add_le (2 * (shapeCap (coefficientCap M)) ^ 2) 3
  have htwo:Nat.size 2=2:=by decide
  have hthree:Nat.size 3=2:=by decide
  omega

theorem magnitude_parameters (n h k:ℕ):
    n * n≤ 2 ^ magnitudeExponent n h k∧
      formHeight n (2 ^ h)≤ 2 ^ magnitudeExponent n h k∧
      2 ^ (2 * k + 3 * n + 9)≤ 2 ^ magnitudeExponent n h k∧
      2 ^ (2 * n + 4)≤ 2 ^ magnitudeExponent n h k:=by
  have hn:n * n < 2 ^ (n * n):=Nat.lt_two_pow_self
  have hexp:n * n≤ magnitudeExponent n h k:=by unfold magnitudeExponent; omega
  refine ⟨hn.le.trans (Nat.pow_le_pow_right (by decide) hexp), ?_, ?_, ?_⟩
  · rw [formHeight_two_pow]
    apply Nat.pow_le_pow_right (by decide)
    unfold magnitudeExponent
    omega
  · apply Nat.pow_le_pow_right (by decide)
    unfold magnitudeExponent
    omega
  · apply Nat.pow_le_pow_right (by decide)
    unfold magnitudeExponent
    omega

theorem wordWidth_sufficient (n h k w:ℕ) (hw:wordWidth n h k≤ w):
    2 * (shapeCap (coefficientCap (2 ^ magnitudeExponent n h k))) ^ 2 + 3 < 2 ^ w:=by
  have hg:=guard_size (2 ^ magnitudeExponent n h k)
  rw [Nat.size_pow] at hg
  have hp:=Nat.lt_size_self (2 * (shapeCap (coefficientCap (2 ^ magnitudeExponent n h k))) ^ 2 + 3)
  apply hp.trans_le
  apply Nat.pow_le_pow_right (by decide)
  unfold wordWidth at hw
  omega

end Lax109476Proofs.RamEllipsoidBitBounds

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

end Lax109476Proofs.RamArrayRelabel

end

section

namespace Lax109476Proofs.RamWriteVector

open Lax109476.RationalEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RationalArithmeticBounds

def Invariant (a:String) (xs:List ℚ) (O:List ℕ) (N:ℕ) (σ:Env):Prop:=
  Represents a xs σ∧ σ.vars "output.i" ≤ N∧ σ.vars "output.count"=N∧
    σ.out=O ++ (xs.take (σ.vars "output.i")).flatMap encodeRational

theorem step_spec (B M N:ℕ) (a:String) (xs:List ℚ) (O:List ℕ)
    (h1:1 < B) (hMB:M < B) (hNB:N < B) (hN:N≤ xs.length)
    (hq:∀ q∈ xs,Height q M):
    Spec B (fun σ => Invariant a xs O N σ∧ σ.vars "output.i" < N) (step a)
      (fun σ τ => Invariant a xs O N τ∧ τ.vars "output.i"=σ.vars "output.i" + 1) 31:=by
  rintro σ ⟨⟨hσa,hσi,hσcount,hσout⟩,hi⟩
  let i:=σ.vars "output.i"
  have hil:i < xs.length:=hi.trans_le hN
  have hiB:i < B:=hi.trans hNB
  have hheight:=hq xs[i] (List.getElem_mem hil)
  have hr₁:Run B (.assign "vec.i" (.var "output.i")) σ (σ.setVar "vec.i" i) 2:=
    Run.assign (evalB_var hiB)
  obtain ⟨τ,hr₂,hτq⟩:=RamArrayResult.load_spec B a xs i hil h1 hiB
    (hheight.1.trans_lt hMB) (hheight.2.trans_lt hMB) (σ.setVar "vec.i" i) ⟨hσa,by simp⟩
  obtain ⟨υ,hr₃,hυout⟩:=RamEncoding.writeReducedFraction_spec B xs[i] h1
    (hheight.1.trans_lt hMB) (hheight.2.trans_lt hMB) τ hτq
  have hυi:υ.vars "output.i"=i:=
    ((hr₁.seq (hr₂.seq hr₃)).frame_var _ (by
      change "output.i" ∉ (Com.seq (.assign "vec.i" (.var "output.i"))
        (.seq (RamArrayResult.load "") RamEncoding.writeReducedFraction)).wvars
      decide)).trans rfl
  have hsum:Bop.add.apply (υ.vars "output.i") 1 < B:=by simpa [hυi] using (show i + 1 < B by dsimp only [i]; omega)
  have hr₄:Run B increment υ (υ.setVar "output.i" (i + 1)) 4:=
    Run.assign (by simpa only [hυi,Bop.apply_add] using (evalB_bin
      (evalB_var (B:=B) (σ:=υ) (x:= "output.i") (hυi ▸ hiB)) (evalB_lit h1) hsum))
  let ρ:=υ.setVar "output.i" (i + 1)
  have hr:=hr₁.seq (hr₂.seq (hr₃.seq hr₄))
  have hτout:τ.out=σ.out:=(hr₁.seq hr₂).out_eq (by
    change (Com.seq (.assign "vec.i" (.var "output.i")) (RamArrayResult.load "")).NoWrite
    decide)
  have hρout:ρ.out=O ++ (xs.take (i + 1)).flatMap encodeRational:=by
    change υ.out=_
    rw [hυout,hτout,hσout,List.take_succ_eq_append_getElem hil,List.flatMap_append]
    simp [i,List.append_assoc]
  refine ⟨ρ,hr, ⟨RamReadBody.represents_frame _ _ hσa hr (by intro s hs; change _∉ ([]:List String); simp),
    ?_, (hr.frame_var "output.count" (by change "output.count" ∉ (step "").wvars; decide)).trans hσcount, ?_⟩, ?_⟩
  · change i + 1≤ N; dsimp only [i]; omega
  · simpa only [ρ,vars_setVar,ite_true] using hρout
  · simp [ρ,i]

theorem writePrefix_spec (B M N:ℕ) (a:String) (xs:List ℚ)
    (h1:1 < B) (hMB:M < B) (hNB:N < B) (hN:N≤ xs.length)
    (hq:∀ q∈ xs,Height q M):
    Spec B (fun σ => Represents a xs σ∧ σ.vars "output.count"=N) (writePrefix a)
      (fun σ τ => τ.out=σ.out ++ (xs.take N).flatMap encodeRational) (35 * N + 6):=by
  rintro σ ⟨hσa,hσcount⟩
  have hlo:=Spec.forRangeZero "output.i" "output.count" (Invariant a xs σ.out N) N 31 hNB
    (fun _ h => h.2.1) (fun _ h => h.2.2.1) (step_spec B M N a xs σ.out h1 hMB hNB hN hq)
  obtain ⟨τ,hr,hτ,hcounter⟩:=hlo σ ⟨hσa,by simp,by simpa using hσcount,by simp⟩
  exact ⟨τ,hr,by simpa only [hcounter] using hτ.2.2.2⟩

end Lax109476Proofs.RamWriteVector

end

section

namespace Lax109476Proofs.RamTransfer

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Transfer
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime

def layoutAllowance (L:Layout):ℕ:=
  L.temps + 2 + L.scalars.length + L.arrays.length + 1

theorem layout_fits {L:Layout} {v w:ℕ} (hv:0 < v)
    (hw:v + layoutAllowance L≤ w):L.FitsWords (2 ^ v) w:=by
  have hB:1 < 2 ^ v:=Nat.one_lt_pow (ne_of_gt hv) (by decide)
  have hc:layoutAllowance L≤ 2 ^ layoutAllowance L:=Nat.lt_two_pow_self.le
  have hs:max (2 ^ v) (L.span (2 ^ v))≤ 2 ^ (v + layoutAllowance L):=by
    rw [pow_add]
    apply max_le
    · exact Nat.le_mul_of_pos_right _ (by positivity)
    · unfold Layout.span
      have hp:1≤ 2 ^ v:=hB.le
      calc
        _≤ (L.temps + 2 + L.scalars.length) * 2 ^ v + L.arrays.length * 2 ^ v:=by
          exact Nat.add_le_add_right (Nat.le_mul_of_pos_right _ hp) _
        _≤ layoutAllowance L * 2 ^ v:=by unfold layoutAllowance; nlinarith
        _≤ _:=by simpa [Nat.mul_comm] using Nat.mul_le_mul_right (2 ^ v) hc
  exact fitsWords_of_max_le hB (hs.trans (Nat.pow_le_pow_right (by decide) hw))

end Lax109476Proofs.RamTransfer

end

section

namespace Lax109476Proofs.RamAutomaticLayout

open Lax808846Proofs.Imp Lax808846Proofs.Compile

def expressionNames:Expr→ List String × List String
  | .lit _ => ([], [])
  | .var x => ([x], [])
  | .get a i => let old:=expressionNames i; (old.1,a::old.2)
  | .bin _ e f => let a:=expressionNames e; let b:=expressionNames f; (a.1 ++ b.1,a.2 ++ b.2)

def conditionNames (b:Cond):List String × List String:=expressionNames (condExpr b)

def commandNames:Com→ List String × List String
  | .skip => ([], [])
  | .assign x e => let a:=expressionNames e; (x::a.1,a.2)
  | .store x i e => let a:=expressionNames i; let b:=expressionNames e; (a.1 ++ b.1,x::(a.2 ++ b.2))
  | .seq c d => let a:=commandNames c; let b:=commandNames d; (a.1 ++ b.1,a.2 ++ b.2)
  | .ite b c d => let a:=conditionNames b; let x:=commandNames c; let y:=commandNames d;
      (a.1 ++ x.1 ++ y.1,a.2 ++ x.2 ++ y.2)
  | .while b c => let a:=conditionNames b; let x:=commandNames c; (a.1 ++ x.1,a.2 ++ x.2)
  | .read x => ([x], [])
  | .write e => expressionNames e

def commandDepth:Com→ ℕ
  | .skip | .read _ => 1
  | .assign _ e | .write e => e.size + 2
  | .store _ i e => max i.size e.size + 2
  | .seq c d => max (commandDepth c) (commandDepth d)
  | .ite b c d => max (condExpr b).size (max (commandDepth c) (commandDepth d)) + 2
  | .while b c => max (condExpr b).size (commandDepth c) + 2

def layout (c:Com):Layout:= ⟨(commandNames c).1, (commandNames c).2,commandDepth c + 2⟩

theorem expression_ok (e:Expr) (L:Layout) (d:ℕ)
    (hv:(expressionNames e).1 ⊆ L.scalars) (ha:(expressionNames e).2 ⊆ L.arrays)
    (hd:d + e.size < L.temps):Expr.Ok L e d:=by
  induction e generalizing d with
  | lit v => trivial
  | var x => exact hv (by simp [expressionNames])
  | get a i ih =>
    refine ⟨ha (by simp [expressionNames]),ih d
      (by simpa [expressionNames] using hv)
      (fun x hx => ha (by simp [expressionNames,hx])) ?_, ?_⟩
    all_goals simp only [Expr.size] at hd; omega
  | bin op e f ihe ihf =>
    have hve:(expressionNames e).1 ⊆ L.scalars:=fun x hx => hv (by simp [expressionNames,hx])
    have hvf:(expressionNames f).1 ⊆ L.scalars:=fun x hx => hv (by simp [expressionNames,hx])
    have hae:(expressionNames e).2 ⊆ L.arrays:=fun x hx => ha (by simp [expressionNames,hx])
    have haf:(expressionNames f).2 ⊆ L.arrays:=fun x hx => ha (by simp [expressionNames,hx])
    simp only [Expr.Ok]
    exact ⟨ihf d hvf haf (by simp only [Expr.size] at hd; omega),
      ihe (d + 1) hve hae (by simp only [Expr.size] at hd; omega),
      by simp only [Expr.size] at hd; omega⟩

theorem command_ok (c:Com) (L:Layout)
    (hv:(commandNames c).1 ⊆ L.scalars) (ha:(commandNames c).2 ⊆ L.arrays)
    (hd:commandDepth c < L.temps):Com.Ok L c:=by
  induction c with
  | skip => trivial
  | read x => exact hv (by simp [commandNames])
  | assign x e =>
    refine ⟨hv (by simp [commandNames]),expression_ok e L 0
      (fun x hx => hv (by simp [commandNames,hx])) (by simpa [commandNames] using ha) ?_⟩
    simp only [commandDepth] at hd; omega
  | store a i e =>
    refine ⟨ha (by simp [commandNames]),expression_ok i L 0
      (fun x hx => hv (by simp [commandNames,hx])) (fun x hx => ha (by simp [commandNames,hx])) ?_,
      expression_ok e L 1 (fun x hx => hv (by simp [commandNames,hx]))
        (fun x hx => ha (by simp [commandNames,hx])) ?_, ?_⟩
    all_goals simp only [commandDepth] at hd; omega
  | write e =>
    refine ⟨expression_ok e L 0 hv ha ?_, ?_⟩
    all_goals simp only [commandDepth] at hd; omega
  | seq c d ihc ihd =>
    refine ⟨ihc (fun x hx => hv (by simp [commandNames,hx]))
      (fun x hx => ha (by simp [commandNames,hx])) ?_,
      ihd (fun x hx => hv (by simp [commandNames,hx]))
        (fun x hx => ha (by simp [commandNames,hx])) ?_⟩
    all_goals simp only [commandDepth] at hd; omega
  | ite b c d ihc ihd =>
    refine ⟨expression_ok (condExpr b) L 0
      (fun x hx => hv (by simp [commandNames,conditionNames,hx]))
      (fun x hx => ha (by simp [commandNames,conditionNames,hx])) ?_,
      ihc (fun x hx => hv (by simp [commandNames,hx])) (fun x hx => ha (by simp [commandNames,hx])) ?_,
      ihd (fun x hx => hv (by simp [commandNames,hx])) (fun x hx => ha (by simp [commandNames,hx])) ?_⟩
    all_goals simp only [commandDepth] at hd; omega
  | «while» b c ih =>
    refine ⟨expression_ok (condExpr b) L 0
      (fun x hx => hv (by simp [commandNames,conditionNames,hx]))
      (fun x hx => ha (by simp [commandNames,conditionNames,hx])) ?_,
      ih (fun x hx => hv (by simp [commandNames,hx])) (fun x hx => ha (by simp [commandNames,hx])) ?_⟩
    all_goals simp only [commandDepth] at hd; omega

theorem layout_ok (c:Com):Com.Ok (layout c) c:=
  command_ok c (layout c) (fun _ h => h) (fun _ h => h) (by simp [layout])

end Lax109476Proofs.RamAutomaticLayout

end

section

namespace Lax263307Proofs.RoundedOracleSearch

open Matrix Lax263307.RoundedOracleSearch
open Lax109476.RationalCertificates

theorem cached_eq {n:ℕ} (state:State n):cached state=state:=by
  apply Prod.ext
  · funext i j
    simp [cached,Vector.get]
    rfl
  · funext i
    simp [cached,Vector.get]
    rfl

end Lax263307Proofs.RoundedOracleSearch

end

section

set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

namespace Lax263307Proofs.NativeRoundedStep

open Matrix
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax109476Proofs
open RamRationalArrays RamEllipsoidStep RamMatrixStorage RationalArithmeticBounds
open Lax109476.RationalEncoding

def body {n:ℕ} (A:Matrix (Fin n) (Fin n) ℚ) (a c:Fin n→ ℚ):List ℕ:=
  WordDecoding.encodeRows A ++ encodeVector a ++ encodeVector c

def rename (a:String):String:=
  if a="lp.A.s" then "ell.shape.s" else
  if a="lp.A.n" then "ell.shape.n" else
  if a="lp.A.d" then "ell.shape.d" else
  if a="lp.b.s" then "ell.normal.s" else
  if a="lp.b.n" then "ell.normal.n" else
  if a="lp.b.d" then "ell.normal.d" else
  if a="lp.c.s" then "ell.center.s" else
  if a="lp.c.n" then "ell.center.n" else
  if a="lp.c.d" then "ell.center.d" else
  if a="ell.shape.s" then "lp.A.s" else
  if a="ell.shape.n" then "lp.A.n" else
  if a="ell.shape.d" then "lp.A.d" else
  if a="ell.normal.s" then "lp.b.s" else
  if a="ell.normal.n" then "lp.b.n" else
  if a="ell.normal.d" then "lp.b.d" else
  if a="ell.center.s" then "lp.c.s" else
  if a="ell.center.n" then "lp.c.n" else
  if a="ell.center.d" then "lp.c.d" else a

theorem rename_involutive:Function.Involutive rename:=by
  intro a
  by_cases h0:a="lp.A.s"
  · subst a
    rfl
  by_cases h1:a="lp.A.n"
  · subst a
    rfl
  by_cases h2:a="lp.A.d"
  · subst a
    rfl
  by_cases h3:a="lp.b.s"
  · subst a
    rfl
  by_cases h4:a="lp.b.n"
  · subst a
    rfl
  by_cases h5:a="lp.b.d"
  · subst a
    rfl
  by_cases h6:a="lp.c.s"
  · subst a
    rfl
  by_cases h7:a="lp.c.n"
  · subst a
    rfl
  by_cases h8:a="lp.c.d"
  · subst a
    rfl
  by_cases h9:a="ell.shape.s"
  · subst a
    rfl
  by_cases h10:a="ell.shape.n"
  · subst a
    rfl
  by_cases h11:a="ell.shape.d"
  · subst a
    rfl
  by_cases h12:a="ell.normal.s"
  · subst a
    rfl
  by_cases h13:a="ell.normal.n"
  · subst a
    rfl
  by_cases h14:a="ell.normal.d"
  · subst a
    rfl
  by_cases h15:a="ell.center.s"
  · subst a
    rfl
  by_cases h16:a="ell.center.n"
  · subst a
    rfl
  by_cases h17:a="ell.center.d"
  · subst a
    rfl
  simp only [rename,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,if_false]

def metadata:Com:=
  .seq (.assign "lp.m" (.var "vec.n"))
  (.seq (.assign "lp.n" (.var "vec.n"))
  (.seq (.assign "decode.count" (.mul (.var "vec.n") (.var "vec.n")))
  (.seq (.assign "input.remaining" (.mul (.lit 3)
    (.add (.var "decode.count") (.mul (.lit 2) (.var "vec.n")))))
    (.assign "input.valid" (.lit 1)))))

def readState:Com:=
  .seq (.read "vec.n") (.seq (.read "iter.k")
    (.seq metadata (.seq (RamArrayRelabel.command rename RamReadBody.readBody)
      (.assign "vec.n" (.var "lp.n")))))

def writeState:Com:=
  .seq (.assign "output.count" (.mul (.var "vec.n") (.var "vec.n")))
  (.seq (RamWriteVector.writePrefix "ell.nextshape")
  (.seq (.assign "output.count" (.var "vec.n"))
    (RamWriteVector.writePrefix "ell.nextcenter")))

def command:Com:=.seq readState (.seq ellipsoidStep writeState)

theorem metadata_spec (B n:ℕ) (hn:n < B) (hnn:n * n < B)
    (hcount:3 * (n * n + 2 * n) < B) (hthree:3 < B):
    Spec B (fun σ => σ.vars "vec.n"=n) metadata
      (fun _ τ => τ.vars "lp.m"=n∧ τ.vars "lp.n"=n∧
        τ.vars "decode.count"=n * n∧ τ.vars "input.remaining"=3 * (n * n + 2 * n)∧
        τ.vars "input.valid"=1∧ τ.vars "vec.n"=n) 18:=by
  have htwo:2 < B:=by omega
  have hmul:2 * n < B:=by omega
  have hadd:n * n + 2 * n < B:=by omega
  rintro σ hσ
  (expose_names;
    refine
        let c0:Nat→ Nat→ Nat:=Nat.mul;
        let c1:Nat:=c0 n n;
        let c2:Nat→ Nat:=c0 ((3:Nat));
        let c3:Nat→ Nat→ Nat:=Nat.add;
        let c4:Nat→ Nat:=c0 ((2:Nat));
        let c5:Nat:=c2 (c3 c1 (c4 n));
        let c6:Env→ Prop:=
          (fun (x τ:Env) =>
              And (@Eq Nat (Env.vars τ "lp.m") n)
                (And (@Eq Nat (Env.vars τ "lp.n") n)
                  (And (@Eq Nat (Env.vars τ "decode.count") c1)
                    (And (@Eq Nat (Env.vars τ "input.remaining") c5)
                      (And (@Eq Nat (Env.vars τ "input.valid") ((1:Nat)))
                        (@Eq Nat (Env.vars τ "vec.n") n))))))
            σ;
        let c7:Nat:=Env.vars (Env.setVar σ "lp.m" (Env.vars σ "vec.n")) "vec.n";
        let c8:Env:=Env.setVar (Env.setVar σ "lp.m" (Env.vars σ "vec.n")) "lp.n" c7;
        let c9:Nat:=Env.vars c8 "vec.n";
        let c10:Nat:=c0 c9 c9;
        let c11:Env:=Env.setVar c8 "decode.count" c10;
        let c12:String→ Nat:=Env.vars c11;
        let c13:Nat:=c12 "decode.count";
        let c14:Nat:=c12 "vec.n";
        let c15:Nat:=c4 c14;
        let c16:Nat:=c3 c13 c15;
        let c17:Nat:=c2 c16;
        let c18:Env:=Env.setVar c11 "input.remaining" c17;
        let c19:Env:=Env.setVar c18 "input.valid" ((1:Nat));
        let c20:Nat→ Nat:=c3 ((1:Nat));
        let c21:Nat:=c20 (Expr.size (Expr.var "vec.n"));
        let c22:Nat→ Nat:=c3 c21;
        let c23:Nat:=c20 (Expr.size (Expr.mul (Expr.var "vec.n") (Expr.var "vec.n")));
        let c24:Expr:=
          Expr.mul (Expr.lit ((2:Nat))) (Expr.var "vec.n");
        let c25:Expr:=Expr.add (Expr.var "decode.count") c24;
        let c26:Expr:=Expr.mul (Expr.lit ((3:Nat))) c25;
        let c27:Nat:=c20 (Expr.size c26);
        let c28:Nat:=c20 (Expr.size (Expr.lit ((1:Nat))));
        let c29:Nat:=c3 c27 c28;
        let c30:Nat:=c3 c23 c29;
        let c31:Nat:=c22 c30;
        let c32:Com:=Com.assign "decode.count" (Expr.mul (Expr.var "vec.n") (Expr.var "vec.n"));
        let c33:Com:=Com.assign "input.remaining" c26;
        let c34:Com:=Com.assign "input.valid" (Expr.lit ((1:Nat)));
        let c35:Com:=Com.seq c33 c34;
        let c36:Com:=Com.seq c32 c35;
        let c37:@Eq (Option Nat) (Expr.evalB B (Expr.var "vec.n") c8) (@some Nat (Env.vars c8 "vec.n")):=
          RunStep.eval_var B c8 "vec.n"
            (?nAX_g9108_0_0_0);
        let c38:
          ∀ (e f:Expr) (m n:Nat),
            @Eq (Option Nat) (Expr.evalB B e c11) (@some Nat m)→
              @Eq (Option Nat) (Expr.evalB B f c11) (@some Nat n)→
                Nat.lt (Nat.mul m n) B→
                  @Eq (Option Nat) (Expr.evalB B (Expr.bin Bop.mul e f) c11)
                    (@some Nat (Nat.mul m n)):=
          RunStep.eval_mul B c11;
        let c39:
          ∀ (x:String),
            Nat.lt (Env.vars c11 x) B→
              @Eq (Option Nat) (Expr.evalB B (Expr.var x) c11) (@some Nat (Env.vars c11 x)):=
          RunStep.eval_var B c11;
        let c40:String→ Nat:=Env.vars c19;
        @Exists.intro Env
          (fun (σ':Env) =>
            And (Run B metadata σ σ' ((18:Nat))) (c6 σ'))
          c19
          (@And.intro (Run B metadata σ c19 ((18:Nat))) (c6 c19)
            (RunStep.mono B metadata σ c19 (c22 c31) ((18:Nat))
              (RunStep.seq B (Com.assign "lp.m" (Expr.var "vec.n")) (Com.seq (Com.assign "lp.n" (Expr.var "vec.n")) c36) σ
                (Env.setVar σ "lp.m" (Env.vars σ "vec.n")) c19 c21 c31
                (RunStep.assign B σ "lp.m" (Expr.var "vec.n") (Env.vars σ "vec.n")
                  (RunStep.eval_var B σ "vec.n"
                    (?nAX_g9108_0_0_1)))
                (RunStep.seq B (Com.assign "lp.n" (Expr.var "vec.n")) c36 (Env.setVar σ "lp.m" (Env.vars σ "vec.n")) c8
                  c19 c21 c30
                  (RunStep.assign B (Env.setVar σ "lp.m" (Env.vars σ "vec.n")) "lp.n" (Expr.var "vec.n") c7
                    (RunStep.eval_var B (Env.setVar σ "lp.m" (Env.vars σ "vec.n")) "vec.n"
                      (?nAX_g9108_0_0_2)))
                  (RunStep.seq B c32 c35 c8 c11 c19 c23 c29
                    (RunStep.assign B c8 "decode.count" (Expr.mul (Expr.var "vec.n") (Expr.var "vec.n")) c10
                      (RunStep.eval_mul B c8 (Expr.var "vec.n") (Expr.var "vec.n") c9 c9 c37 c37 ?_))
                    (RunStep.seq B c33 c34 c11 c18 c19 c27 c28
                      (RunStep.assign B c11 "input.remaining" c26 c17
                        (c38 (Expr.lit ((3:Nat))) c25
                          ((3:Nat)) c16
                          (RunStep.eval_lit B ((3:Nat)) c11 hthree)
                          (RunStep.eval_add B c11 (Expr.var "decode.count") c24 c13 c15 (c39 "decode.count" ?_)
                            (c38 (Expr.lit ((2:Nat))) (Expr.var "vec.n")
                              ((2:Nat)) c14
                              (RunStep.eval_lit B ((2:Nat)) c11 htwo)
                              (c39 "vec.n"
                                (?nAX_g9108_0_0_3))
                              (?nAX_g9108_0_0_4))
                            ?_)
                          ?_))
                      (RunStep.assign B c18 "input.valid"
                        (Expr.lit ((1:Nat)))
                        ((1:Nat))
                        (RunStep.eval_lit B ((1:Nat)) c18
                          (?nAX_g9108_0_0_5)))))))
              (?nAX_g9108_0_0_6))
            ?_) <;> try dsimp +zetaDelta at *
   all_goals try dsimp +zetaDelta at *
   try case nAX_g9108_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g9108_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g9108_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g9108_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g9108_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g9108_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case nAX_g9108_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all
  )
  all_goals simp_all [Env.setVar]

theorem write_state_spec {n:ℕ} (B M:ℕ)
    (A:Matrix (Fin n) (Fin n) ℚ) (c:Fin n→ ℚ)
    (h1:1 < B) (hM:M < B) (hn:n < B) (hnn:n * n < B)
    (hA:∀ i j,Height (A i j) M) (hc:∀ i,Height (c i) M):
    Spec B (fun σ => Represents "ell.nextshape" (flatten A) σ∧
        Represents "ell.nextcenter" (List.ofFn c) σ∧ σ.vars "vec.n"=n)
      writeState
      (fun σ τ => τ.out=σ.out ++ (flatten A).flatMap encodeRational ++ encodeVector c)
      (35 * (n * n + n) + 20):=by
  have hflat:∀ q∈ flatten A,Height q M:=by
    intro q hq
    simp only [flatten,List.mem_ofFn] at hq
    obtain ⟨i,rfl⟩:=hq
    exact hA i.divNat i.modNat
  have hvec:∀ q∈ List.ofFn c,Height q M:=by
    intro q hq
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hq
    exact hc i
  rintro σ ⟨hσA,hσc,hσn⟩
  have hr₁:Run B (.assign "output.count" (.mul (.var "vec.n") (.var "vec.n")))
      σ (σ.setVar "output.count" (n * n)) 4:=by
    apply Run.assign
    simpa only [Bop.apply_mul,hσn] using
      evalB_bin (op:=.mul) (evalB_var (B:=B) (σ:=σ) (x:= "vec.n") (hσn ▸ hn))
        (evalB_var (B:=B) (σ:=σ) (x:= "vec.n") (hσn ▸ hn))
        (by simpa only [Bop.apply_mul,hσn] using hnn)
  obtain ⟨τ,hr₂,hout₂⟩:=RamWriteVector.writePrefix_spec B M (n * n) "ell.nextshape"
    (flatten A) h1 hM hnn (by simp [flatten]) hflat
    (σ.setVar "output.count" (n * n)) ⟨hσA,by simp⟩
  have hτn:τ.vars "vec.n"=n:=((hr₁.seq hr₂).frame_var _ (by decide)).trans hσn
  have hτc:Represents "ell.nextcenter" (List.ofFn c) τ:=
    RamReadBody.represents_frame _ _ hσc (hr₁.seq hr₂) (by decide)
  have hr₃:Run B (.assign "output.count" (.var "vec.n")) τ (τ.setVar "output.count" n) 2:=by
    apply Run.assign
    simpa only [hτn] using evalB_var (B:=B) (σ:=τ) (x:= "vec.n") (hτn ▸ hn)
  obtain ⟨υ,hr₄,hout₄⟩:=RamWriteVector.writePrefix_spec B M n "ell.nextcenter"
    (List.ofFn c) h1 hM hn (by simp) hvec
    (τ.setVar "output.count" n) ⟨hτc,by simp⟩
  refine ⟨υ, (hr₁.seq (hr₂.seq (hr₃.seq hr₄))).mono (by omega), ?_⟩
  change υ.out=_
  rw [hout₄]
  change τ.out ++ _=_
  rw [hout₂]
  have htakeA:(flatten A).take (n * n)=flatten A:=List.take_of_length_le (by simp [flatten])
  have htakec:(List.ofFn c).take n=List.ofFn c:=List.take_of_length_le (by simp)
  simp only [Env.setVar,htakeA,htakec,encodeVector,List.append_assoc]

theorem body_length {n:ℕ} (A:Matrix (Fin n) (Fin n) ℚ) (a c:Fin n→ ℚ):
    (body A a c).length=3 * (n * n + 2 * n):=by
  simp only [body,List.length_append]
  rw [WordDecoding.encodeRows_length n n A,WordDecoding.encodeVector_length n a,
    WordDecoding.encodeVector_length n c]
  ring

theorem read_state_spec {n:ℕ} (B H k:ℕ)
    (A:Matrix (Fin n) (Fin n) ℚ) (a c:Fin n→ ℚ)
    (hthree:3 < B) (hH:1≤ H) (hHB:H < B) (hnB:n < B) (hnnB:n * n < B)
    (hbodyB:(body A a c).length < B) (hwords:∀ x∈ body A a c,x≤ H):
    Spec B (fun σ => Extents "ell.shape" (n * n) σ∧ Extents "ell.normal" n σ∧
        Extents "ell.center" n σ∧ Workspace n σ∧
        σ.inp=n::k::body A a c∧ σ.InpBounded B)
      readState
      (fun σ τ => Represents "ell.shape" (flatten A) τ∧ Represents "ell.normal" (List.ofFn a) τ∧
        Represents "ell.center" (List.ofFn c) τ∧ Workspace n τ∧
        τ.vars "vec.n"=n∧ τ.vars "iter.k"=k∧ τ.inp=[]∧ τ.out=σ.out)
      ((36 * H.size + 115) * (n * n + 2 * n) + 110):=by
  let P:Lax109476.LinearProgram.Program ℚ n n:= ⟨A,a,c⟩
  have hread:=RamArrayRelabel.spec_relabel rename rename_involutive.injective
    (RamReadBody.readBody_valid_spec B H n n P (by omega) hHB hH hnB hnB hnnB
      hbodyB hwords)
  rintro σ ⟨hσA,hσa,hσc,hσwork,hσinp,hσbound⟩
  let σ₁:Env:= {σ.setVar "vec.n" n with inp:=k::body A a c}
  let σ₂:Env:= {σ₁.setVar "iter.k" k with inp:=body A a c}
  have hr₁:Run B (.read "vec.n") σ σ₁ 1:=Run.read hσinp
  have hr₂:Run B (.read "iter.k") σ₁ σ₂ 1:=Run.read rfl
  have hhead:=hr₁.seq hr₂
  have hcount:3 * (n * n + 2 * n) < B:=by rwa [body_length] at hbodyB
  obtain ⟨τ,hr₃,hτm,hτn,hτcount,hτremaining,hτvalid,hτvec⟩:=
    metadata_spec B n hnB hnnB hcount hthree σ₂ (by simp [σ₂,σ₁])
  have hfirst:=hhead.seq hr₃
  have hτinp:τ.inp=body A a c:=(hr₃.frame_inp (by decide)).trans rfl
  have hτA:=RamAdvanceState.extents_of_run hfirst "ell.shape" (n * n) hσA
  have hτa:=RamAdvanceState.extents_of_run hfirst "ell.normal" n hσa
  have hτc:=RamAdvanceState.extents_of_run hfirst "ell.center" n hσc
  have hviewA:Extents "lp.A" (n * n) (RamArrayRelabel.view rename τ):=by
    simpa [Extents,RamArrayRelabel.view,rename,Equiv.swap_apply_def] using hτA
  have hviewa:Extents "lp.b" n (RamArrayRelabel.view rename τ):=by
    simpa [Extents,RamArrayRelabel.view,rename,Equiv.swap_apply_def] using hτa
  have hviewc:Extents "lp.c" n (RamArrayRelabel.view rename τ):=by
    simpa [Extents,RamArrayRelabel.view,rename,Equiv.swap_apply_def] using hτc
  obtain ⟨υ,hr₄,hυA,hυa,hυc,hυinp,_,_,_,_,hυn,_⟩:=hread τ
    ⟨hviewA,hviewa,hviewc,hτinp,by change τ.vars "input.remaining"=(body A a c).length; rw [body_length]; exact hτremaining,
      hτvalid,hfirst.inpBounded hσbound,hτm,hτn,hτcount⟩
  have hυA':Represents "ell.shape" (flatten A) υ:=by
    simpa [RamArrayRelabel.view,RamRationalArrays.Represents,rename,P] using hυA
  have hυa':Represents "ell.normal" (List.ofFn a) υ:=by
    simpa [RamArrayRelabel.view,RamRationalArrays.Represents,rename,P] using hυa
  have hυc':Represents "ell.center" (List.ofFn c) υ:=by
    simpa [RamArrayRelabel.view,RamRationalArrays.Represents,rename,P] using hυc
  have hυn':υ.vars "lp.n"=n:=hυn
  have hr₅:Run B (.assign "vec.n" (.var "lp.n")) υ (υ.setVar "vec.n" n) 2:=by
    apply Run.assign
    simpa only [hυn'] using evalB_var (B:=B) (σ:=υ) (x:= "lp.n") (hυn' ▸ hnB)
  have hrun:=hr₁.seq (hr₂.seq (hr₃.seq (hr₄.seq hr₅)))
  refine ⟨_,hrun.mono (by rw [show n * n + n + n=n * n + 2 * n by omega]; omega), ?_, ?_, ?_,RamAdvanceState.workspace_of_run hrun n hσwork,
    by simp, ?_, ?_, ?_⟩
  · exact hυA'
  · exact hυa'
  · exact hυc'
  · have hk:υ.vars "iter.k"=k:=(hr₃.seq hr₄).frame_var "iter.k" (by decide)
    simpa [σ₂,σ₁] using hk
  · exact hυinp
  · exact hrun.out_eq (by decide)

def cost (n H M:ℕ):ℕ:=
  ((36 * H.size + 115) * (n * n + 2 * n) + 110) +
    RamEllipsoidStep.stepCost n H M + (35 * (n * n + n) + 20)

theorem command_spec {n:ℕ} (B H M k:ℕ)
    (A:Matrix (Fin n) (Fin n) ℚ) (a c:Fin n→ ℚ)
    (hn:2≤ n) (hH:1≤ H) (hA:∀ i j,Height (A i j) H)
    (ha:∀ i,Height (a i) H) (hc:∀ i,Height (c i) H)
    (hqpos:0 < a ⬝ᵥ (A *ᵥ a)) (hnM:n * n≤ M)
    (hFM:RamEllipsoidForm.formHeight n H≤ M)
    (hDM:2 ^ (2 * k + 3 * n + 9)≤ M) (hEM:2 ^ (2 * n + 4)≤ M)
    (hB:2 * (RamShapeCoordinate.shapeCap (RamEllipsoidCoefficients.coefficientCap M)) ^ 2 + 3 < B)
    (hbodyB:(body A a c).length < B) (hwords:∀ x∈ body A a c,x≤ H):
    Spec B (fun σ => Extents "ell.shape" (n * n) σ∧ Extents "ell.normal" n σ∧
        Extents "ell.center" n σ∧ Workspace n σ∧
        σ.inp=n::k::body A a c∧ σ.InpBounded B)
      command
      (fun σ τ => τ.out=σ.out ++
        (flatten (EllipsoidCenter.roundedStepShape n A a (2 ^ (2 * k + 3 * n + 9))
          (EllipsoidIteration.stepAccuracy n))).flatMap encodeRational ++
        encodeVector (EllipsoidCenter.roundedCenter n A a c (2 ^ (2 * k + 3 * n + 9))))
      (cost n H M):=by
  let S:=RamShapeCoordinate.shapeCap (RamEllipsoidCoefficients.coefficientCap M)
  have hcaps:=RamEllipsoidWordBounds.unified_word_bounds B M n hn hnM hB
  have h1:1 < B:=by omega
  have hthree:3 < B:=by omega
  have hMB:M < B:=hcaps.2.1
  have hHM:H≤ M:=((RamDotProduct.cap_ge n H hH).2.trans
    (RamEllipsoidForm.formHeight_ge n H hH)).trans hFM
  have hHB:H < B:=hHM.trans_lt hMB
  have hnB:n < B:=hcaps.2.2.2.1
  have hnnB:n * n < B:=by simpa only [pow_two] using hcaps.2.2.1
  have hSpos:1≤ S:=by
    have hp:1≤ (RamEllipsoidCoefficients.coefficientCap M + 1) ^ 8:=by
      exact Nat.one_le_pow 8 _ (by omega)
    dsimp [S,RamShapeCoordinate.shapeCap]
    omega
  have hSB:S < B:=by change 2 * S ^ 2 + 3 < B at hB; nlinarith [le_self_pow hSpos (by decide:(2:ℕ) ≠ 0)]
  have hnew:=RamEllipsoidStoredBounds.step_stored_bounds n H M k A a c hH hA ha hc
    ((Nat.le_mul_self n).trans hnM) hFM hDM hEM
  rintro σ hσ
  obtain ⟨τ,hr₁,hτA,hτa,hτc,hτw,hτn,hτk,_,hτout⟩:=
    read_state_spec B H k A a c hthree hH hHB hnB hnnB hbodyB hwords σ hσ
  obtain ⟨υ,hr₂,hυc,hυA,_,_,hυn,_⟩:=
    RamEllipsoidStep.ellipsoidStep_spec B n H M k A a c hn hH hA ha hc hqpos hnM hFM hDM hEM hB
      τ ⟨hτA,hτa,hτc,hτw,hτn,hτk⟩
  obtain ⟨ξ,hr₃,hξout⟩:=write_state_spec B S
    (EllipsoidCenter.roundedStepShape n A a (2 ^ (2 * k + 3 * n + 9)) (EllipsoidIteration.stepAccuracy n))
    (EllipsoidCenter.roundedCenter n A a c (2 ^ (2 * k + 3 * n + 9))) h1 hSB hnB hnnB hnew.2 hnew.1
      υ ⟨hυA,hυc,hυn⟩
  have hυout:υ.out=σ.out:=(hr₂.out_eq (by decide)).trans hτout
  refine ⟨ξ, (hr₁.seq (hr₂.seq hr₃)).mono (by dsimp [cost]; omega), ?_⟩
  change ξ.out=_
  rw [hξout,hυout]

def costEnvelope (X:ℕ):ℕ:=
  ((36 * X + 115) * (X * X + 2 * X) + 110) +
    ((144 * ((X + 1) * (2 * X + 3) + 1) + 220) * X ^ 2 +
      (144 * ((X + 1) * (2 * ((X + 1) * (2 * X + 3) + 1) + 3) + 1) + 292) * X +
      (2880 * X + 7559) * X + (14976 * X + 36767) * (X * X) + 582 * X + 1000) +
    (35 * (X * X + X) + 20)

theorem cost_polynomial (n H M:ℕ):
    10 * cost n H M + 1≤ 1000000 * (n + H.size + M.size + 1) ^ 4:=by
  let X:=n + H.size + M.size + 1
  have hX:1≤ X:=by dsimp [X]; omega
  have hn:n≤ X:=by dsimp [X]; omega
  have hH:H.size≤ X:=by dsimp [X]; omega
  have hM:M.size≤ X:=by dsimp [X]; omega
  have hstep:=RamEllipsoidStep.stepCost_polynomial n H M
  have hcost:cost n H M≤ costEnvelope X:=by
    unfold cost costEnvelope
    apply (Nat.add_le_add_right (Nat.add_le_add_left hstep _) _).trans
    gcongr
  have hpoly:costEnvelope X=864 * X ^ 4 + 17748 * X ^ 3 + 43689 * X ^ 2 + 10426 * X + 1130:=by
    unfold costEnvelope
    ring
  have h0:1≤ X ^ 4:=Nat.one_le_pow 4 X (by omega)
  have h1:X≤ X ^ 4:=le_self_pow hX (by decide)
  have h2:X ^ 2≤ X ^ 4:=Nat.pow_le_pow_right hX (by decide)
  have h3:X ^ 3≤ X ^ 4:=Nat.pow_le_pow_right hX (by decide)
  rw [hpoly] at hcost
  change 10 * cost n H M + 1≤ 1000000 * X ^ 4
  nlinarith

def ext (n:ℕ) (a:String):ℕ:=
  if a∈ ["ell.shape.s", "ell.shape.n", "ell.shape.d",
      "ell.nextshape.s", "ell.nextshape.n", "ell.nextshape.d"] then n * n
  else if a∈ ["ell.coeff.s", "ell.coeff.n", "ell.coeff.d"] then 5 else n

def layout:=RamAutomaticLayout.layout command
def program:Lax808846.Ram.Program:=Lax808846Proofs.Compile.compileProgram layout command

theorem initial_extents (n:ℕ) (input:List ℕ):
    Extents "ell.shape" (n * n) (initEnv (ext n) input)∧
      Extents "ell.normal" n (initEnv (ext n) input)∧
      Extents "ell.center" n (initEnv (ext n) input)∧
      Workspace n (initEnv (ext n) input):=by
  simp [Extents,Workspace,initEnv,ext]

theorem compiled_runs_to {n:ℕ} (v w H M k:ℕ)
    (A:Matrix (Fin n) (Fin n) ℚ) (a c:Fin n→ ℚ)
    (hv:0 < v) (hw:v + RamTransfer.layoutAllowance layout≤ w)
    (hn:2≤ n) (hH:1≤ H) (hA:∀ i j,Height (A i j) H)
    (ha:∀ i,Height (a i) H) (hc:∀ i,Height (c i) H)
    (hqpos:0 < a ⬝ᵥ (A *ᵥ a)) (hnM:n * n≤ M)
    (hFM:RamEllipsoidForm.formHeight n H≤ M)
    (hDM:2 ^ (2 * k + 3 * n + 9)≤ M) (hEM:2 ^ (2 * n + 4)≤ M)
    (hB:2 * (RamShapeCoordinate.shapeCap (RamEllipsoidCoefficients.coefficientCap M)) ^ 2 + 3 < 2 ^ v)
    (hbodyB:(body A a c).length < 2 ^ v) (hwords:∀ x∈ body A a c,x≤ H)
    (hinput:∀ x∈ n::k::body A a c,x < 2 ^ v):
    ∃ t≤ 10 * cost n H M + 1,Lax808846.Ram.RunsTo w program
      (n::k::body A a c)
      ((flatten (EllipsoidCenter.roundedStepShape n A a (2 ^ (2 * k + 3 * n + 9))
        (EllipsoidIteration.stepAccuracy n))).flatMap encodeRational ++
        encodeVector (EllipsoidCenter.roundedCenter n A a c (2 ^ (2 * k + 3 * n + 9)))) t:=by
  have hinit:=initial_extents n (n::k::body A a c)
  obtain ⟨τ,hr,hout⟩:=command_spec (2 ^ v) H M k A a c hn hH hA ha hc hqpos hnM hFM hDM hEM
    hB hbodyB hwords (initEnv (ext n) (n::k::body A a c))
    ⟨hinit.1,hinit.2.1,hinit.2.2.1,hinit.2.2.2,rfl,hinput⟩
  obtain ⟨K,hK,hbs⟩:=hr
  obtain ⟨t,ht,hrun⟩:=Lax808846Proofs.Simulation.compileProgram_runsTo
    (RamTransfer.layout_fits hv hw) (RamAutomaticLayout.layout_ok command) hinput hbs
  refine ⟨t,ht.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 10 hK) 1), ?_⟩
  simpa only [program,layout,hout,initEnv,List.nil_append] using hrun

theorem encoded_words {n:ℕ} (H:ℕ) (hH:1≤ H)
    (A:Matrix (Fin n) (Fin n) ℚ) (a c:Fin n→ ℚ)
    (hA:∀ i j,Height (A i j) H) (ha:∀ i,Height (a i) H)
    (hc:∀ i,Height (c i) H):∀ x∈ body A a c,x≤ H:=by
  have rational_words:∀ q:ℚ,Height q H→ ∀ x∈ encodeRational q,x≤ H:=by
    intro q hq x hx
    simp only [encodeRational,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl
    · split_ifs <;> omega
    · exact hq.1
    · exact hq.2
  have vector_words:∀ v:Fin n→ ℚ, (∀ i,Height (v i) H)→
      ∀ x∈ encodeVector v,x≤ H:=by
    intro v hv x hx
    obtain ⟨q,hq,hx⟩:=List.mem_flatMap.mp hx
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hq
    exact rational_words _ (hv i) x hx
  intro x hx
  simp only [body,List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · obtain ⟨row,hrow,hx⟩:=List.mem_flatten.mp hx
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hrow
    exact vector_words (A i) (hA i) x hx
  · exact vector_words a ha x hx
  · exact vector_words c hc x hx

theorem magnitude_polynomial (n h k:ℕ):
    RamEllipsoidBitBounds.magnitudeExponent n h k≤ 26 * (n + h + k + 1) ^ 3:=by
  let X:=n + h + k + 1
  have hX:1≤ X:=by dsimp [X]; omega
  have hn:n≤ X:=by dsimp [X]; omega
  have hh:h≤ X:=by dsimp [X]; omega
  have hk:k≤ X:=by dsimp [X]; omega
  have hn1:n + 1≤ X:=by dsimp [X]; omega
  have hnn:n * n≤ X ^ 2:=by simpa only [pow_two] using Nat.mul_le_mul hn hn
  have hform:RamEllipsoidBitBounds.formExponent n h≤ (2 * (2 * X * X) + 1) * X:=by
    unfold RamEllipsoidBitBounds.formExponent
    gcongr
    dsimp [X]
    omega
  have h1:X≤ X ^ 3:=le_self_pow hX (by decide)
  have h2:X ^ 2≤ X ^ 3:=Nat.pow_le_pow_right hX (by decide)
  have h0:1≤ X ^ 3:=Nat.one_le_pow 3 X (by omega)
  change RamEllipsoidBitBounds.formExponent n h + n * n + 2 * k + 5 * n + 13≤ 26 * X ^ 3
  nlinarith only [hform,hnn,hk,hn,h0,h1,h2]

theorem exists_program:∃ p:Lax808846.Ram.Program, ∃ c:ℕ,0 < c∧
    ∀ (n k h:ℕ),2≤ n→ 1≤ h→
      ∀ (state:Lax263307.RoundedOracleSearch.State n) (a:Fin n→ ℤ),
        (∀ i j,Lax263307.NativeRoundedStep.height (state.1 i j) h)→
        (∀ i,Lax263307.NativeRoundedStep.height (Lax263307.RoundedOracleSearch.rationalNormal a i) h)→
        (∀ i,Lax263307.NativeRoundedStep.height (state.2 i) h)→
        0 < Lax263307.RoundedOracleSearch.rationalNormal a ⬝ᵥ
          (state.1 *ᵥ Lax263307.RoundedOracleSearch.rationalNormal a)→
        ∀ w:ℕ,c * (n + h + k + 1) ^ 12≤ w→
          ∃ t≤ c * (n + h + k + 1) ^ 12,Lax808846.Ram.RunsTo w p
            (Lax263307.NativeRoundedStep.encodeInput k state a)
            (Lax263307.NativeRoundedStep.encodeOutput
              (Lax263307.RoundedOracleSearch.update k state a)) t:=by
  let C:=1000000000000000 + RamTransfer.layoutAllowance layout
  refine ⟨program,C,by dsimp [C]; omega, ?_⟩
  intro n k h hn hh state a hA ha hc hpos w hw
  let X:=n + h + k + 1
  let E:=RamEllipsoidBitBounds.magnitudeExponent n h k
  let H:=2 ^ h
  let M:=2 ^ E
  let v:=RamEllipsoidBitBounds.wordWidth n h k + 3 * (n * n + 2 * n) + h + k + 1
  have hX:1≤ X:=by dsimp [X]; omega
  have hnX:n≤ X:=by dsimp [X]; omega
  have hhX:h≤ X:=by dsimp [X]; omega
  have hkX:k≤ X:=by dsimp [X]; omega
  have h1:X≤ X ^ 3:=le_self_pow hX (by decide)
  have h2:X ^ 2≤ X ^ 3:=Nat.pow_le_pow_right hX (by decide)
  have h0:1≤ X ^ 3:=Nat.one_le_pow 3 X (by omega)
  have hE:E≤ 26 * X ^ 3:=magnitude_polynomial n h k
  have hnn:n * n≤ X ^ 2:=by simpa only [pow_two] using Nat.mul_le_mul hnX hnX
  have hvbound:v≤ 2000 * X ^ 3:=by
    dsimp [v,RamEllipsoidBitBounds.wordWidth]
    change 64 * E + 224 + 3 * (n * n + 2 * n) + h + k + 1≤ _
    nlinarith only [hE,hnn,hnX,hhX,hkX,h0,h1,h2]
  have hX12:X ^ 3≤ X ^ 12:=Nat.pow_le_pow_right hX (by decide)
  have h012:1≤ X ^ 12:=Nat.one_le_pow 12 X (by omega)
  have hwv:v + RamTransfer.layoutAllowance layout≤ w:=by
    change C * X ^ 12≤ w at hw
    have hallow:=Nat.mul_le_mul_left (RamTransfer.layoutAllowance layout) h012
    dsimp [C] at hw
    nlinarith only [hw,hvbound,hX12,hallow]
  have hv:0 < v:=by dsimp [v]; omega
  have hH:1≤ H:=Nat.one_le_pow h 2 (by decide)
  have hparams:=RamEllipsoidBitBounds.magnitude_parameters n h k
  have hguard:=RamEllipsoidBitBounds.wordWidth_sufficient n h k v (by dsimp [v]; omega)
  have hlength:(body state.1 (Lax263307.RoundedOracleSearch.rationalNormal a) state.2).length < 2 ^ v:=by
    rw [body_length]
    have hlen:3 * (n * n + 2 * n) < v:=by dsimp [v]; omega
    exact hlen.trans Nat.lt_two_pow_self
  have hwords:=encoded_words H hH state.1 (Lax263307.RoundedOracleSearch.rationalNormal a) state.2 hA ha hc
  have hinput:∀ x∈ n::k::body state.1 (Lax263307.RoundedOracleSearch.rationalNormal a) state.2,x < 2 ^ v:=by
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with hxn | hxk | hx
    · rw [hxn]
      have hnV:n < v:=by dsimp [v]; nlinarith only [hn]
      exact hnV.trans Nat.lt_two_pow_self
    · rw [hxk]
      have hkV:k < v:=by dsimp [v]; omega
      exact hkV.trans Nat.lt_two_pow_self
    · have hhV:h < v:=by dsimp [v]; omega
      exact (hwords x hx).trans_lt (Nat.pow_lt_pow_right (by decide) hhV)
  obtain ⟨t,ht,hrun⟩:=compiled_runs_to v w H M k state.1
    (Lax263307.RoundedOracleSearch.rationalNormal a) state.2 hv hwv hn hH hA ha hc hpos
    hparams.1 hparams.2.1 hparams.2.2.1 hparams.2.2.2 hguard hlength hwords hinput
  have hsize:n + H.size + M.size + 1≤ 30 * X ^ 3:=by
    dsimp only [H,M]
    rw [Nat.size_pow,Nat.size_pow]
    have hs:n + h + 3≤ 3 * X:=by dsimp [X]; omega
    nlinarith only [hE,hs,h1]
  have htime:10 * cost n H M + 1≤ C * X ^ 12:=by
    calc
      _≤ 1000000 * (n + H.size + M.size + 1) ^ 4:=cost_polynomial n H M
      _≤ 1000000 * (30 * X ^ 3) ^ 4:=Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsize 4)
      _=810000000000 * X ^ 12:=by ring
      _≤ _:=Nat.mul_le_mul_right _ (by dsimp [C]; omega)
  refine ⟨t,ht.trans htime, ?_⟩
  have hgrid:Lax263307.RoundedOracleSearch.grid n k=2 ^ (2 * k + 3 * n + 9):=by
    unfold Lax263307.RoundedOracleSearch.grid
    congr 1
    omega
  have hstep:Lax263307.RoundedOracleSearch.update k state a =
      (EllipsoidCenter.roundedStepShape n state.1
        (Lax263307.RoundedOracleSearch.rationalNormal a) (2 ^ (2 * k + 3 * n + 9))
        (EllipsoidIteration.stepAccuracy n),
       EllipsoidCenter.roundedCenter n state.1
        (Lax263307.RoundedOracleSearch.rationalNormal a) state.2 (2 ^ (2 * k + 3 * n + 9))):=by
    simp only [Lax263307.RoundedOracleSearch.update,Lax263307Proofs.RoundedOracleSearch.cached_eq,hgrid]
    rfl
  rw [hstep]
  exact hrun

end Lax263307Proofs.NativeRoundedStep

end

theorem solution:∃ (p:Lax808846.Ram.Program) (c:ℕ),
  0 < c∧
    ∀ (n k h:ℕ),
      2≤ n→
        1≤ h→
          ∀ (state:Lax263307.RoundedOracleSearch.State n) (a:Fin n→ ℤ),
            (∀ (i j:Fin n),Lax263307.NativeRoundedStep.height (state.1 i j) h)→
              (∀ (i:Fin n),Lax263307.NativeRoundedStep.height (Lax263307.RoundedOracleSearch.rationalNormal a i) h)→
                (∀ (i:Fin n),Lax263307.NativeRoundedStep.height (state.2 i) h)→
                  0 <
                      Lax263307.RoundedOracleSearch.rationalNormal a ⬝ᵥ
                        state.1.mulVec (Lax263307.RoundedOracleSearch.rationalNormal a)→
                    ∀ (w:ℕ),
                      c * (n + h + k + 1) ^ 12≤ w→
                        ∃ t≤ c * (n + h + k + 1) ^ 12,
                          Lax808846.Ram.RunsTo w p (Lax263307.NativeRoundedStep.encodeInput k state a)
                            (Lax263307.NativeRoundedStep.encodeOutput (Lax263307.RoundedOracleSearch.update k state a))
                            t:= @Lax263307Proofs.NativeRoundedStep.exists_program
