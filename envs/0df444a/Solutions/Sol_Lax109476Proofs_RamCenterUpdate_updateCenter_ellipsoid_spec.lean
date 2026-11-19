-- Prove2me | solution 1 for Lax109476Proofs.RamCenterUpdate.updateCenter_ellipsoid_spec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T13:53:08.353832+00:00
-- url     : https://prove2.me/submissions/1efe1d7a-bbcd-4725-879c-6d95c1c0fde5

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
import Definitions.Def_EdgeSublinearMWIS_Main_NativeOracleInterfaces

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
    (refine let c0:Nat:= @HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a b; let c1:Env→ Prop:=(fun (x σ':Env) => And (@Eq Nat (Env.vars σ' "gcd.a") b) (@Eq Nat (Env.vars σ' "gcd.b") c0)) σ; let c2:Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) (Env.vars σ "gcd.a") (Env.vars σ "gcd.b"); let c3:Nat:=Nat.mul c2 (Env.vars σ "gcd.b"); let c4:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (Env.vars σ "gcd.a") c3; let c5:Env:=Env.setVar σ "gcd.t" c4; let c6:Nat:=Env.vars c5 "gcd.b"; let c7:Env:=Env.setVar c5 "gcd.a" c6; let c8:Nat:=Env.vars c7 "gcd.t"; let c9:Env:=Env.setVar c7 "gcd.b" c8; let c10:Nat→ Nat→ Nat:=Nat.add; let c11:Nat→ Nat:=c10 ((1:Nat)); let c12:Expr:=Expr.mul (Expr.div (Expr.var "gcd.a") (Expr.var "gcd.b")) (Expr.var "gcd.b"); let c13:Expr:=Expr.sub (Expr.var "gcd.a") c12; let c14:Nat:=c11 (Expr.size c13); let c15:Nat:=c11 (Expr.size (Expr.var "gcd.b")); let c16:Nat:=c11 (Expr.size (Expr.var "gcd.t")); let c17:Nat:=c10 c15 c16; let c18:String→ Nat:=Env.vars c9; @Exists.intro Env (fun (σ':Env) => And (Run B gcdStep σ σ' ((12:Nat))) (c1 σ')) c9 (@And.intro (Run B gcdStep σ c9 ((12:Nat))) (c1 c9) (RunStep.mono B gcdStep σ c9 (c10 c14 c17) ((12:Nat)) (RunStep.seq B (Com.assign "gcd.t" c13) (Com.seq (Com.assign "gcd.a" (Expr.var "gcd.b")) (Com.assign "gcd.b" (Expr.var "gcd.t"))) σ c5 c9 c14 c17 (RunStep.assign B σ "gcd.t" c13 c4 (RunStep.eval_sub B σ (Expr.var "gcd.a") c12 (Env.vars σ "gcd.a") c3 (RunStep.eval_var B σ "gcd.a" (?nAX_g3873_0_0_0)) (RunStep.eval_mul B σ (Expr.div (Expr.var "gcd.a") (Expr.var "gcd.b")) (Expr.var "gcd.b") c2 (Env.vars σ "gcd.b") (RunStep.eval_div B σ (Expr.var "gcd.a") (Expr.var "gcd.b") (Env.vars σ "gcd.a") (Env.vars σ "gcd.b") (RunStep.eval_var B σ "gcd.a" (?nAX_g3873_0_0_1)) (RunStep.eval_var B σ "gcd.b" (?nAX_g3873_0_0_2)) ?_) (RunStep.eval_var B σ "gcd.b" (?nAX_g3873_0_0_3)) ?_) (?nAX_g3873_0_0_4))) (RunStep.seq B (Com.assign "gcd.a" (Expr.var "gcd.b")) (Com.assign "gcd.b" (Expr.var "gcd.t")) c5 c7 c9 c15 c16 (RunStep.assign B c5 "gcd.a" (Expr.var "gcd.b") c6 (RunStep.eval_var B c5 "gcd.b" (?nAX_g3873_0_0_5))) (RunStep.assign B c7 "gcd.b" (Expr.var "gcd.t") c8 (RunStep.eval_var B c7 "gcd.t" (?nAX_g3873_0_0_6))))) (?nAX_g3873_0_0_7)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g3873_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3873_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3873_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3873_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3873_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3873_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3873_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3873_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all))
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
    (refine let c0:Nat:=Env.vars (Env.setVar σ "gcd.a" (Env.vars σ "rat.n")) "rat.d"; let c1:Env:=Env.setVar (Env.setVar σ "gcd.a" (Env.vars σ "rat.n")) "gcd.b" c0; let c2:Env→ Nat→ Prop:=Run B gcdLoop c1; let c3:Nat→ Nat→ Nat:=Nat.add; let c4:Nat→ Nat:=c3 (Nat.mul ((36:Nat)) (Nat.size d)); let c5:Nat:=c4 ((4:Nat)); let c6:String→ Nat:=Env.vars c1; let c7:List Nat:=Env.inp c1; let c8:List Nat:=Env.out c1; let c9:Env→ Prop:=fun (σ':Env) => And (c2 σ' c5) (And (And (@Eq Nat (Env.vars σ' "gcd.a") (Nat.gcd n d)) (@Eq Nat (Env.vars σ' "gcd.b") ((0:Nat)))) (And (∀ y∉ Com.wvars gcdLoop, @Eq Nat (Env.vars σ' y) (c6 y)) (And (∀ a∉ Com.warrs gcdLoop, @Eq (List Nat) (Env.arrs σ' a) (Env.arrs c1 a)) (And (Not (Com.reads gcdLoop)→ @Eq (List Nat) (Env.inp σ') c7) (Com.NoWrite gcdLoop→ @Eq (List Nat) (Env.out σ') c8))))); let c10:Nat:=c4 ((16:Nat)); let c11:Nat→ Nat→ Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv); let c12:Nat:=c11 n (Nat.gcd n d); let c13:Nat:=c11 d (Nat.gcd n d); let c14:Env→ Prop:=(fun (x σ':Env) => And (@Eq Nat (Env.vars σ' "rat.n") c12) (@Eq Nat (Env.vars σ' "rat.d") c13)) σ; let c15:Env→ Prop:=fun (σ':Env) => And (Run B normalizeFraction σ σ' c10) (c14 σ'); let c16:Prop:= @Exists Env c15; let c17:Nat→ Nat:=c3 ((1:Nat)); let c18:Nat:=c17 (Expr.size (Expr.var "rat.n")); let c19:Nat:=c17 (Expr.size (Expr.var "rat.d")); let c20:Nat:=c17 (Expr.size (Expr.div (Expr.var "rat.n") (Expr.var "gcd.a"))); let c21:Nat:=c17 (Expr.size (Expr.div (Expr.var "rat.d") (Expr.var "gcd.a"))); let c22:Nat:=c3 c20 c21; let c23:Nat:=c3 c5 c22; let c24:Nat:=c3 c19 c23; let c25:Com:=Com.assign "rat.n" (Expr.div (Expr.var "rat.n") (Expr.var "gcd.a")); let c26:Com:=Com.assign "rat.d" (Expr.div (Expr.var "rat.d") (Expr.var "gcd.a")); let c27:Com:=Com.seq c25 c26; let c28:Com:=Com.seq gcdLoop c27; @Exists.casesOn Env c9 (fun (x:@Exists Env c9) => c16) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "gcd.a") n) (@Eq Nat (Env.vars σ_1 "gcd.b") d)) gcdLoop (fun (σ_1 σ':Env) => And (And (@Eq Nat (Env.vars σ' "gcd.a") (Nat.gcd n d)) (@Eq Nat (Env.vars σ' "gcd.b") ((0:Nat)))) (And (∀ y∉ Com.wvars gcdLoop, @Eq Nat (Env.vars σ' y) (Env.vars σ_1 y)) (And (∀ a∉ Com.warrs gcdLoop, @Eq (List Nat) (Env.arrs σ' a) (Env.arrs σ_1 a)) (And (Not (Com.reads gcdLoop)→ @Eq (List Nat) (Env.inp σ') (Env.inp σ_1)) (Com.NoWrite gcdLoop→ @Eq (List Nat) (Env.out σ') (Env.out σ_1)))))) c5 hs c1 ?_) fun (w:Env) (h:And (c2 w c5) (And (And (@Eq Nat (Env.vars w "gcd.a") (Nat.gcd n d)) (@Eq Nat (Env.vars w "gcd.b") ((0:Nat)))) (And (∀ y∉ Com.wvars gcdLoop, @Eq Nat (Env.vars w y) (c6 y)) (And (∀ a∉ Com.warrs gcdLoop, @Eq (List Nat) (Env.arrs w a) (Env.arrs c1 a)) (And (Not (Com.reads gcdLoop)→ @Eq (List Nat) (Env.inp w) c7) (Com.NoWrite gcdLoop→ @Eq (List Nat) (Env.out w) c8)))))) => let c0_1:Prop:=And (And (@Eq Nat (Env.vars w "gcd.a") (Nat.gcd n d)) (@Eq Nat (Env.vars w "gcd.b") ((0:Nat)))) (And (∀ y∉ Com.wvars gcdLoop, @Eq Nat (Env.vars w y) (c6 y)) (And (∀ a∉ Com.warrs gcdLoop, @Eq (List Nat) (Env.arrs w a) (Env.arrs c1 a)) (And (Not (Com.reads gcdLoop)→ @Eq (List Nat) (Env.inp w) c7) (Com.NoWrite gcdLoop→ @Eq (List Nat) (Env.out w) c8)))); let c1_1:Nat:=c11 (Env.vars w "rat.n") (Env.vars w "gcd.a"); let c2_1:Env:=Env.setVar w "rat.n" c1_1; let c3_1:String→ Nat:=Env.vars c2_1; let c4_1:Nat:=c3_1 "rat.d"; let c5_1:Nat:=c3_1 "gcd.a"; let c6_1:Nat:=c11 c4_1 c5_1; let c7_1:Env:=Env.setVar c2_1 "rat.d" c6_1; let c8_1:String→ Nat:=Env.vars c7_1; @And.casesOn (c2 w c5) c0_1 (fun (x:And (c2 w c5) c0_1) => c16) h fun (left:c2 w c5) (right:c0_1) => @Exists.intro Env c15 c7_1 (@And.intro (Run B normalizeFraction σ c7_1 c10) (c14 c7_1) (RunStep.mono B normalizeFraction σ c7_1 (c3 c18 c24) c10 (RunStep.seq B (Com.assign "gcd.a" (Expr.var "rat.n")) (Com.seq (Com.assign "gcd.b" (Expr.var "rat.d")) c28) σ (Env.setVar σ "gcd.a" (Env.vars σ "rat.n")) c7_1 c18 c24 (RunStep.assign B σ "gcd.a" (Expr.var "rat.n") (Env.vars σ "rat.n") (RunStep.eval_var B σ "rat.n" (?nAX_g3882_0_0_0))) (RunStep.seq B (Com.assign "gcd.b" (Expr.var "rat.d")) c28 (Env.setVar σ "gcd.a" (Env.vars σ "rat.n")) c1 c7_1 c19 c23 (RunStep.assign B (Env.setVar σ "gcd.a" (Env.vars σ "rat.n")) "gcd.b" (Expr.var "rat.d") c0 (RunStep.eval_var B (Env.setVar σ "gcd.a" (Env.vars σ "rat.n")) "rat.d" (?nAX_g3882_0_0_1))) (RunStep.seq B gcdLoop c27 c1 w c7_1 c5 c22 left (RunStep.seq B c25 c26 w c2_1 c7_1 c20 c21 (RunStep.assign B w "rat.n" (Expr.div (Expr.var "rat.n") (Expr.var "gcd.a")) c1_1 (RunStep.eval_div B w (Expr.var "rat.n") (Expr.var "gcd.a") (Env.vars w "rat.n") (Env.vars w "gcd.a") (RunStep.eval_var B w "rat.n" ?_) (RunStep.eval_var B w "gcd.a" (?nAX_g3882_0_0_2)) ?_)) (RunStep.assign B c2_1 "rat.d" (Expr.div (Expr.var "rat.d") (Expr.var "gcd.a")) c6_1 (RunStep.eval_div B c2_1 (Expr.var "rat.d") (Expr.var "gcd.a") c4_1 c5_1 (RunStep.eval_var B c2_1 "rat.d" ?_) (RunStep.eval_var B c2_1 "gcd.a" (?nAX_g3882_0_0_3)) ?_)))))) (?nAX_g3882_0_0_4)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g3882_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3882_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3882_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3882_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3882_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
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

def fractionInputs (s₁ n₁ d₁ s₂ n₂ d₂:ℕ) (σ:Env):Prop:=
  σ.vars "left.s"=s₁∧ σ.vars "left.n"=n₁∧ σ.vars "left.d"=d₁∧
    σ.vars "right.s"=s₂∧ σ.vars "right.n"=n₂∧ σ.vars "right.d"=d₂

theorem multiplyFraction_spec (B M s₁ n₁ d₁ s₂ n₂ d₂:ℕ)
    (hB:2 * M ^ 2 + 3 < B) (hs₁:s₁≤ 1) (hs₂:s₂≤ 1)
    (hn₁:n₁≤ M) (hd₁:d₁≤ M) (hn₂:n₂≤ M) (hd₂:d₂≤ M)
    (hd₁pos:0 < d₁) (hd₂pos:0 < d₂):
    Spec B (fractionInputs s₁ n₁ d₁ s₂ n₂ d₂) multiplyFraction
      (fun _ σ' => FractionOutput (fractionValue s₁ n₁ d₁ * fractionValue s₂ n₂ d₂) σ')
      (36 * (d₁ * d₂).size + 64):=by
  have hM:M < B:=by nlinarith
  have hn₁B:=hn₁.trans_lt hM
  have hd₁B:=hd₁.trans_lt hM
  have hn₂B:=hn₂.trans_lt hM
  have hd₂B:=hd₂.trans_lt hM
  have hnn:n₁ * n₂ < B:=(Nat.mul_le_mul hn₁ hn₂).trans_lt (by nlinarith)
  have hdd:d₁ * d₂ < B:=(Nat.mul_le_mul hd₁ hd₂).trans_lt (by nlinarith)
  have h1:1 < B:=by nlinarith
  have hs₁B:s₁ < B:=hs₁.trans_lt h1
  have hs₂B:s₂ < B:=hs₂.trans_lt h1
  have hmul:fractionValue (if s₁=s₂ then 0 else 1) (n₁ * n₂) (d₁ * d₂) =
      fractionValue s₁ n₁ d₁ * fractionValue s₂ n₂ d₂:=by
    have hs₁cases:s₁=0∨ s₁=1:=by omega
    have hs₂cases:s₂=0∨ s₂=1:=by omega
    rcases hs₁cases with rfl | rfl <;> rcases hs₂cases with rfl | rfl <;>
      norm_num [fractionValue,Nat.cast_mul] <;> ring
  have hn:=normalizeFraction_output_spec B (if s₁=s₂ then 0 else 1)
    (n₁ * n₂) (d₁ * d₂) (by split_ifs <;> omega) hnn hdd
    (Nat.mul_pos hd₁pos hd₂pos)
  rintro σ ⟨hσs₁,hσn₁,hσd₁,hσs₂,hσn₂,hσd₂⟩
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.mul; let c1:Nat:=c0 (Env.vars σ "left.n") (Env.vars σ "right.n"); let c2:Env:=Env.setVar σ "rat.n" c1; let c3:String→ Nat:=Env.vars c2; let c4:Nat:=c3 "left.d"; let c5:Nat:=c3 "right.d"; let c6:Nat:=c0 c4 c5; let c7:Env:=Env.setVar c2 "rat.d" c6; let c8:String→ Nat:=Env.vars c7; let c9:Nat:=c8 "left.s"; let c10:Nat:=c8 "right.s"; let c11:Prop:= @Eq Nat c9 c10; let c12:Prop:=Not c11; let c13:Nat→ Nat→ Nat:=Nat.add; let c14:Nat:=c0 d₁ d₂; let c15:Nat→ Nat:=c13 (c0 ((36:Nat)) (Nat.size c14)); let c16:Nat:=c15 ((64:Nat)); let c17:Env→ Prop:=FractionOutput (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul) (fractionValue s₁ n₁ d₁) (fractionValue s₂ n₂ d₂)); let c18:Env→ Prop:=(fun (x σ':Env) => c17 σ') σ; let c19:Env→ Prop:=fun (σ':Env) => And (Run B multiplyFraction σ σ' c16) (c18 σ'); let c20:Prop:= @Exists Env c19; let c21:Nat→ Env:=Env.setVar c7 "rat.s"; let c22:Env:=c21 ((0:Nat)); let c23:Env→ Nat→ Prop:=Run B normalizeFraction c22; let c24:Nat:=c15 ((16:Nat)); let c25:Nat:= @ite Nat (@Eq Nat s₁ s₂) (instDecidableEqNat s₁ s₂) ((0:Nat)) ((1:Nat)); let c26:Nat:=c0 n₁ n₂; let c27:Env→ Prop:=FractionOutput (fractionValue c25 c26 c14); let c28:Env→ Prop:=fun (σ':Env) => And (c23 σ' c24) (c27 σ'); let c29:String→ Nat:=Env.vars c22; let c30:Nat→ Nat:=c13 ((1:Nat)); let c31:Nat:=c30 (Expr.size (Expr.mul (Expr.var "left.n") (Expr.var "right.n"))); let c32:Nat→ Nat:=c13 c31; let c33:Nat:=c30 (Expr.size (Expr.mul (Expr.var "left.d") (Expr.var "right.d"))); let c34:Nat→ Nat:=c13 c33; let c35:Nat→ Nat:=c13 (c30 (Cond.size (Cond.eq (Expr.var "left.s") (Expr.var "right.s")))); let c36:Nat:=c30 (Expr.size (Expr.lit ((0:Nat)))); let c37:Nat:=c35 c36; let c38:Nat:=c13 c37 c24; let c39:Nat:=c34 c38; let c40:Com:=Com.assign "rat.d" (Expr.mul (Expr.var "left.d") (Expr.var "right.d")); let c41:Com:=Com.assign "rat.s" (Expr.lit ((0:Nat))); let c42:Com:=Com.assign "rat.s" (Expr.lit ((1:Nat))); let c43:Com:=Com.ite (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c41 c42; let c44:Com:=Com.seq c43 normalizeFraction; let c45:Env:=c21 ((1:Nat)); let c46:Env→ Nat→ Prop:=Run B normalizeFraction c45; let c47:Env→ Prop:=fun (σ':Env) => And (c46 σ' c24) (c27 σ'); let c48:String→ Nat:=Env.vars c45; let c49:Nat:=c30 (Expr.size (Expr.lit ((1:Nat)))); let c50:Nat:=c35 c49; let c51:Nat:=c13 c50 c24; let c52:Nat:=c34 c51; @Or.casesOn c11 c12 (fun (x:Or c11 c12) => c20) (Classical.em c11) (fun (hcase:c11) => @Exists.casesOn Env c28 (fun (x:@Exists Env c28) => c20) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "rat.n") c26) (And (@Eq Nat (Env.vars σ_1 "rat.d") c14) (@Eq Nat (Env.vars σ_1 "rat.s") c25))) normalizeFraction (fun (x σ':Env) => c27 σ') c24 hn c22 ?_) fun (w:Env) (h:And (c23 w c24) (c27 w)) => @And.casesOn (c23 w c24) (c27 w) (fun (x:And (c23 w c24) (c27 w)) => c20) h fun (left:c23 w c24) (right:c27 w) => @Exists.intro Env c19 w (@And.intro (Run B multiplyFraction σ w c16) (c18 w) (RunStep.mono B multiplyFraction σ w (c32 c39) c16 (RunStep.seq B (Com.assign "rat.n" (Expr.mul (Expr.var "left.n") (Expr.var "right.n"))) (Com.seq c40 c44) σ c2 w c31 c39 (RunStep.assign B σ "rat.n" (Expr.mul (Expr.var "left.n") (Expr.var "right.n")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.n") (Env.vars σ "left.n") (Env.vars σ "right.n") (RunStep.eval_var B σ "left.n" (?nAX_g3894_0_0_0)) (RunStep.eval_var B σ "right.n" (?nAX_g3894_0_0_1)) ?_)) (RunStep.seq B c40 c44 c2 c7 w c33 c38 (RunStep.assign B c2 "rat.d" (Expr.mul (Expr.var "left.d") (Expr.var "right.d")) c6 (RunStep.eval_mul B c2 (Expr.var "left.d") (Expr.var "right.d") c4 c5 (RunStep.eval_var B c2 "left.d" (?nAX_g3894_0_0_2)) (RunStep.eval_var B c2 "right.d" (?nAX_g3894_0_0_3)) ?_)) (RunStep.seq B c43 normalizeFraction c7 c22 w c37 c24 (RunStep.ite_true B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c41 c42 c7 c22 c36 (RunStep.cond_eq_true B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c10 (RunStep.eval_var B c7 "left.s" (?nAX_g3894_0_0_4)) (RunStep.eval_var B c7 "right.s" (?nAX_g3894_0_0_5)) hcase) (RunStep.assign B c7 "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g3894_0_0_6)))) left))) (?nAX_g3894_0_0_7)) ?_)) fun (hcase:c12) => @Exists.casesOn Env c47 (fun (x:@Exists Env c47) => c20) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "rat.n") c26) (And (@Eq Nat (Env.vars σ_1 "rat.d") c14) (@Eq Nat (Env.vars σ_1 "rat.s") c25))) normalizeFraction (fun (x σ':Env) => c27 σ') c24 hn c45 ?_) fun (w:Env) (h:And (c46 w c24) (c27 w)) => @And.casesOn (c46 w c24) (c27 w) (fun (x:And (c46 w c24) (c27 w)) => c20) h fun (left:c46 w c24) (right:c27 w) => @Exists.intro Env c19 w (@And.intro (Run B multiplyFraction σ w c16) (c18 w) (RunStep.mono B multiplyFraction σ w (c32 c52) c16 (RunStep.seq B (Com.assign "rat.n" (Expr.mul (Expr.var "left.n") (Expr.var "right.n"))) (Com.seq c40 c44) σ c2 w c31 c52 (RunStep.assign B σ "rat.n" (Expr.mul (Expr.var "left.n") (Expr.var "right.n")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.n") (Env.vars σ "left.n") (Env.vars σ "right.n") (RunStep.eval_var B σ "left.n" (?nAX_g3894_0_0_8)) (RunStep.eval_var B σ "right.n" (?nAX_g3894_0_0_9)) ?_)) (RunStep.seq B c40 c44 c2 c7 w c33 c51 (RunStep.assign B c2 "rat.d" (Expr.mul (Expr.var "left.d") (Expr.var "right.d")) c6 (RunStep.eval_mul B c2 (Expr.var "left.d") (Expr.var "right.d") c4 c5 (RunStep.eval_var B c2 "left.d" (?nAX_g3894_0_0_10)) (RunStep.eval_var B c2 "right.d" (?nAX_g3894_0_0_11)) ?_)) (RunStep.seq B c43 normalizeFraction c7 c45 w c50 c24 (RunStep.ite_false B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c41 c42 c7 c45 c49 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c10 (RunStep.eval_var B c7 "left.s" (?nAX_g3894_0_0_12)) (RunStep.eval_var B c7 "right.s" (?nAX_g3894_0_0_13)) hcase) (RunStep.assign B c7 "rat.s" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c7 h1))) left))) (?nAX_g3894_0_0_14)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g3894_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3894_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3894_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3894_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3894_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3894_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3894_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3894_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3894_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3894_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3894_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3894_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3894_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3894_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3894_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals simp_all

def sumNumerator (s₁ n₁ d₁ s₂ n₂ d₂:ℕ):ℕ:=
  if s₁=s₂ then n₁ * d₂ + n₂ * d₁
  else if n₁ * d₂ < n₂ * d₁ then n₂ * d₁ - n₁ * d₂ else n₁ * d₂ - n₂ * d₁

def sumSign (s₁ n₁ d₁ s₂ n₂ d₂:ℕ):ℕ:=
  if s₁=s₂ then s₁ else if n₁ * d₂ < n₂ * d₁ then s₂ else s₁

theorem fractionValue_sum (s₁ n₁ d₁ s₂ n₂ d₂:ℕ) (hs₁:s₁≤ 1) (hs₂:s₂≤ 1)
    (hd₁:0 < d₁) (hd₂:0 < d₂):
    fractionValue (sumSign s₁ n₁ d₁ s₂ n₂ d₂) (sumNumerator s₁ n₁ d₁ s₂ n₂ d₂) (d₁ * d₂) =
      fractionValue s₁ n₁ d₁ + fractionValue s₂ n₂ d₂:=by
  have hd₁q:(d₁:ℚ) ≠ 0:=by positivity
  have hd₂q:(d₂:ℚ) ≠ 0:=by positivity
  have hs₁cases:s₁=0∨ s₁=1:=by omega
  have hs₂cases:s₂=0∨ s₂=1:=by omega
  rcases hs₁cases with rfl | rfl <;> rcases hs₂cases with rfl | rfl <;>
    by_cases h:n₁ * d₂ < n₂ * d₁
  all_goals first
    | (have hu:n₁ * d₂≤ n₂ * d₁:=by omega
       simp [sumSign,sumNumerator,fractionValue,h,Nat.cast_sub hu]
       field_simp <;> ring)
    | (have hv:n₂ * d₁≤ n₁ * d₂:=by omega
       simp [sumSign,sumNumerator,fractionValue,h,Nat.cast_sub hv]
       field_simp <;> ring)

set_option maxHeartbeats 0 in
theorem addFraction_spec (B M s₁ n₁ d₁ s₂ n₂ d₂:ℕ)
    (hB:2 * M ^ 2 + 3 < B) (hs₁:s₁≤ 1) (hs₂:s₂≤ 1)
    (hn₁:n₁≤ M) (hd₁:d₁≤ M) (hn₂:n₂≤ M) (hd₂:d₂≤ M)
    (hd₁pos:0 < d₁) (hd₂pos:0 < d₂):
    Spec B (fractionInputs s₁ n₁ d₁ s₂ n₂ d₂) addFraction
      (fun _ σ' => FractionOutput (fractionValue s₁ n₁ d₁ + fractionValue s₂ n₂ d₂) σ')
      (36 * (d₁ * d₂).size + 96):=by
  have hM:M < B:=by nlinarith
  have hn₁B:=hn₁.trans_lt hM
  have hd₁B:=hd₁.trans_lt hM
  have hn₂B:=hn₂.trans_lt hM
  have hd₂B:=hd₂.trans_lt hM
  have hu:n₁ * d₂≤ M * M:=Nat.mul_le_mul hn₁ hd₂
  have hv:n₂ * d₁≤ M * M:=Nat.mul_le_mul hn₂ hd₁
  have huB:n₁ * d₂ < B:=hu.trans_lt (by nlinarith)
  have hvB:n₂ * d₁ < B:=hv.trans_lt (by nlinarith)
  have huvB:n₁ * d₂ + n₂ * d₁ < B:=by nlinarith
  have hdd:d₁ * d₂ < B:=(Nat.mul_le_mul hd₁ hd₂).trans_lt (by nlinarith)
  have hnB:sumNumerator s₁ n₁ d₁ s₂ n₂ d₂ < B:=by
    unfold sumNumerator
    split_ifs <;> omega
  have h1:1 < B:=by nlinarith
  have hs₁B:=hs₁.trans_lt h1
  have hs₂B:=hs₂.trans_lt h1
  have hss:sumSign s₁ n₁ d₁ s₂ n₂ d₂≤ 1:=by unfold sumSign; split_ifs <;> omega
  have hn:=normalizeFraction_output_spec B (sumSign s₁ n₁ d₁ s₂ n₂ d₂)
    (sumNumerator s₁ n₁ d₁ s₂ n₂ d₂) (d₁ * d₂) hss hnB hdd
    (Nat.mul_pos hd₁pos hd₂pos)
  have hsum:=fractionValue_sum s₁ n₁ d₁ s₂ n₂ d₂ hs₁ hs₂ hd₁pos hd₂pos
  rintro σ ⟨hσs₁,hσn₁,hσd₁,hσs₂,hσn₂,hσd₂⟩
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.mul; let c1:Nat:=c0 (Env.vars σ "left.n") (Env.vars σ "right.d"); let c2:Env:=Env.setVar σ "sum.u" c1; let c3:String→ Nat:=Env.vars c2; let c4:Nat:=c3 "right.n"; let c5:Nat:=c3 "left.d"; let c6:Nat:=c0 c4 c5; let c7:Env:=Env.setVar c2 "sum.v" c6; let c8:String→ Nat:=Env.vars c7; let c9:Nat:=c8 "left.d"; let c10:Nat:=c8 "right.d"; let c11:Nat:=c0 c9 c10; let c12:Env:=Env.setVar c7 "rat.d" c11; let c13:String→ Nat:=Env.vars c12; let c14:Nat:=c13 "left.s"; let c15:Nat:=c13 "right.s"; let c16:Prop:= @Eq Nat c14 c15; let c17:Prop:=Not c16; let c18:Nat→ Nat→ Nat:=Nat.add; let c19:Nat:=c0 d₁ d₂; let c20:Nat→ Nat:=c18 (c0 ((36:Nat)) (Nat.size c19)); let c21:Nat:=c20 ((96:Nat)); let c22:Env→ Prop:=FractionOutput (@HAdd.hAdd Rat Rat Rat (@instHAdd Rat Rat.instAdd) (fractionValue s₁ n₁ d₁) (fractionValue s₂ n₂ d₂)); let c23:Env→ Prop:=(fun (x σ':Env) => c22 σ') σ; let c24:Env→ Prop:=fun (σ':Env) => And (Run B addFraction σ σ' c21) (c23 σ'); let c25:Prop:= @Exists Env c24; let c26:Nat→ Env:=Env.setVar c12 "rat.n"; let c27:Nat:=c13 "sum.u"; let c28:Nat:=c13 "sum.v"; let c29:Nat:=c18 c27 c28; let c30:Env:=c26 c29; let c31:Nat:=Env.vars c30 "left.s"; let c32:Env:=Env.setVar c30 "rat.s" c31; let c33:Env→ Nat→ Prop:=Run B normalizeFraction c32; let c34:Nat:=c20 ((16:Nat)); let c35:Nat:=sumSign s₁ n₁ d₁ s₂ n₂ d₂; let c36:Nat:=sumNumerator s₁ n₁ d₁ s₂ n₂ d₂; let c37:Env→ Prop:=FractionOutput (fractionValue c35 c36 c19); let c38:Env→ Prop:=fun (σ':Env) => And (c33 σ' c34) (c37 σ'); let c39:String→ Nat:=Env.vars c32; let c40:Nat→ Nat:=c18 ((1:Nat)); let c41:Nat:=c40 (Expr.size (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))); let c42:Nat→ Nat:=c18 c41; let c43:Nat:=c40 (Expr.size (Expr.mul (Expr.var "right.n") (Expr.var "left.d"))); let c44:Nat→ Nat:=c18 c43; let c45:Nat:=c40 (Expr.size (Expr.mul (Expr.var "left.d") (Expr.var "right.d"))); let c46:Nat→ Nat:=c18 c45; let c47:Nat→ Nat:=c18 (c40 (Cond.size (Cond.eq (Expr.var "left.s") (Expr.var "right.s")))); let c48:Nat:=c40 (Expr.size (Expr.add (Expr.var "sum.u") (Expr.var "sum.v"))); let c49:Nat:=c40 (Expr.size (Expr.var "left.s")); let c50:Nat:=c18 c48 c49; let c51:Nat:=c47 c50; let c52:Nat:=c18 c51 c34; let c53:Nat:=c46 c52; let c54:Nat:=c44 c53; let c55:Com:=Com.assign "sum.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")); let c56:Com:=Com.assign "rat.d" (Expr.mul (Expr.var "left.d") (Expr.var "right.d")); let c57:Com:=Com.assign "rat.n" (Expr.add (Expr.var "sum.u") (Expr.var "sum.v")); let c58:Com:=Com.seq c57 (Com.assign "rat.s" (Expr.var "left.s")); let c59:Com:=Com.assign "rat.n" (Expr.sub (Expr.var "sum.v") (Expr.var "sum.u")); let c60:Com:=Com.seq c59 (Com.assign "rat.s" (Expr.var "right.s")); let c61:Com:=Com.assign "rat.n" (Expr.sub (Expr.var "sum.u") (Expr.var "sum.v")); let c62:Com:=Com.seq c61 (Com.assign "rat.s" (Expr.var "left.s")); let c63:Com:=Com.ite (Cond.lt (Expr.var "sum.u") (Expr.var "sum.v")) c60 c62; let c64:Com:=Com.ite (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c58 c63; let c65:Com:=Com.seq c64 normalizeFraction; let c66:Com:=Com.seq c56 c65; let c67:Nat→ Prop:=Nat.lt c27; let c68:Prop:=c67 c28; let c69:Prop:=Not c68; let c70:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c71:Nat:=c70 c28 c27; let c72:Env:=c26 c71; let c73:Nat:=Env.vars c72 "right.s"; let c74:Env:=Env.setVar c72 "rat.s" c73; let c75:Env→ Nat→ Prop:=Run B normalizeFraction c74; let c76:Env→ Prop:=fun (σ':Env) => And (c75 σ' c34) (c37 σ'); let c77:String→ Nat:=Env.vars c74; let c78:Nat→ Nat:=c18 (c40 (Cond.size (Cond.lt (Expr.var "sum.u") (Expr.var "sum.v")))); let c79:Nat:=c40 (Expr.size (Expr.sub (Expr.var "sum.v") (Expr.var "sum.u"))); let c80:Nat:=c40 (Expr.size (Expr.var "right.s")); let c81:Nat:=c18 c79 c80; let c82:Nat:=c78 c81; let c83:Nat:=c47 c82; let c84:Nat:=c18 c83 c34; let c85:Nat:=c46 c84; let c86:Nat:=c44 c85; let c87:Nat:=c70 c27 c28; let c88:Env:=c26 c87; let c89:Nat:=Env.vars c88 "left.s"; let c90:Env:=Env.setVar c88 "rat.s" c89; let c91:Env→ Nat→ Prop:=Run B normalizeFraction c90; let c92:Env→ Prop:=fun (σ':Env) => And (c91 σ' c34) (c37 σ'); let c93:String→ Nat:=Env.vars c90; let c94:Nat:=c40 (Expr.size (Expr.sub (Expr.var "sum.u") (Expr.var "sum.v"))); let c95:Nat:=c18 c94 c49; let c96:Nat:=c78 c95; let c97:Nat:=c47 c96; let c98:Nat:=c18 c97 c34; let c99:Nat:=c46 c98; let c100:Nat:=c44 c99; @Or.casesOn c16 c17 (fun (x:Or c16 c17) => c25) (Classical.em c16) (fun (hcase:c16) => @Exists.casesOn Env c38 (fun (x:@Exists Env c38) => c25) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "rat.n") c36) (And (@Eq Nat (Env.vars σ_1 "rat.d") c19) (@Eq Nat (Env.vars σ_1 "rat.s") c35))) normalizeFraction (fun (x σ':Env) => c37 σ') c34 hn c32 ?_) fun (w:Env) (h:And (c33 w c34) (c37 w)) => @And.casesOn (c33 w c34) (c37 w) (fun (x:And (c33 w c34) (c37 w)) => c25) h fun (left:c33 w c34) (right:c37 w) => @Exists.intro Env c24 w (@And.intro (Run B addFraction σ w c21) (c23 w) (RunStep.mono B addFraction σ w (c42 c54) c21 (RunStep.seq B (Com.assign "sum.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c55 c66) σ c2 w c41 c54 (RunStep.assign B σ "sum.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g3899_0_0_0)) (RunStep.eval_var B σ "right.d" (?nAX_g3899_0_0_1)) ?_)) (RunStep.seq B c55 c66 c2 c7 w c43 c53 (RunStep.assign B c2 "sum.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g3899_0_0_2)) (RunStep.eval_var B c2 "left.d" (?nAX_g3899_0_0_3)) ?_)) (RunStep.seq B c56 c65 c7 c12 w c45 c52 (RunStep.assign B c7 "rat.d" (Expr.mul (Expr.var "left.d") (Expr.var "right.d")) c11 (RunStep.eval_mul B c7 (Expr.var "left.d") (Expr.var "right.d") c9 c10 (RunStep.eval_var B c7 "left.d" (?nAX_g3899_0_0_4)) (RunStep.eval_var B c7 "right.d" (?nAX_g3899_0_0_5)) ?_)) (RunStep.seq B c64 normalizeFraction c12 c32 w c51 c34 (RunStep.ite_true B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c58 c63 c12 c32 c50 (RunStep.cond_eq_true B c12 (Expr.var "left.s") (Expr.var "right.s") c14 c15 (RunStep.eval_var B c12 "left.s" (?nAX_g3899_0_0_6)) (RunStep.eval_var B c12 "right.s" (?nAX_g3899_0_0_7)) hcase) (RunStep.seq B c57 (Com.assign "rat.s" (Expr.var "left.s")) c12 c30 c32 c48 c49 (RunStep.assign B c12 "rat.n" (Expr.add (Expr.var "sum.u") (Expr.var "sum.v")) c29 (RunStep.eval_add B c12 (Expr.var "sum.u") (Expr.var "sum.v") c27 c28 (RunStep.eval_var B c12 "sum.u" ?_) (RunStep.eval_var B c12 "sum.v" ?_) ?_)) (RunStep.assign B c30 "rat.s" (Expr.var "left.s") c31 (RunStep.eval_var B c30 "left.s" (?nAX_g3899_0_0_8))))) left)))) (?nAX_g3899_0_0_9)) ?_)) fun (hcase:c17) => @Or.casesOn c68 c69 (fun (x:Or c68 c69) => c25) (Classical.em c68) (fun (hcase_1:c68) => @Exists.casesOn Env c76 (fun (x:@Exists Env c76) => c25) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "rat.n") c36) (And (@Eq Nat (Env.vars σ_1 "rat.d") c19) (@Eq Nat (Env.vars σ_1 "rat.s") c35))) normalizeFraction (fun (x σ':Env) => c37 σ') c34 hn c74 ?_) fun (w:Env) (h:And (c75 w c34) (c37 w)) => @And.casesOn (c75 w c34) (c37 w) (fun (x:And (c75 w c34) (c37 w)) => c25) h fun (left:c75 w c34) (right:c37 w) => @Exists.intro Env c24 w (@And.intro (Run B addFraction σ w c21) (c23 w) (RunStep.mono B addFraction σ w (c42 c86) c21 (RunStep.seq B (Com.assign "sum.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c55 c66) σ c2 w c41 c86 (RunStep.assign B σ "sum.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g3899_0_0_10)) (RunStep.eval_var B σ "right.d" (?nAX_g3899_0_0_11)) ?_)) (RunStep.seq B c55 c66 c2 c7 w c43 c85 (RunStep.assign B c2 "sum.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g3899_0_0_12)) (RunStep.eval_var B c2 "left.d" (?nAX_g3899_0_0_13)) ?_)) (RunStep.seq B c56 c65 c7 c12 w c45 c84 (RunStep.assign B c7 "rat.d" (Expr.mul (Expr.var "left.d") (Expr.var "right.d")) c11 (RunStep.eval_mul B c7 (Expr.var "left.d") (Expr.var "right.d") c9 c10 (RunStep.eval_var B c7 "left.d" (?nAX_g3899_0_0_14)) (RunStep.eval_var B c7 "right.d" (?nAX_g3899_0_0_15)) ?_)) (RunStep.seq B c64 normalizeFraction c12 c74 w c83 c34 (RunStep.ite_false B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c58 c63 c12 c74 c82 (RunStep.cond_eq_false B c12 (Expr.var "left.s") (Expr.var "right.s") c14 c15 (RunStep.eval_var B c12 "left.s" (?nAX_g3899_0_0_16)) (RunStep.eval_var B c12 "right.s" (?nAX_g3899_0_0_17)) hcase) (RunStep.ite_true B (Cond.lt (Expr.var "sum.u") (Expr.var "sum.v")) c60 c62 c12 c74 c81 (RunStep.cond_lt_true B c12 (Expr.var "sum.u") (Expr.var "sum.v") c27 c28 (RunStep.eval_var B c12 "sum.u" ?_) (RunStep.eval_var B c12 "sum.v" ?_) hcase_1) (RunStep.seq B c59 (Com.assign "rat.s" (Expr.var "right.s")) c12 c72 c74 c79 c80 (RunStep.assign B c12 "rat.n" (Expr.sub (Expr.var "sum.v") (Expr.var "sum.u")) c71 (RunStep.eval_sub B c12 (Expr.var "sum.v") (Expr.var "sum.u") c28 c27 (RunStep.eval_var B c12 "sum.v" ?_) (RunStep.eval_var B c12 "sum.u" ?_) ?_)) (RunStep.assign B c72 "rat.s" (Expr.var "right.s") c73 (RunStep.eval_var B c72 "right.s" (?nAX_g3899_0_0_18)))))) left)))) (?nAX_g3899_0_0_19)) ?_)) fun (hcase_1:c69) => @Exists.casesOn Env c92 (fun (x:@Exists Env c92) => c25) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "rat.n") c36) (And (@Eq Nat (Env.vars σ_1 "rat.d") c19) (@Eq Nat (Env.vars σ_1 "rat.s") c35))) normalizeFraction (fun (x σ':Env) => c37 σ') c34 hn c90 ?_) fun (w:Env) (h:And (c91 w c34) (c37 w)) => @And.casesOn (c91 w c34) (c37 w) (fun (x:And (c91 w c34) (c37 w)) => c25) h fun (left:c91 w c34) (right:c37 w) => @Exists.intro Env c24 w (@And.intro (Run B addFraction σ w c21) (c23 w) (RunStep.mono B addFraction σ w (c42 c100) c21 (RunStep.seq B (Com.assign "sum.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c55 c66) σ c2 w c41 c100 (RunStep.assign B σ "sum.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g3899_0_0_20)) (RunStep.eval_var B σ "right.d" (?nAX_g3899_0_0_21)) ?_)) (RunStep.seq B c55 c66 c2 c7 w c43 c99 (RunStep.assign B c2 "sum.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g3899_0_0_22)) (RunStep.eval_var B c2 "left.d" (?nAX_g3899_0_0_23)) ?_)) (RunStep.seq B c56 c65 c7 c12 w c45 c98 (RunStep.assign B c7 "rat.d" (Expr.mul (Expr.var "left.d") (Expr.var "right.d")) c11 (RunStep.eval_mul B c7 (Expr.var "left.d") (Expr.var "right.d") c9 c10 (RunStep.eval_var B c7 "left.d" (?nAX_g3899_0_0_24)) (RunStep.eval_var B c7 "right.d" (?nAX_g3899_0_0_25)) ?_)) (RunStep.seq B c64 normalizeFraction c12 c90 w c97 c34 (RunStep.ite_false B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c58 c63 c12 c90 c96 (RunStep.cond_eq_false B c12 (Expr.var "left.s") (Expr.var "right.s") c14 c15 (RunStep.eval_var B c12 "left.s" (?nAX_g3899_0_0_26)) (RunStep.eval_var B c12 "right.s" (?nAX_g3899_0_0_27)) hcase) (RunStep.ite_false B (Cond.lt (Expr.var "sum.u") (Expr.var "sum.v")) c60 c62 c12 c90 c95 (RunStep.cond_lt_false B c12 (Expr.var "sum.u") (Expr.var "sum.v") c27 c28 (RunStep.eval_var B c12 "sum.u" ?_) (RunStep.eval_var B c12 "sum.v" ?_) hcase_1) (RunStep.seq B c61 (Com.assign "rat.s" (Expr.var "left.s")) c12 c88 c90 c94 c49 (RunStep.assign B c12 "rat.n" (Expr.sub (Expr.var "sum.u") (Expr.var "sum.v")) c87 (RunStep.eval_sub B c12 (Expr.var "sum.u") (Expr.var "sum.v") c27 c28 (RunStep.eval_var B c12 "sum.u" ?_) (RunStep.eval_var B c12 "sum.v" ?_) ?_)) (RunStep.assign B c88 "rat.s" (Expr.var "left.s") c89 (RunStep.eval_var B c88 "left.s" (?nAX_g3899_0_0_28)))))) left)))) (?nAX_g3899_0_0_29)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g3899_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals simp_all [sumNumerator,sumSign]
  all_goals try omega

end Lax109476Proofs.RamRational

end

section

namespace Lax109476Proofs.RamRounding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamArithmetic RationalRounding

def ceilQuotient (n d:ℕ):ℕ:=n / d + if n % d=0 then 0 else 1

theorem ceilQuotient_int (n d:ℕ) (hd:0 < d):
    Int.ceil ((n:ℚ) / d)=(ceilQuotient n d:ℤ):=by
  have hdq:(0:ℚ) < d:=by exact_mod_cast hd
  have hrem:((n % d:ℕ):ℚ) < d:=by exact_mod_cast Nat.mod_lt n hd
  have heq:(d:ℚ) * (n / d:ℕ) + (n % d:ℕ)=n:=by
    exact_mod_cast Nat.div_add_mod n d
  apply Int.ceil_eq_iff.mpr
  rw [lt_div_iff₀ hdq,div_le_iff₀ hdq]
  by_cases hz:n % d=0
  · rw [hz,Nat.cast_zero,add_zero] at heq
    simp only [ceilQuotient,if_pos hz,add_zero,Int.cast_natCast]
    constructor <;> nlinarith
  · have hrpos:(0:ℚ) < ((n % d:ℕ):ℚ):=by exact_mod_cast Nat.pos_of_ne_zero hz
    simp only [ceilQuotient,if_neg hz,Int.cast_add,Int.cast_natCast,Int.cast_one,
      Nat.cast_add,Nat.cast_one]
    constructor <;> nlinarith

def roundMagnitude (s n d D:ℕ):ℕ:=
  if s=1 then ceilQuotient (n * D) d else (n * D) / d

theorem roundMagnitude_correct (s n d D:ℕ) (hd:0 < d):
    fractionValue s (roundMagnitude s n d D) D=roundDown (fractionValue s n d) D:=by
  have hpos:(n:ℚ) / d * D=((n * D:ℕ):ℚ) / d:=by push_cast; ring
  have hneg:-(n:ℚ) / d * D=-(((n * D:ℕ):ℚ) / d):=by push_cast; ring
  unfold fractionValue roundMagnitude roundDown
  by_cases hs:s=1
  · simp only [if_pos hs,hneg,Int.floor_neg,ceilQuotient_int (n * D) d hd,
      Int.cast_neg,Int.cast_natCast]
  · simp only [if_neg hs,hpos,Rat.floor_natCast_div_natCast]
    rw [← Int.natCast_ediv,Int.cast_natCast]

set_option maxHeartbeats 0 in
theorem roundFraction_spec (B M s n d D:ℕ) (hB:2 * M ^ 2 + 3 < B)
    (hs:s≤ 1) (hn:n≤ M) (hd:d≤ M) (hD:D≤ M)
    (hdpos:0 < d) (hDpos:0 < D):
    Spec B (fun σ => σ.vars "left.s"=s∧ σ.vars "left.n"=n∧
      σ.vars "left.d"=d∧ σ.vars "grid.D"=D) roundFraction
      (fun _ σ' => FractionOutput (roundDown (fractionValue s n d) D) σ')
      (36 * D.size + 96):=by
  have hM:M < B:=by nlinarith
  have hnB:=hn.trans_lt hM
  have hdB:=hd.trans_lt hM
  have hDB:=hD.trans_lt hM
  have ha:n * D≤ M * M:=Nat.mul_le_mul hn hD
  have haB:n * D < B:=ha.trans_lt (by nlinarith)
  have hqB:n * D / d < B:=(Nat.div_le_self _ _).trans_lt haB
  have hqdB:n * D / d * d < B:=(Nat.div_mul_le_self _ _).trans_lt haB
  have hrB:n * D - n * D / d * d < B:=(Nat.sub_le _ _).trans_lt haB
  have hq1B:n * D / d + 1 < B:=by have hq:=Nat.div_le_self (n * D) d; nlinarith
  have h1:1 < B:=by nlinarith
  have hsB:=hs.trans_lt h1
  have hmB:roundMagnitude s n d D < B:=by
    unfold roundMagnitude ceilQuotient
    split_ifs <;> omega
  have hnorm:=normalizeFraction_output_spec B s (roundMagnitude s n d D) D
    hs hmB hDB hDpos
  have hc:=roundMagnitude_correct s n d D hdpos
  have hmod:n * D - n * D / d * d=n * D % d:=by
    simpa only [Nat.mul_comm] using (Nat.mod_def (n * D) d).symm
  rintro σ ⟨hσs,hσn,hσd,hσD⟩
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.mul; let c1:Nat:=c0 (Env.vars σ "left.n") (Env.vars σ "grid.D"); let c2:Env:=Env.setVar σ "round.a" c1; let c3:String→ Nat:=Env.vars c2; let c4:Nat:=c3 "round.a"; let c5:Nat:=c3 "left.d"; let c6:Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) c4 c5; let c7:Env:=Env.setVar c2 "round.q" c6; let c8:String→ Nat:=Env.vars c7; let c9:Nat:=c8 "round.a"; let c10:Nat:=c8 "round.q"; let c11:Nat:=c8 "left.d"; let c12:Nat:=c0 c10 c11; let c13:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) c9 c12; let c14:Env:=Env.setVar c7 "round.r" c13; let c15:Nat:=Env.vars c14 "round.q"; let c16:Env:=Env.setVar c14 "rat.n" c15; let c17:String→ Nat:=Env.vars c16; let c18:Nat:=c17 "left.s"; let c19:Prop:= @Eq Nat c18 ((1:Nat)); let c20:Prop:=Not c19; let c21:Nat→ Nat→ Nat:=Nat.add; let c22:Nat→ Nat:=c21 (c0 ((36:Nat)) (Nat.size D)); let c23:Nat:=c22 ((96:Nat)); let c24:Env→ Prop:=FractionOutput (roundDown (fractionValue s n d) D); let c25:Env→ Prop:=(fun (x σ':Env) => c24 σ') σ; let c26:Env→ Prop:=fun (σ':Env) => And (Run B roundFraction σ σ' c23) (c25 σ'); let c27:Prop:= @Exists Env c26; let c28:Nat:=c17 "round.r"; let c29:Prop:= @Eq Nat c28 ((0:Nat)); let c30:Prop:=Not c29; let c31:String→ Nat→ Env:=Env.setVar c16; let c32:Env:=c31 "rat.s" c18; let c33:Nat:=Env.vars c32 "grid.D"; let c34:Env:=Env.setVar c32 "rat.d" c33; let c35:Env→ Nat→ Prop:=Run B normalizeFraction c34; let c36:Nat:=c22 ((16:Nat)); let c37:Env→ Prop:=FractionOutput (fractionValue s (roundMagnitude s n d D) D); let c38:Env→ Prop:=fun (σ':Env) => And (c35 σ' c36) (c37 σ'); let c39:String→ Nat:=Env.vars c34; let c40:Nat→ Nat:=c21 ((1:Nat)); let c41:Nat:=c40 (Expr.size (Expr.mul (Expr.var "left.n") (Expr.var "grid.D"))); let c42:Nat→ Nat:=c21 c41; let c43:Nat:=c40 (Expr.size (Expr.div (Expr.var "round.a") (Expr.var "left.d"))); let c44:Nat→ Nat:=c21 c43; let c45:Expr:=Expr.sub (Expr.var "round.a") (Expr.mul (Expr.var "round.q") (Expr.var "left.d")); let c46:Nat:=c40 (Expr.size c45); let c47:Nat→ Nat:=c21 c46; let c48:Nat:=c40 (Expr.size (Expr.var "round.q")); let c49:Nat→ Nat:=c21 c48; let c50:Cond:=Cond.eq (Expr.var "left.s") (Expr.lit ((1:Nat))); let c51:Nat→ Nat:=c21 (c40 (Cond.size c50)); let c52:Cond:=Cond.eq (Expr.var "round.r") (Expr.lit ((0:Nat))); let c53:Nat→ Nat:=c21 (c40 (Cond.size c52)); let c54:Nat:=c53 ((1:Nat)); let c55:Nat:=c51 c54; let c56:Nat:=c40 (Expr.size (Expr.var "left.s")); let c57:Nat:=c40 (Expr.size (Expr.var "grid.D")); let c58:Nat:=c21 c57 c36; let c59:Nat:=c21 c56 c58; let c60:Nat:=c21 c55 c59; let c61:Nat:=c49 c60; let c62:Nat:=c47 c61; let c63:Nat:=c44 c62; let c64:Com:=Com.assign "round.q" (Expr.div (Expr.var "round.a") (Expr.var "left.d")); let c65:Com:=Com.assign "round.r" c45; let c66:Expr:=Expr.add (Expr.var "rat.n") (Expr.lit ((1:Nat))); let c67:Com:=Com.assign "rat.n" c66; let c68:Com:=Com.ite c52 Com.skip c67; let c69:Com:=Com.ite c50 c68 Com.skip; let c70:Com:=Com.seq (Com.assign "rat.s" (Expr.var "left.s")) (Com.seq (Com.assign "rat.d" (Expr.var "grid.D")) normalizeFraction); let c71:Com:=Com.seq c69 c70; let c72:Com:=Com.seq (Com.assign "rat.n" (Expr.var "round.q")) c71; let c73:Com:=Com.seq c65 c72; let c74:Nat:=c17 "rat.n"; let c75:Nat:=c21 c74 ((1:Nat)); let c76:Env:=c31 "rat.n" c75; let c77:Nat:=Env.vars c76 "left.s"; let c78:Env:=Env.setVar c76 "rat.s" c77; let c79:Nat:=Env.vars c78 "grid.D"; let c80:Env:=Env.setVar c78 "rat.d" c79; let c81:Env→ Nat→ Prop:=Run B normalizeFraction c80; let c82:Env→ Prop:=fun (σ':Env) => And (c81 σ' c36) (c37 σ'); let c83:String→ Nat:=Env.vars c80; let c84:Nat:=c40 (Expr.size c66); let c85:Nat:=c53 c84; let c86:Nat:=c51 c85; let c87:Nat:=c21 c86 c59; let c88:Nat:=c49 c87; let c89:Nat:=c47 c88; let c90:Nat:=c44 c89; let c91:Nat:=c51 ((1:Nat)); let c92:Nat:=c21 c91 c59; let c93:Nat:=c49 c92; let c94:Nat:=c47 c93; let c95:Nat:=c44 c94; @Or.casesOn c19 c20 (fun (x:Or c19 c20) => c27) (Classical.em c19) (fun (hcase:c19) => @Or.casesOn c29 c30 (fun (x:Or c29 c30) => c27) (Classical.em c29) (fun (hcase_1:c29) => @Exists.casesOn Env c38 (fun (x:@Exists Env c38) => c27) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "rat.n") (roundMagnitude s n d D)) (And (@Eq Nat (Env.vars σ_1 "rat.d") D) (@Eq Nat (Env.vars σ_1 "rat.s") s))) normalizeFraction (fun (x σ':Env) => c37 σ') c36 hnorm c34 ?_) fun (w:Env) (h:And (c35 w c36) (c37 w)) => @And.casesOn (c35 w c36) (c37 w) (fun (x:And (c35 w c36) (c37 w)) => c27) h fun (left:c35 w c36) (right:c37 w) => @Exists.intro Env c26 w (@And.intro (Run B roundFraction σ w c23) (c25 w) (RunStep.mono B roundFraction σ w (c42 c63) c23 (RunStep.seq B (Com.assign "round.a" (Expr.mul (Expr.var "left.n") (Expr.var "grid.D"))) (Com.seq c64 c73) σ c2 w c41 c63 (RunStep.assign B σ "round.a" (Expr.mul (Expr.var "left.n") (Expr.var "grid.D")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "grid.D") (Env.vars σ "left.n") (Env.vars σ "grid.D") (RunStep.eval_var B σ "left.n" (?nAX_g3913_0_0_0)) (RunStep.eval_var B σ "grid.D" (?nAX_g3913_0_0_1)) ?_)) (RunStep.seq B c64 c73 c2 c7 w c43 c62 (RunStep.assign B c2 "round.q" (Expr.div (Expr.var "round.a") (Expr.var "left.d")) c6 (RunStep.eval_div B c2 (Expr.var "round.a") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "round.a" ?_) (RunStep.eval_var B c2 "left.d" (?nAX_g3913_0_0_2)) ?_)) (RunStep.seq B c65 c72 c7 c14 w c46 c61 (RunStep.assign B c7 "round.r" c45 c13 (RunStep.eval_sub B c7 (Expr.var "round.a") (Expr.mul (Expr.var "round.q") (Expr.var "left.d")) c9 c12 (RunStep.eval_var B c7 "round.a" ?_) (RunStep.eval_mul B c7 (Expr.var "round.q") (Expr.var "left.d") c10 c11 (RunStep.eval_var B c7 "round.q" ?_) (RunStep.eval_var B c7 "left.d" (?nAX_g3913_0_0_3)) ?_) ?_)) (RunStep.seq B (Com.assign "rat.n" (Expr.var "round.q")) c71 c14 c16 w c48 c60 (RunStep.assign B c14 "rat.n" (Expr.var "round.q") c15 (RunStep.eval_var B c14 "round.q" ?_)) (RunStep.seq B c69 c70 c16 c16 w c55 c59 (RunStep.ite_true B c50 c68 Com.skip c16 c16 c54 (RunStep.cond_eq_true B c16 (Expr.var "left.s") (Expr.lit ((1:Nat))) c18 ((1:Nat)) (RunStep.eval_var B c16 "left.s" (?nAX_g3913_0_0_4)) (RunStep.eval_lit B ((1:Nat)) c16 h1) hcase) (RunStep.ite_true B c52 Com.skip c67 c16 c16 ((1:Nat)) (RunStep.cond_eq_true B c16 (Expr.var "round.r") (Expr.lit ((0:Nat))) c28 ((0:Nat)) (RunStep.eval_var B c16 "round.r" ?_) (RunStep.eval_lit B ((0:Nat)) c16 (?nAX_g3913_0_0_5)) hcase_1) (RunStep.skip B c16))) (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s")) (Com.seq (Com.assign "rat.d" (Expr.var "grid.D")) normalizeFraction) c16 c32 w c56 c58 (RunStep.assign B c16 "rat.s" (Expr.var "left.s") c18 (RunStep.eval_var B c16 "left.s" (?nAX_g3913_0_0_6))) (RunStep.seq B (Com.assign "rat.d" (Expr.var "grid.D")) normalizeFraction c32 c34 w c57 c36 (RunStep.assign B c32 "rat.d" (Expr.var "grid.D") c33 (RunStep.eval_var B c32 "grid.D" (?nAX_g3913_0_0_7))) left))))))) (?nAX_g3913_0_0_8)) ?_)) fun (hcase_1:c30) => @Exists.casesOn Env c82 (fun (x:@Exists Env c82) => c27) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "rat.n") (roundMagnitude s n d D)) (And (@Eq Nat (Env.vars σ_1 "rat.d") D) (@Eq Nat (Env.vars σ_1 "rat.s") s))) normalizeFraction (fun (x σ':Env) => c37 σ') c36 hnorm c80 ?_) fun (w:Env) (h:And (c81 w c36) (c37 w)) => @And.casesOn (c81 w c36) (c37 w) (fun (x:And (c81 w c36) (c37 w)) => c27) h fun (left:c81 w c36) (right:c37 w) => @Exists.intro Env c26 w (@And.intro (Run B roundFraction σ w c23) (c25 w) (RunStep.mono B roundFraction σ w (c42 c90) c23 (RunStep.seq B (Com.assign "round.a" (Expr.mul (Expr.var "left.n") (Expr.var "grid.D"))) (Com.seq c64 c73) σ c2 w c41 c90 (RunStep.assign B σ "round.a" (Expr.mul (Expr.var "left.n") (Expr.var "grid.D")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "grid.D") (Env.vars σ "left.n") (Env.vars σ "grid.D") (RunStep.eval_var B σ "left.n" (?nAX_g3913_0_0_9)) (RunStep.eval_var B σ "grid.D" (?nAX_g3913_0_0_10)) ?_)) (RunStep.seq B c64 c73 c2 c7 w c43 c89 (RunStep.assign B c2 "round.q" (Expr.div (Expr.var "round.a") (Expr.var "left.d")) c6 (RunStep.eval_div B c2 (Expr.var "round.a") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "round.a" ?_) (RunStep.eval_var B c2 "left.d" (?nAX_g3913_0_0_11)) ?_)) (RunStep.seq B c65 c72 c7 c14 w c46 c88 (RunStep.assign B c7 "round.r" c45 c13 (RunStep.eval_sub B c7 (Expr.var "round.a") (Expr.mul (Expr.var "round.q") (Expr.var "left.d")) c9 c12 (RunStep.eval_var B c7 "round.a" ?_) (RunStep.eval_mul B c7 (Expr.var "round.q") (Expr.var "left.d") c10 c11 (RunStep.eval_var B c7 "round.q" ?_) (RunStep.eval_var B c7 "left.d" (?nAX_g3913_0_0_12)) ?_) ?_)) (RunStep.seq B (Com.assign "rat.n" (Expr.var "round.q")) c71 c14 c16 w c48 c87 (RunStep.assign B c14 "rat.n" (Expr.var "round.q") c15 (RunStep.eval_var B c14 "round.q" ?_)) (RunStep.seq B c69 c70 c16 c76 w c86 c59 (RunStep.ite_true B c50 c68 Com.skip c16 c76 c85 (RunStep.cond_eq_true B c16 (Expr.var "left.s") (Expr.lit ((1:Nat))) c18 ((1:Nat)) (RunStep.eval_var B c16 "left.s" (?nAX_g3913_0_0_13)) (RunStep.eval_lit B ((1:Nat)) c16 h1) hcase) (RunStep.ite_false B c52 Com.skip c67 c16 c76 c84 (RunStep.cond_eq_false B c16 (Expr.var "round.r") (Expr.lit ((0:Nat))) c28 ((0:Nat)) (RunStep.eval_var B c16 "round.r" ?_) (RunStep.eval_lit B ((0:Nat)) c16 (?nAX_g3913_0_0_14)) hcase_1) (RunStep.assign B c16 "rat.n" c66 c75 (RunStep.eval_add B c16 (Expr.var "rat.n") (Expr.lit ((1:Nat))) c74 ((1:Nat)) (RunStep.eval_var B c16 "rat.n" ?_) (RunStep.eval_lit B ((1:Nat)) c16 h1) ?_)))) (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s")) (Com.seq (Com.assign "rat.d" (Expr.var "grid.D")) normalizeFraction) c76 c78 w c56 c58 (RunStep.assign B c76 "rat.s" (Expr.var "left.s") c77 (RunStep.eval_var B c76 "left.s" (?nAX_g3913_0_0_15))) (RunStep.seq B (Com.assign "rat.d" (Expr.var "grid.D")) normalizeFraction c78 c80 w c57 c36 (RunStep.assign B c78 "rat.d" (Expr.var "grid.D") c79 (RunStep.eval_var B c78 "grid.D" (?nAX_g3913_0_0_16))) left))))))) (?nAX_g3913_0_0_17)) ?_)) fun (hcase:c20) => @Exists.casesOn Env c38 (fun (x:@Exists Env c38) => c27) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "rat.n") (roundMagnitude s n d D)) (And (@Eq Nat (Env.vars σ_1 "rat.d") D) (@Eq Nat (Env.vars σ_1 "rat.s") s))) normalizeFraction (fun (x σ':Env) => c37 σ') c36 hnorm c34 ?_) fun (w:Env) (h:And (c35 w c36) (c37 w)) => @And.casesOn (c35 w c36) (c37 w) (fun (x:And (c35 w c36) (c37 w)) => c27) h fun (left:c35 w c36) (right:c37 w) => @Exists.intro Env c26 w (@And.intro (Run B roundFraction σ w c23) (c25 w) (RunStep.mono B roundFraction σ w (c42 c95) c23 (RunStep.seq B (Com.assign "round.a" (Expr.mul (Expr.var "left.n") (Expr.var "grid.D"))) (Com.seq c64 c73) σ c2 w c41 c95 (RunStep.assign B σ "round.a" (Expr.mul (Expr.var "left.n") (Expr.var "grid.D")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "grid.D") (Env.vars σ "left.n") (Env.vars σ "grid.D") (RunStep.eval_var B σ "left.n" (?nAX_g3913_0_0_18)) (RunStep.eval_var B σ "grid.D" (?nAX_g3913_0_0_19)) ?_)) (RunStep.seq B c64 c73 c2 c7 w c43 c94 (RunStep.assign B c2 "round.q" (Expr.div (Expr.var "round.a") (Expr.var "left.d")) c6 (RunStep.eval_div B c2 (Expr.var "round.a") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "round.a" ?_) (RunStep.eval_var B c2 "left.d" (?nAX_g3913_0_0_20)) ?_)) (RunStep.seq B c65 c72 c7 c14 w c46 c93 (RunStep.assign B c7 "round.r" c45 c13 (RunStep.eval_sub B c7 (Expr.var "round.a") (Expr.mul (Expr.var "round.q") (Expr.var "left.d")) c9 c12 (RunStep.eval_var B c7 "round.a" ?_) (RunStep.eval_mul B c7 (Expr.var "round.q") (Expr.var "left.d") c10 c11 (RunStep.eval_var B c7 "round.q" ?_) (RunStep.eval_var B c7 "left.d" (?nAX_g3913_0_0_21)) ?_) ?_)) (RunStep.seq B (Com.assign "rat.n" (Expr.var "round.q")) c71 c14 c16 w c48 c92 (RunStep.assign B c14 "rat.n" (Expr.var "round.q") c15 (RunStep.eval_var B c14 "round.q" ?_)) (RunStep.seq B c69 c70 c16 c16 w c91 c59 (RunStep.ite_false B c50 c68 Com.skip c16 c16 ((1:Nat)) (RunStep.cond_eq_false B c16 (Expr.var "left.s") (Expr.lit ((1:Nat))) c18 ((1:Nat)) (RunStep.eval_var B c16 "left.s" (?nAX_g3913_0_0_22)) (RunStep.eval_lit B ((1:Nat)) c16 h1) hcase) (RunStep.skip B c16)) (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s")) (Com.seq (Com.assign "rat.d" (Expr.var "grid.D")) normalizeFraction) c16 c32 w c56 c58 (RunStep.assign B c16 "rat.s" (Expr.var "left.s") c18 (RunStep.eval_var B c16 "left.s" (?nAX_g3913_0_0_23))) (RunStep.seq B (Com.assign "rat.d" (Expr.var "grid.D")) normalizeFraction c32 c34 w c57 c36 (RunStep.assign B c32 "rat.d" (Expr.var "grid.D") c33 (RunStep.eval_var B c32 "grid.D" (?nAX_g3913_0_0_24))) left))))))) (?nAX_g3913_0_0_25)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g3913_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals simp_all [roundMagnitude,ceilQuotient]

end Lax109476Proofs.RamRounding

end

section

open scoped BigOperators

namespace Lax109476Proofs.RationalArithmeticBounds

open DeterminantBounds RationalSizeBounds
open Lax109476.RationalEncoding Lax759944.BinaryWordEncoding

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

theorem height_sub (q r:ℚ) (B C:ℕ) (hq:Height q B) (hr:Height r C):
    Height (q - r) (2 * B * C):=by
  simpa only [sub_eq_add_neg] using height_add q (-r) B C hq (height_neg r C hr)

end Lax109476Proofs.RationalArithmeticBounds

end

section

namespace Lax109476Proofs.RamPrimitiveBounds

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRounding RationalSizeBounds RationalArithmeticBounds

theorem multiplyFraction_uniform_spec (B M s₁ n₁ d₁ s₂ n₂ d₂:ℕ)
    (hB:2 * M ^ 2 + 3 < B) (hs₁:s₁≤ 1) (hs₂:s₂≤ 1)
    (hn₁:n₁≤ M) (hd₁:d₁≤ M) (hn₂:n₂≤ M) (hd₂:d₂≤ M)
    (hd₁pos:0 < d₁) (hd₂pos:0 < d₂):
    Spec B (fractionInputs s₁ n₁ d₁ s₂ n₂ d₂) multiplyFraction
      (fun _ τ => FractionOutput (fractionValue s₁ n₁ d₁ * fractionValue s₂ n₂ d₂) τ)
      (72 * M.size + 64):=by
  apply (multiplyFraction_spec B M s₁ n₁ d₁ s₂ n₂ d₂ hB hs₁ hs₂ hn₁ hd₁ hn₂ hd₂
    hd₁pos hd₂pos).mono
  have hs:=size_mul_le d₁ d₂
  have h₁:=Nat.size_le_size hd₁
  have h₂:=Nat.size_le_size hd₂
  omega

theorem addFraction_uniform_spec (B M s₁ n₁ d₁ s₂ n₂ d₂:ℕ)
    (hB:2 * M ^ 2 + 3 < B) (hs₁:s₁≤ 1) (hs₂:s₂≤ 1)
    (hn₁:n₁≤ M) (hd₁:d₁≤ M) (hn₂:n₂≤ M) (hd₂:d₂≤ M)
    (hd₁pos:0 < d₁) (hd₂pos:0 < d₂):
    Spec B (fractionInputs s₁ n₁ d₁ s₂ n₂ d₂) addFraction
      (fun _ τ => FractionOutput (fractionValue s₁ n₁ d₁ + fractionValue s₂ n₂ d₂) τ)
      (72 * M.size + 96):=by
  apply (addFraction_spec B M s₁ n₁ d₁ s₂ n₂ d₂ hB hs₁ hs₂ hn₁ hd₁ hn₂ hd₂
    hd₁pos hd₂pos).mono
  have hs:=size_mul_le d₁ d₂
  have h₁:=Nat.size_le_size hd₁
  have h₂:=Nat.size_le_size hd₂
  omega

theorem roundFraction_uniform_spec (B M s n d D:ℕ) (hB:2 * M ^ 2 + 3 < B)
    (hs:s≤ 1) (hn:n≤ M) (hd:d≤ M) (hD:D≤ M)
    (hdpos:0 < d) (hDpos:0 < D):
    Spec B (fun σ => σ.vars "left.s"=s∧ σ.vars "left.n"=n∧
      σ.vars "left.d"=d∧ σ.vars "grid.D"=D) roundFraction
      (fun _ τ => FractionOutput (RationalRounding.roundDown (fractionValue s n d) D) τ)
      (36 * M.size + 96):=by
  apply (roundFraction_spec B M s n d D hB hs hn hd hD hdpos hDpos).mono
  have hs:=Nat.size_le_size hD
  omega

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
    (refine let c0:Env→ Prop:=LeftOutput (@getElem (List Rat) Nat Rat (fun (as:List Rat) (i_1:Nat) => Nat.lt i_1 (@List.length Rat as)) (@List.instGetElemNatLtLength Rat) qs i hi); let c1:Env→ Prop:=(fun (x τ:Env) => c0 τ) σ; let c2:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a; let c3:String:=c2 ".s"; let c4:Nat:= @List.getD Nat (Env.arrs σ c3) (Env.vars σ "vec.i") ((0:Nat)); let c5:Env:=Env.setVar σ "left.s" c4; let c6:String:=c2 ".n"; let c7:Nat:=Env.vars c5 "vec.i"; let c8:Nat:= @List.getD Nat (Env.arrs c5 c6) c7 ((0:Nat)); let c9:Env:=Env.setVar c5 "left.n" c8; let c10:String:=c2 ".d"; let c11:Nat:=Env.vars c9 "vec.i"; let c12:Nat:= @List.getD Nat (Env.arrs c9 c10) c11 ((0:Nat)); let c13:Env:=Env.setVar c9 "left.d" c12; let c14:Nat→ Nat→ Nat:=Nat.add; let c15:Nat→ Nat:=c14 ((1:Nat)); let c16:Expr:=Expr.get c3 (Expr.var "vec.i"); let c17:Nat:=c15 (Expr.size c16); let c18:Expr:=Expr.get c6 (Expr.var "vec.i"); let c19:Nat:=c15 (Expr.size c18); let c20:Expr:=Expr.get c10 (Expr.var "vec.i"); let c21:Nat:=c15 (Expr.size c20); let c22:Nat:=c14 c19 c21; let c23:Com:=Com.assign "left.n" c18; let c24:Com:=Com.assign "left.d" c20; @Exists.intro Env (fun (σ':Env) => And (Run B (loadLeft a) σ σ' ((9:Nat))) (c1 σ')) c13 (@And.intro (Run B (loadLeft a) σ c13 ((9:Nat))) (c1 c13) (RunStep.mono B (loadLeft a) σ c13 (c14 c17 c22) ((9:Nat)) (RunStep.seq B (Com.assign "left.s" c16) (Com.seq c23 c24) σ c5 c13 c17 c22 (RunStep.assign B σ "left.s" c16 c4 (RunStep.eval_get B σ c3 (Expr.var "vec.i") (Env.vars σ "vec.i") (RunStep.eval_var B σ "vec.i" (?nAX_g3955_0_0_0)) (?nAX_g3955_0_0_1) ?_)) (RunStep.seq B c23 c24 c5 c9 c13 c19 c21 (RunStep.assign B c5 "left.n" c18 c8 (RunStep.eval_get B c5 c6 (Expr.var "vec.i") c7 (RunStep.eval_var B c5 "vec.i" (?nAX_g3955_0_0_2)) (?nAX_g3955_0_0_3) ?_)) (RunStep.assign B c9 "left.d" c20 c12 (RunStep.eval_get B c9 c10 (Expr.var "vec.i") c11 (RunStep.eval_var B c9 "vec.i" (?nAX_g3955_0_0_4)) (?nAX_g3955_0_0_5) ?_)))) (?nAX_g3955_0_0_6)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g3955_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3955_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3955_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3955_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3955_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3955_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3955_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [LeftOutput]

def RightOutput (q:ℚ) (σ:Env):Prop:=
  σ.vars "right.s"=rationalSign q∧ σ.vars "right.n"=q.num.natAbs∧ σ.vars "right.d"=q.den

theorem loadRight_spec (B:ℕ) (a:String) (qs:List ℚ) (i:ℕ) (hi:i < qs.length)
    (hB:1 < B) (hiB:i < B) (hn:qs[i].num.natAbs < B) (hd:qs[i].den < B):
    Spec B (fun σ => Represents a qs σ∧ σ.vars "vec.i"=i) (loadRight a)
      (fun _ τ => RightOutput qs[i] τ) 9:=by
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
    (refine let c0:Env→ Prop:=RightOutput (@getElem (List Rat) Nat Rat (fun (as:List Rat) (i_1:Nat) => Nat.lt i_1 (@List.length Rat as)) (@List.instGetElemNatLtLength Rat) qs i hi); let c1:Env→ Prop:=(fun (x τ:Env) => c0 τ) σ; let c2:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a; let c3:String:=c2 ".s"; let c4:Nat:= @List.getD Nat (Env.arrs σ c3) (Env.vars σ "vec.i") ((0:Nat)); let c5:Env:=Env.setVar σ "right.s" c4; let c6:String:=c2 ".n"; let c7:Nat:=Env.vars c5 "vec.i"; let c8:Nat:= @List.getD Nat (Env.arrs c5 c6) c7 ((0:Nat)); let c9:Env:=Env.setVar c5 "right.n" c8; let c10:String:=c2 ".d"; let c11:Nat:=Env.vars c9 "vec.i"; let c12:Nat:= @List.getD Nat (Env.arrs c9 c10) c11 ((0:Nat)); let c13:Env:=Env.setVar c9 "right.d" c12; let c14:Nat→ Nat→ Nat:=Nat.add; let c15:Nat→ Nat:=c14 ((1:Nat)); let c16:Expr:=Expr.get c3 (Expr.var "vec.i"); let c17:Nat:=c15 (Expr.size c16); let c18:Expr:=Expr.get c6 (Expr.var "vec.i"); let c19:Nat:=c15 (Expr.size c18); let c20:Expr:=Expr.get c10 (Expr.var "vec.i"); let c21:Nat:=c15 (Expr.size c20); let c22:Nat:=c14 c19 c21; let c23:Com:=Com.assign "right.n" c18; let c24:Com:=Com.assign "right.d" c20; @Exists.intro Env (fun (σ':Env) => And (Run B (loadRight a) σ σ' ((9:Nat))) (c1 σ')) c13 (@And.intro (Run B (loadRight a) σ c13 ((9:Nat))) (c1 c13) (RunStep.mono B (loadRight a) σ c13 (c14 c17 c22) ((9:Nat)) (RunStep.seq B (Com.assign "right.s" c16) (Com.seq c23 c24) σ c5 c13 c17 c22 (RunStep.assign B σ "right.s" c16 c4 (RunStep.eval_get B σ c3 (Expr.var "vec.i") (Env.vars σ "vec.i") (RunStep.eval_var B σ "vec.i" (?nAX_g3959_0_0_0)) (?nAX_g3959_0_0_1) ?_)) (RunStep.seq B c23 c24 c5 c9 c13 c19 c21 (RunStep.assign B c5 "right.n" c18 c8 (RunStep.eval_get B c5 c6 (Expr.var "vec.i") c7 (RunStep.eval_var B c5 "vec.i" (?nAX_g3959_0_0_2)) (?nAX_g3959_0_0_3) ?_)) (RunStep.assign B c9 "right.d" c20 c12 (RunStep.eval_get B c9 c10 (Expr.var "vec.i") c11 (RunStep.eval_var B c9 "vec.i" (?nAX_g3959_0_0_4)) (?nAX_g3959_0_0_5) ?_)))) (?nAX_g3959_0_0_6)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g3959_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3959_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3959_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3959_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3959_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3959_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3959_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [RightOutput]

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
    (refine let c0:Prop:= @Eq Nat (Env.vars σ "rat.n") ((0:Nat)); let c1:Prop:=Not c0; let c2:Env→ Prop:=Represents a (@List.set Rat qs i q); let c3:Env→ Prop:=(fun (x τ:Env) => c2 τ) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B (storeReduced a) σ σ' ((13:Nat))) (c3 σ'); let c5:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a; let c6:String:=c5 ".s"; let c7:Nat→ Env:=Env.setArr σ c6 (Env.vars σ "vec.i"); let c8:Env:=c7 ((0:Nat)); let c9:String:=c5 ".n"; let c10:String→ Nat:=Env.vars c8; let c11:Nat:=c10 "vec.i"; let c12:Nat:=c10 "rat.n"; let c13:Env:=Env.setArr c8 c9 c11 c12; let c14:String:=c5 ".d"; let c15:String→ Nat:=Env.vars c13; let c16:Nat:=c15 "vec.i"; let c17:Nat:=c15 "rat.d"; let c18:Env:=Env.setArr c13 c14 c16 c17; let c19:Nat→ Nat→ Nat:=Nat.add; let c20:Nat→ Nat:=c19 ((1:Nat)); let c21:Cond:=Cond.eq (Expr.var "rat.n") (Expr.lit ((0:Nat))); let c22:Nat→ Nat:=c19 (c20 (Cond.size c21)); let c23:Nat→ Nat:=c19 (c20 (Expr.size (Expr.var "vec.i"))); let c24:Nat:=c23 (Expr.size (Expr.lit ((0:Nat)))); let c25:Nat:=c22 c24; let c26:Nat:=c23 (Expr.size (Expr.var "rat.n")); let c27:Nat:=c23 (Expr.size (Expr.var "rat.d")); let c28:Nat:=c19 c26 c27; let c29:Expr→ Com:=Com.store c6 (Expr.var "vec.i"); let c30:Com:=c29 (Expr.lit ((0:Nat))); let c31:Com:=c29 (Expr.var "rat.s"); let c32:Com:=Com.store c9 (Expr.var "vec.i") (Expr.var "rat.n"); let c33:Com:=Com.store c14 (Expr.var "vec.i") (Expr.var "rat.d"); let c34:Env:=c7 (Env.vars σ "rat.s"); let c35:String→ Nat:=Env.vars c34; let c36:Nat:=c35 "vec.i"; let c37:Nat:=c35 "rat.n"; let c38:Env:=Env.setArr c34 c9 c36 c37; let c39:String→ Nat:=Env.vars c38; let c40:Nat:=c39 "vec.i"; let c41:Nat:=c39 "rat.d"; let c42:Env:=Env.setArr c38 c14 c40 c41; let c43:Nat:=c23 (Expr.size (Expr.var "rat.s")); let c44:Nat:=c22 c43; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c4) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c4 c18 (@And.intro (Run B (storeReduced a) σ c18 ((13:Nat))) (c3 c18) (RunStep.mono B (storeReduced a) σ c18 (c19 c25 c28) ((13:Nat)) (RunStep.seq B (Com.ite c21 c30 c31) (Com.seq c32 c33) σ c8 c18 c25 c28 (RunStep.ite_true B c21 c30 c31 σ c8 c24 (RunStep.cond_eq_true B σ (Expr.var "rat.n") (Expr.lit ((0:Nat))) (Env.vars σ "rat.n") ((0:Nat)) (RunStep.eval_var B σ "rat.n" hnB) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g3962_0_0_0)) hcase) (RunStep.store B σ c6 (Expr.var "vec.i") (Expr.lit ((0:Nat))) (Env.vars σ "vec.i") ((0:Nat)) (RunStep.eval_var B σ "vec.i" (?nAX_g3962_0_0_1)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g3962_0_0_2)) (?nAX_g3962_0_0_3))) (RunStep.seq B c32 c33 c8 c13 c18 c26 c27 (RunStep.store B c8 c9 (Expr.var "vec.i") (Expr.var "rat.n") c11 c12 (RunStep.eval_var B c8 "vec.i" (?nAX_g3962_0_0_4)) (RunStep.eval_var B c8 "rat.n" (?nAX_g3962_0_0_5)) (?nAX_g3962_0_0_6)) (RunStep.store B c13 c14 (Expr.var "vec.i") (Expr.var "rat.d") c16 c17 (RunStep.eval_var B c13 "vec.i" (?nAX_g3962_0_0_7)) (RunStep.eval_var B c13 "rat.d" (?nAX_g3962_0_0_8)) (?nAX_g3962_0_0_9)))) (?nAX_g3962_0_0_10)) ?_)) fun (hcase:c1) => @Exists.intro Env c4 c42 (@And.intro (Run B (storeReduced a) σ c42 ((13:Nat))) (c3 c42) (RunStep.mono B (storeReduced a) σ c42 (c19 c44 c28) ((13:Nat)) (RunStep.seq B (Com.ite c21 c30 c31) (Com.seq c32 c33) σ c34 c42 c44 c28 (RunStep.ite_false B c21 c30 c31 σ c34 c43 (RunStep.cond_eq_false B σ (Expr.var "rat.n") (Expr.lit ((0:Nat))) (Env.vars σ "rat.n") ((0:Nat)) (RunStep.eval_var B σ "rat.n" hnB) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g3962_0_0_11)) hcase) (RunStep.store B σ c6 (Expr.var "vec.i") (Expr.var "rat.s") (Env.vars σ "vec.i") (Env.vars σ "rat.s") (RunStep.eval_var B σ "vec.i" (?nAX_g3962_0_0_12)) (RunStep.eval_var B σ "rat.s" hsB) (?nAX_g3962_0_0_13))) (RunStep.seq B c32 c33 c34 c38 c42 c26 c27 (RunStep.store B c34 c9 (Expr.var "vec.i") (Expr.var "rat.n") c36 c37 (RunStep.eval_var B c34 "vec.i" (?nAX_g3962_0_0_14)) (RunStep.eval_var B c34 "rat.n" (?nAX_g3962_0_0_15)) (?nAX_g3962_0_0_16)) (RunStep.store B c38 c14 (Expr.var "vec.i") (Expr.var "rat.d") c40 c41 (RunStep.eval_var B c38 "vec.i" (?nAX_g3962_0_0_17)) (RunStep.eval_var B c38 "rat.d" (?nAX_g3962_0_0_18)) (?nAX_g3962_0_0_19)))) (?nAX_g3962_0_0_20)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g3962_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Represents,Env.setArr,List.map_set]

end Lax109476Proofs.RamRationalArrays

end

section

namespace Lax109476Proofs.RamFractionInterface

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamPrimitiveBounds RamRationalArrays RamRounding RationalArithmeticBounds

def LeftValue (q:ℚ) (σ:Env):Prop:=
  fractionValue (σ.vars "left.s") (σ.vars "left.n") (σ.vars "left.d")=q∧
    σ.vars "left.n"=q.num.natAbs∧ σ.vars "left.d"=q.den∧ σ.vars "left.s" ≤ 1

def RightValue (q:ℚ) (σ:Env):Prop:=
  fractionValue (σ.vars "right.s") (σ.vars "right.n") (σ.vars "right.d")=q∧
    σ.vars "right.n"=q.num.natAbs∧ σ.vars "right.d"=q.den∧ σ.vars "right.s" ≤ 1

theorem leftValue_of_output (q:ℚ) (σ:Env) (h:LeftOutput q σ):LeftValue q σ:=by
  rcases h with ⟨hs,hn,hd⟩
  exact ⟨by rw [hs,hn,hd]; exact canonical_fractionValue q,hn,hd,hs ▸ rationalSign_le_one q⟩

theorem rightValue_of_output (q:ℚ) (σ:Env) (h:RightOutput q σ):RightValue q σ:=by
  rcases h with ⟨hs,hn,hd⟩
  exact ⟨by rw [hs,hn,hd]; exact canonical_fractionValue q,hn,hd,hs ▸ rationalSign_le_one q⟩

theorem multiply_spec (B M:ℕ) (q r:ℚ) (hB:2 * M ^ 2 + 3 < B)
    (hq:Height q M) (hr:Height r M):
    Spec B (fun σ => LeftValue q σ∧ RightValue r σ) multiplyFraction
      (fun _ τ => FractionOutput (q * r) τ) (72 * M.size + 64):=by
  rintro σ ⟨⟨hqval,hqn,hqd,hqs⟩, ⟨hrval,hrn,hrd,hrs⟩⟩
  rw [hqn,hqd] at hqval
  rw [hrn,hrd] at hrval
  obtain ⟨τ,hrun,hτ⟩:=multiplyFraction_uniform_spec B M (σ.vars "left.s") q.num.natAbs q.den
    (σ.vars "right.s") r.num.natAbs r.den hB hqs hrs hq.1 hq.2 hr.1 hr.2 q.den_pos r.den_pos
    σ ⟨rfl,hqn,hqd,rfl,hrn,hrd⟩
  exact ⟨τ,hrun,by simpa only [hqval,hrval] using hτ⟩

theorem add_spec (B M:ℕ) (q r:ℚ) (hB:2 * M ^ 2 + 3 < B)
    (hq:Height q M) (hr:Height r M):
    Spec B (fun σ => LeftValue q σ∧ RightValue r σ) addFraction
      (fun _ τ => FractionOutput (q + r) τ) (72 * M.size + 96):=by
  rintro σ ⟨⟨hqval,hqn,hqd,hqs⟩, ⟨hrval,hrn,hrd,hrs⟩⟩
  rw [hqn,hqd] at hqval
  rw [hrn,hrd] at hrval
  obtain ⟨τ,hrun,hτ⟩:=addFraction_uniform_spec B M (σ.vars "left.s") q.num.natAbs q.den
    (σ.vars "right.s") r.num.natAbs r.den hB hqs hrs hq.1 hq.2 hr.1 hr.2 q.den_pos r.den_pos
    σ ⟨rfl,hqn,hqd,rfl,hrn,hrd⟩
  exact ⟨τ,hrun,by simpa only [hqval,hrval] using hτ⟩

theorem round_spec (B M D:ℕ) (q:ℚ) (hB:2 * M ^ 2 + 3 < B)
    (hq:Height q M) (hD:D≤ M) (hDpos:0 < D):
    Spec B (fun σ => LeftValue q σ∧ σ.vars "grid.D"=D) roundFraction
      (fun _ τ => FractionOutput (RationalRounding.roundDown q D) τ) (36 * M.size + 96):=by
  rintro σ ⟨⟨hqval,hqn,hqd,hqs⟩,hσD⟩
  rw [hqn,hqd] at hqval
  obtain ⟨τ,hrun,hτ⟩:=roundFraction_uniform_spec B M (σ.vars "left.s") q.num.natAbs q.den D
    hB hqs hq.1 hq.2 hD q.den_pos hDpos σ ⟨rfl,hqn,hqd,hσD⟩
  exact ⟨τ,hrun,by simpa only [hqval] using hτ⟩

theorem resultToLeft_spec (B:ℕ) (q:ℚ) (h1:1 < B)
    (hn:q.num.natAbs < B) (hd:q.den < B):
    Spec B (FractionOutput q) resultToLeft (fun _ τ => LeftValue q τ) 6:=by
  rintro σ ⟨hqval,hqn,hqd,hqs⟩
  have hsB:=hqs.trans_lt h1
  (expose_names;
    (refine let c0:Nat:=Env.vars (Env.setVar σ "left.s" (Env.vars σ "rat.s")) "rat.n"; let c1:Env:=Env.setVar (Env.setVar σ "left.s" (Env.vars σ "rat.s")) "left.n" c0; let c2:Nat:=Env.vars c1 "rat.d"; let c3:Env:=Env.setVar c1 "left.d" c2; let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat→ Nat:=c4 ((1:Nat)); let c6:Nat:=c5 (Expr.size (Expr.var "rat.s")); let c7:Nat:=c5 (Expr.size (Expr.var "rat.n")); let c8:Nat:=c5 (Expr.size (Expr.var "rat.d")); let c9:Nat:=c4 c7 c8; @Exists.intro Env (fun (σ':Env) => And (Run B resultToLeft σ σ' ((6:Nat))) ((fun (x τ:Env) => LeftValue q τ) σ σ')) c3 (@And.intro (Run B resultToLeft σ c3 ((6:Nat))) ((fun (x τ:Env) => LeftValue q τ) σ c3) (RunStep.mono B resultToLeft σ c3 (c4 c6 c9) ((6:Nat)) (RunStep.seq B (Com.assign "left.s" (Expr.var "rat.s")) (Com.seq (Com.assign "left.n" (Expr.var "rat.n")) (Com.assign "left.d" (Expr.var "rat.d"))) σ (Env.setVar σ "left.s" (Env.vars σ "rat.s")) c3 c6 c9 (RunStep.assign B σ "left.s" (Expr.var "rat.s") (Env.vars σ "rat.s") (RunStep.eval_var B σ "rat.s" hsB)) (RunStep.seq B (Com.assign "left.n" (Expr.var "rat.n")) (Com.assign "left.d" (Expr.var "rat.d")) (Env.setVar σ "left.s" (Env.vars σ "rat.s")) c1 c3 c7 c8 (RunStep.assign B (Env.setVar σ "left.s" (Env.vars σ "rat.s")) "left.n" (Expr.var "rat.n") c0 (RunStep.eval_var B (Env.setVar σ "left.s" (Env.vars σ "rat.s")) "rat.n" (?nAX_g3972_0_0_0))) (RunStep.assign B c1 "left.d" (Expr.var "rat.d") c2 (RunStep.eval_var B c1 "rat.d" (?nAX_g3972_0_0_1))))) (?nAX_g3972_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g3972_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3972_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3972_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [LeftValue]

theorem resultToRight_spec (B:ℕ) (q:ℚ) (h1:1 < B)
    (hn:q.num.natAbs < B) (hd:q.den < B):
    Spec B (FractionOutput q) resultToRight (fun _ τ => RightValue q τ) 6:=by
  rintro σ ⟨hqval,hqn,hqd,hqs⟩
  have hsB:=hqs.trans_lt h1
  (expose_names;
    (refine let c0:Nat:=Env.vars (Env.setVar σ "right.s" (Env.vars σ "rat.s")) "rat.n"; let c1:Env:=Env.setVar (Env.setVar σ "right.s" (Env.vars σ "rat.s")) "right.n" c0; let c2:Nat:=Env.vars c1 "rat.d"; let c3:Env:=Env.setVar c1 "right.d" c2; let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat→ Nat:=c4 ((1:Nat)); let c6:Nat:=c5 (Expr.size (Expr.var "rat.s")); let c7:Nat:=c5 (Expr.size (Expr.var "rat.n")); let c8:Nat:=c5 (Expr.size (Expr.var "rat.d")); let c9:Nat:=c4 c7 c8; @Exists.intro Env (fun (σ':Env) => And (Run B resultToRight σ σ' ((6:Nat))) ((fun (x τ:Env) => RightValue q τ) σ σ')) c3 (@And.intro (Run B resultToRight σ c3 ((6:Nat))) ((fun (x τ:Env) => RightValue q τ) σ c3) (RunStep.mono B resultToRight σ c3 (c4 c6 c9) ((6:Nat)) (RunStep.seq B (Com.assign "right.s" (Expr.var "rat.s")) (Com.seq (Com.assign "right.n" (Expr.var "rat.n")) (Com.assign "right.d" (Expr.var "rat.d"))) σ (Env.setVar σ "right.s" (Env.vars σ "rat.s")) c3 c6 c9 (RunStep.assign B σ "right.s" (Expr.var "rat.s") (Env.vars σ "rat.s") (RunStep.eval_var B σ "rat.s" hsB)) (RunStep.seq B (Com.assign "right.n" (Expr.var "rat.n")) (Com.assign "right.d" (Expr.var "rat.d")) (Env.setVar σ "right.s" (Env.vars σ "rat.s")) c1 c3 c7 c8 (RunStep.assign B (Env.setVar σ "right.s" (Env.vars σ "rat.s")) "right.n" (Expr.var "rat.n") c0 (RunStep.eval_var B (Env.setVar σ "right.s" (Env.vars σ "rat.s")) "rat.n" (?nAX_g3973_0_0_0))) (RunStep.assign B c1 "right.d" (Expr.var "rat.d") c2 (RunStep.eval_var B c1 "rat.d" (?nAX_g3973_0_0_1))))) (?nAX_g3973_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g3973_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3973_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3973_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [RightValue]

theorem fractionValue_flip (s n d:ℕ) (hs:s≤ 1):
    fractionValue (1 - s) n d=-fractionValue s n d:=by
  interval_cases s <;> simp [fractionValue,neg_div]

theorem negateRight_spec (B:ℕ) (q:ℚ) (h1:1 < B):
    Spec B (RightValue q) negateRight (fun _ τ => RightValue (-q) τ) 4:=by
  rintro σ ⟨hqval,hqn,hqd,hqs⟩
  have hsB:=hqs.trans_lt h1
  have hflip:=fractionValue_flip (σ.vars "right.s") (σ.vars "right.n") (σ.vars "right.d") hqs
  rw [hqval] at hflip
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => RightValue (@Neg.neg Rat Rat.instNeg q) τ) σ; let c1:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) ((1:Nat)) (Env.vars σ "right.s"); let c2:Env:=Env.setVar σ "right.s" c1; let c3:Expr:=Expr.sub (Expr.lit ((1:Nat))) (Expr.var "right.s"); @Exists.intro Env (fun (σ':Env) => And (Run B negateRight σ σ' ((4:Nat))) (c0 σ')) c2 (@And.intro (Run B negateRight σ c2 ((4:Nat))) (c0 c2) (RunStep.mono B negateRight σ c2 (Nat.add ((1:Nat)) (Expr.size c3)) ((4:Nat)) (RunStep.assign B σ "right.s" c3 c1 (RunStep.eval_sub B σ (Expr.lit ((1:Nat))) (Expr.var "right.s") ((1:Nat)) (Env.vars σ "right.s") (RunStep.eval_lit B ((1:Nat)) σ h1) (RunStep.eval_var B σ "right.s" hsB) (?nAX_g3979_0_0_0))) (?nAX_g3979_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g3979_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3979_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [RightValue]

theorem subtract_spec (B M:ℕ) (q r:ℚ) (hB:2 * M ^ 2 + 3 < B)
    (hq:Height q M) (hr:Height r M):
    Spec B (fun σ => LeftValue q σ∧ RightValue r σ) subtractFraction
      (fun _ τ => FractionOutput (q - r) τ) (72 * M.size + 100):=by
  have h1:1 < B:=by nlinarith
  rintro σ ⟨hσq,hσr⟩
  obtain ⟨τ,hr₁,hτr⟩:=negateRight_spec B r h1 σ hσr
  have hτq:LeftValue q τ:=by
    simpa only [LeftValue,hr₁.frame_var "left.s" (by simp [negateRight,Com.wvars]),
      hr₁.frame_var "left.n" (by simp [negateRight,Com.wvars]),
      hr₁.frame_var "left.d" (by simp [negateRight,Com.wvars])] using hσq
  obtain ⟨υ,hr₂,hυ⟩:=add_spec B M q (-r) hB hq (height_neg _ _ hr) τ ⟨hτq,hτr⟩
  exact ⟨υ, (hr₁.seq hr₂).mono (by omega),by simpa only [sub_eq_add_neg] using hυ⟩

end Lax109476Proofs.RamFractionInterface

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

def loopFields:List String:= ["center.i", "vec.n", "grid.D", "vec.i"]

theorem arithmetic_frames (c:Com)
    (hc:c∈ [multiplyFraction,subtractFraction,resultToRight,resultToLeft,RamRounding.roundFraction]):
    (∀ x∈ loopFields,x∉ c.wvars)∧ c.warrs=[]:=by
  simp at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  all_goals constructor
  all_goals try (intro x hx; simp [loopFields] at hx; rcases hx with rfl | rfl | rfl | rfl)
  all_goals simp [multiplyFraction,subtractFraction,negateRight,resultToRight,resultToLeft,
    RamRounding.roundFraction,addFraction,RamArithmetic.normalizeFraction,RamArithmetic.gcdLoop,
    RamArithmetic.gcdDoubleStep,RamArithmetic.gcdStep,Com.wvars,Com.warrs]

theorem framed_arithmetic {B K:ℕ} {P:Env→ Prop} {Q:Env→ Env→ Prop} {c:Com}
    (hc:c∈ [multiplyFraction,subtractFraction,resultToRight,resultToLeft,RamRounding.roundFraction])
    (h:Spec B P c Q K):
    Spec B P c (fun σ τ => Q σ τ∧ FieldsAgree loopFields σ τ∧ τ.arrs=σ.arrs) K:=
  spec_with_fields loopFields h (arithmetic_frames c hc).1 (arithmetic_frames c hc).2

set_option maxHeartbeats 0 in
theorem centerCoordinate_spec (B M D i:ℕ) (us cs gs next:List ℚ)
    (hiu:i < us.length) (hic:i < cs.length) (hig:2 < gs.length) (hin:i < next.length)
    (hiB:i < B) (hM:1≤ M) (hD:D≤ M) (hDpos:0 < D)
    (hu:Height us[i] M) (hc:Height cs[i] M) (hg:Height gs[2] M)
    (hB:2 * (centerCap M) ^ 2 + 3 < B):
    Spec B (fun σ => Represents "ell.u" us σ∧ Represents "ell.center" cs σ∧
        Represents "ell.coeff" gs σ∧ Represents "ell.nextcenter" next σ∧
        σ.vars "center.i"=i∧ σ.vars "grid.D"=D)
      centerCoordinate
      (fun _ τ => Represents "ell.nextcenter"
          (next.set i (RationalRounding.roundDown (cs[i] - us[i] * gs[2]) D)) τ∧
        Represents "ell.u" us τ∧ Represents "ell.center" cs τ∧ Represents "ell.coeff" gs τ)
      (180 * (centerCap M).size + 318):=by
  have hcaps:=centerCap_bounds M hM
  have hSB:centerCap M < B:=by nlinarith
  have h1:1 < B:=by nlinarith
  have h2:2 < B:=by nlinarith
  have hmB:M < B:=hcaps.1.trans_lt hSB
  have hproduct:=height_mul _ _ M M hu hg
  have hdiff:=height_sub _ _ M (M * M) hc hproduct
  have hdiff':Height (cs[i] - us[i] * gs[2]) (2 * M ^ 3):=by
    convert hdiff using 1
    ring
  have hround:=EllipsoidArithmeticBounds.height_roundDown (cs[i] - us[i] * gs[2]) (2 * M ^ 3) D hdiff' hDpos
  have hfinal:Height (RationalRounding.roundDown (cs[i] - us[i] * gs[2]) D) (centerCap M):=by
    have hm:=Nat.mul_le_mul_left (2 * M ^ 3) hD
    apply height_mono _ hround
    exact (by nlinarith:2 * M ^ 3 * D + 1≤ 2 * M ^ 4 + 1) |>.trans hcaps.2.2.2
  have hprodS:Height (us[i] * gs[2]) (centerCap M):=by
    exact height_mono _ hproduct (by simpa only [pow_two] using hcaps.2.1)
  have hdiffS:=height_mono _ hdiff' hcaps.2.2.1
  have huS:=height_mono _ hu hcaps.1
  have hcS:=height_mono _ hc hcaps.1
  have hgS:=height_mono _ hg hcaps.1
  have hloadU:=spec_with_fields loopFields
    ((loadLeft_spec B "ell.u" us i hiu h1 hiB (hu.1.trans_lt hmB) (hu.2.trans_lt hmB)).post
      (fun _ τ _ h => leftValue_of_output _ τ h))
    (by intro x hx; simp [loopFields] at hx; rcases hx with rfl | rfl | rfl | rfl <;> simp [loadLeft,Com.wvars])
    (by simp [loadLeft,Com.warrs])
  have hloadG:=spec_with_fields (loopFields ++ ["left.s", "left.n", "left.d"])
    ((loadRight_spec B "ell.coeff" gs 2 hig h1 h2 (hg.1.trans_lt hmB) (hg.2.trans_lt hmB)).post
      (fun _ τ _ h => rightValue_of_output _ τ h))
    (by
      intro x hx
      simp [loopFields] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [loadRight,Com.wvars])
    (by simp [loadRight,Com.warrs])
  have hmul:=framed_arithmetic (by simp) (multiply_spec B (centerCap M) us[i] gs[2] hB huS hgS)
  have hright:=framed_arithmetic (by simp) (resultToRight_spec B (us[i] * gs[2]) h1
    (hprodS.1.trans_lt hSB) (hprodS.2.trans_lt hSB))
  have hloadC:=spec_with_fields (loopFields ++ ["right.s", "right.n", "right.d"])
    ((loadLeft_spec B "ell.center" cs i hic h1 hiB (hc.1.trans_lt hmB) (hc.2.trans_lt hmB)).post
      (fun _ τ _ h => leftValue_of_output _ τ h))
    (by
      intro x hx
      simp [loopFields] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [loadLeft,Com.wvars])
    (by simp [loadLeft,Com.warrs])
  have hsub:=framed_arithmetic (by simp) (subtract_spec B (centerCap M) cs[i] (us[i] * gs[2]) hB hcS hprodS)
  have hleft:=framed_arithmetic (by simp) (resultToLeft_spec B (cs[i] - us[i] * gs[2]) h1
    (hdiffS.1.trans_lt hSB) (hdiffS.2.trans_lt hSB))
  have hroundSpec:=framed_arithmetic (by simp) (round_spec B (centerCap M) D
    (cs[i] - us[i] * gs[2]) hB hdiffS (hD.trans hcaps.1) hDpos)
  have hstore:=spec_with_write_frame loopFields
    (storeReduced_spec B "ell.nextcenter" next (RationalRounding.roundDown (cs[i] - us[i] * gs[2]) D)
      i hin h1 hiB (hfinal.1.trans_lt hSB) (hfinal.2.trans_lt hSB))
    (by intro x hx; simp [loopFields] at hx; rcases hx with rfl | rfl | rfl | rfl <;> simp [storeReduced,Com.wvars])
  rintro σ ⟨hσu,hσc,hσg,hσnext,hσi,hσD⟩
  (expose_names;
    (refine let c0:Env→ Nat→ Prop:=Run B (loadLeft "ell.u") (Env.setVar σ "vec.i" (Env.vars σ "center.i")); let c1:(xs:List Rat)→ (i_1:Nat)→ Nat.lt i_1 (@List.length Rat xs)→ Rat:= @getElem (List Rat) Nat Rat (fun (as:List Rat) (i_1:Nat) => Nat.lt i_1 (@List.length Rat as)) (@List.instGetElemNatLtLength Rat); let c2:Rat:=c1 us i hiu; let c3:Env→ Prop:=LeftValue c2; let c4:Env→ Prop:=FieldsAgree loopFields (Env.setVar σ "vec.i" (Env.vars σ "center.i")); let c5:String→ List Nat:=Env.arrs (Env.setVar σ "vec.i" (Env.vars σ "center.i")); let c6:Env→ Prop:=fun (σ':Env) => And (c0 σ' ((9:Nat))) (And (c3 σ') (And (c4 σ') (@Eq (String→ List Nat) (Env.arrs σ') c5))); let c7:Nat→ Nat→ Nat:=Nat.add; let c8:Nat→ Nat→ Nat:=Nat.mul; let c9:Nat:=c7 (c8 ((180:Nat)) (Nat.size (centerCap M))) ((318:Nat)); let c10:Rat:=c1 cs i hic; let c11:Rat:=c1 gs ((2:Nat)) hig; let c12:Rat:= @HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul) c2 c11; let c13:Rat:= @HSub.hSub Rat Rat Rat (@instHSub Rat Rat.instSub) c10 c12; let c14:Rat:=RationalRounding.roundDown c13 D; let c15:Env→ Prop:=Represents "ell.nextcenter" (@List.set Rat next i c14); let c16:Env→ Prop:=(fun (x τ:Env) => And (c15 τ) (And (Represents "ell.u" us τ) (And (Represents "ell.center" cs τ) (Represents "ell.coeff" gs τ)))) σ; let c17:Env→ Prop:=fun (σ':Env) => And (Run B centerCoordinate σ σ' c9) (c16 σ'); let c18:Prop:= @Exists Env c17; let c19:Env→ Prop:=RightValue c11; let c20:List String→ List String:= @HAppend.hAppend (List String) (List String) (List String) (@instHAppendOfAppend (List String) (@List.instAppend String)) loopFields; let c21:Env→ Env→ Prop:=FieldsAgree (c20 (@List.cons String "left.s" (@List.cons String "left.n" (@List.cons String "left.d" (@List.nil String))))); let c22:Nat→ Nat:=c7 (c8 ((72:Nat)) (Nat.size (centerCap M))); let c23:Nat:=c22 ((64:Nat)); let c24:Env→ Prop:=FractionOutput c12; let c25:Env→ Prop:=RightValue c12; let c26:Env→ Prop:=LeftValue c10; let c27:Env→ Env→ Prop:=FieldsAgree (c20 (@List.cons String "right.s" (@List.cons String "right.n" (@List.cons String "right.d" (@List.nil String))))); let c28:Nat:=c22 ((100:Nat)); let c29:Env→ Prop:=FractionOutput c13; let c30:Env→ Prop:=LeftValue c13; let c31:Nat:=c7 (c8 ((36:Nat)) (Nat.size (centerCap M))) ((96:Nat)); let c32:Env→ Prop:=FractionOutput c14; let c33:Nat→ Nat:=c7 ((1:Nat)); let c34:Nat:=c33 (Expr.size (Expr.var "center.i")); let c35:Nat→ Nat:=c7 c34; let c36:Nat→ Nat:=c7 ((9:Nat)); let c37:Nat:=c33 (Expr.size (Expr.lit ((2:Nat)))); let c38:Nat→ Nat:=c7 ((6:Nat)); let c39:Nat:=c7 c31 ((13:Nat)); let c40:Nat:=c38 c39; let c41:Nat:=c7 c28 c40; let c42:Nat:=c36 c41; let c43:Nat:=c35 c42; let c44:Nat:=c38 c43; let c45:Nat:=c7 c23 c44; let c46:Nat:=c36 c45; let c47:Nat:=c7 c37 c46; let c48:Nat:=c36 c47; let c49:Com:=Com.assign "vec.i" (Expr.lit ((2:Nat))); let c50:Com:=Com.seq subtractFraction (Com.seq resultToLeft (Com.seq RamRounding.roundFraction (storeReduced "ell.nextcenter"))); let c51:Com:=Com.seq (loadLeft "ell.center") c50; let c52:Com:=Com.seq (Com.assign "vec.i" (Expr.var "center.i")) c51; let c53:Com:=Com.seq resultToRight c52; let c54:Com:=Com.seq multiplyFraction c53; let c55:Com:=Com.seq (loadRight "ell.coeff") c54; let c56:Com:=Com.seq c49 c55; @Exists.casesOn Env c6 (fun (x:@Exists Env c6) => c18) (RunStep.use B (fun (σ_1:Env) => And (Represents "ell.u" us σ_1) (@Eq Nat (Env.vars σ_1 "vec.i") i)) (loadLeft "ell.u") (fun (σ_1 τ:Env) => And (c3 τ) (And (FieldsAgree loopFields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) ((9:Nat)) hloadU (Env.setVar σ "vec.i" (Env.vars σ "center.i")) ?_) fun (w:Env) (h:And (c0 w ((9:Nat))) (And (c3 w) (And (c4 w) (@Eq (String→ List Nat) (Env.arrs w) c5)))) => let c0_1:Prop:=c0 w ((9:Nat)); let c1_1:Prop:=And (c3 w) (And (c4 w) (@Eq (String→ List Nat) (Env.arrs w) c5)); let c2_1:Env:=Env.setVar w "vec.i" ((2:Nat)); let c3_1:Env→ Nat→ Prop:=Run B (loadRight "ell.coeff") c2_1; let c4_1:Env→ Prop:=c21 c2_1; let c5_1:String→ List Nat:=Env.arrs c2_1; let c6_1:Env→ Prop:=fun (σ':Env) => And (c3_1 σ' ((9:Nat))) (And (c19 σ') (And (c4_1 σ') (@Eq (String→ List Nat) (Env.arrs σ') c5_1))); @And.casesOn c0_1 c1_1 (fun (x:And c0_1 c1_1) => c18) h fun (left:c0_1) (right:c1_1) => @Exists.casesOn Env c6_1 (fun (x:@Exists Env c6_1) => c18) (RunStep.use B (fun (σ_1:Env) => And (Represents "ell.coeff" gs σ_1) (@Eq Nat (Env.vars σ_1 "vec.i") ((2:Nat)))) (loadRight "ell.coeff") (fun (σ_1 τ:Env) => And (c19 τ) (And (c21 σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) ((9:Nat)) hloadG c2_1 ?_) fun (w_1:Env) (h_1:And (c3_1 w_1 ((9:Nat))) (And (c19 w_1) (And (c4_1 w_1) (@Eq (String→ List Nat) (Env.arrs w_1) c5_1)))) => let c0_2:Prop:=c3_1 w_1 ((9:Nat)); let c1_2:Prop:=And (c19 w_1) (And (c4_1 w_1) (@Eq (String→ List Nat) (Env.arrs w_1) c5_1)); let c2_2:Env→ Prop:=fun (σ':Env) => And (Run B multiplyFraction w_1 σ' c23) (And (c24 σ') (And (FieldsAgree loopFields w_1 σ') (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs w_1)))); @And.casesOn c0_2 c1_2 (fun (x:And c0_2 c1_2) => c18) h_1 fun (left_1:c0_2) (right_1:c1_2) => @Exists.casesOn Env c2_2 (fun (x:@Exists Env c2_2) => c18) (RunStep.use B (fun (σ_1:Env) => And (c3 σ_1) (c19 σ_1)) multiplyFraction (fun (σ_1 τ:Env) => And (c24 τ) (And (FieldsAgree loopFields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) c23 hmul w_1 ?_) fun (w_2:Env) (h_2:And (Run B multiplyFraction w_1 w_2 c23) (And (c24 w_2) (And (FieldsAgree loopFields w_1 w_2) (@Eq (String→ List Nat) (Env.arrs w_2) (Env.arrs w_1))))) => let c0_3:Prop:=And (c24 w_2) (And (FieldsAgree loopFields w_1 w_2) (@Eq (String→ List Nat) (Env.arrs w_2) (Env.arrs w_1))); let c1_3:Env→ Prop:=fun (σ':Env) => And (Run B resultToRight w_2 σ' ((6:Nat))) (And (c25 σ') (And (FieldsAgree loopFields w_2 σ') (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs w_2)))); @And.casesOn (Run B multiplyFraction w_1 w_2 c23) c0_3 (fun (x:And (Run B multiplyFraction w_1 w_2 c23) c0_3) => c18) h_2 fun (left_2:Run B multiplyFraction w_1 w_2 c23) (right_2:c0_3) => @Exists.casesOn Env c1_3 (fun (x:@Exists Env c1_3) => c18) (RunStep.use B c24 resultToRight (fun (σ_1 τ:Env) => And (c25 τ) (And (FieldsAgree loopFields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) ((6:Nat)) hright w_2 ?_) fun (w_3:Env) (h_3:And (Run B resultToRight w_2 w_3 ((6:Nat))) (And (c25 w_3) (And (FieldsAgree loopFields w_2 w_3) (@Eq (String→ List Nat) (Env.arrs w_3) (Env.arrs w_2))))) => let c0_4:Prop:=Run B resultToRight w_2 w_3 ((6:Nat)); let c1_4:Prop:=And (c25 w_3) (And (FieldsAgree loopFields w_2 w_3) (@Eq (String→ List Nat) (Env.arrs w_3) (Env.arrs w_2))); let c2_3:Env→ Nat→ Prop:=Run B (loadLeft "ell.center") (Env.setVar w_3 "vec.i" (Env.vars w_3 "center.i")); let c3_2:Env→ Prop:=c27 (Env.setVar w_3 "vec.i" (Env.vars w_3 "center.i")); let c4_2:String→ List Nat:=Env.arrs (Env.setVar w_3 "vec.i" (Env.vars w_3 "center.i")); let c5_2:Env→ Prop:=fun (σ':Env) => And (c2_3 σ' ((9:Nat))) (And (c26 σ') (And (c3_2 σ') (@Eq (String→ List Nat) (Env.arrs σ') c4_2))); @And.casesOn c0_4 c1_4 (fun (x:And c0_4 c1_4) => c18) h_3 fun (left_3:c0_4) (right_3:c1_4) => @Exists.casesOn Env c5_2 (fun (x:@Exists Env c5_2) => c18) (RunStep.use B (fun (σ_1:Env) => And (Represents "ell.center" cs σ_1) (@Eq Nat (Env.vars σ_1 "vec.i") i)) (loadLeft "ell.center") (fun (σ_1 τ:Env) => And (c26 τ) (And (c27 σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) ((9:Nat)) hloadC (Env.setVar w_3 "vec.i" (Env.vars w_3 "center.i")) ?_) fun (w_4:Env) (h_4:And (c2_3 w_4 ((9:Nat))) (And (c26 w_4) (And (c3_2 w_4) (@Eq (String→ List Nat) (Env.arrs w_4) c4_2)))) => let c0_5:Prop:=c2_3 w_4 ((9:Nat)); let c1_5:Prop:=And (c26 w_4) (And (c3_2 w_4) (@Eq (String→ List Nat) (Env.arrs w_4) c4_2)); let c2_4:Env→ Prop:=fun (σ':Env) => And (Run B subtractFraction w_4 σ' c28) (And (c29 σ') (And (FieldsAgree loopFields w_4 σ') (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs w_4)))); @And.casesOn c0_5 c1_5 (fun (x:And c0_5 c1_5) => c18) h_4 fun (left_4:c0_5) (right_4:c1_5) => @Exists.casesOn Env c2_4 (fun (x:@Exists Env c2_4) => c18) (RunStep.use B (fun (σ_1:Env) => And (c26 σ_1) (c25 σ_1)) subtractFraction (fun (σ_1 τ:Env) => And (c29 τ) (And (FieldsAgree loopFields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) c28 hsub w_4 ?_) fun (w_5:Env) (h_5:And (Run B subtractFraction w_4 w_5 c28) (And (c29 w_5) (And (FieldsAgree loopFields w_4 w_5) (@Eq (String→ List Nat) (Env.arrs w_5) (Env.arrs w_4))))) => let c0_6:Prop:=And (c29 w_5) (And (FieldsAgree loopFields w_4 w_5) (@Eq (String→ List Nat) (Env.arrs w_5) (Env.arrs w_4))); let c1_6:Env→ Prop:=fun (σ':Env) => And (Run B resultToLeft w_5 σ' ((6:Nat))) (And (c30 σ') (And (FieldsAgree loopFields w_5 σ') (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs w_5)))); @And.casesOn (Run B subtractFraction w_4 w_5 c28) c0_6 (fun (x:And (Run B subtractFraction w_4 w_5 c28) c0_6) => c18) h_5 fun (left_5:Run B subtractFraction w_4 w_5 c28) (right_5:c0_6) => @Exists.casesOn Env c1_6 (fun (x:@Exists Env c1_6) => c18) (RunStep.use B c29 resultToLeft (fun (σ_1 τ:Env) => And (c30 τ) (And (FieldsAgree loopFields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) ((6:Nat)) hleft w_5 ?_) fun (w_6:Env) (h_6:And (Run B resultToLeft w_5 w_6 ((6:Nat))) (And (c30 w_6) (And (FieldsAgree loopFields w_5 w_6) (@Eq (String→ List Nat) (Env.arrs w_6) (Env.arrs w_5))))) => let c0_7:Prop:=Run B resultToLeft w_5 w_6 ((6:Nat)); let c1_7:Prop:=And (c30 w_6) (And (FieldsAgree loopFields w_5 w_6) (@Eq (String→ List Nat) (Env.arrs w_6) (Env.arrs w_5))); let c2_5:Env→ Prop:=fun (σ':Env) => And (Run B RamRounding.roundFraction w_6 σ' c31) (And (c32 σ') (And (FieldsAgree loopFields w_6 σ') (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs w_6)))); @And.casesOn c0_7 c1_7 (fun (x:And c0_7 c1_7) => c18) h_6 fun (left_6:c0_7) (right_6:c1_7) => @Exists.casesOn Env c2_5 (fun (x:@Exists Env c2_5) => c18) (RunStep.use B (fun (σ_1:Env) => And (c30 σ_1) (@Eq Nat (Env.vars σ_1 "grid.D") D)) RamRounding.roundFraction (fun (σ_1 τ:Env) => And (c32 τ) (And (FieldsAgree loopFields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) c31 hroundSpec w_6 ?_) fun (w_7:Env) (h_7:And (Run B RamRounding.roundFraction w_6 w_7 c31) (And (c32 w_7) (And (FieldsAgree loopFields w_6 w_7) (@Eq (String→ List Nat) (Env.arrs w_7) (Env.arrs w_6))))) => let c0_8:Prop:=And (c32 w_7) (And (FieldsAgree loopFields w_6 w_7) (@Eq (String→ List Nat) (Env.arrs w_7) (Env.arrs w_6))); let c1_8:Env→ Prop:=fun (σ':Env) => And (Run B (storeReduced "ell.nextcenter") w_7 σ' ((13:Nat))) (And (c15 σ') (And (FieldsAgree loopFields w_7 σ') (∀ a∉ Com.warrs (storeReduced "ell.nextcenter"), @Eq (List Nat) (Env.arrs σ' a) (Env.arrs w_7 a)))); @And.casesOn (Run B RamRounding.roundFraction w_6 w_7 c31) c0_8 (fun (x:And (Run B RamRounding.roundFraction w_6 w_7 c31) c0_8) => c18) h_7 fun (left_7:Run B RamRounding.roundFraction w_6 w_7 c31) (right_7:c0_8) => @Exists.casesOn Env c1_8 (fun (x:@Exists Env c1_8) => c18) (RunStep.use B (fun (σ_1:Env) => And (Represents "ell.nextcenter" next σ_1) (And (@Eq Nat (Env.vars σ_1 "vec.i") i) (c32 σ_1))) (storeReduced "ell.nextcenter") (fun (σ_1 τ:Env) => And (c15 τ) (And (FieldsAgree loopFields σ_1 τ) (∀ a∉ Com.warrs (storeReduced "ell.nextcenter"), @Eq (List Nat) (Env.arrs τ a) (Env.arrs σ_1 a)))) ((13:Nat)) hstore w_7 ?_) fun (w_8:Env) (h_8:And (Run B (storeReduced "ell.nextcenter") w_7 w_8 ((13:Nat))) (And (c15 w_8) (And (FieldsAgree loopFields w_7 w_8) (∀ a∉ Com.warrs (storeReduced "ell.nextcenter"), @Eq (List Nat) (Env.arrs w_8 a) (Env.arrs w_7 a))))) => let c0_9:Prop:=Run B (storeReduced "ell.nextcenter") w_7 w_8 ((13:Nat)); let c1_9:Prop:=And (c15 w_8) (And (FieldsAgree loopFields w_7 w_8) (∀ a∉ Com.warrs (storeReduced "ell.nextcenter"), @Eq (List Nat) (Env.arrs w_8 a) (Env.arrs w_7 a))); @And.casesOn c0_9 c1_9 (fun (x:And c0_9 c1_9) => c18) h_8 fun (left_8:c0_9) (right_8:c1_9) => @Exists.intro Env c17 w_8 (@And.intro (Run B centerCoordinate σ w_8 c9) (c16 w_8) (RunStep.mono B centerCoordinate σ w_8 (c35 c48) c9 (RunStep.seq B (Com.assign "vec.i" (Expr.var "center.i")) (Com.seq (loadLeft "ell.u") c56) σ (Env.setVar σ "vec.i" (Env.vars σ "center.i")) w_8 c34 c48 (RunStep.assign B σ "vec.i" (Expr.var "center.i") (Env.vars σ "center.i") (RunStep.eval_var B σ "center.i" (?nAX_g4005_0_0_0))) (RunStep.seq B (loadLeft "ell.u") c56 (Env.setVar σ "vec.i" (Env.vars σ "center.i")) w w_8 ((9:Nat)) c47 left (RunStep.seq B c49 c55 w c2_1 w_8 c37 c46 (RunStep.assign B w "vec.i" (Expr.lit ((2:Nat))) ((2:Nat)) (RunStep.eval_lit B ((2:Nat)) w h2)) (RunStep.seq B (loadRight "ell.coeff") c54 c2_1 w_1 w_8 ((9:Nat)) c45 left_1 (RunStep.seq B multiplyFraction c53 w_1 w_2 w_8 c23 c44 left_2 (RunStep.seq B resultToRight c52 w_2 w_3 w_8 ((6:Nat)) c43 left_3 (RunStep.seq B (Com.assign "vec.i" (Expr.var "center.i")) c51 w_3 (Env.setVar w_3 "vec.i" (Env.vars w_3 "center.i")) w_8 c34 c42 (RunStep.assign B w_3 "vec.i" (Expr.var "center.i") (Env.vars w_3 "center.i") (RunStep.eval_var B w_3 "center.i" ?_)) (RunStep.seq B (loadLeft "ell.center") c50 (Env.setVar w_3 "vec.i" (Env.vars w_3 "center.i")) w_4 w_8 ((9:Nat)) c41 left_4 (RunStep.seq B subtractFraction (Com.seq resultToLeft (Com.seq RamRounding.roundFraction (storeReduced "ell.nextcenter"))) w_4 w_5 w_8 c28 c40 left_5 (RunStep.seq B resultToLeft (Com.seq RamRounding.roundFraction (storeReduced "ell.nextcenter")) w_5 w_6 w_8 ((6:Nat)) c39 left_6 (RunStep.seq B RamRounding.roundFraction (storeReduced "ell.nextcenter") w_6 w_7 w_8 c31 ((13:Nat)) left_7 left_8))))))))))) (?nAX_g4005_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4005_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4005_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1); (all_goals try clear h_2); (all_goals try clear left_2); (all_goals try clear h_3); (all_goals try clear left_3); (all_goals try clear h_4); (all_goals try clear left_4); (all_goals try clear h_5); (all_goals try clear left_5); (all_goals try clear h_6); (all_goals try clear left_6); (all_goals try clear h_7); (all_goals try clear left_7); (all_goals try clear h_8); (all_goals try clear left_8))
  all_goals clear hloadU hloadG hmul hright hloadC hsub hleft hroundSpec hstore
  all_goals simp_all [LeftValue,RightValue,FractionOutput,Represents,FieldsAgree,loopFields,storeReduced,Com.warrs]
  all_goals aesop

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

def CenterInvariant {n:ℕ} (u c:Fin n→ ℚ) (gs:List ℚ) (D:ℕ) (hg:2 < gs.length)
    (σ:Env):Prop:=
  Represents "ell.u" (List.ofFn u) σ∧ Represents "ell.center" (List.ofFn c) σ∧
    Represents "ell.coeff" gs σ∧
    Represents "ell.nextcenter" (filled (centerValues u c gs[2] D) (σ.vars "center.i")) σ∧
    σ.vars "center.i" ≤ n∧ σ.vars "vec.n"=n∧ σ.vars "grid.D"=D

theorem centerStep_spec (B n M D:ℕ) (u c:Fin n→ ℚ) (gs:List ℚ)
    (hg:2 < gs.length) (hM:1≤ M) (hu:∀ j,Height (u j) M) (hc:∀ j,Height (c j) M)
    (hgamma:Height gs[2] M) (hD:D≤ M) (hDpos:0 < D)
    (hnB:n < B) (hB:2 * (centerCap M) ^ 2 + 3 < B):
    Spec B (fun σ => CenterInvariant u c gs D hg σ∧ σ.vars "center.i" < n) centerStep
      (fun σ τ => CenterInvariant u c gs D hg τ∧ τ.vars "center.i"=σ.vars "center.i" + 1)
      (180 * (centerCap M).size + 318 + 4):=by
  rintro σ ⟨⟨hσu,hσc,hσg,hσnext,hσin,hσn,hσD⟩,hσi⟩
  let i:Fin n:= ⟨σ.vars "center.i",hσi⟩
  have hui:Height (List.ofFn u)[i.val] M:=by simpa using hu i
  have hci:Height (List.ofFn c)[i.val] M:=by simpa using hc i
  obtain ⟨τ,hr₁,hτnext,hτu,hτc,hτg⟩:=centerCoordinate_spec B M D i.val
    (List.ofFn u) (List.ofFn c) gs (filled (centerValues u c gs[2] D) i.val)
    (by simp) (by simp) hg (by simp [filled]) (hσi.trans hnB) hM hD hDpos hui hci hgamma hB
    σ ⟨hσu,hσc,hσg,hσnext,rfl,hσD⟩
  have hfields:FieldsAgree ["center.i", "vec.n", "grid.D"] σ τ:=by
    intro x hx
    apply hr₁.frame_var
    simp at hx
    rcases hx with rfl | rfl | rfl
    all_goals simp [centerCoordinate,loadLeft,loadRight,storeReduced,multiplyFraction,subtractFraction,
      negateRight,resultToRight,resultToLeft,RamRounding.roundFraction,addFraction,
      RamArithmetic.normalizeFraction,RamArithmetic.gcdLoop,RamArithmetic.gcdDoubleStep,
      RamArithmetic.gcdStep,Com.wvars]
  have hτi:τ.vars "center.i"=i.val:=hfields _ (by simp)
  have hτn:τ.vars "vec.n"=n:=(hfields _ (by simp)).trans hσn
  have hτD:τ.vars "grid.D"=D:=(hfields _ (by simp)).trans hσD
  have h1:1 < B:=by nlinarith
  have hiB:i.val < B:=hσi.trans hnB
  have hi1B:i.val + 1 < B:=lt_of_le_of_lt i.isLt hnB
  have hτiB:τ.vars "center.i" < B:=hτi ▸ hiB
  have hsumB:Bop.add.apply (τ.vars "center.i") 1 < B:=by simpa [Bop.apply,hτi] using hi1B
  have hr₂:Run B (.assign "center.i" (.add (.var "center.i") (.lit 1))) τ
      (τ.setVar "center.i" (i.val + 1)) 4:=by
    exact Run.assign (by simpa [Bop.apply,hτi] using
      (evalB_bin (evalB_var hτiB) (evalB_lit h1) hsumB))
  have hnext:Represents "ell.nextcenter" (filled (centerValues u c gs[2] D) (i.val + 1)) τ:=by
    rw [← filled_step]
    simpa only [centerValues,List.getElem_ofFn,Fin.eta] using hτnext
  refine ⟨_,hr₁.seq hr₂, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [Represents,arrs_setVar] using hτu
  · simpa only [Represents,arrs_setVar] using hτc
  · simpa only [Represents,arrs_setVar] using hτg
  · simpa only [Represents,arrs_setVar,vars_setVar,ite_true] using hnext
  · change i.val + 1≤ n
    exact i.isLt
  · simpa using hτn
  · simpa using hτD
  · simp [i]

theorem centerLoop_spec (B n M D:ℕ) (u c:Fin n→ ℚ) (gs:List ℚ)
    (hg:2 < gs.length) (hM:1≤ M) (hu:∀ j,Height (u j) M) (hc:∀ j,Height (c j) M)
    (hgamma:Height gs[2] M) (hD:D≤ M) (hDpos:0 < D)
    (hnB:n < B) (hB:2 * (centerCap M) ^ 2 + 3 < B):
    Spec B (fun σ => Represents "ell.u" (List.ofFn u) σ∧ Represents "ell.center" (List.ofFn c) σ∧
        Represents "ell.coeff" gs σ∧ Represents "ell.nextcenter" (List.replicate n 0) σ∧
        σ.vars "vec.n"=n∧ σ.vars "grid.D"=D)
      centerLoop
      (fun _ τ => Represents "ell.nextcenter" (List.ofFn (centerValues u c gs[2] D)) τ∧
        Represents "ell.u" (List.ofFn u) τ∧ Represents "ell.center" (List.ofFn c) τ∧
        Represents "ell.coeff" gs τ∧ τ.vars "vec.n"=n∧ τ.vars "grid.D"=D)
      ((180 * (centerCap M).size + 318 + 4 + 4) * n + 6):=by
  have hlo:=Spec.forRangeZero "center.i" "vec.n" (CenterInvariant u c gs D hg) n
    (180 * (centerCap M).size + 318 + 4) hnB
    (fun _ h => h.2.2.2.2.1) (fun _ h => h.2.2.2.2.2.1)
    (centerStep_spec B n M D u c gs hg hM hu hc hgamma hD hDpos hnB hB)
  refine (hlo.pre ?_).post ?_
  · rintro σ ⟨hσu,hσc,hσg,hσnext,hσn,hσD⟩
    simp_all [CenterInvariant,Represents,filled_zero]
  · rintro σ τ _ ⟨hτ,hcounter⟩
    refine ⟨?_,hτ.1,hτ.2.1,hτ.2.2.1,hτ.2.2.2.2.2.1,hτ.2.2.2.2.2.2⟩
    simpa only [hcounter,filled_done] using hτ.2.2.2.1

theorem updateCenter_spec (B n M D:ℕ) (u c:Fin n→ ℚ) (gs:List ℚ)
    (hg:2 < gs.length) (hM:1≤ M) (hu:∀ j,Height (u j) M) (hc:∀ j,Height (c j) M)
    (hgamma:Height gs[2] M) (hD:D≤ M) (hDpos:0 < D)
    (hnB:n < B) (hB:2 * (centerCap M) ^ 2 + 3 < B):
    Spec B (fun σ => Represents "ell.u" (List.ofFn u) σ∧ Represents "ell.center" (List.ofFn c) σ∧
        Represents "ell.coeff" gs σ∧ (σ.arrs "ell.nextcenter.s").length=n∧
        (σ.arrs "ell.nextcenter.n").length=n∧ (σ.arrs "ell.nextcenter.d").length=n∧
        σ.vars "vec.n"=n∧ σ.vars "grid.D"=D)
      updateCenter
      (fun _ τ => Represents "ell.nextcenter" (List.ofFn (centerValues u c gs[2] D)) τ∧
        Represents "ell.u" (List.ofFn u) τ∧ Represents "ell.center" (List.ofFn c) τ∧
        Represents "ell.coeff" gs τ∧ τ.vars "vec.n"=n∧ τ.vars "grid.D"=D)
      (33 * n + 18 + ((180 * (centerCap M).size + 318 + 4 + 4) * n + 6)):=by
  have h1:1 < B:=by nlinarith
  rintro σ ⟨hσu,hσc,hσg,hσs,hσN,hσd,hσn,hσD⟩
  obtain ⟨τ,hr₁,hτnext,hτn,hτa⟩:=zeroRationalArray_spec B n "ell.nextcenter" hnB h1
    σ ⟨hσs,hσN,hσd,hσn⟩
  have hτu:Represents "ell.u" (List.ofFn u) τ:=by
    simpa only [Represents,hτa ("ell.u" ++ ".s") (by decide),hτa ("ell.u" ++ ".n") (by decide),
      hτa ("ell.u" ++ ".d") (by decide)] using hσu
  have hτc:Represents "ell.center" (List.ofFn c) τ:=by
    simpa only [Represents,hτa ("ell.center" ++ ".s") (by decide),hτa ("ell.center" ++ ".n") (by decide),
      hτa ("ell.center" ++ ".d") (by decide)] using hσc
  have hτg:Represents "ell.coeff" gs τ:=by
    simpa only [Represents,hτa ("ell.coeff" ++ ".s") (by decide),hτa ("ell.coeff" ++ ".n") (by decide),
      hτa ("ell.coeff" ++ ".d") (by decide)] using hσg
  have hτD:τ.vars "grid.D"=D:=
    (hr₁.frame_var "grid.D" (by simp [zeroRationalArray,fillConstant,Lib.Fill.put,Com.wvars])).trans hσD
  obtain ⟨υ,hr₂,hυ⟩:=centerLoop_spec B n M D u c gs hg hM hu hc hgamma hD hDpos hnB hB
    τ ⟨hτu,hτc,hτg,hτnext,hτn,hτD⟩
  exact ⟨υ,hr₁.seq hr₂,hυ⟩

theorem centerValues_eq_roundedCenter {n:ℕ} (A:Matrix (Fin n) (Fin n) ℚ)
    (a c:Fin n→ ℚ) (D:ℕ):
    centerValues (A *ᵥ a) c (1 / (((n:ℚ) + 1) * RationalRounding.sqrtUpper (a ⬝ᵥ (A *ᵥ a)) D)) D =
      EllipsoidCenter.roundedCenter n A a c D:=by
  funext i
  simp only [centerValues,EllipsoidCenter.roundedCenter,EllipsoidCenter.approximateCenter,
    Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  rw [mul_comm]

theorem updateCenter_ellipsoid_spec (B n M D:ℕ) (A:Matrix (Fin n) (Fin n) ℚ)
    (a c:Fin n→ ℚ) (gs:List ℚ) (hg:2 < gs.length) (hM:1≤ M)
    (hu:∀ j,Height ((A *ᵥ a) j) M) (hc:∀ j,Height (c j) M)
    (hgamma:Height gs[2] M)
    (hgeq:gs[2]=1 / (((n:ℚ) + 1) * RationalRounding.sqrtUpper (a ⬝ᵥ (A *ᵥ a)) D))
    (hD:D≤ M) (hDpos:0 < D) (hnB:n < B) (hB:2 * (centerCap M) ^ 2 + 3 < B):
    Spec B (fun σ => Represents "ell.u" (List.ofFn (A *ᵥ a)) σ∧ Represents "ell.center" (List.ofFn c) σ∧
        Represents "ell.coeff" gs σ∧ (σ.arrs "ell.nextcenter.s").length=n∧
        (σ.arrs "ell.nextcenter.n").length=n∧ (σ.arrs "ell.nextcenter.d").length=n∧
        σ.vars "vec.n"=n∧ σ.vars "grid.D"=D)
      updateCenter
      (fun _ τ => Represents "ell.nextcenter" (List.ofFn (EllipsoidCenter.roundedCenter n A a c D)) τ∧
        Represents "ell.u" (List.ofFn (A *ᵥ a)) τ∧ Represents "ell.center" (List.ofFn c) τ∧
        Represents "ell.coeff" gs τ∧ τ.vars "vec.n"=n∧ τ.vars "grid.D"=D)
      (33 * n + 18 + ((180 * (centerCap M).size + 318 + 4 + 4) * n + 6)):=by
  apply (updateCenter_spec B n M D (A *ᵥ a) c gs hg hM hu hc hgamma hD hDpos hnB hB).post
  rintro σ τ _ ⟨hnext,hu',hc',hg',hn',hD'⟩
  refine ⟨?_,hu',hc',hg',hn',hD'⟩
  rw [hgeq,centerValues_eq_roundedCenter] at hnext
  exact hnext

end Lax109476Proofs.RamCenterUpdate

end

theorem solution:∀ (B n M D:ℕ) (A:Matrix (Fin n) (Fin n) ℚ) (a c:Fin n→ ℚ) (gs:List ℚ) (hg:2 < gs.length),
  1≤ M→
    (∀ (j:Fin n),Lax109476Proofs.RationalArithmeticBounds.Height (A.mulVec a j) M)→
      (∀ (j:Fin n),Lax109476Proofs.RationalArithmeticBounds.Height (c j) M)→
        Lax109476Proofs.RationalArithmeticBounds.Height gs[2] M→
          gs[2]=1 / ((↑n + 1) * Lax109476Proofs.RationalRounding.sqrtUpper (a ⬝ᵥ A.mulVec a) D)→
            D≤ M→
              0 < D→
                n < B→
                  2 * Lax109476Proofs.RamCenterCoordinate.centerCap M ^ 2 + 3 < B→
                    Lax808846Proofs.Reasoning.Spec B
                      (fun (σ:Lax808846Proofs.Imp.Env) =>
                        Lax109476Proofs.RamRationalArrays.Represents "ell.u" (List.ofFn (A.mulVec a)) σ∧
                          Lax109476Proofs.RamRationalArrays.Represents "ell.center" (List.ofFn c) σ∧
                            Lax109476Proofs.RamRationalArrays.Represents "ell.coeff" gs σ∧
                              (σ.arrs "ell.nextcenter.s").length=n∧
                                (σ.arrs "ell.nextcenter.n").length=n∧
                                  (σ.arrs "ell.nextcenter.d").length=n∧ σ.vars "vec.n"=n∧ σ.vars "grid.D"=D)
                      Lax109476Proofs.RamCenterUpdate.updateCenter
                      (fun (x τ:Lax808846Proofs.Imp.Env) =>
                        Lax109476Proofs.RamRationalArrays.Represents "ell.nextcenter"
                            (List.ofFn (Lax109476Proofs.EllipsoidCenter.roundedCenter n A a c D)) τ∧
                          Lax109476Proofs.RamRationalArrays.Represents "ell.u" (List.ofFn (A.mulVec a)) τ∧
                            Lax109476Proofs.RamRationalArrays.Represents "ell.center" (List.ofFn c) τ∧
                              Lax109476Proofs.RamRationalArrays.Represents "ell.coeff" gs τ∧
                                τ.vars "vec.n"=n∧ τ.vars "grid.D"=D)
                      (33 * n + 18 +
                        ((180 * (Lax109476Proofs.RamCenterCoordinate.centerCap M).size + 318 + 4 + 4) * n + 6)):= @Lax109476Proofs.RamCenterUpdate.updateCenter_ellipsoid_spec
