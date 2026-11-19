-- Prove2me | solution 1 for Lax263307Proofs.NativeWeightedOutput.command_spec_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T15:02:01.491868+00:00
-- url     : https://prove2.me/submissions/b2f1bec4-aa01-43c9-be8f-283c819cc781

import Mathlib.Tactic
import Mathlib.Data.NNRat.Lemmas
import Mathlib.Data.Nat.Log
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Combinatorics.Colex
import Mathlib.Data.List.Sort
import Definitions.Def_EdgeSublinearMWIS_Main_NativePhaseInterfaces

namespace Lax109476.RationalFeasibility
end Lax109476.RationalFeasibility
namespace Lax109476Proofs.BinaryOptimization
end Lax109476Proofs.BinaryOptimization
namespace Lax109476Proofs.BinaryOptimizationBounds
end Lax109476Proofs.BinaryOptimizationBounds
namespace Lax109476Proofs.CertificateSystems
end Lax109476Proofs.CertificateSystems
namespace Lax109476Proofs.CoordinateOptimization
end Lax109476Proofs.CoordinateOptimization
namespace Lax109476Proofs.DeterminantBounds
end Lax109476Proofs.DeterminantBounds
namespace Lax109476Proofs.EllipsoidDeterminant
end Lax109476Proofs.EllipsoidDeterminant
namespace Lax109476Proofs.EllipsoidTermination
end Lax109476Proofs.EllipsoidTermination
namespace Lax109476Proofs.IterationBudget
end Lax109476Proofs.IterationBudget
namespace Lax109476Proofs.LexicographicBounds
end Lax109476Proofs.LexicographicBounds
namespace Lax109476Proofs.PointRecovery
end Lax109476Proofs.PointRecovery
namespace Lax109476Proofs.RamEllipsoidStoredBounds
end Lax109476Proofs.RamEllipsoidStoredBounds
namespace Lax109476Proofs.RamEllipsoidWordBounds
end Lax109476Proofs.RamEllipsoidWordBounds
namespace Lax109476Proofs.RamFrame
end Lax109476Proofs.RamFrame
namespace Lax109476Proofs.RamPadEntries
end Lax109476Proofs.RamPadEntries
namespace Lax109476Proofs.RamPrimitiveBounds
end Lax109476Proofs.RamPrimitiveBounds
namespace Lax109476Proofs.RamRecoveryData
end Lax109476Proofs.RamRecoveryData
namespace Lax109476Proofs.RamScalarFrame
end Lax109476Proofs.RamScalarFrame
namespace Lax109476Proofs.RationalFeasibility
end Lax109476Proofs.RationalFeasibility
namespace Lax109476Proofs.RationalMinima
end Lax109476Proofs.RationalMinima
namespace Lax109476Proofs.SmallFeasiblePoint
end Lax109476Proofs.SmallFeasiblePoint
namespace Lax263307.ConditioningDistribution
end Lax263307.ConditioningDistribution
namespace Lax263307.PowerBagBounds
end Lax263307.PowerBagBounds
namespace Lax263307Proofs.ConditioningDistribution
end Lax263307Proofs.ConditioningDistribution
namespace Lax263307Proofs.EntropyDecrease
end Lax263307Proofs.EntropyDecrease
namespace Lax263307Proofs.NativeDistanceEntries
end Lax263307Proofs.NativeDistanceEntries
namespace Lax263307Proofs.NativeMachineSegment
end Lax263307Proofs.NativeMachineSegment
namespace Lax263307Proofs.NativeUniformWordGuards
end Lax263307Proofs.NativeUniformWordGuards
namespace Lax455465.ShortPathFlow
end Lax455465.ShortPathFlow
namespace Lax455465Proofs.AcyclicFlowPath
end Lax455465Proofs.AcyclicFlowPath
namespace Lax455465Proofs.LargePotentialData
end Lax455465Proofs.LargePotentialData
namespace Lax455465Proofs.PathSubtraction
end Lax455465Proofs.PathSubtraction
namespace Lax455465Proofs.RamFlowData
end Lax455465Proofs.RamFlowData
namespace Lax455465Proofs.RationalParser
end Lax455465Proofs.RationalParser
namespace Lax455465Proofs.RegionHistory
end Lax455465Proofs.RegionHistory
namespace Lax455465Proofs.RegionInterval
end Lax455465Proofs.RegionInterval
namespace Lax455465Proofs.RegionRuntimeState
end Lax455465Proofs.RegionRuntimeState
namespace Lax455465Proofs.RoundingConstants
end Lax455465Proofs.RoundingConstants
namespace Lax759944.TuringPolytime
end Lax759944.TuringPolytime
namespace Lax759944Proofs.Legacy.RamPolytime
end Lax759944Proofs.Legacy.RamPolytime
namespace Lax808846.RamComputes
end Lax808846.RamComputes
namespace Lax808846Proofs.Machine
end Lax808846Proofs.Machine

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

open scoped NNReal NNRat

namespace Lax455465.RationalEncoding

open Lax455465.ProductNetwork Lax455465.ConcurrentFlow

structure FlowCertificate (n:ℕ) where

  value:ℚ≥0

  paths:List (List (Fin n) × ℚ≥0)

end Lax455465.RationalEncoding

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

theorem mono (B:ℕ) (c:Com) (σ σ':Env) (K K':ℕ)
    (h:Run B c σ σ' K) (hK:K≤ K'):Run B c σ σ' K':=h.mono hK

theorem use (B:ℕ) (P:Env→ Prop) (c:Com) (Q:Env→ Env→ Prop) (K:ℕ)
    (h:Spec B P c Q K) (σ:Env) (hσ:P σ):∃ σ',Run B c σ σ' K∧ Q σ σ':=h σ hσ

end RunStep

end Lax808846Proofs.Reasoning
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

open Lax808846.Ram Lax808846Proofs.Machine

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

namespace Lax263307.HeavyConditioning

open LinearRelaxation ConditioningDistribution Entropy

noncomputable def probabilityFloor (n p:ℕ):ℝ:=
  1 / (2 * (n:ℝ) * p * ((Nat.log2 n:ℝ) + 1))

end Lax263307.HeavyConditioning

end

section

namespace Lax455465Proofs.RamFrames

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem array_length {c:Com} {σ τ:Env} {k:ℕ} (h:BigStep c σ τ k) (a:String):
    (τ.arrs a).length=(σ.arrs a).length:=by
  induction h with
  | skip => rfl
  | assign _ => rfl
  | store _ _ _ => simp only [length_arrs_setArr]
  | seq _ _ ih ih' => rw [ih',ih]
  | ite_true _ _ ih => exact ih
  | ite_false _ _ ih => exact ih
  | while_true _ _ _ ih ih' => rw [ih',ih]
  | while_false _ => rfl
  | read _ => rfl
  | write _ => rfl

theorem run_array_length {B K:ℕ} {c:Com} {σ τ:Env} (h:Run B c σ τ K) (a:String):
    (τ.arrs a).length=(σ.arrs a).length:=by
  obtain ⟨_,_,hs⟩:=h.bigStep
  exact array_length hs a

end Lax455465Proofs.RamFrames

end

section

namespace Lax455465Proofs.RamWordBuffer

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState

private theorem prefix_set (words buffer:List ℕ) (value:ℕ)
    (h:∀ i (hi:i < words.length),buffer[i]?=some words[i])
    (hroom:words.length < buffer.length):
    ∀ i (hi:i < (words ++ [value]).length),
      (buffer.set words.length value)[i]?=some (words ++ [value])[i]:=by
  intro i hi
  by_cases hlt:i < words.length
  · rw [← List.getElem_append_left' hlt,List.getElem?_set_ne (by omega:words.length ≠ i)]
    exact h i hlt
  · have he:i=words.length:=by simp only [List.length_append,List.length_singleton] at hi; omega
    subst i
    simp [List.getElem?_set_self hroom]

theorem append_spec (B:ℕ) (array cursor:String) (words:List ℕ) (value:ℕ) (e:Expr)
    (h1:1 < B) (hlen:words.length + 1 < B):
    Spec B (fun σ => Prefix words array σ∧ σ.vars cursor=words.length∧
      words.length < (σ.arrs array).length∧ e.evalB B σ=some value) (append array cursor e)
      (fun _ τ => Prefix (words ++ [value]) array τ∧ τ.vars cursor=words.length + 1)
      (e.size + 6):=by
  rintro σ ⟨hprefix,hcursor,hroom,he⟩
  have hindex:(Expr.var cursor).evalB B σ=some words.length:=by
    rw [evalB_var_iff]
    exact ⟨hcursor.symm,hcursor ▸ (by omega:words.length < B)⟩
  have hstore:=Run.store hindex he hroom
  let ν:=σ.setArr array words.length value
  have hcounter:(Expr.add (.var cursor) (.lit 1)).evalB B ν=some (words.length + 1):=by
    apply evalB_bin (op:=.add) _ (evalB_lit h1) hlen
    rw [evalB_var_iff]
    exact ⟨by simpa [ν] using hcursor.symm,by simp [ν,hcursor]; omega⟩
  have hnext:=Run.assign (x:=cursor) hcounter
  refine ⟨ν.setVar cursor (words.length + 1), (hstore.seq hnext).mono (by simp [Expr.size]; omega), ?_⟩
  constructor
  · simpa only [Prefix,ν,arrs_setVar,arrs_setArr,if_true] using
      prefix_set words (σ.arrs array) value hprefix hroom
  · simp

end Lax455465Proofs.RamWordBuffer

end

section

namespace Lax455465Proofs.RamEmitWords
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState

def Data (array:String) (stride:ℕ) (xs:List ℕ) (σ:Env):Prop:=
  ∀ i,∀ hi:i < xs.length,(σ.arrs array)[stride*i]?=some xs[i]

def Invariant (array:String) (stride:ℕ) (xs front:List ℕ) (σ:Env):Prop:=
  Data array stride xs σ∧ σ.vars "emit.count"=xs.length∧ σ.vars "emit.i"≤ xs.length∧
    σ.out=front++xs.take (σ.vars "emit.i")

theorem command_spec (B:ℕ) (array:String) (stride:ℕ) (xs front:List ℕ)
    (h1:1 < B) (hstride:stride < B) (hoffset:stride*xs.length < B) (hlen:xs.length < B) (hwords:∀ x∈xs,x < B):
    Spec B (fun σ => Data array stride xs σ∧ σ.vars "emit.count"=xs.length∧ σ.out=front)
      (command array stride) (fun _ τ => τ.out=front++xs) (13*xs.length+6):=by
  have hstep:Spec B (fun σ => Invariant array stride xs front σ∧ σ.vars "emit.i" < xs.length)
      (step array stride) (fun σ τ => Invariant array stride xs front τ∧ τ.vars "emit.i"=σ.vars "emit.i"+1) 9:=by
    rintro σ ⟨⟨hp,hcount,hle,hout⟩,hlt⟩
    let i:=σ.vars "emit.i"
    have hi:i < xs.length:=hlt
    have hval:xs[i] < B:=hwords _ (List.getElem_mem hi)
    have he:(Expr.get array (.mul (.lit stride) (.var "emit.i"))).evalB B σ=some xs[i]:=
      evalB_get (evalB_bin (op:=.mul) (evalB_lit hstride) (evalB_var (hi.trans hlen))
        ((Nat.mul_le_mul_left stride hi.le).trans_lt hoffset)) (hp i hi) hval
    let ν:Env:= {σ with out:=σ.out++[xs[i]]}
    have r1:Run B (.write (.get array (.mul (.lit stride) (.var "emit.i")))) σ ν 5:=Run.write he
    have r2:Run B (.assign "emit.i" (.add (.var "emit.i") (.lit 1))) ν (ν.setVar "emit.i" (i+1)) 4:=
      Run.assign (evalB_bin (op:=.add) (evalB_var (hi.trans hlen)) (evalB_lit h1) (by dsimp [Bop.apply]; omega))
    refine ⟨_,r1.seq r2,⟨hp,by simpa [ν] using hcount,by simp; omega,?_⟩,by simp [i,ν]⟩
    change σ.out++[xs[i]]=front++xs.take (i+1)
    rw [List.take_succ_eq_append_getElem hi,←List.append_assoc]
    exact congrArg (fun a => a++[xs[i]]) hout
  have hloop:=Spec.forRangeZero "emit.i" "emit.count" (Invariant array stride xs front) xs.length 9 hlen
    (fun _ h => h.2.2.1) (fun _ h => h.2.1) hstep
  rintro σ ⟨hp,hcount,hout⟩
  obtain ⟨τ,rr,pr⟩:=hloop σ ⟨hp,by simpa using hcount,by simp,by simpa using hout⟩
  exact ⟨τ,by simpa [command] using rr,by simpa only [pr.2,List.take_length] using pr.1.2.2.2⟩

end Lax455465Proofs.RamEmitWords

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeBlowUp

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax263307.WeightedAlgorithm

theorem blocks_length {n:ℕ} (copies:Fin n→ ℕ):(blocks copies).length=n:=by
  simp [blocks]

theorem owners_length {n:ℕ} (copies:Fin n→ ℕ):(owners copies).length=∑ v,copies v:=by
  simp [owners,blocks,List.length_flatten,List.map_ofFn,List.sum_ofFn]

theorem flattened_coordinate {α:Type*} (xs:List (List α)) (i:ℕ) (hi:i< xs.length)
    (j:ℕ) (hj:j< xs[i].length):
    xs.flatten[((xs.take i).map List.length).sum+j]?=some xs[i][j]:=by
  have he:xs=xs.take i++xs[i]::xs.drop (i+1):=by
    rw [← List.drop_eq_getElem_cons hi,List.take_append_drop]
  have hf:xs.flatten=(xs.take i).flatten++xs[i]++(xs.drop (i+1)).flatten:=by
    conv_lhs => rw [he]
    simp only [List.flatten_append,List.flatten_cons,List.append_assoc]
  rw [hf,List.append_assoc]
  rw [List.getElem?_append_right (by rw [List.length_flatten]; omega)]
  rw [List.length_flatten]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left hj,List.getElem?_eq_getElem hj]

theorem owners_coordinate {n:ℕ} (copies:Fin n→ ℕ)
    (v:Fin n) (j:Fin (copies v)):
    (owners copies)[(finSigmaFinEquiv ⟨v,j⟩).val]?=some v.val:=by
  have hi:v.val<(blocks copies).length:=by rw [blocks_length]; exact v.isLt
  have hb:(blocks copies)[v.val]=List.replicate (copies v) v.val:=by
    simp [blocks]
  have hp:((blocks copies).take v.val).map List.length =
      List.ofFn (fun i:Fin v.val => copies (Fin.castLE v.isLt.le i)):=by
    rw [List.map_take]
    have hm:(blocks copies).map List.length=List.ofFn copies:=by
      rw [blocks,List.map_ofFn]
      congr 1
      funext v
      exact List.length_replicate
    rw [hm]
    exact (Fin.ofFn_take_eq_take_ofFn v.isLt.le copies).symm
  have hx:=flattened_coordinate (blocks copies) v.val hi j.val (by simpa only [hb,List.length_replicate] using j.isLt)
  simpa only [owners,finSigmaFinEquiv_apply,hp,List.sum_ofFn,hb,List.getElem_replicate] using hx

theorem owners_labeling {n:ℕ} (copies:Fin n→ ℕ) (i:Fin (∑ v,copies v)):
    (owners copies)[i.val]?=some (labeling copies i).1.val:=by
  have hx:=owners_coordinate copies (labeling copies i).1 (labeling copies i).2
  simpa only [labeling,Sigma.eta,Equiv.apply_symm_apply] using hx

open Lax263307.WeightRounding Lax263307.WeightedIndependentSet NativeFrontend

open Lax109476Proofs

end Lax263307Proofs.NativeBlowUp

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeMasks

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax263307.WeightedIndependentSet

theorem mask_test_bit {n:ℕ} (I:Finset (Fin n)) (j:ℕ):
    (mask I).testBit j=decide (j∈I.image Fin.val):=by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff,←Nat.mem_bitIndices,←List.mem_toFinset]
  change j∈Finset.equivBitIndices (mask I)↔ j∈I.image Fin.val
  rw [mask,Lax263307.NativeCatalog.subsetMask,Equiv.apply_symm_apply]

theorem mask_member {n:ℕ} (I:Finset (Fin n)) (v:Fin n):
    (mask I).testBit v.val=decide (v∈I):=by
  rw [mask_test_bit]
  congr 1
  simp [Finset.mem_image,Fin.val_inj]

theorem mask_empty (n:ℕ):mask (∅:Finset (Fin n))=0:=by
  simp [mask,Lax263307.NativeCatalog.subsetMask,Finset.equivBitIndices]

theorem mask_bound {n:ℕ} (I:Finset (Fin n)):mask I<2^n:=by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  rw [mask_test_bit]
  apply decide_eq_false_iff_not.mpr
  intro hjm
  obtain ⟨v,hv,hvj⟩:=Finset.mem_image.mp hjm
  have hvn:=v.isLt
  omega

theorem mask_insert {n:ℕ} (I:Finset (Fin n)) (v:Fin n):
    mask (insert v I)=Nat.lor (mask I) (2^v.val):=by
  apply Nat.eq_of_testBit_eq
  intro j
  change (mask (insert v I)).testBit j=((mask I) ||| (2^v.val)).testBit j
  rw [Nat.testBit_or,mask_test_bit,mask_test_bit,Nat.testBit_two_pow]
  simp only [Finset.image_insert,Finset.mem_insert]
  by_cases he:j=v.val <;> by_cases hm:j∈I.image Fin.val <;> simp [he,hm,eq_comm]

def initialSet {n:ℕ} (I:Finset (Fin n)) (i:ℕ):Finset (Fin n):=
  I.filter fun v => v.val < i

theorem prefix_zero {n:ℕ} (I:Finset (Fin n)):initialSet I 0=∅:=by simp [initialSet]

theorem prefix_full {n:ℕ} (I:Finset (Fin n)):initialSet I n=I:=by simp [initialSet]

theorem prefix_succ {n:ℕ} (I:Finset (Fin n)) (i:ℕ) (hi:i< n):
    initialSet I (i+1)=if (⟨i,hi⟩:Fin n)∈I then insert ⟨i,hi⟩ (initialSet I i) else initialSet I i:=by
  ext v
  by_cases hv:v.val=i
  · have he:v=⟨i,hi⟩:=Fin.ext hv
    subst v
    by_cases hm:(⟨i,hi⟩:Fin n)∈I <;> simp [initialSet,hm]
  · have he:v≠⟨i,hi⟩:=fun h => hv (congrArg Fin.val h)
    by_cases hm:(⟨i,hi⟩:Fin n)∈I <;> simp [hm,initialSet,he] <;> omega

theorem prefix_step {n:ℕ} (I:Finset (Fin n)) (i:ℕ) (hi:i< n):
    Nat.lor (mask (initialSet I i)) ((if (⟨i,hi⟩:Fin n)∈I then 1 else 0)*2^i)=mask (initialSet I (i+1)):=by
  rw [prefix_succ I i hi]
  by_cases h:(⟨i,hi⟩:Fin n)∈I
  · simp only [if_pos h,one_mul,mask_insert]
  · simp [h]

def Invariant {n:ℕ} (I:Finset (Fin n)) (σ:Env):Prop:=
  σ.vars "graph.n"=n∧ σ.vars "mask.i"≤ n∧
  Prefix (encodeOutput I) "subset.bits" σ∧ σ.vars "mask.value"=mask (initialSet I (σ.vars "mask.i"))

theorem step_spec {n:ℕ} (B:ℕ) (I:Finset (Fin n)) (hB:n+2< B) (hm:2^n< B):
    Spec B (fun σ => Invariant I σ∧ σ.vars "mask.i"< n) step
      (fun σ τ => Invariant I τ∧ τ.vars "mask.i"=σ.vars "mask.i"+1) 11:=by
  rintro σ ⟨⟨hn,hle,hbits,hmask⟩,hlt⟩
  let i:=σ.vars "mask.i"
  let bit:=if (⟨i,hlt⟩:Fin n)∈I then 1 else 0
  have hbit:bit≤1:=by dsimp [bit]; split_ifs <;> omega
  have hbitB:bit< B:=by omega
  have hiB:i< B:=by omega
  have hpow:2^i<2^n:=Nat.pow_lt_pow_right (by omega) hlt
  have hshift:bit*2^i< B:=(by simpa only [one_mul] using Nat.mul_le_mul_right (2^i) hbit:bit*2^i≤2^i).trans_lt (hpow.trans hm)
  have hget:(σ.arrs "subset.bits")[i]?=some bit:=by
    have hh:=hbits i (by simpa [encodeOutput] using hlt)
    simpa [encodeOutput,bit] using hh
  have hprev:mask (initialSet I i)< B:=(mask_bound _).trans hm
  have hnext:mask (initialSet I (i+1))< B:=(mask_bound _).trans hm
  have hval:(Expr.or (.var "mask.value") (.shiftl (.get "subset.bits" (.var "mask.i")) (.var "mask.i"))).evalB B σ=
      some (mask (initialSet I (i+1))):=by
    have hh:=evalB_bin (op:=.or)
      (by rw [evalB_var_iff]; exact ⟨hmask.symm,hmask ▸ hprev⟩)
      (evalB_bin (op:=.shiftl) (evalB_get (evalB_var hiB) hget hbitB) (evalB_var hiB) hshift)
      (by change Nat.lor (mask (initialSet I i)) (bit*2^i)< B; rw [prefix_step]; exact hnext)
    simpa only [Bop.apply_or,Bop.apply_shiftl,←show σ.vars "mask.i"=i from rfl,bit,prefix_step] using hh
  let ν:=σ.setVar "mask.value" (mask (initialSet I (i+1)))
  have r1:Run B (.assign "mask.value"
      (.or (.var "mask.value") (.shiftl (.get "subset.bits" (.var "mask.i")) (.var "mask.i")))) σ ν 7:=
    Run.assign hval
  have hiν:ν.vars "mask.i"=i:=by simp [ν,i]
  let τ:=ν.setVar "mask.i" (i+1)
  have r2:Run B (.assign "mask.i" (.add (.var "mask.i") (.lit 1))) ν τ 4:=
    Run.assign (evalB_bin (op:=.add)
      (by rw [evalB_var_iff]; exact ⟨hiν.symm,hiν ▸ hiB⟩) (evalB_lit (by omega))
      (by change i+1< B; omega))
  have rr:=r1.seq r2
  have ht:τ.vars "mask.i"=i+1:=by simp [τ]
  refine ⟨τ,rr,⟨(rr.frame_var "graph.n" (by decide)).trans hn,by rw [ht]; omega,?_,?_⟩,ht⟩
  · simpa only [Prefix,rr.frame_arr "subset.bits" (by decide)] using hbits
  · simp [τ,ν]

theorem command_spec {n:ℕ} (B:ℕ) (I:Finset (Fin n)) (hB:n+2< B) (hm:2^n< B):
    Spec B (fun σ => σ.vars "graph.n"=n∧ Prefix (encodeOutput I) "subset.bits" σ) command
      (fun _ τ => τ.vars "mask.value"=mask I) (15*n+8):=by
  have hloop:=Spec.forRangeZero "mask.i" "graph.n" (Invariant I) n 11 (by omega)
    (fun _ h => h.2.1) (fun _ h => h.1) (step_spec B I hB hm)
  rintro σ ⟨hn,hbits⟩
  let ν:=σ.setVar "mask.value" 0
  have r1:Run B (.assign "mask.value" (.lit 0)) σ ν 2:=Run.assign (evalB_lit (by omega))
  have hi:Invariant I (ν.setVar "mask.i" 0):=by
    refine ⟨?_,by simp,hbits,?_⟩
    · simpa only [ν,vars_setVar,String.reduceEq,if_false] using hn
    · simp [ν,prefix_zero,mask_empty]
  obtain ⟨τ,r2,p2⟩:=hloop ν hi
  refine ⟨τ,(r1.seq r2).mono (by omega),?_⟩
  simpa only [p2.2,prefix_full] using p2.1.2.2.2

end Lax263307Proofs.NativeMasks

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeTabulate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState

def Invariant (array:String) (P:Env→ Prop) (xs:List ℕ) (σ:Env):Prop:=
  P σ∧ σ.vars "fill.length"=xs.length∧ σ.vars "fill.i"≤ xs.length∧
  xs.length≤(σ.arrs array).length∧ Prefix (xs.take (σ.vars "fill.i")) array σ

theorem command_spec (B:ℕ) (xs:List ℕ) (array:String) (P:Env→ Prop) (read:Com) (K:ℕ)
    (hB:xs.length+1< B) (hwords:∀ x∈xs,x< B)
    (hri:"fill.i"∉read.wvars) (hrl:"fill.length"∉read.wvars) (hra:array∉read.warrs)
    (hinit:∀ σ,P σ→ P (σ.setVar "fill.i" 0))
    (hwrite:∀ σ τ,Run B (append array) σ τ 7→ P σ→ P τ)
    (hread:∀ i (hi:i< xs.length),Spec B (fun σ => P σ∧ σ.vars "fill.i"=i) read
      (fun _ τ => P τ∧ τ.vars "fill.value"=xs[i]) K):
    Spec B (fun σ => P σ∧ σ.vars "fill.length"=xs.length∧ xs.length≤(σ.arrs array).length)
      (command array read) (fun _ τ => P τ∧ Prefix xs array τ) ((K+11)*xs.length+6):=by
  have h1:1< B:=by omega
  have hbody:Spec B (fun σ => Invariant array P xs σ∧ σ.vars "fill.i"< xs.length)
      (.seq read (append array))
      (fun σ τ => Invariant array P xs τ∧ τ.vars "fill.i"=σ.vars "fill.i"+1) (K+7):=by
    rintro σ ⟨⟨hPσ,hlen,hle,hroom,hprefix⟩,hlt⟩
    let i:=σ.vars "fill.i"
    have htlen:(xs.take i).length=i:=by rw [List.length_take,Nat.min_eq_left hle]
    obtain ⟨ν,r1,p1⟩:=hread i hlt σ ⟨hPσ,rfl⟩
    have hiν:ν.vars "fill.i"=i:=r1.frame_var "fill.i" hri
    obtain ⟨τ,r2,p2⟩:=Lax455465Proofs.RamWordBuffer.append_spec B array "fill.i" (xs.take i) xs[i]
      (.var "fill.value") h1 (by rw [htlen]; omega) ν
      ⟨by simpa only [Prefix,r1.frame_arr array hra] using hprefix,by rwa [htlen],
        by rw [htlen,Lax455465Proofs.RamFrames.run_array_length r1]; omega,
        by rw [evalB_var_iff]; exact ⟨p1.2.symm,p1.2 ▸ hwords _ (List.getElem_mem hlt)⟩⟩
    have r2':Run B (append array) ν τ 7:=r2
    have ht:τ.vars "fill.i"=i+1:=by simpa only [htlen] using p2.2
    have rr:=r1.seq r2'
    refine ⟨τ,rr,⟨hwrite ν τ r2' p1.1,?_,by rw [ht]; omega,?_,?_⟩,ht⟩
    · exact (r2'.frame_var "fill.length" (by simp [append,Lax455465Proofs.RamWordBuffer.append,Com.wvars])).trans
        ((r1.frame_var "fill.length" hrl).trans hlen)
    · rwa [Lax455465Proofs.RamFrames.run_array_length rr]
    · rw [ht,List.take_succ_eq_append_getElem hlt]
      exact p2.1
  have hloop:=Spec.forRangeZero "fill.i" "fill.length" (Invariant array P xs) xs.length (K+7)
    (by omega) (fun _ h => h.2.2.1) (fun _ h => h.2.1) hbody
  rintro σ ⟨hP,hlen,hroom⟩
  have hi:Invariant array P xs (σ.setVar "fill.i" 0):=by
    refine ⟨hinit σ hP,?_,by simp,hroom,?_⟩
    · simpa only [vars_setVar,String.reduceEq,if_false] using hlen
    · simp only [vars_setVar,if_true,List.take_zero,Prefix,List.length_nil]
      intro i hi
      omega
  obtain ⟨τ,rr,p⟩:=hloop σ hi
  refine ⟨τ,rr.mono (by nlinarith),p.1.1,?_⟩
  simpa only [p.2,List.take_length] using p.1.2.2.2.2

end Lax263307Proofs.NativeTabulate

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeMaskUnpack

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax263307.WeightedIndependentSet
open NativeMasks

theorem bit_value {n:ℕ} (I:Finset (Fin n)) (v:Fin n):
    Nat.land (mask I / 2^v.val) 1=if v∈I then 1 else 0:=by
  rw [Nat.land_eq,Nat.and_one_is_mod]
  have h:=mask_member I v
  rw [Nat.testBit_eq_decide_div_mod_eq] at h
  have hm:=Nat.mod_lt (mask I / 2^v.val) (by omega:0<2)
  by_cases hv:v∈I
  · simp only [hv,decide_true,decide_eq_true_eq,if_true] at h ⊢
    exact h
  · simp only [hv,decide_false,decide_eq_false_iff_not,if_false] at h ⊢
    omega

end Lax263307Proofs.NativeMaskUnpack

end

section

namespace Lax263307Proofs.NativeSlice

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs

def Context (source:String) (front xs tail:List ℕ) (σ:Env):Prop:=
  Prefix (front++(xs++tail)) source σ∧ σ.vars "slice.start"=front.length

theorem read_spec (B:ℕ) (source:String) (front xs tail:List ℕ)
    (i:ℕ) (hi:i< xs.length) (hB:front.length+xs.length+1< B) (hv:xs[i]< B):
    Spec B (fun σ => Context source front xs tail σ∧ σ.vars "fill.i"=i) (read source)
      (fun _ τ => Context source front xs tail τ∧ τ.vars "fill.value"=xs[i]) 5:=by
  rintro σ ⟨⟨hp,hstart⟩,hindex⟩
  have hlen:front.length+i<(front++(xs++tail)).length:=by simp; omega
  have hget:(σ.arrs source)[front.length+i]?=some xs[i]:=by
    have hh:=hp (front.length+i) hlen
    simpa only [List.getElem_append_right (by omega:front.length≤ front.length+i),
      Nat.add_sub_cancel_left,List.getElem_append_left hi] using hh
  have hroom:front.length+i<(σ.arrs source).length:=by
    by_contra hh
    rw [List.getElem?_eq_none (by omega)] at hget
    cases hget
  (expose_names;
    (refine let c0:Nat:= @getElem (List Nat) Nat Nat (fun (as:List Nat) (i_1:Nat) => Nat.lt i_1 (@List.length Nat as)) (@List.instGetElemNatLtLength Nat) xs i hi; let c1:Env→ Prop:=(fun (x τ:Env) => And (Context source front xs tail τ) (@Eq Nat (Env.vars τ "fill.value") c0)) σ; let c2:Nat→ Nat→ Nat:=Nat.add; let c3:Nat:=c2 (Env.vars σ "slice.start") (Env.vars σ "fill.i"); let c4:Nat:= @List.getD Nat (Env.arrs σ source) c3 ((0:Nat)); let c5:Env:=Env.setVar σ "fill.value" c4; let c6:Expr:=Expr.get source (Expr.add (Expr.var "slice.start") (Expr.var "fill.i")); @Exists.intro Env (fun (σ':Env) => And (Run B (read source) σ σ' ((5:Nat))) (c1 σ')) c5 (@And.intro (Run B (read source) σ c5 ((5:Nat))) (c1 c5) (RunStep.mono B (read source) σ c5 (c2 ((1:Nat)) (Expr.size c6)) ((5:Nat)) (RunStep.assign B σ "fill.value" c6 c4 (RunStep.eval_get B σ source (Expr.add (Expr.var "slice.start") (Expr.var "fill.i")) c3 (RunStep.eval_add B σ (Expr.var "slice.start") (Expr.var "fill.i") (Env.vars σ "slice.start") (Env.vars σ "fill.i") (RunStep.eval_var B σ "slice.start" (?nAX_g8333_0_0_0)) (RunStep.eval_var B σ "fill.i" (?nAX_g8333_0_0_1)) (?nAX_g8333_0_0_2)) (?nAX_g8333_0_0_3) ?_)) (?nAX_g8333_0_0_4)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8333_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8333_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8333_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8333_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8333_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Context,Prefix]

theorem command_spec (B:ℕ) (source target:String) (front xs tail:List ℕ)
    (hne:source≠target) (hB:front.length+xs.length+1< B) (hv:∀ z∈xs,z< B):
    Spec B (fun σ => Context source front xs tail σ∧ σ.vars "fill.length"=xs.length∧
      xs.length≤(σ.arrs target).length) (command source target)
      (fun _ τ => Context source front xs tail τ∧ Prefix xs target τ) (16*xs.length+6):=by
  have hh:=NativeTabulate.command_spec B xs target (Context source front xs tail) (read source) 5
    (by omega) hv (by simp [read,Com.wvars]) (by simp [read,Com.wvars])
    (by simp [read,Com.warrs])
    (fun σ h => by simpa only [Context,Prefix,arrs_setVar,vars_setVar,String.reduceEq,if_false] using h)
    (fun σ τ rr h => by
      simpa only [Context,Prefix,rr.frame_arr source (by simp [NativeTabulate.append,RamWordBuffer.append,Com.warrs,hne]),
        rr.frame_var "slice.start" (by simp [NativeTabulate.append,RamWordBuffer.append,Com.wvars])] using h)
    (fun i hi => read_spec B source front xs tail i hi hB (hv _ (List.getElem_mem hi)))
  exact hh

end Lax263307Proofs.NativeSlice

end

section

namespace Lax263307Proofs.NativeProgramCache

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

theorem copy_spec (B:ℕ) (source target lengthVar:String) (xs:List ℕ)
    (hne:source≠target) (hB:xs.length+2< B) (hv:∀ z∈xs,z< B):
    Spec B (fun σ => Prefix xs source σ∧ σ.vars lengthVar=xs.length∧ xs.length≤(σ.arrs target).length)
      (copy source target lengthVar)
      (fun _ τ => Prefix xs source τ∧ Prefix xs target τ) (16*xs.length+10):=by
  rintro σ ⟨hp,hlen,hroom⟩
  let ν:=σ.setVar "fill.length" xs.length
  have r1:Run B (.assign "fill.length" (.var lengthVar)) σ ν 2:=Run.assign
    (by rw [evalB_var_iff]; exact ⟨hlen.symm,hlen ▸ (by omega)⟩)
  let μ:=ν.setVar "slice.start" 0
  have r2:Run B (.assign "slice.start" (.lit 0)) ν μ 2:=Run.assign (evalB_lit (show 0< B by omega))
  obtain ⟨τ,r3,p3⟩:=NativeSlice.command_spec B source target [] xs [] hne (by simp; omega) hv μ
    ⟨⟨by simpa only [List.nil_append,List.append_nil,Prefix,(r1.seq r2).frame_arr source (by simp [Com.warrs])] using hp,
      by rfl⟩,by simp [μ,ν],by rw [RamFrames.run_array_length (r1.seq r2)]; exact hroom⟩
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),
    by simpa only [NativeSlice.Context,List.nil_append,List.append_nil] using p3.1.1,p3.2⟩

end Lax263307Proofs.NativeProgramCache

end

section

namespace Lax263307Proofs.NativeImageOutput

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 WeightedIndependentSet NativeMasks

def prefixImage {n N:ℕ} (owner:Fin N→ Fin n) (I:Finset (Fin N)) (i:ℕ):Finset (Fin n):=
  (initialSet I i).image owner

theorem prefixImage_step {n N:ℕ} (owner:Fin N→ Fin n) (I:Finset (Fin N)) (i:ℕ) (hi:i< N):
    prefixImage owner I (i+1)=if (⟨i,hi⟩:Fin N)∈I then insert (owner ⟨i,hi⟩) (prefixImage owner I i) else prefixImage owner I i:=by
  unfold prefixImage
  rw [prefix_succ I i hi]
  split_ifs <;> simp

theorem prefix_insert {n:ℕ} (I:Finset (Fin n)) (v:Fin n) (σ:Env)
    (hp:Prefix (encodeOutput I) "image.output" σ) (hn:n≤(σ.arrs "image.output").length):
    Prefix (encodeOutput (insert v I)) "image.output" (σ.setArr "image.output" v.val 1):=by
  intro j hj
  have hjn:j< n:=by simpa [encodeOutput] using hj
  have hval:v.val<(σ.arrs "image.output").length:=v.isLt.trans_le hn
  simp only [arrs_setArr,if_true]
  by_cases he:v.val=j
  · subst j
    rw [List.getElem?_set_self hval]
    simp [encodeOutput]
  · rw [List.getElem?_set_ne he]
    have hvj:(⟨j,hjn⟩:Fin n)≠v:=by intro hh; exact he (congrArg Fin.val hh).symm
    simpa [encodeOutput,hvj] using hp j (by simpa [encodeOutput] using hjn)

structure Context {n N:ℕ} (owner:Fin N→ Fin n) (I:Finset (Fin N)) (σ:Env):Prop where
  order:σ.vars "image.n"=n
  count:σ.vars "image.count"=N
  mask:σ.vars "image.mask"=NativeMasks.mask I
  labels:Prefix (List.ofFn (fun i => (owner i).val)) "image.labels" σ
  room:(σ.arrs "image.output").length=n

def Invariant {n N:ℕ} (owner:Fin N→ Fin n) (I:Finset (Fin N)) (σ:Env):Prop:=
  Context owner I σ∧ σ.vars "image.i"≤ N∧ Prefix (encodeOutput (prefixImage owner I (σ.vars "image.i"))) "image.output" σ

theorem context_frame {n N B t:ℕ} {owner:Fin N→ Fin n} {I:Finset (Fin N)}
    {c:Com} {σ τ:Env} (rr:Run B c σ τ t) (hc:Context owner I σ)
    (hv:∀ s∈["image.n","image.count","image.mask"],s∉c.wvars) (hl:"image.labels"∉c.warrs):
    Context owner I τ:=by
  refine ⟨(rr.frame_var _ (hv _ (by simp))).trans hc.order,
    (rr.frame_var _ (hv _ (by simp))).trans hc.count,(rr.frame_var _ (hv _ (by simp))).trans hc.mask,?_,?_⟩
  · simpa only [Prefix,rr.frame_arr "image.labels" hl] using hc.labels
  · rw [RamFrames.run_array_length rr]; exact hc.room

private theorem value {B x:ℕ} {name:String} {σ:Env} (hx:σ.vars name=x) (hB:x< B):
    (Expr.var name).evalB B σ=some x:=by
  rw [evalB_var_iff]; exact ⟨hx.symm,hx ▸ hB⟩

theorem step_spec {n N:ℕ} (B:ℕ) (owner:Fin N→ Fin n) (I:Finset (Fin N))
    (hB:n+N+5< B) (hm:2^N< B):
    Spec B (fun σ => Invariant owner I σ∧ σ.vars "image.i"< N) step
      (fun σ τ => Invariant owner I τ∧ τ.vars "image.i"=σ.vars "image.i"+1) 24:=by
  rintro σ ⟨⟨hc,hle,hprefix⟩,hlt⟩
  let i:=σ.vars "image.i"
  let v:Fin N:= ⟨i,hlt⟩
  let bit:=if v∈I then 1 else 0
  have hiB:i< B:=by dsimp [i]; omega
  have hbit:bit≤1:=by dsimp [bit]; split_ifs <;> omega
  have hmask:mask I< B:=(mask_bound I).trans hm
  have hdiv:mask I/2^i< B:=(Nat.div_le_self _ _).trans_lt hmask
  have he:(Expr.and (.shiftr (.var "image.mask") (.var "image.i")) (.lit 1)).evalB B σ=some bit:=by
    have hh:=evalB_bin (op:=.and)
      (evalB_bin (op:=.shiftr) (value hc.mask hmask) (evalB_var hiB) hdiv)
      (evalB_lit (show 1< B by omega)) (by
        change Nat.land (mask I/2^i) 1< B
        rw [NativeMaskUnpack.bit_value I v]
        exact hbit.trans_lt (by omega))
    exact hh.trans (congrArg some (NativeMaskUnpack.bit_value I v))
  let ν:=σ.setVar "image.bit" bit
  have r1:Run B (.assign "image.bit" (.and (.shiftr (.var "image.mask") (.var "image.i")) (.lit 1))) σ ν 6:=Run.assign he
  have hip:ν.vars "image.i"=i:=by simp [ν,i]
  have hlabels:Prefix (List.ofFn (fun j => (owner j).val)) "image.labels" ν:=by simpa [Prefix,ν] using hc.labels
  have hget:(ν.arrs "image.labels")[i]?=some (owner v).val:=by
    have hh:=hlabels i (by simpa only [List.length_ofFn] using hlt)
    rw [List.getElem_ofFn] at hh
    exact hh
  have howner:(owner v).val< B:=(owner v).isLt.trans (by omega)
  let μ:=ν.setVar "image.owner" (owner v).val
  have r2:Run B (.assign "image.owner" (.get "image.labels" (.var "image.i"))) ν μ 3:=
    Run.assign (evalB_get (value hip hiB) hget howner)
  have rd:Run B read σ μ 9:=r1.seq r2
  have hiμ:μ.vars "image.i"=i:=by simp [μ,ν,i]
  have hbμ:μ.vars "image.bit"=bit:=by simp [μ,ν]
  have hoμ:μ.vars "image.owner"=(owner v).val:=by simp [μ]
  have hpμ:Prefix (encodeOutput (prefixImage owner I i)) "image.output" μ:=by simpa only [Prefix,μ,ν,arrs_setVar] using hprefix
  have hnμ:(μ.arrs "image.output").length=n:=by simpa only [μ,ν,arrs_setVar] using hc.room
  have htest:=evalB_condEq (value hbμ (show bit< B by omega)) (evalB_lit (show 1< B by omega))
  obtain ⟨η,rb,hpη,hiη⟩:∃ η,Run B branch μ η 7∧
      Prefix (encodeOutput (prefixImage owner I (i+1))) "image.output" η∧ η.vars "image.i"=i:=by
    by_cases hv:v∈I
    · let η:=μ.setArr "image.output" (owner v).val 1
      have rs:Run B (.store "image.output" (.var "image.owner") (.lit 1)) μ η 3:=
        Run.store (value hoμ howner) (evalB_lit (show 1< B by omega)) (by rw [hnμ]; exact (owner v).isLt)
      have hc':(Cond.eq (.var "image.bit") (.lit 1)).evalB B μ=some true:=by simpa [bit,hv] using htest
      have rr:Run B branch μ η 7:=(Run.ite_true (d:=.skip) hc' rs).mono (by simp [Cond.size,Expr.size])
      refine ⟨η,rr,?_,by simpa [η] using hiμ⟩
      rw [prefixImage_step owner I i hlt,if_pos hv]
      exact prefix_insert (prefixImage owner I i) (owner v) μ hpμ hnμ.ge
    · have hc':(Cond.eq (.var "image.bit") (.lit 1)).evalB B μ=some false:=by simpa [bit,hv] using htest
      have rr:Run B branch μ μ 7:=(Run.ite_false (c:=.store "image.output" (.var "image.owner") (.lit 1)) hc' Run.skip).mono
        (by simp [Cond.size,Expr.size])
      exact ⟨μ,rr,by simpa only [prefixImage_step owner I i hlt,show ¬(⟨i,hlt⟩:Fin N)∈I from hv,if_false] using hpμ,hiμ⟩
  let τ:=η.setVar "image.i" (i+1)
  have r3:Run B (.assign "image.i" (.add (.var "image.i") (.lit 1))) η τ 4:=Run.assign
    (evalB_bin (op:=.add) (value hiη hiB) (evalB_lit (show 1< B by omega)) (by change i+1< B; omega))
  have rr:Run B step σ τ 24:=(rd.seq (rb.seq r3)).mono (by omega)
  refine ⟨τ,rr,⟨?_,by simp [τ]; dsimp [i] at *; omega,?_⟩,by simp [τ,i]⟩
  · apply context_frame rr hc
    · intro name hname
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hname
      rcases hname with rfl|rfl|rfl <;> decide
    · decide
  · simpa [τ,Prefix] using hpη

theorem prefixImage_full {n N:ℕ} (owner:Fin N→ Fin n) (I:Finset (Fin N)):prefixImage owner I N=I.image owner:=by
  unfold prefixImage
  congr 1
  ext v
  simp [initialSet,v.isLt]

theorem command_spec {n N:ℕ} (B:ℕ) (owner:Fin N→ Fin n) (I:Finset (Fin N))
    (hB:n+N+5< B) (hm:2^N< B):
    Spec B (Context owner I) command
      (fun σ τ => τ.out=σ.out++encodeOutput (I.image owner)) (24*n+28*N+20):=by
  have hfill:=Fill.loop_spec B n "image.output" "image.clear.i" "image.n" (.lit 0) (fun _ => 0)
    (by decide) (by omega) (fun _ _ _ _ => evalB_lit (by omega:0< B))
  have hloop:=Spec.forRangeZero "image.i" "image.count" (Invariant owner I) N 24 (by omega)
    (fun _ h => h.2.1) (fun _ h => h.1.count) (step_spec B owner I hB hm)
  intro σ hc
  have harray:∃ g,σ.arrs "image.output"=arrOf n g:=by
    refine ⟨fun i => (σ.arrs "image.output").getD i 0,?_⟩
    apply List.ext_getElem
    · simp [arrOf,hc.room]
    · intro i hi hj
      simp only [arrOf,List.getElem_map,List.getElem_range]
      exact List.getElem_eq_getD 0
  obtain ⟨ν,r1,⟨g,hg,hzero⟩,hi⟩:=hfill σ ⟨harray,hc.order⟩
  have hcν:Context owner I ν:=by
    apply context_frame r1 hc
    · intro name hname
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hname
      rcases hname with rfl|rfl|rfl <;> decide
    · decide
  have hzeros:ν.arrs "image.output"=List.replicate n 0:=by
    rw [hg]
    apply List.ext_getElem
    · simp [arrOf]
    · intro i hi hj
      simp only [arrOf,List.getElem_map,List.getElem_range,List.getElem_replicate]
      exact hzero i (by simpa [arrOf] using hi)
  have hin:Invariant owner I (ν.setVar "image.i" 0):=by
    refine ⟨⟨?_,?_,?_,?_,?_⟩,by simp,?_⟩
    · simpa using hcν.order
    · simpa using hcν.count
    · simpa using hcν.mask
    · simpa [Prefix] using hcν.labels
    · simpa using hcν.room
    · intro i hii
      have hin:i< n:=by simpa [prefixImage,initialSet,encodeOutput] using hii
      simp [prefixImage,initialSet,Prefix,hzeros,encodeOutput,hin]
  obtain ⟨μ,r2,po⟩:=hloop ν hin
  have hprefix:Prefix (encodeOutput (I.image owner)) "image.output" μ:=by
    simpa only [po.2,prefixImage_full] using po.1.2.2
  let η:=μ.setVar "emit.count" n
  have r3:Run B (.assign "emit.count" (.var "image.n")) μ η 2:=
    Run.assign (value po.1.1.order (by omega))
  have hdata:RamEmitWords.Data "image.output" 1 (encodeOutput (I.image owner)) η:=by
    simpa only [RamEmitWords.Data,Prefix,Nat.one_mul,η,arrs_setVar] using hprefix
  have hout:η.out=σ.out:=by
    exact (r3.out_eq (by decide)).trans ((r2.out_eq (by decide)).trans (r1.out_eq (by decide)))
  obtain ⟨τ,r4,houtτ⟩:=RamEmitWords.command_spec B "image.output" 1 (encodeOutput (I.image owner)) σ.out
    (by omega) (by omega) (by simp [encodeOutput]; omega) (by simp [encodeOutput]; omega)
    (by intro z hz; obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hz; split_ifs <;> omega) η
    ⟨hdata,by simp [η,encodeOutput],hout⟩
  exact ⟨τ,(r1.seq (r2.seq (r3.seq r4))).mono (by simp [Expr.size,encodeOutput]; omega),houtτ⟩

end Lax263307Proofs.NativeImageOutput

end

section

namespace Lax263307Proofs.NativeWeightedOutput

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 WeightedAlgorithm IndependentBlowUp WeightedIndependentSet

abbrev owner {n:ℕ} (copies:Fin n→ ℕ) (i:Fin (∑ v,copies v)):Fin n:=(labeling copies i).1

theorem owner_words {n:ℕ} (copies:Fin n→ ℕ):
    NativeBlowUp.owners copies=List.ofFn (fun i => (owner copies i).val):=by
  apply List.ext_getElem (by simp [NativeBlowUp.owners_length])
  intro i hi hj
  have hin:i<∑ v,copies v:=by simpa only [NativeBlowUp.owners_length] using hi
  have hh:=NativeBlowUp.owners_labeling copies ⟨i,hin⟩
  rw [List.getElem?_eq_getElem hi] at hh
  rw [List.getElem_ofFn]
  exact Option.some.inj hh

theorem projected {n:ℕ} (copies:Fin n→ ℕ) (I:Finset (Fin (∑ v,copies v))):
    I.image (owner copies)=project (I.image (labeling copies)):=by
  simp only [project,Finset.image_image]
  rfl

private theorem value {B x:ℕ} {name:String} {σ:Env} (hx:σ.vars name=x) (hB:x< B):
    (Expr.var name).evalB B σ=some x:=by
  rw [evalB_var_iff]; exact ⟨hx.symm,hx ▸ hB⟩

theorem command_spec {n:ℕ} (B:ℕ) (copies:Fin n→ ℕ) (I:Finset (Fin (∑ v,copies v)))
    (hB:n+(∑ v,copies v)+5< B) (hm:2^(∑ v,copies v)< B):
    Spec B (fun σ => σ.vars "input.n"=n∧ σ.vars "blowup.length"=∑ v,copies v∧
      σ.vars "root.mask"=NativeMasks.mask I∧ Prefix (NativeBlowUp.owners copies) "blowup.owner" σ∧
      (∑ v,copies v)≤(σ.arrs "image.labels").length∧ (σ.arrs "image.output").length=n)
      command (fun σ τ => τ.out=σ.out++encodeOutput (project (I.image (labeling copies))))
      (24*n+44*(∑ v,copies v)+36):=by
  rintro σ ⟨hn,hN,hmask,howners,hroom,houtput⟩
  let N:= ∑ v,copies v
  let σ1:=σ.setVar "image.n" n
  let σ2:=σ1.setVar "image.count" N
  let σ3:=σ2.setVar "image.mask" (NativeMasks.mask I)
  have r1:Run B (.assign "image.n" (.var "input.n")) σ σ1 2:=Run.assign (value hn (by omega))
  have r2:Run B (.assign "image.count" (.var "blowup.length")) σ1 σ2 2:=Run.assign (value (by simpa [σ1] using hN) (by omega))
  have r3:Run B (.assign "image.mask" (.var "root.mask")) σ2 σ3 2:=Run.assign
    (value (by simpa [σ2,σ1] using hmask) ((NativeMasks.mask_bound I).trans hm))
  have rm:Run B metadata σ σ3 6:=r1.seq (r2.seq r3)
  have hwords:∀ z∈NativeBlowUp.owners copies,z< B:=by
    rw [owner_words copies]
    intro z hz
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hz
    exact (owner copies i).isLt.trans (by omega)
  obtain ⟨ν,rc,pc⟩:=NativeProgramCache.copy_spec B "blowup.owner" "image.labels" "image.count"
    (NativeBlowUp.owners copies) (by decide) (by simp [NativeBlowUp.owners_length]; omega) hwords σ3
    ⟨by simpa only [Prefix,σ3,σ2,σ1,arrs_setVar] using howners,
      by simp [σ3,σ2,σ1,N,NativeBlowUp.owners_length],
      by simpa only [NativeBlowUp.owners_length,σ3,σ2,σ1,arrs_setVar] using hroom⟩
  have hc:NativeImageOutput.Context (owner copies) I ν:=by
    refine ⟨?_,?_,?_,?_,?_⟩
    · simpa [σ3,σ2,σ1] using rc.frame_var "image.n" (by decide)
    · simpa [σ3,σ2,σ1] using rc.frame_var "image.count" (by decide)
    · simpa [σ3,σ2,σ1] using rc.frame_var "image.mask" (by decide)
    · simpa only [owner_words copies] using pc.2
    · rw [RamFrames.run_array_length rc]
      simpa only [σ3,σ2,σ1,arrs_setVar] using houtput
  obtain ⟨τ,ri,pi⟩:=NativeImageOutput.command_spec B (owner copies) I hB hm ν hc
  refine ⟨τ,(rm.seq (rc.seq ri)).mono (by simp only [NativeBlowUp.owners_length]; omega),?_⟩
  have hout:ν.out=σ.out:=(rc.out_eq (by decide)).trans (rm.out_eq (by decide))
  simpa only [hout,projected copies I] using pi

end Lax263307Proofs.NativeWeightedOutput

end

theorem solution:∀ {n:Nat} (B:Nat) (copies:Fin n→ Nat) (I:Finset (Fin (∑ v:Fin n,copies v))),
  Nat.lt
      (Nat.add
        (Nat.add n (∑ v:Fin n,copies v))
        ((5:Nat)))
      B→
    Nat.lt
        (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
          ((2:Nat)) (∑ v:Fin n,copies v))
        B→
      Lax808846Proofs.Reasoning.Spec B
        (fun (σ:Lax808846Proofs.Imp.Env) =>
          And (@Eq Nat (σ.vars "input.n") n)
            (And (@Eq Nat (σ.vars "blowup.length") (∑ v:Fin n,copies v))
              (And (@Eq Nat (σ.vars "root.mask") (@Lax263307Proofs.NativeMasks.mask (∑ v:Fin n,copies v) I))
                (And
                  (Lax455465Proofs.RamVirtualState.Prefix (@Lax263307Proofs.NativeBlowUp.owners n copies) "blowup.owner"
                    σ)
                  (And (Nat.le (∑ v:Fin n,copies v) (@List.length Nat (σ.arrs "image.labels")))
                    (@Eq Nat (@List.length Nat (σ.arrs "image.output")) n))))))
        Lax263307Proofs.NativeWeightedOutput.command
        (fun (σ τ:Lax808846Proofs.Imp.Env) =>
          @Eq (List Nat) τ.out
            (@HAppend.hAppend (List Nat) (List Nat) (List Nat) (@instHAppendOfAppend (List Nat) (@List.instAppend Nat))
              σ.out
              (@Lax263307.IndependentSetEncoding.encodeOutput n
                (@Lax263307.IndependentBlowUp.project n copies
                  (@Finset.image (Fin (∑ v:Fin n,copies v)) (@Lax263307.IndependentBlowUp.Vertex n copies)
                    (fun (a b:@Lax263307.IndependentBlowUp.Vertex n copies) =>
                      @Sigma.instDecidableEqSigma (Fin n) (fun (v:Fin n) => Fin (copies v)) (instDecidableEqFin n)
                        (fun (a:Fin n) => instDecidableEqFin (copies a)) a b)
                    (@DFunLike.coe (Equiv (Fin (∑ v:Fin n,copies v)) (@Lax263307.IndependentBlowUp.Vertex n copies))
                      (Fin (∑ v:Fin n,copies v))
                      (fun (x:Fin (∑ v:Fin n,copies v)) => @Lax263307.IndependentBlowUp.Vertex n copies)
                      (@EquivLike.toFunLike
                        (Equiv (Fin (∑ v:Fin n,copies v)) (@Lax263307.IndependentBlowUp.Vertex n copies))
                        (Fin (∑ v:Fin n,copies v)) (@Lax263307.IndependentBlowUp.Vertex n copies)
                        (@Equiv.instEquivLike (Fin (∑ v:Fin n,copies v))
                          (@Lax263307.IndependentBlowUp.Vertex n copies)))
                      (@Lax263307.WeightedAlgorithm.labeling n copies))
                    I)))))
        (Nat.add
          (Nat.add
            (Nat.mul
              ((24:Nat)) n)
            (Nat.mul
              ((44:Nat)) (∑ v:Fin n,copies v)))
          ((36:Nat))):= @Lax263307Proofs.NativeWeightedOutput.command_spec
