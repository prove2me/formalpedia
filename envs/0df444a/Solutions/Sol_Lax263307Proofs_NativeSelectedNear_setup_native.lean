-- Prove2me | solution 1 for Lax263307Proofs.NativeSelectedNear.setup_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T16:34:07.127249+00:00
-- url     : https://prove2.me/submissions/70aeba61-c2f0-4c46-a187-3e59d6a54af0

import Mathlib.Tactic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Log
import Mathlib.Combinatorics.Colex
import Mathlib.Data.List.Sort
import Definitions.Def_EdgeSublinearMWIS_Main_NativeBoundsInterfaces

set_option maxHeartbeats 0
set_option maxRecDepth 30000

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
namespace Lax109476Proofs.EllipsoidStateSize
end Lax109476Proofs.EllipsoidStateSize
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
namespace Lax263307Proofs.LightSeparators
end Lax263307Proofs.LightSeparators
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

theorem Expr.lt_of_evalB {B:ℕ} {σ:Env} {e:Expr} {v:ℕ}
    (h:e.evalB B σ=some v):v < B:=(eval_and_lt_of_evalB h).2

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

theorem Run.bigStep {B:ℕ} {c:Com} {σ σ':Env} {K:ℕ} (h:Run B c σ σ' K):
    ∃ k≤ K,BigStep c σ σ' k:=by
  obtain ⟨k,hk,hbs⟩:=h; exact ⟨k,hk,hbs.bigStep⟩

end Lax808846Proofs.Reasoning

end

section

namespace Lax263307Proofs.RecursionDepth

open Lax263307.RecursionDepth Lax263307.WeightedIndependentSet

theorem depth_mono:Monotone depth:=by
  intro n m hnm
  induction m using Nat.strong_induction_on generalizing n with
  | h m ih =>
    by_cases hn:n≤ 1
    · rw [depth,if_pos hn]
      exact Nat.zero_le _
    · have hm:¬m≤ 1:=by omega
      rw [depth.eq_def n,if_neg hn,depth.eq_def m,if_neg hm]
      exact Nat.add_le_add_left (ih (2 * m / 3) (by omega)
        (Nat.div_le_div_right (Nat.mul_le_mul_left 2 hnm))) 1

theorem balanced_decrease (n m:ℕ) (nontrivial:1 < n) (balanced:3 * m≤ 2 * n):
    depth m + 1≤ depth n:=by
  have hm:m≤ 2 * n / 3:=by omega
  have hdepth:=depth_mono hm
  rw [depth.eq_def n,if_neg (by omega)]
  omega

end Lax263307Proofs.RecursionDepth

end

section

namespace Lax263307.LinearRelaxation

noncomputable def conditioned {n r:ℕ} (y:MomentVector n r)
    (A:Finset (Fin n)) (v:Fin n):ℝ:=
  value y (insert v A) / value y A

end Lax263307.LinearRelaxation

end

section

namespace Lax263307Proofs.RelaxationAlgebra

open Lax263307.LinearRelaxation

theorem value_of_size {n r:ℕ} (y:MomentVector n r)
    (A:Finset (Fin n)) (hA:A.card≤ r + 2):value y A=y ⟨A,hA⟩:=by
  simp [value,hA]

theorem insert_size {n r:ℕ} (A:Finset (Fin n))
    (hA:A.card≤ r + 1) (v:Fin n):(insert v A).card≤ r + 2:=by
  have:=Finset.card_insert_le v A
  omega

end Lax263307Proofs.RelaxationAlgebra

end

section

namespace Lax263307.Entropy

def IsProbability {n:ℕ} (π:Fin n→ ℝ):Prop:=
  (∀ v,0≤ π v)∧ (∑ v,π v)=1

noncomputable def naturalEntropy {n:ℕ} (π:Fin n→ ℝ):ℝ:=
  ∑ v,Real.negMulLog (π v)

noncomputable def entropy {n:ℕ} (π:Fin n→ ℝ):ℝ:=
  naturalEntropy π / Real.log 2

end Lax263307.Entropy

end

section

namespace Lax263307.ConditioningDistribution

open LinearRelaxation

noncomputable def marginal {n r:ℕ} (y:MomentVector n r)
    (A:Finset (Fin n)) (k:ℕ) (v:Fin n):ℝ:=
  conditioned y A v / k

noncomputable def joint {n r:ℕ} (y:MomentVector n r)
    (A:Finset (Fin n)) (k:ℕ) (u v:Fin n):ℝ:=
  value y (insert u (insert v A)) / ((k:ℝ) ^ 2 * value y A)

end Lax263307.ConditioningDistribution

end

section

namespace Lax263307Proofs.EntropyAlgebra

open Lax263307.Entropy

theorem log_two_pos:0 < Real.log 2:=Real.log_pos (by norm_num)

theorem log_two_le_one:Real.log 2≤ 1:=by
  have:=Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
  norm_num at this ⊢
  exact this

theorem probability_entry_le_one {n:ℕ} (π:Fin n→ ℝ) (hπ:IsProbability π)
    (v:Fin n):π v≤ 1:=by
  rw [← hπ.2]
  exact Finset.single_le_sum (fun u _ => hπ.1 u) (Finset.mem_univ v)

theorem scaled_negMulLog_div (a x:ℝ) (ha:0 < a):
    a * Real.negMulLog (x / a)=Real.negMulLog x + x * Real.log a:=by
  by_cases hx:x=0
  · simp [hx]
  · dsimp [Real.negMulLog]
    rw [Real.log_div hx (ne_of_gt ha)]
    field_simp
    ring

theorem relative_term_bound (x a b:ℝ) (hx:0 < x) (ha:0 < a) (hb:0 < b):
    x - a * b≤ -Real.negMulLog x - x * Real.log a - x * Real.log b:=by
  have hab:0 < a * b:=mul_pos ha hb
  have h:=Real.log_le_sub_one_of_pos (div_pos hab hx)
  rw [Real.log_div (ne_of_gt hab) (ne_of_gt hx),
    Real.log_mul (ne_of_gt ha) (ne_of_gt hb)] at h
  have hm:=mul_le_mul_of_nonneg_left h hx.le
  simp_rw [mul_sub] at hm
  rw [mul_div_cancel₀ _ (ne_of_gt hx),mul_one] at hm
  dsimp [Real.negMulLog]
  nlinarith

theorem natural_entropy_nonneg {n:ℕ} (π:Fin n→ ℝ) (hπ:IsProbability π):
    0≤ naturalEntropy π:=
  Finset.sum_nonneg fun v _ => Real.negMulLog_nonneg (hπ.1 v) (probability_entry_le_one π hπ v)

theorem natural_entropy_le_log {n:ℕ} (π:Fin n→ ℝ) (hπ:IsProbability π):
    naturalEntropy π≤ Real.log n:=by
  have hn:0 < n:=by
    by_contra hn
    have hn0:n=0:=by omega
    subst n
    simpa using hπ.2
  have hnR:(0:ℝ) < n:=by exact_mod_cast hn
  have hn0:(n:ℝ) ≠ 0:=ne_of_gt hnR
  have hw:(∑ _v:Fin n, (1 / (n:ℝ)))=1:=by simp [hn0]
  have h:=Real.concaveOn_negMulLog.le_map_sum
    (t:=Finset.univ) (w:=fun _:Fin n => 1 / (n:ℝ)) (p:=π)
    (fun _ _ => (one_div_pos.mpr hnR).le) hw (fun v _ => hπ.1 v)
  simp only [smul_eq_mul] at h
  simp_rw [← Finset.mul_sum] at h
  rw [hπ.2,mul_one] at h
  have hm:=mul_le_mul_of_nonneg_left h hnR.le
  rw [← mul_assoc,mul_one_div_cancel hn0,one_mul] at hm
  have heq:(n:ℝ) * Real.negMulLog (1 / (n:ℝ))=Real.log n:=by
    simp [Real.negMulLog,hn0]
  exact hm.trans_eq heq

end Lax263307Proofs.EntropyAlgebra

end

section

namespace Lax263307Proofs.EntropyDecrease

open Lax263307.LinearRelaxation Lax263307.ConditioningDistribution
open Lax263307.Entropy EntropyAlgebra

theorem adjacencyMass_div {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℝ) (k:ℝ) (hk:k ≠ 0):
    adjacencyMass G (fun v => x v / k)=adjacencyMass G x / k ^ 2:=by
  unfold adjacencyMass
  simp_rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  split_ifs
  · field_simp
  · simp

end Lax263307Proofs.EntropyDecrease

end

section

namespace Lax263307Proofs.RationalConditioning

open Lax263307.LinearRelaxation Lax263307.Entropy Lax263307.RationalConditioning
open EntropyDecrease

theorem value_cast {n r:ℕ} (y:RationalVector n r) (A:Finset (Fin n)):
    value (realVector y) A=(rationalValue y A:ℝ):=by
  by_cases hA:A.card≤ r + 2 <;> simp [value,realVector,rationalValue,hA]

theorem edge_cost_formula {n r:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (y:RationalVector n r) (A:Finset (Fin n)) (hA:0 < rationalValue y A):
    edgeCost G (conditioned (realVector y) A) =
      (edgeNumerator G y A:ℝ) / (2 * (rationalValue y A:ℝ) ^ 2):=by
  have hpos:(0:ℝ) < (rationalValue y A:ℝ):=by exact_mod_cast hA
  have hcost:conditioned (realVector y) A=fun v =>
      (rationalValue y (insert v A):ℝ) / (rationalValue y A:ℝ):=by
    funext v
    simp [conditioned,value_cast]
  have hnum:adjacencyMass G (fun v => (rationalValue y (insert v A):ℝ)) =
      (edgeNumerator G y A:ℝ):=by
    unfold adjacencyMass edgeNumerator
    push_cast
    simp only [apply_ite,Rat.cast_mul,Rat.cast_zero]
  rw [edgeCost,hcost,adjacencyMass_div G _ _ (ne_of_gt hpos),hnum]
  ring

theorem passes_iff {n r:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k p:ℕ) (y:RationalVector n r) (A:Finset (Fin n)) (hp:0 < p):
    Passes G k p y A↔ 0 < value (realVector y) A∧
      edgeCost G (conditioned (realVector y) A)≤ (k:ℝ) ^ 2 / p:=by
  have hpR:(0:ℝ) < p:=by exact_mod_cast hp
  constructor
  · rintro ⟨hpos,hineq⟩
    have hposR:(0:ℝ) < (rationalValue y A:ℝ):=by exact_mod_cast hpos
    refine ⟨by rw [value_cast]; exact hposR, ?_⟩
    rw [edge_cost_formula G y A hpos]
    apply (div_le_div_iff₀ (mul_pos (by norm_num) (sq_pos_of_pos hposR)) hpR).2
    have hR:(p:ℝ) * (edgeNumerator G y A:ℝ)≤
        2 * (k:ℝ) ^ 2 * (rationalValue y A:ℝ) ^ 2:=by exact_mod_cast hineq
    nlinarith
  · rintro ⟨hposR,hineq⟩
    rw [value_cast] at hposR
    have hpos:0 < rationalValue y A:=by exact_mod_cast hposR
    refine ⟨hpos, ?_⟩
    rw [edge_cost_formula G y A hpos] at hineq
    have hR:=(div_le_div_iff₀ (mul_pos (by norm_num) (sq_pos_of_pos hposR)) hpR).1 hineq
    have hresult:(p:ℝ) * (edgeNumerator G y A:ℝ)≤
        2 * (k:ℝ) ^ 2 * (rationalValue y A:ℝ) ^ 2:=by nlinarith
    exact_mod_cast hresult

theorem candidate_complete (n r:ℕ) (A:Finset (Fin n)):
    A∈ candidates n r↔ A.card≤ r:=by
  constructor
  · intro h
    obtain ⟨j,hj,hm⟩:=List.mem_flatMap.mp h
    obtain ⟨l,hl,rfl⟩:=List.mem_map.mp hm
    have hsub:=(List.mem_sublistsLen.mp hl).1
    have hlen:=(List.mem_sublistsLen.mp hl).2
    have hnd:=hsub.nodup (List.nodup_finRange n)
    rw [List.toFinset_card_of_nodup hnd,hlen]
    have:=List.mem_range.mp hj
    omega
  · intro hA
    let l:=(List.finRange n).filter fun v => decide (v∈ A)
    have hsub:List.Sublist l (List.finRange n):=List.filter_sublist
    have hnd:l.Nodup:=hsub.nodup (List.nodup_finRange n)
    have heq:l.toFinset=A:=by ext v; simp [l]
    have hlen:l.length=A.card:=by rw [← List.toFinset_card_of_nodup hnd,heq]
    apply List.mem_flatMap.mpr
    refine ⟨A.card,List.mem_range.mpr (by omega), ?_⟩
    apply List.mem_map.mpr
    exact ⟨l,List.mem_sublistsLen.mpr ⟨hsub,hlen⟩,heq⟩

end Lax263307Proofs.RationalConditioning

end

section

namespace Lax808846Proofs.Imp

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

theorem Run.frame_var {B:ℕ} {c:Com} {σ σ':Env} {K:ℕ} (h:Run B c σ σ' K)
    (y:String) (hy:y∉ c.wvars):σ'.vars y=σ.vars y:=by
  obtain ⟨_,_,hbs⟩:=h.bigStep; exact hbs.vars_eq hy

end Lax808846Proofs.Reasoning

end

section

namespace Lax455465Proofs.RamRational

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamArithmetic

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

end Lax455465Proofs.RamRational

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

namespace Lax455465Proofs.RamLpRationalRead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open Lax109476.RationalEncoding

def sign (q:ℚ):ℕ:=if q.num < 0 then 1 else 0

theorem value_eq (q:ℚ):fractionValue (sign q) q.num.natAbs q.den=q:=by
  have hnum:(if q.num < 0 then -((q.num.natAbs:ℕ):ℚ) else ((q.num.natAbs:ℕ):ℚ))=(q.num:ℚ):=by
    generalize q.num=z
    cases z <;> simp
  by_cases h:q.num < 0
  · simp only [if_pos h] at hnum
    simpa only [fractionValue,sign,if_pos h,if_true,hnum] using q.num_div_den
  · simp only [if_neg h] at hnum
    simpa only [fractionValue,sign,if_neg h,show ¬(0:ℕ)=1 by decide,if_false,hnum] using q.num_div_den

def command:Com:=.seq (.assign "rat.s" (.get "vm.output" (.var "cert.cursor")))
  (.seq (.assign "rat.n" (.get "vm.output" (.add (.var "cert.cursor") (.lit 1))))
    (.seq (.assign "rat.d" (.get "vm.output" (.add (.var "cert.cursor") (.lit 2))))
      (.assign "cert.cursor" (.add (.var "cert.cursor") (.lit 3)))))

end Lax455465Proofs.RamLpRationalRead

end

section

namespace Lax263307Proofs.LightSeparators

open scoped NNReal NNRat
open Lax263307.GraphClasses Lax263307.EdgeSublinearSeparators
open Lax263307.PowerBagBounds Lax263307.VertexSplitting
open Lax263307.RepeatedCutAccounting Lax263307.Entropy
open Lax455465.ProductNetwork Lax455465.ConcurrentFlow Lax455465.RationalEncoding

theorem logFactor_upper (n:ℕ):logFactor n≤ (Nat.log2 n:ℝ) + 1:=by
  by_cases hn:n=0
  · simp [hn,logFactor]
  · have hp:=(Nat.lt_pow_succ_log_self Nat.one_lt_two n).le
    rw [← Nat.log2_eq_log_two] at hp
    have hpr:(n:ℝ)≤ (2:ℝ) ^ (Nat.log2 n + 1):=by exact_mod_cast hp
    have h:=Real.log_le_log (by exact_mod_cast (show 0 < n by omega)) hpr
    rw [Real.log_pow,Nat.cast_add,Nat.cast_one] at h
    exact (div_le_iff₀ (Real.log_pos (by norm_num))).mpr h

end Lax263307Proofs.LightSeparators

end

section

namespace Lax263307Proofs.ComputedSeparators

open scoped NNReal NNRat
open Lax263307.ComputedSeparators Lax263307.GraphClasses Lax263307.PowerBagBounds
open Lax263307.VertexSplitting Lax263307.Entropy Lax263307.RepeatedCutAccounting
open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax455465.ConcurrentFlow
open Lax263307Proofs.LightSeparators

def embedding {n:ℕ} (G:SimpleGraph (Fin n)) (R:Finset (Fin n)):restriction G R ↪g G where
  toFun:=label R
  inj':=(label R).injective
  map_rel_iff':=Iff.rfl

end Lax263307Proofs.ComputedSeparators

end

section

namespace Lax263307Proofs.AlgorithmParameters

open Lax263307.AlgorithmParameters

theorem sparsity_positive {a K B n D:ℕ} (hK:0 < K):0 < sparsity a K B n D:=by
  unfold sparsity targetThreshold
  positivity

theorem budgets {a K B n D k:ℕ} (hK:0 < K) (hB:0 < B)
    (hD:4≤ D) (large:cutoff a K B n D < k):
    0 < load B n D∧ 0 < sparsity a K B n D∧ 0 < level a K B n D∧
      0 < (1 / (D:ℝ))∧ (1 / (D:ℝ))≤ 1 / 4∧
      12 * (B:ℝ) * ((Nat.log2 (2 * n):ℝ) + 1)≤
        (1 / (D:ℝ)) * load B n D∧
      (sparsity a K B n D:ℝ) * ((Nat.log2 n:ℝ) + 1)≤ level a K B n D∧
      (K:ℝ) * ((load B n D:ℝ) + 1) ^ (4 * a + 2)≤ k∧
      (2 * K:ℝ) * ((load B n D:ℝ) + 1) ^ (4 * a + 2)≤ sparsity a K B n D:=by
  have hp:=sparsity_positive (a:=a) (B:=B) (n:=n) (D:=D) hK
  have hD':(0:ℝ) < D:=by exact_mod_cast (show 0 < D by omega)
  have hD4:(4:ℝ)≤ D:=by exact_mod_cast hD
  have ht:targetThreshold a K B n D≤ k:=
    (le_max_left _ _).trans large.le
  refine ⟨?_,hp, ?_,by positivity, ?_, ?_, ?_, ?_, ?_⟩
  · unfold load logarithm
    positivity
  · unfold level
    positivity
  · exact one_div_le_one_div_of_le (by norm_num) hD4
  · have heq:(1 / (D:ℝ)) * load B n D =
        12 * (B:ℝ) * ((Nat.log2 (2 * n):ℝ) + 1):=by
      simp only [load,logarithm,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one]
      field_simp
    exact heq.ge
  · simp [level,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  · exact_mod_cast ht
  · simp only [sparsity,targetThreshold,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one,
      Nat.cast_ofNat]
    ring_nf
    exact le_rfl

end Lax263307Proofs.AlgorithmParameters

end

section

namespace Lax263307Proofs.ConditionedCosts

open Lax263307.LinearRelaxation RelaxationAlgebra

theorem conditioning_invariants {n:ℕ} (G:SimpleGraph (Fin n)) (k r:ℕ)
    (y:MomentVector n r) (feasible:IsFeasible G k r y)
    (A:Finset (Fin n)) (size:A.card≤ r) (positive:0 < value y A):
    (∀ v,0≤ conditioned y A v∧ conditioned y A v≤ 1)∧
    (∑ v:Fin n,conditioned y A v)=k∧
    (∀ v∈ A,conditioned y A v=1)∧
    (∀ v,0 < conditioned y A v→ 0 < value y (insert v A)):=by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v
    have hsize:=insert_size A (show A.card≤ r + 1 by omega) v
    have hnonneg:0≤ value y (insert v A):=by
      rw [value_of_size y _ hsize]
      exact (feasible.bounds _).1
    exact ⟨div_nonneg hnonneg positive.le,
      (div_le_one positive).2 (feasible.monotone A (by omega) v)⟩
  · simp_rw [conditioned, ← Finset.sum_div]
    rw [feasible.mass A (by omega)]
    exact mul_div_cancel_right₀ _ (ne_of_gt positive)
  · intro v hv
    simp [conditioned,Finset.insert_eq_of_mem hv,ne_of_gt positive]
  · intro v hv
    exact (div_pos_iff_of_pos_right positive).1 hv

end Lax263307Proofs.ConditionedCosts

end

section

namespace Lax263307Proofs.ConditioningDistribution

open Lax263307.LinearRelaxation Lax263307.ConditioningDistribution RelaxationAlgebra

theorem distribution_identities {n:ℕ} (G:SimpleGraph (Fin n)) (k r:ℕ)
    (y:MomentVector n r) (feasible:IsFeasible G k r y)
    (A:Finset (Fin n)) (size:A.card < r) (positive:0 < value y A)
    (target_positive:0 < k):
    (∀ v,0≤ marginal y A k v)∧
    (∑ v:Fin n,marginal y A k v)=1∧
    (∀ u v,0≤ joint y A k u v)∧
    (∀ u v,joint y A k u v=joint y A k v u)∧
    (∀ v, (∑ u:Fin n,joint y A k u v)=marginal y A k v)∧
    (∀ u v,G.Adj u v→ joint y A k u v=0)∧
    (∀ u v,0 < marginal y A k v→
      marginal y (insert v A) k u=joint y A k u v / marginal y A k v):=by
  have hk:(0:ℝ) < k:=by exact_mod_cast target_positive
  have hk0:(k:ℝ) ≠ 0:=ne_of_gt hk
  have hA0:value y A ≠ 0:=ne_of_gt positive
  have invariants:=Lax263307Proofs.ConditionedCosts.conditioning_invariants
    G k r y feasible A (by omega) positive
  have hsize (v:Fin n):(insert v A).card≤ r + 1:=by
    have:=Finset.card_insert_le v A
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    exact div_nonneg (invariants.1 v).1 hk.le
  · simp_rw [marginal, ← Finset.sum_div]
    rw [invariants.2.1,div_self hk0]
  · intro u v
    have hnonneg:0≤ value y (insert u (insert v A)):=by
      rw [value_of_size y _ (insert_size _ (hsize v) u)]
      exact (feasible.bounds _).1
    exact div_nonneg hnonneg (mul_nonneg (sq_nonneg _) positive.le)
  · intro u v
    simp only [joint,Finset.insert_comm]
  · intro v
    simp_rw [joint, ← Finset.sum_div]
    rw [feasible.mass (insert v A) (hsize v)]
    dsimp [marginal,conditioned]
    field_simp
  · intro u v huv
    have hnot:¬G.IsIndepSet (↑(insert u (insert v A)):Set (Fin n)):=by
      intro hi
      exact hi (by simp) (by simp) huv.ne huv
    have hz:=feasible.vanishes
      ⟨insert u (insert v A),insert_size _ (hsize v) u⟩ hnot
    rw [joint,value_of_size y _ (insert_size _ (hsize v) u),hz,zero_div]
  · intro u v hv
    have hv0:value y (insert v A) ≠ 0:=by
      have hcost:0 < conditioned y A v:=(div_pos_iff_of_pos_right hk).1 hv
      exact ne_of_gt (invariants.2.2.2 v hcost)
    dsimp [marginal,conditioned,joint]
    field_simp

end Lax263307Proofs.ConditioningDistribution

end

section

namespace Lax263307Proofs.EntropyBounds

open Lax263307.Entropy EntropyAlgebra

theorem entropy_bounds {n:ℕ} (π:Fin n→ ℝ) (probability:IsProbability π):
    0≤ entropy π∧ entropy π≤ Real.logb 2 n:=by
  constructor
  · exact div_nonneg (natural_entropy_nonneg π probability) log_two_pos.le
  · exact div_le_div_of_nonneg_right (natural_entropy_le_log π probability) log_two_pos.le

end Lax263307Proofs.EntropyBounds

end

section

namespace Lax263307Proofs.EntropyGap

open Lax263307.Entropy EntropyAlgebra

theorem joint_entry_le {n:ℕ} (π:Fin n→ ℝ) (q:Fin n→ Fin n→ ℝ)
    (hq:∀ u v,0≤ q u v) (hm:∀ v, (∑ u,q u v)=π v) (u v:Fin n):
    q u v≤ π v:=by
  rw [← hm v]
  exact Finset.single_le_sum (fun i _ => hq i v) (Finset.mem_univ u)

theorem row_marginal {n:ℕ} (π:Fin n→ ℝ) (q:Fin n→ Fin n→ ℝ)
    (hs:∀ u v,q u v=q v u) (hm:∀ v, (∑ u,q u v)=π v) (u:Fin n):
    (∑ v,q u v)=π u:=by
  simp_rw [hs u]
  exact hm u

theorem weighted_conditional_entropy {n:ℕ} (π:Fin n→ ℝ) (q:Fin n→ Fin n→ ℝ)
    (hπ:IsProbability π) (hq:∀ u v,0≤ q u v)
    (hm:∀ v, (∑ u,q u v)=π v):
    (∑ v,π v * naturalEntropy (fun u => q u v / π v)) =
      (∑ v, ∑ u,Real.negMulLog (q u v)) - naturalEntropy π:=by
  have hpoint (u v:Fin n):
      π v * Real.negMulLog (q u v / π v) =
        Real.negMulLog (q u v) + q u v * Real.log (π v):=by
    rcases eq_or_lt_of_le (hπ.1 v) with hv | hv
    · have hzero:q u v=0:=le_antisymm
        ((joint_entry_le π q hq hm u v).trans_eq hv.symm) (hq u v)
      simp [← hv,hzero]
    · exact scaled_negMulLog_div _ _ hv
  simp_rw [naturalEntropy,Finset.mul_sum,hpoint,Finset.sum_add_distrib,
    ← Finset.sum_mul,hm]
  simp [Real.negMulLog,Finset.sum_neg_distrib,sub_eq_add_neg]

theorem natural_gap_bound {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (π:Fin n→ ℝ) (q:Fin n→ Fin n→ ℝ)
    (hπ:IsProbability π) (hq:∀ u v,0≤ q u v)
    (hs:∀ u v,q u v=q v u) (hm:∀ v, (∑ u,q u v)=π v)
    (he:∀ u v,G.Adj u v→ q u v=0):
    adjacencyMass G π≤ naturalEntropy π -
      ∑ v,π v * naturalEntropy (fun u => q u v / π v):=by
  let cost:=fun u v => -Real.negMulLog (q u v) -
    q u v * Real.log (π u) - q u v * Real.log (π v)
  have hpoint (u v:Fin n):
      q u v - π u * π v + (if G.Adj u v then π u * π v else 0)≤ cost u v:=by
    by_cases hedge:G.Adj u v
    · simp [cost,hedge,he u v hedge]
    · simp only [if_neg hedge,add_zero]
      rcases eq_or_lt_of_le (hq u v) with hzero | hpos
      · simp only [← hzero,Real.negMulLog_zero,zero_mul,sub_zero,zero_sub,cost]
        simpa using neg_nonpos.mpr (mul_nonneg (hπ.1 u) (hπ.1 v))
      · have hv:=lt_of_lt_of_le hpos (joint_entry_le π q hq hm u v)
        have hu:=lt_of_lt_of_le (hpos.trans_eq (hs u v)) (joint_entry_le π q hq hm v u)
        exact relative_term_bound _ _ _ hpos hu hv
  have htotal:(∑ v, ∑ u,q u v)=1:=by simp_rw [hm]; exact hπ.2
  have hproduct:(∑ v, ∑ u,π u * π v)=1:=by
    simp_rw [← Finset.sum_mul,hπ.2,one_mul]
    exact hπ.2
  have hcrossV:(∑ v, ∑ u,q u v * Real.log (π v))=-naturalEntropy π:=by
    simp only [← Finset.sum_mul,hm,naturalEntropy,Real.negMulLog,
      neg_mul,Finset.sum_neg_distrib,neg_neg]
  have hcrossU:(∑ v, ∑ u,q u v * Real.log (π u))=-naturalEntropy π:=by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul,row_marginal π q hs hm,naturalEntropy,
      Real.negMulLog,neg_mul,Finset.sum_neg_distrib,neg_neg]
  have hsum:=Finset.sum_le_sum (s:=Finset.univ) fun v _ =>
    Finset.sum_le_sum (s:=Finset.univ) fun u _ => hpoint u v
  have hadj:(∑ v, ∑ u,if G.Adj u v then π u * π v else 0)=adjacencyMass G π:=by
    rw [Finset.sum_comm]
    rfl
  simp_rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,cost,
    Finset.sum_sub_distrib,Finset.sum_neg_distrib] at hsum
  rw [htotal,hproduct,hadj,hcrossU,hcrossV] at hsum
  rw [weighted_conditional_entropy π q hπ hq hm]
  linarith

theorem average_entropy_gap {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (π:Fin n→ ℝ) (q:Fin n→ Fin n→ ℝ)
    (probability:IsProbability π) (nonnegative:∀ u v,0≤ q u v)
    (symmetric:∀ u v,q u v=q v u)
    (marginals:∀ v, (∑ u,q u v)=π v)
    (edge_zero:∀ u v,G.Adj u v→ q u v=0):
    adjacencyMass G π≤ entropy π - ∑ v,π v * entropy (fun u => q u v / π v):=by
  have hgap:=natural_gap_bound G π q probability nonnegative symmetric marginals edge_zero
  have hmass:0≤ adjacencyMass G π:=by
    apply Finset.sum_nonneg
    intro u _
    apply Finset.sum_nonneg
    intro v _
    split_ifs
    · exact mul_nonneg (probability.1 u) (probability.1 v)
    · exact le_rfl
  have hm:adjacencyMass G π * Real.log 2≤ adjacencyMass G π:=by
    nlinarith [log_two_le_one]
  simp_rw [entropy, ← mul_div_assoc, ← Finset.sum_div, ← sub_div]
  exact (le_div_iff₀ log_two_pos).2 (hm.trans hgap)

end Lax263307Proofs.EntropyGap

end

section

namespace Lax263307Proofs.ConditioningExistence

open Lax263307.LinearRelaxation Lax263307.ConditioningDistribution Lax263307.Entropy
open EntropyAlgebra RelaxationAlgebra

theorem marginal_probability {n:ℕ} (G:SimpleGraph (Fin n)) (k r:ℕ)
    (y:MomentVector n r) (hy:IsFeasible G k r y)
    (A:Finset (Fin n)) (hA:A.card≤ r) (hpos:0 < value y A) (hk:0 < k):
    IsProbability (marginal y A k):=by
  have hkR:(0:ℝ) < k:=by exact_mod_cast hk
  have h:=Lax263307Proofs.ConditionedCosts.conditioning_invariants G k r y hy A hA hpos
  refine ⟨fun v => div_nonneg (h.1 v).1 hkR.le, ?_⟩
  simp_rw [marginal, ← Finset.sum_div]
  rw [h.2.1,div_self (ne_of_gt hkR)]

end Lax263307Proofs.ConditioningExistence

end

section

namespace Lax263307Proofs.HeavyConditioning

open Lax263307.Entropy Lax263307.HeavyConditioning

theorem heavy_weight_decrease {n:ℕ} (π f:Fin n→ ℝ) (probability:IsProbability π)
    (nonnegative:∀ v,0 < π v→ 0≤ f v) (H L p:ℝ)
    (hH:0≤ H) (hHL:H≤ L) (hL:0 < L) (hp:0 < p) (hn:0 < n)
    (average:(∑ v,π v * f v) < H - 2 / p):
    ∃ v:Fin n,1 / (2 * (n:ℝ) * p * L)≤ π v∧ f v < H - 1 / p:=by
  classical
  let τ:ℝ:=1 / (2 * (n:ℝ) * p * L)
  have hn':(0:ℝ) < n:=by exact_mod_cast hn
  have hτ:0 < τ:=by dsimp [τ]; positivity
  by_contra hnone
  push Not at hnone
  have each (v:Fin n):π v * (H - f v)≤ π v / p + τ * L:=by
    by_cases hv:τ≤ π v
    · have hfv:=hnone v hv
      have hprod:=mul_le_mul_of_nonneg_left (show H - f v≤ 1 / p by linarith) (probability.1 v)
      have hτL:0≤ τ * L:=mul_nonneg hτ.le hL.le
      simpa only [mul_one_div] using hprod.trans (le_add_of_nonneg_right hτL)
    · have hsmall:π v≤ τ:=(not_le.mp hv).le
      have hprod:π v * (H - f v)≤ π v * H:=by
        by_cases hpos:0 < π v
        · exact mul_le_mul_of_nonneg_left (by linarith [nonnegative v hpos]) (probability.1 v)
        · have hz:π v=0:=le_antisymm (not_lt.mp hpos) (probability.1 v)
          simp [hz]
      have hmul:π v * H≤ τ * L:=
        (mul_le_mul_of_nonneg_right hsmall hH).trans (mul_le_mul_of_nonneg_left hHL hτ.le)
      exact (hprod.trans hmul).trans (le_add_of_nonneg_left (div_nonneg (probability.1 v) hp.le))
  have hsum:=Finset.sum_le_sum (fun v (_:v∈ (Finset.univ:Finset (Fin n))) => each v)
  simp only [Finset.sum_sub_distrib,mul_sub, ← Finset.sum_mul,Finset.sum_add_distrib,
    ← Finset.sum_div,probability.2,one_mul,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul] at hsum
  have hτeq:(n:ℝ) * τ * L=1 / (2 * p):=by
    dsimp [τ]
    field_simp
  rw [hτeq] at hsum
  have hfrac:1 / p + 1 / (2 * p) < 2 / p:=by
    field_simp
    nlinarith
  linarith

open Lax263307.LinearRelaxation Lax263307.ConditioningDistribution
open Lax263307Proofs.EntropyDecrease Lax263307Proofs.ConditioningExistence

theorem heavy_entropy_decrease {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k r p:ℕ) (y:MomentVector n r) (feasible:IsFeasible G k r y)
    (A:Finset (Fin n)) (size:A.card < r) (positive:0 < value y A)
    (target_positive:0 < k) (threshold_positive:0 < p) (order_positive:0 < n)
    (expensive:(k:ℝ) ^ 2 / p < edgeCost G (conditioned y A)):
    ∃ v:Fin n,probabilityFloor n p≤ marginal y A k v∧
      entropy (marginal y (insert v A) k) < entropy (marginal y A k) - 1 / p:=by
  have hk:(0:ℝ) < k:=by exact_mod_cast target_positive
  have hp:(0:ℝ) < p:=by exact_mod_cast threshold_positive
  obtain ⟨hπ,hsum,hq,hsym,hmarg,hedge,hcond⟩:=
    Lax263307Proofs.ConditioningDistribution.distribution_identities
      G k r y feasible A size positive target_positive
  have hprob:IsProbability (marginal y A k):= ⟨hπ,hsum⟩
  have hgap:=Lax263307Proofs.EntropyGap.average_entropy_gap
    G (marginal y A k) (joint y A k) hprob hq hsym hmarg hedge
  have hscaled:adjacencyMass G (marginal y A k) =
      adjacencyMass G (conditioned y A) / (k:ℝ) ^ 2:=
    adjacencyMass_div G (conditioned y A) k (ne_of_gt hk)
  have hmass:(2:ℝ) / p < adjacencyMass G (marginal y A k):=by
    rw [hscaled]
    apply (div_lt_div_iff₀ hp (sq_pos_of_pos hk)).2
    have h:=(div_lt_iff₀ hp).1 expensive
    unfold edgeCost at h
    nlinarith
  have havg:(∑ v,marginal y A k v * entropy (fun u => joint y A k u v / marginal y A k v)) <
      entropy (marginal y A k) - 2 / p:=by linarith
  have hnonnegative (v:Fin n) (hv:0 < marginal y A k v):
      0≤ entropy (fun u => joint y A k u v / marginal y A k v):=by
    have hcost:0 < conditioned y A v:=(div_pos_iff_of_pos_right hk).mp hv
    have hnext:=(Lax263307Proofs.ConditionedCosts.conditioning_invariants
      G k r y feasible A size.le positive).2.2.2 v hcost
    have hcard:(insert v A).card≤ r:=(Finset.card_insert_le v A).trans (by omega)
    have h:=(Lax263307Proofs.EntropyBounds.entropy_bounds _
      (marginal_probability G k r y feasible (insert v A) hcard hnext target_positive)).1
    have heq:marginal y (insert v A) k=fun u => joint y A k u v / marginal y A k v:=
      funext (fun u => hcond u v hv)
    rwa [heq] at h
  have hb:=Lax263307Proofs.EntropyBounds.entropy_bounds _ hprob
  have hL:Real.logb 2 n≤ (Nat.log2 n:ℝ) + 1:=
    Lax263307Proofs.LightSeparators.logFactor_upper n
  obtain ⟨v,hv,hdrop⟩:=heavy_weight_decrease (marginal y A k)
    (fun v => entropy (fun u => joint y A k u v / marginal y A k v)) hprob hnonnegative
    (entropy (marginal y A k)) ((Nat.log2 n:ℝ) + 1) p hb.1 (hb.2.trans hL)
    (by positivity) hp order_positive havg
  have hfloor:0 < probabilityFloor n p:=by unfold probabilityFloor; positivity
  have hvpos:0 < marginal y A k v:=hfloor.trans_le hv
  refine ⟨v,hv, ?_⟩
  have heq:marginal y (insert v A) k=fun u => joint y A k u v / marginal y A k v:=
    funext (fun u => hcond u v hvpos)
  rwa [heq]

theorem heavy_low_edge_cost {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k r p:ℕ) (y:MomentVector n r) (feasible:IsFeasible G k r y)
    (order_positive:0 < n) (target_positive:0 < k)
    (level_positive:0 < r) (threshold_positive:0 < p)
    (budget:(p:ℝ) * ((Nat.log2 n:ℝ) + 1)≤ r):
    ∃ A:Finset (Fin n),A.card≤ r∧ probabilityFloor n p ^ r≤ value y A∧
      0 < value y A∧ (∀ v,0≤ conditioned y A v∧ conditioned y A v≤ 1)∧
      (∑ v,conditioned y A v)=k∧ edgeCost G (conditioned y A)≤ (k:ℝ) ^ 2 / p:=by
  classical
  have hn:(0:ℝ) < n:=by exact_mod_cast order_positive
  have hk:(0:ℝ) < k:=by exact_mod_cast target_positive
  have hp:(0:ℝ) < p:=by exact_mod_cast threshold_positive
  let τ:=probabilityFloor n p
  have hτ:0 < τ:=by dsimp [τ,probabilityFloor]; positivity
  have hτ1:τ≤ 1:=by
    have hn1:(1:ℝ)≤ n:=by exact_mod_cast order_positive
    have hp1:(1:ℝ)≤ p:=by exact_mod_cast threshold_positive
    dsimp [τ,probabilityFloor]
    apply (div_le_one (by positivity)).mpr
    have hL:(1:ℝ)≤ (Nat.log2 n:ℝ) + 1:=le_add_of_nonneg_left (Nat.cast_nonneg _)
    nlinarith [mul_le_mul hn1 hp1 (by positivity) (by norm_num)]
  have hzero:value y (∅:Finset (Fin n))=1:=feasible.normalized
  have hprob0:=marginal_probability G k r y feasible ∅ (by simp) (by rw [hzero]; norm_num) target_positive
  have hbounds0:=Lax263307Proofs.EntropyBounds.entropy_bounds _ hprob0
  have hL:entropy (marginal y ∅ k)≤ (Nat.log2 n:ℝ) + 1:=
    hbounds0.2.trans (Lax263307Proofs.LightSeparators.logFactor_upper n)
  suffices hgood:∃ A:Finset (Fin n),A.card≤ r∧ τ ^ r≤ value y A∧
      0 < value y A∧ edgeCost G (conditioned y A)≤ (k:ℝ) ^ 2 / p by
    obtain ⟨A,hA,hval,hpos,he⟩:=hgood
    have h:=Lax263307Proofs.ConditionedCosts.conditioning_invariants G k r y feasible A hA hpos
    exact ⟨A,hA,hval,hpos,h.1,h.2.1,he⟩
  by_contra hnone
  push Not at hnone
  have hstep:∀ t:ℕ,t≤ r→ ∃ A:Finset (Fin n),A.card≤ t∧ τ ^ t≤ value y A∧
      0 < value y A∧ entropy (marginal y A k)≤ entropy (marginal y ∅ k) - (t:ℝ) / p∧
      (0 < t→ entropy (marginal y A k) < entropy (marginal y ∅ k) - (t:ℝ) / p):=by
    intro t
    induction t with
    | zero =>
      intro _
      exact ⟨∅,by simp,by simp [hzero],by rw [hzero]; norm_num,by simp,by simp⟩
    | succ t ih =>
      intro ht
      obtain ⟨A,hA,hval,hpos,hH,_⟩:=ih (by omega)
      have hvalr:τ ^ r≤ value y A:=
        (pow_le_pow_of_le_one hτ.le hτ1 (by omega:t≤ r)).trans hval
      obtain ⟨v,hv,hdrop⟩:=Lax263307Proofs.HeavyConditioning.heavy_entropy_decrease G k r p y feasible A (by omega) hpos
        target_positive threshold_positive order_positive (hnone A (by omega) hvalr hpos)
      have hvpos:0 < marginal y A k v:=hτ.trans_le hv
      have hcost:0 < conditioned y A v:=(div_pos_iff_of_pos_right hk).mp hvpos
      have hnext:=(Lax263307Proofs.ConditionedCosts.conditioning_invariants
        G k r y feasible A (by omega) hpos).2.2.2 v hcost
      have heq:value y (insert v A)=(k:ℝ) * marginal y A k v * value y A:=by
        unfold marginal conditioned
        field_simp
      have hk1:(1:ℝ)≤ k:=by exact_mod_cast target_positive
      have hprod:τ * value y A≤ value y (insert v A):=by
        rw [heq]
        have hkmarg:τ≤ (k:ℝ) * marginal y A k v:=
          hv.trans (by nlinarith)
        exact mul_le_mul_of_nonneg_right hkmarg hpos.le
      have hnextval:τ ^ (t + 1)≤ value y (insert v A):=by
        rw [pow_succ]
        exact (mul_le_mul_of_nonneg_right hval hτ.le).trans (by simpa [mul_comm] using hprod)
      have hcard:(insert v A).card≤ t + 1:=(Finset.card_insert_le v A).trans (by omega)
      have hstrict:entropy (marginal y (insert v A) k) <
          entropy (marginal y ∅ k) - ((t + 1:ℕ):ℝ) / p:=by
        push_cast
        rw [add_div]
        linarith
      exact ⟨insert v A,hcard,hnextval,hnext,hstrict.le,fun _ => hstrict⟩
  obtain ⟨A,hA,_hval,hpos,_hH,hstrict⟩:=hstep r le_rfl
  have hnonnegative:=(Lax263307Proofs.EntropyBounds.entropy_bounds _
    (marginal_probability G k r y feasible A hA hpos target_positive)).1
  have hbudget:(Nat.log2 n:ℝ) + 1≤ (r:ℝ) / p:=(le_div_iff₀ hp).mpr (by nlinarith [budget])
  have hfinal:=hstrict level_positive
  linarith

end Lax263307Proofs.HeavyConditioning

end

section

namespace Lax263307Proofs.HeavyRationalConditioning

open Lax263307.LinearRelaxation Lax263307.Entropy Lax263307.RationalConditioning
open Lax263307.HeavyConditioning Lax263307.HeavyRationalConditioning

theorem floor_cast (n p:ℕ):(rationalFloor n p:ℝ)=probabilityFloor n p:=by
  unfold rationalFloor probabilityFloor
  push_cast
  rfl

theorem heavy_passes_iff {n r:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k p:ℕ) (y:RationalVector n r) (A:Finset (Fin n)) (hp:0 < p):
    HeavyPasses G k p y A↔ 0 < value (realVector y) A∧
      edgeCost G (conditioned (realVector y) A)≤ (k:ℝ) ^ 2 / p∧
      probabilityFloor n p ^ r≤ value (realVector y) A:=by
  have hfloor:rationalFloor n p ^ r≤ rationalValue y A↔
      probabilityFloor n p ^ r≤ value (realVector y) A:=by
    rw [Lax263307Proofs.RationalConditioning.value_cast, ← floor_cast]
    norm_cast
  rw [HeavyPasses,Lax263307Proofs.RationalConditioning.passes_iff G k p y A hp,hfloor]
  tauto

theorem search_correct {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k r p:ℕ) (y:RationalVector n r) (feasible:IsFeasible G k r (realVector y))
    (order_positive:0 < n) (target_positive:0 < k)
    (level_positive:0 < r) (threshold_positive:0 < p)
    (budget:(p:ℝ) * ((Nat.log2 n:ℝ) + 1)≤ r):
    ∃ A:Finset (Fin n),findHeavyConditioning G k p y=some A∧ A.card≤ r∧
      probabilityFloor n p ^ r≤ value (realVector y) A∧ 0 < value (realVector y) A∧
      (∀ v,0≤ conditioned (realVector y) A v∧ conditioned (realVector y) A v≤ 1)∧
      (∑ v,conditioned (realVector y) A v)=k∧
      edgeCost G (conditioned (realVector y) A)≤ (k:ℝ) ^ 2 / p:=by
  obtain ⟨B,hB,hfloorB,hposB,_,_,heB⟩:=Lax263307Proofs.HeavyConditioning.heavy_low_edge_cost
    G k r p (realVector y) feasible order_positive target_positive level_positive threshold_positive budget
  have hpassB:=(heavy_passes_iff G k p y B threshold_positive).mpr ⟨hposB,heB,hfloorB⟩
  have hmemB:=(Lax263307Proofs.RationalConditioning.candidate_complete n r B).mpr hB
  cases hsearch:findHeavyConditioning G k p y with
  | none =>
    have hnone:=List.find?_eq_none.mp hsearch B hmemB
    simp [hpassB] at hnone
  | some A =>
    have hpass:HeavyPasses G k p y A:=by
      have h:=List.find?_some hsearch
      simpa using h
    have hA:=(Lax263307Proofs.RationalConditioning.candidate_complete n r A).mp
      (List.mem_of_find?_eq_some hsearch)
    have htest:=(heavy_passes_iff G k p y A threshold_positive).mp hpass
    have h:=Lax263307Proofs.ConditionedCosts.conditioning_invariants
      G k r (realVector y) feasible A hA htest.1
    exact ⟨A,rfl,hA,htest.2.2,htest.1,h.1,h.2.1,htest.2.1⟩

end Lax263307Proofs.HeavyRationalConditioning

end

section

namespace Lax263307Proofs.NearOracle

open scoped NNRat
open Lax263307.NearOracle Lax263307.GraphClasses Lax263307.PowerBagBounds
open Lax263307.LinearRelaxation Lax263307.RationalConditioning
open Lax263307.AlgorithmParameters Lax263307.ComputedSeparators
open Lax263307.RepeatedCutAccounting

theorem costs_cast {n r:ℕ} (y:RationalVector n r) (A:Finset (Fin n))
    (nonnegative:∀ v,0≤ conditioned (realVector y) A v) (v:Fin n):
    (costs y A v:ℝ)=conditioned (realVector y) A v:=by
  have heq:((rationalValue y (insert v A) / rationalValue y A:ℚ):ℝ) =
      conditioned (realVector y) A v:=by
    simp only [conditioned,Lax263307Proofs.RationalConditioning.value_cast,Rat.cast_div]
  have hq:(0:ℚ)≤ rationalValue y (insert v A) / rationalValue y A:=by
    exact_mod_cast (heq.symm ▸ nonnegative v)
  change ((max 0 (rationalValue y (insert v A) / rationalValue y A):ℚ):ℝ)=_
  rw [max_eq_right hq]
  exact heq

end Lax263307Proofs.NearOracle

end

section

namespace Lax263307Proofs.NativeSumHeight

open Lax455465Proofs.RamRational Lax455465Proofs.RamLpRationalRead
open NativeSignedArithmetic

theorem multiply (A C:ℕ) (a b:ℚ) (ha:Bounded A a) (hb:Bounded C b):
    Bounded (A*C) (a*b):=by
  have hprod (s t u v d e:ℕ) (hs:s≤1) (ht:t≤1):
      fractionValue (if s=t then 0 else 1) (u*v) (d*e)=fractionValue s u d*fractionValue t v e:=by
    have hs':s=0∨ s=1:=by omega
    have ht':t=0∨ t=1:=by omega
    rcases hs' with rfl | rfl <;> rcases ht' with rfl | rfl <;>
      norm_num [fractionValue,Nat.cast_mul] <;> ring
  have hs (q:ℚ):sign q≤1:=by unfold sign; split_ifs <;> omega
  have he:=hprod (sign a) (sign b) a.num.natAbs b.num.natAbs a.den b.den (hs a) (hs b)
  rw [value_eq,value_eq] at he
  have hnd:=fractionValue_num_den (if sign a=sign b then 0 else 1)
    (a.num.natAbs*b.num.natAbs) (a.den*b.den) (Nat.mul_pos a.den_pos b.den_pos)
  rw [he] at hnd
  exact ⟨hnd.1.trans_le ((Nat.div_le_self _ _).trans (Nat.mul_le_mul ha.1 hb.1)),
    hnd.2.trans_le ((Nat.div_le_self _ _).trans (Nat.mul_le_mul ha.2 hb.2))⟩

end Lax263307Proofs.NativeSumHeight

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

theorem prefix_succ {n:ℕ} (I:Finset (Fin n)) (i:ℕ) (hi:i< n):
    initialSet I (i+1)=if (⟨i,hi⟩:Fin n)∈I then insert ⟨i,hi⟩ (initialSet I i) else initialSet I i:=by
  ext v
  by_cases hv:v.val=i
  · have he:v=⟨i,hi⟩:=Fin.ext hv
    subst v
    by_cases hm:(⟨i,hi⟩:Fin n)∈I <;> simp [initialSet,hm]
  · have he:v≠⟨i,hi⟩:=fun h => hv (congrArg Fin.val h)
    by_cases hm:(⟨i,hi⟩:Fin n)∈I <;> simp [hm,initialSet,he] <;> omega

end Lax263307Proofs.NativeMasks

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeMaskUnpack

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax263307.WeightedIndependentSet
open NativeMasks

theorem card_bound {n:ℕ} (I:Finset (Fin n)):I.card≤ n:=by
  simpa using Finset.card_le_univ I

end Lax263307Proofs.NativeMaskUnpack

end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.NativePositiveQuotient

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamRational
open NativeSignedArithmetic

theorem inverse_bounded (M:ℕ) (q:ℚ) (hM:1≤ M) (hq:Bounded M q):Bounded M q⁻¹:=by
  constructor
  · simp only [Rat.num_inv,Int.natAbs_mul,Int.natAbs_natCast]
    have hs:q.num.sign.natAbs≤1:=by
      rcases lt_trichotomy q.num 0 with h | h | h
      · simp [Int.sign_eq_neg_one_of_neg h]
      · simp [h]
      · simp [Int.sign_eq_one_of_pos h]
    exact (Nat.mul_le_mul_right q.den hs).trans (by simpa using hq.2)
  · rw [Rat.den_inv]
    split_ifs <;> first | exact hM | exact hq.1

theorem positive_bounded (M:ℕ) (q:ℚ) (hM:1≤ M) (hq:Bounded M q):
    Bounded M (max 0 q):=by
  rcases le_total q 0 with h | h
  · simp only [max_eq_left h]
    exact ⟨by simp,by simpa using hM⟩
  · simpa only [max_eq_right h] using hq

theorem height (M:ℕ) (a b:ℚ) (hM:1≤ M) (ha:Bounded M a) (hb:Bounded M b):
    Bounded (M^2) (max 0 (a/b)):=by
  apply positive_bounded (M^2) (a/b) (by nlinarith)
  simpa only [div_eq_mul_inv,pow_two] using NativeSumHeight.multiply M M a b⁻¹ ha (inverse_bounded M b hM hb)

end Lax263307Proofs.NativePositiveQuotient

end

section

namespace Lax263307Proofs.NativeShoreMasks

open Lax263307 ComputedSeparators VertexSplitting

def partialMask {r n:ℕ} (f:Fin r→ Fin n) (S:Finset (Fin r)) (i:ℕ):ℕ:=
  NativeMasks.mask ((NativeMasks.initialSet S i).image f)

theorem step {r n:ℕ} (f:Fin r→ Fin n) (S:Finset (Fin r)) (i:Fin r):
    Nat.lor (partialMask f S i.val) ((if i∈S then 1 else 0)*2^(f i).val)=partialMask f S (i.val+1):=by
  simp only [partialMask]
  rw [NativeMasks.prefix_succ S i.val i.isLt]
  by_cases h:i∈S
  · simp only [h,if_true,one_mul,Finset.image_insert,NativeMasks.mask_insert]
  · simp [h]

end Lax263307Proofs.NativeShoreMasks

end

section

namespace Lax263307Proofs.NativeStateBounds

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem set_var {B:ℕ} {σ:Env} (hd:Bounded B σ) (s:String) (v:ℕ) (hv:v< B):
    Bounded B (σ.setVar s v):=by
  refine ⟨?_,hd.2.1,hd.2.2⟩
  intro t
  simp only [vars_setVar]
  split_ifs <;> first | exact hv | exact hd.1 t

theorem set_arr {B:ℕ} {σ:Env} (hd:Bounded B σ) (a:String) (i v:ℕ) (hv:v< B):
    Bounded B (σ.setArr a i v):=by
  refine ⟨hd.1,?_,hd.2.2⟩
  intro b z hz
  simp only [arrs_setArr] at hz
  split_ifs at hz
  · rcases List.mem_or_eq_of_mem_set hz with hz | rfl
    · exact hd.2.1 a z hz
    · exact hv
  · exact hd.2.1 b z hz

theorem big_step {B:ℕ} {c:Com} {σ τ:Env} {K:ℕ} (rr:BigStepB B c σ τ K)
    (hd:Bounded B σ):Bounded B τ:=by
  induction rr with
  | skip => exact hd
  | assign he => exact set_var hd _ _ (Expr.lt_of_evalB he)
  | store hi he hk => exact set_arr hd _ _ _ (Expr.lt_of_evalB he)
  | seq r1 r2 ih1 ih2 => exact ih2 (ih1 hd)
  | ite_true hc rr ih => exact ih hd
  | ite_false hc rr ih => exact ih hd
  | while_true hc r1 r2 ih1 ih2 => exact ih2 (ih1 hd)
  | while_false hc => exact hd
  | read hh =>
    rename_i σ0 s v rest
    have hv:=hd.2.2 _ (by rw [hh]; exact List.mem_cons_self)
    have hs:=set_var hd s v hv
    refine ⟨hs.1,hs.2.1,?_⟩
    intro z hz
    exact hd.2.2 z (by rw [hh]; exact List.mem_cons_of_mem _ hz)
  | write he => exact ⟨hd.1,hd.2.1,hd.2.2⟩

theorem run {B:ℕ} {c:Com} {σ τ:Env} {K:ℕ} (rr:Run B c σ τ K)
    (hd:Bounded B σ):Bounded B τ:=by
  obtain ⟨_,_,rr⟩:=rr
  exact big_step rr hd

end Lax263307Proofs.NativeStateBounds

end

section

namespace Lax263307Proofs.NativeFrameBuffers

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

theorem words_length (names:List String) (S:ℕ) (σ:Env)
    (hS:∀ a∈names,(σ.arrs a).length=S):(words names σ).length=S*names.length:=by
  induction names with
  | nil => simp [words]
  | cons a as ih =>
    have hi:=ih (fun b hb => hS b (List.mem_cons_of_mem a hb))
    change (List.flatMap σ.arrs as).length=S*as.length at hi
    simp only [words,List.flatMap_cons,List.length_append,List.length_cons]
    rw [hS a (by simp),hi]
    nlinarith only []

end Lax263307Proofs.NativeFrameBuffers

end

section

namespace Lax263307Proofs.NativeFrameScalars

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

theorem save_variable (names:List String) (s:String) (hs:s≠"stack.words"):s∉(save names).wvars:=by
  induction names with
  | nil => simp [save,Com.wvars]
  | cons t ts ih => simp [save,Com.wvars,RamWordBuffer.append,hs,ih]

end Lax263307Proofs.NativeFrameScalars

end

section

namespace Lax263307Proofs.NativeRecursionFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

theorem buffers_variable (names:List String) (s:String)
    (hs:s∉["stack.i","stack.copy.length","stack.words"]):s∉(NativeFrameBuffers.save names).wvars:=by
  induction names with
  | nil => simp [NativeFrameBuffers.save,Com.wvars]
  | cons a as ih =>
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hs
    simp [NativeFrameBuffers.save,NativeBlockAppend.command,NativeBlockAppend.step,RamWordBuffer.append,
      Com.wvars,hs.1,hs.2.1,hs.2.2,ih]

end Lax263307Proofs.NativeRecursionFrame

end

section

namespace Lax263307Proofs.NativeChildCall

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

theorem save_variable (arrays scalars:List String) (s:String)
    (hs:s∉["stack.i","stack.copy.length","stack.words"]):
    s∉(NativeRecursionFrame.save arrays scalars).wvars:=by
  have hw:s≠"stack.words" :=fun h => hs (by simp [h])
  simpa only [NativeRecursionFrame.save,Com.wvars,List.mem_append,not_or] using
    And.intro (NativeRecursionFrame.buffers_variable arrays s hs) (NativeFrameScalars.save_variable scalars s hw)

end Lax263307Proofs.NativeChildCall

end

section

namespace Lax263307Proofs.NativeMachineSegment

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NativeMachineTrace

theorem phase {B K:ℕ} {cases:List Com} {σ τ:Env}
    (running:σ.vars "machine.running"=1) (j:Fin cases.length)
    (phase:σ.vars "machine.phase"=j.val) (rr:Run B cases[j.val] σ τ K):
    Segment B cases 1 K σ τ:=by
  simpa only [Nat.zero_add,Nat.add_zero] using Segment.step running j phase rr (Segment.nil τ)

end Lax263307Proofs.NativeMachineSegment

end

section

namespace Lax263307Proofs.NativeMachineFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NativeMachineSegment

theorem array_length {B steps total:ℕ} {cases:List Com} {σ τ:Env}
    (trace:Segment B cases steps total σ τ) (a:String):(τ.arrs a).length=(σ.arrs a).length:=by
  induction trace with
  | nil => rfl
  | step h j hj rr rest ih =>
    exact ih.trans (Lax455465Proofs.RamFrames.run_array_length rr a)

theorem single_run {B total:ℕ} {cases:List Com} {σ τ:Env}
    (trace:Segment B cases 1 total σ τ) (j:Fin cases.length)
    (hp:σ.vars "machine.phase"=j.val):Run B cases[j.val] σ τ total:=by
  cases trace with
  | step hr i hi rr rest =>
    cases rest with
    | nil =>
      have he:i=j:=Fin.ext (hi.symm.trans hp)
      subst i
      simpa only [Nat.add_zero] using rr

end Lax263307Proofs.NativeMachineFrame

end

section

namespace Lax263307Proofs.NativeMachineBounds

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning NativeMachineSegment

theorem state {B steps total:ℕ} {phases:List Com} {σ τ:Env}
    (trace:Segment B phases steps total σ τ) (hσ:NativeStateBounds.Bounded B σ):
    NativeStateBounds.Bounded B τ:=by
  induction trace with
  | nil => exact hσ
  | step hr j hj rr rest ih => exact ih (NativeStateBounds.run rr hσ)

end Lax263307Proofs.NativeMachineBounds

end

section

namespace Lax263307Proofs.NativeOracleContext

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 NativeCoreMachine NativeMachineSegment

theorem protocol {n B D k r p b load F fuel S v limit:ℕ} {cfg:Config}
    {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {extent:String→ ℕ} {front:List ℕ}
    {σ:Env} (hc:Context B D k r p b load F fuel S v limit cfg G extent front σ):
    Protocol B D S v cfg extent front σ:=
  ⟨hc.bounded,hc.lengths,hc.stack,hc.cursor,hc.stride,hc.frameLength,hc.roundWidth,hc.nodeD⟩

theorem collection {n B D k r p b load F fuel S v limit steps total:ℕ} {cfg:Config}
    {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {extent:String→ ℕ} {front:List ℕ}
    {base τ:Env} (hc:Context B D k r p b load F fuel S v limit cfg G extent front base)
    (trace:Segment B (phases cfg) steps total base τ)
    (anchor:NativeCollectionAnchor.Anchor base τ)
    (order:τ.vars "graph.n"=n)
    (stack:Prefix front "recursion.frames" τ) (cursor:τ.vars "stack.words"=front.length):
    Context B D k r p b load F fuel S v limit cfg G extent front τ:=by
  have v (s:String) (hs:s∉NativeCollectionAnchor.workScalars):=anchor.1 s hs
  have a (s:String) (hs:s∉NativeCollectionAnchor.workArrays):=anchor.2 s hs
  refine ⟨?_,(v _ (by decide)).trans hc.target,(v _ (by decide)).trans hc.sparsity,
    (v _ (by decide)).trans hc.denominator,(v _ (by decide)).trans hc.classB,
    (v _ (by decide)).trans hc.loadValue,(v _ (by decide)).trans hc.nodeD,
    (v _ (by decide)).trans hc.floorPower,?_,(v _ (by decide)).trans hc.programLength,
    (v _ (by decide)).trans hc.roundLimit,(v _ (by decide)).trans hc.roundWidth,NativeMachineBounds.state trace hc.bounded,
    ?_,stack,cursor,(v _ (by decide)).trans hc.stride,(v _ (by decide)).trans hc.depth,
    (v _ (by decide)).trans hc.frameLength⟩
  · rcases hc.moments with ⟨⟨hn,hN,hm,hg,hbits⟩,hcard,hind,hr⟩
    refine ⟨⟨order,(v _ (by decide)).trans hN,?_,?_,?_⟩,
      ?_,?_,(v _ (by decide)).trans hr⟩
    · simpa only [Prefix,a "catalog.mask" (by decide)] using hm
    · simpa only [Prefix,a "search.graph" (by decide)] using hg
    · rw [NativeMachineFrame.array_length trace]; exact hbits
    · simpa only [Prefix,a "catalog.card" (by decide)] using hcard
    · simpa only [Prefix,a "catalog.independent" (by decide)] using hind
  · simpa only [Prefix,a "moment.program" (by decide)] using hc.program
  · intro s; rw [NativeMachineFrame.array_length trace]; exact hc.lengths s

end Lax263307Proofs.NativeOracleContext

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeNodeProtocol

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 NativeCoreMachine NativeMachineSegment NativeOracleContext

theorem child_variable (cfg:Config) (s:String)
    (hg:s∉NativeChildGraph.command.wvars) (hc:s∉NativeChildActivate.command.wvars)
    (he:s∉(NativeChildCall.enter 1).wvars) (hphase:s≠"machine.phase")
    (hstack:s∉["stack.i","stack.copy.length","stack.words"]):
    s∉((phases cfg)[11]'(by change 11<16; decide)).wvars:=by
  have hsave:=NativeChildCall.save_variable (frameArrays cfg) (frameScalars cfg) s hstack
  simp_all only [phases,cases,List.getElem_cons_succ,List.getElem_cons_zero,
    NativeChildCall.command,go,Com.wvars,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false,not_or,not_false_eq_true]

theorem pushed_length {B D S v t:ℕ} {cfg:Config} {extent:String→ ℕ} {front:List ℕ}
    {σ saved:Env} {c:Com} (rr:Run B c σ saved t)
    (hc:Protocol B D S v cfg extent front σ) (hext:∀ a∈frameArrays cfg,extent a=S):
    (front++NativeRecursionFrame.words (frameArrays cfg) (frameScalars cfg) saved).length=
      front.length+S*(frameArrays cfg).length+(frameScalars cfg).length:=by
  have h:(NativeFrameBuffers.words (frameArrays cfg) saved).length=S*(frameArrays cfg).length:=
    NativeFrameBuffers.words_length _ S saved (fun a ha => by rw [RamFrames.run_array_length rr,hc.lengths]; exact hext a ha)
  simp only [List.length_append,NativeRecursionFrame.words,NativeFrameScalars.words,List.length_map,h,Nat.add_assoc]

theorem child_entry {B D S v t cost:ℕ} (cfg:Config) {extent:String→ ℕ} {front:List ℕ}
    {σ saved entry:Env} {c:Com} (snapshot:Run B c σ saved t)
    (call:Segment B (phases cfg) 1 cost σ entry)
    (hc:Protocol B D S v cfg extent front σ) (hext:∀ a∈frameArrays cfg,extent a=S)
    (hp:σ.vars "machine.phase"=11)
    (hfront:Prefix (front++NativeRecursionFrame.words (frameArrays cfg) (frameScalars cfg) saved) "recursion.frames" entry)
    (hwords:entry.vars "stack.words"=front.length+S*(frameArrays cfg).length+(frameScalars cfg).length):
    Protocol B D S v cfg extent
      (front++NativeRecursionFrame.words (frameArrays cfg) (frameScalars cfg) saved) entry:=by
  have rr:=NativeMachineFrame.single_run call ⟨11,by change 11<16; decide⟩ hp
  refine ⟨NativeMachineBounds.state call hc.bounded,?_,hfront,?_,?_,?_,?_,?_⟩
  · intro a; rw [NativeMachineFrame.array_length call]; exact hc.lengths a
  · rw [pushed_length snapshot hc hext]; exact hwords
  all_goals apply (rr.frame_var _ (child_variable cfg _ (by decide) (by decide) (by decide) (by decide) (by decide))).trans
  all_goals first | exact hc.stride | exact hc.frameLength | exact hc.roundWidth | exact hc.accuracy

theorem children {n:ℕ} (B D fuel S v childSteps childTime:ℕ) (cfg:Config)
    (lp flow:List ℕ→ List ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (extent:String→ ℕ) (front:List ℕ) (eligible:Eligible)
    (hext:∀ a∈frameArrays cfg,extent a=S)
    (ih:Executes B D fuel S v childSteps childTime cfg lp flow extent eligible):
    Children B D fuel S v childSteps childTime cfg G extent front eligible
      (fun C t => RecursiveAlgorithm.attempt lp flow cfg.a cfg.K cfg.b D fuel (ComputedSeparators.restriction G C) t):=by
  intro C target σ hel hp phase saved entry snapshot call hfront hwords hgraph horder hk hf hr he
  have protocolEntry:=child_entry cfg snapshot call hp hext phase hfront hwords
  have hlength:=pushed_length snapshot hp hext
  obtain ⟨τ,s,t,trace,hs,ht,answer,protocolDone,rootDone,graphDone⟩:=ih C.card (ComputedSeparators.restriction G C) target
    (front++NativeRecursionFrame.words (frameArrays cfg) (frameScalars cfg) saved) entry
    (by simpa only [hlength] using hel) ⟨protocolEntry,horder,hgraph,hk,hf⟩ hr he
  exact ⟨τ,s,t,trace,hs,ht,answer,protocolDone.stack,
    by simpa only [hlength] using protocolDone.cursor,protocolDone.frameLength,protocolDone.stride⟩

end Lax263307Proofs.NativeNodeProtocol

end

section

namespace Lax263307Proofs.NativeChildResources

open Lax263307 ComputedRounding

theorem target_le (δ c:ℚ) (q:ℕ) (hδ:0<δ) (hc:0< c) (hq:c≤ q):target δ c≤ q:=by
  have hq0:q≠0:=by intro he; subst q; norm_num at hq; linarith
  have hlt:(1-δ)*c<(q:ℚ):=by nlinarith
  have hfloor:=(Nat.floor_lt' hq0).mpr hlt
  simpa only [target,Nat.add_one_le_iff] using hfloor

theorem component_cost_le {n:ℕ} (x:Fin n→ ℚ≥0) (C:Finset (Fin n))
    (hx:∀ v,x v≤1):(∑ v∈C,(x v:ℚ))≤ C.card:=by
  calc
    _≤ ∑ _v∈C,(1:ℚ):=Finset.sum_le_sum (fun v _ => by exact_mod_cast hx v)
    _=_:=by simp

theorem active_child {n:ℕ} (D k:ℕ) (x:Fin n→ ℚ≥0) (C:Finset (Fin n))
    (hD:0< D) (hx:∀ v,x v≤1)
    (hactive:(1/(D:ℚ))*k/(4*(n:ℚ))<(∑ v∈C,(x v:ℚ))):
    0< C.card∧ target (1/(D:ℚ)) (∑ v∈C,(x v:ℚ))≤ C.card∧ C.card≤ n:=by
  have hδ:(0:ℚ)<1/D:=by positivity
  have hc:(0:ℚ)<∑ v∈C,(x v:ℚ):=lt_of_le_of_lt (by positivity) hactive
  have hcost:=component_cost_le x C hx
  have hpos:(0:ℚ)< C.card:=hc.trans_le hcost
  exact ⟨by exact_mod_cast hpos,target_le _ _ _ hδ hc hcost,
    C.card_le_univ.trans_eq (Fintype.card_fin n)⟩

end Lax263307Proofs.NativeChildResources

end

section

namespace Lax263307Proofs.NativeRecursiveDomain

open Lax263307 GraphClasses ComputedSeparators NativeNodeProtocol

theorem child {C:GraphClass} (hereditary:IsHereditary C)
    {N frameSize capacity fuel n k cursor:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hi:eligible C N frameSize capacity (fuel+1) n G k cursor) (hn:1< n)
    (vertices:Finset (Fin n)) (hbalanced:3*vertices.card≤2*n)
    (hvertices:0< vertices.card) (target:ℕ) (ht:0< target) (htv:target≤ vertices.card):
    eligible C N frameSize capacity fuel vertices.card (restriction G vertices) target (cursor+frameSize):=by
  have hclass:=hereditary vertices.card n (restriction G vertices) G hi.1 ⟨Lax263307Proofs.ComputedSeparators.embedding G vertices⟩
  have hdep:=Lax263307Proofs.RecursionDepth.balanced_decrease n vertices.card hn hbalanced
  have hdepth:=hi.2.2.2.2.2.1
  refine ⟨hclass,hvertices,(NativeMaskUnpack.card_bound vertices).trans hi.2.2.1,ht,htv,by omega,?_⟩
  have heq:(cursor+frameSize)+fuel*frameSize=cursor+(fuel+1)*frameSize:=by ring
  rw [heq]
  exact hi.2.2.2.2.2.2

theorem heavy_child {C:GraphClass} (hereditary:IsHereditary C)
    {N frameSize capacity fuel n k cursor D:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hi:eligible C N frameSize capacity (fuel+1) n G k cursor) (hn:1< n) (hD:0< D)
    (x:Fin n→ ℚ≥0) (hx:∀ v,x v≤1) (vertices:Finset (Fin n))
    (hbalanced:3*vertices.card≤2*n)
    (hheavy:(1/(D:ℚ))*k/(4*(n:ℚ))<(∑ v∈vertices,(x v:ℚ))):
    eligible C N frameSize capacity fuel vertices.card (restriction G vertices)
      (ComputedRounding.target (1/(D:ℚ)) (∑ v∈vertices,(x v:ℚ))) (cursor+frameSize):=by
  have hc:=NativeChildResources.active_child D k x vertices hD hx hheavy
  exact child hereditary G hi hn vertices hbalanced hc.1 _ (by unfold ComputedRounding.target; omega) hc.2.1

end Lax263307Proofs.NativeRecursiveDomain

end

section

namespace Lax263307Proofs.NativeSelectedParts

open Lax263307 GraphClasses AlgorithmParameters RationalConditioning HeavyRationalConditioning ComputedSeparators LinearRelaxation

theorem selected {C:GraphClass} {flow:List ℕ→ List ℕ} {a K b:ℕ}
    (hsep:Lax263307Proofs.NearOracle.SeparatorCorrect C flow a K b)
    (hK:0< K) (hb:0< b) {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG:G∈C n) (hn:0< n) (D k:ℕ) (hD:4≤ D) (hlarge:cutoff a K b n D< k)
    (y:RationalVector n (level a K b n D))
    (hy:LinearRelaxation.IsFeasible G k (level a K b n D) (realVector y))
    (A:Finset (Fin n)) (hfind:findHeavyConditioning G k (sparsity a K b n D) y=some A):
    A.card≤ level a K b n D∧ (∀ v,NearOracle.costs y A v≤1)∧
      let cs:=cuts (step flow G (NearOracle.costs y A) b (load b n D) k) n Finset.univ
      ∀ i,3*(pieces cs i).card≤2*n:=by
  have bud:=Lax263307Proofs.AlgorithmParameters.budgets hK hb hD hlarge
  obtain ⟨A',choice,hsize,hmoment,hpositive,hcosts,hmass,hedge⟩:=
    Lax263307Proofs.HeavyRationalConditioning.search_correct G k (level a K b n D) (sparsity a K b n D) y hy hn
      (by omega) bud.2.2.1 bud.2.1 bud.2.2.2.2.2.2.1
  have heq:A'=A:=Option.some.inj (choice.symm.trans hfind)
  subst A'
  let x:=NearOracle.costs y A
  have cast (v:Fin n):(x v:ℝ)=conditioned (realVector y) A v:=
    Lax263307Proofs.NearOracle.costs_cast y A (fun v => (hcosts v).1) v
  have hunit (v:Fin n):(x v:ℝ)≤1:=by rw [cast]; exact (hcosts v).2
  have hsum:(∑ v,(x v:ℝ))≤ k:=by simp only [cast]; exact hmass.le
  have hedge':Entropy.edgeCost G (fun v => (x v:ℝ))≤(k:ℝ)^2/(sparsity a K b n D):=by
    simpa only [cast] using hedge
  obtain ⟨hlen,hbalanced,hlight,P,hverts,hparts⟩:=hsep n G hG hn x k (sparsity a K b n D) (load b n D)
    (by omega) bud.2.1 bud.1 hunit hsum hedge' bud.2.2.2.2.2.2.2.1 bud.2.2.2.2.2.2.2.2
  refine ⟨hsize,?_,?_⟩
  · intro v
    have h:=hunit v
    exact_mod_cast h
  · dsimp only
    intro i
    rw [←hverts i]
    exact hparts i

theorem target_bound {n:ℕ} (D:ℕ) (hD:0< D) (x:Fin n→ ℚ≥0) (hx:∀ v,x v≤1)
    (vertices:Finset (Fin n)):
    ComputedRounding.target (1/(D:ℚ)) (∑ v∈vertices,(x v:ℚ))≤ n+1:=by
  have hnonnegative:(0:ℚ)≤∑ v∈vertices,(x v:ℚ):=Finset.sum_nonneg (fun v _ => by positivity)
  by_cases hz:(∑ v∈vertices,(x v:ℚ))=0
  · simp [ComputedRounding.target,hz]
  · have ht:=NativeChildResources.target_le (1/(D:ℚ)) _ vertices.card (by positivity)
      (lt_of_le_of_ne hnonnegative (Ne.symm hz)) (NativeChildResources.component_cost_le x vertices hx)
    exact ht.trans ((NativeMaskUnpack.card_bound vertices).trans (Nat.le_succ n))

theorem children {C:GraphClass} (hereditary:IsHereditary C)
    {flow:List ℕ→ List ℕ} {a K b N frameSize capacity fuel n k cursor D:ℕ}
    (hsep:Lax263307Proofs.NearOracle.SeparatorCorrect C flow a K b) (hK:0< K) (hb:0< b)
    (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hi:NativeRecursiveDomain.eligible C N frameSize capacity (fuel+1) n G k cursor)
    (hn:1< n) (hD:4≤ D) (hlarge:cutoff a K b n D< k)
    (y:RationalVector n (level a K b n D))
    (hy:LinearRelaxation.IsFeasible G k (level a K b n D) (realVector y))
    (A:Finset (Fin n)) (hfind:findHeavyConditioning G k (sparsity a K b n D) y=some A):
    let costs:=NearOracle.costs y A
    let cs:=cuts (step flow G costs b (load b n D) k) n Finset.univ
    ∀ i,(1/(D:ℚ))*k/(4*(n:ℚ))<(∑ v∈pieces cs i,(costs v:ℚ))→
      NativeRecursiveDomain.eligible C N frameSize capacity fuel (pieces cs i).card (restriction G (pieces cs i))
        (ComputedRounding.target (1/(D:ℚ)) (∑ v∈pieces cs i,(costs v:ℚ))) (cursor+frameSize):=by
  have parts:=selected hsep hK hb G hi.1 (by omega) D k hD hlarge y hy A hfind
  dsimp only
  intro i heavy
  exact NativeRecursiveDomain.heavy_child hereditary G hi hn (by omega) (NearOracle.costs y A) parts.2.1
    _ (parts.2.2 i) heavy

end Lax263307Proofs.NativeSelectedParts

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeSelectedNear

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 GraphClasses AlgorithmParameters RationalConditioning HeavyRationalConditioning ComputedSeparators
open NativeCoreMachine NativeUniformFlow
open scoped NNRat

theorem setup {C:GraphClass} (hereditary:IsHereditary C)
    {flow:List ℕ→ List ℕ} (fp:Program flow) (cfg:Config)
    (hcode:fp.code=cfg.flow) (hcoeff:fp.coeff=cfg.flowWidth)
    (hsep:NearOracle.SeparatorCorrect C flow cfg.a cfg.K cfg.b) (hK:0< cfg.K) (hb:0< cfg.b)
    {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D k fuel S v H T w rootN capacity childSteps childTime:ℕ)
    (extent:String→ ℕ) (front:List ℕ)
    (hi:NativeRecursiveDomain.eligible C rootN (S*(frameArrays cfg).length+(frameScalars cfg).length)
      capacity (fuel+1) n G k front.length)
    (hn:1< n) (hD:4≤ D) (hlarge:cutoff cfg.a cfg.K cfg.b n D< k)
    (x:Fin (MomentLP.dimension n (level cfg.a cfg.K cfg.b n D))→ ℚ)
    (hy:LinearRelaxation.IsFeasible G k (level cfg.a cfg.K cfg.b n D) (realVector (MomentLP.decode x)))
    (hx:∀ i,NativeSignedArithmetic.Bounded (2^H) (x i))
    (htarget:n+1≤ T)
    (bounds:NativeNearExecution.Bounds n (level cfg.a cfg.K cfg.b n D) D k
      (sparsity cfg.a cfg.K cfg.b n D) (2^H) (2*H) T fuel S w cfg extent front)
    (hwidth:wordHeight n (NativeLargeResources.heightExponent cfg.b n (load cfg.b n D) k (2*H))
      fp.code fp.width fp.time fp.output≤ w)
    (hspace:∀ a∈NativeSeparatorContext.workspace,
      spaceBound n (NativeLargeResources.heightExponent cfg.b n (load cfg.b n D) k (2*H)) fp.time≤ extent a)
    (child:(A:Finset (Fin n))→ ℕ→ Option (Finset (Fin A.card))):
    NativeRecursiveSetup.Near D k (sparsity cfg.a cfg.K cfg.b n D) cfg.b (load cfg.b n D)
      fuel S v (2^H) (2*H) T w
      (spaceBound n (NativeLargeResources.heightExponent cfg.b n (load cfg.b n D) k (2*H)) fp.time)
      (NativeSeparatorOutput.timeBound n (NativeLargeResources.heightExponent cfg.b n (load cfg.b n D) k (2*H))
        fp.code fp.coeff fp.time) childSteps childTime cfg G flow x extent front child
      (NativeRecursiveDomain.eligible C rootN (S*(frameArrays cfg).length+(frameScalars cfg).length) capacity):=by
  have hnroot:n≤ rootN:=hi.2.2.1
  have hload:0< load cfg.b n D:=by unfold load logarithm; positivity
  have decoded:∀ T,NativeSignedArithmetic.Bounded (2^H) (MomentLP.decode x T):=by
    intro T
    exact hx ((CoordinateCatalog.indexing n _).symm T)
  have parts:=NativeSelectedParts.selected hsep hK hb G hi.1 (by omega) D k hD hlarge (MomentLP.decode x) hy
  refine ⟨bounds,hx,fun A hA => (parts A hA).1,?_,hspace,?_,?_⟩
  · intro A hA vertices
    exact (NativeSelectedParts.target_bound D (by omega) _ (parts A hA).2.1 vertices).trans htarget
  · intro A
    dsimp only
    have hcost:∀ v,NativeSignedArithmetic.Bounded (2^(2*H))
        (NearOracle.costs (MomentLP.decode x) A v:ℚ):=by

      intro v
      have hnum:NativeSignedArithmetic.Bounded (2^H)
          (rationalValue (MomentLP.decode x) (insert v A)):=by
        unfold rationalValue
        split_ifs
        · exact decoded _
        · exact ⟨by simp,by simp; exact Nat.one_le_two_pow⟩
      have hden:NativeSignedArithmetic.Bounded (2^H) (rationalValue (MomentLP.decode x) A):=by
        unfold rationalValue
        split_ifs
        · exact decoded _
        · exact ⟨by simp,by simp; exact Nat.one_le_two_pow⟩
      have h:=NativePositiveQuotient.height (2^H) _ _ Nat.one_le_two_pow hnum hden
      change NativeSignedArithmetic.Bounded (2^(2*H))
        (max 0 (rationalValue (MomentLP.decode x) (insert v A) / rationalValue (MomentLP.decode x) A))
      simpa only [←pow_mul,Nat.mul_comm H 2] using h
    simpa only [hcode,hcoeff] using fp.call cfg.b n (load cfg.b n D) k (2*H) G
      (NearOracle.costs (MomentLP.decode x) A) (by omega) hload hcost w hwidth
  · intro A hA
    dsimp only
    intro i _ heavy
    simpa only [Nat.add_assoc] using NativeSelectedParts.children hereditary hsep hK hb G hi hn hD hlarge
      (MomentLP.decode x) hy A hA i heavy

end Lax263307Proofs.NativeSelectedNear

end

theorem solution:∀ {C:Lax263307.GraphClasses.GraphClass},
  Lax263307.GraphClasses.IsHereditary C→
    ∀ {flow:List Nat→ List Nat} (fp:Lax263307Proofs.NativeSelectedNear.Program flow)
      (cfg:Lax263307Proofs.NativeCoreMachine.Config),
      @Eq Lax808846.Ram.Program (@Lax263307Proofs.NativeSelectedNear.Program.code flow fp) cfg.flow→
        @Eq (List Nat) (@Lax263307Proofs.NativeSelectedNear.Program.coeff flow fp) cfg.flowWidth→
          Lax263307Proofs.NearOracle.SeparatorCorrect C flow cfg.a cfg.K cfg.b→
            Nat.lt ((0:Nat)) cfg.K→
              Nat.lt ((0:Nat)) cfg.b→
                ∀ {n:Nat} (G:SimpleGraph (Fin n))
                  [inst:@DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)]
                  (D k fuel S v H T w rootN capacity childSteps childTime:Nat) (extent:String→ Nat)
                  (front:List Nat),
                  Lax263307Proofs.NativeRecursiveDomain.eligible C rootN
                      (Nat.add
                        (Nat.mul S
                          (@List.length String (Lax263307Proofs.NativeCoreMachine.frameArrays cfg)))
                        (@List.length String (Lax263307Proofs.NativeCoreMachine.frameScalars cfg)))
                      capacity
                      (Nat.add fuel
                        ((1:Nat)))
                      n G k (@List.length Nat front)→
                    Nat.lt ((1:Nat)) n→
                      Nat.le ((4:Nat)) D→
                        Nat.lt (Lax263307.AlgorithmParameters.cutoff cfg.a cfg.K cfg.b n D) k→
                          ∀
                            (x:
                              Fin
                                  (Lax263307.MomentLP.dimension n
                                    (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D))→
                                Rat),
                            @Lax263307.LinearRelaxation.IsFeasible n G k
                                (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D)
                                (@Lax263307.RationalConditioning.realVector n
                                  (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D)
                                  (@Lax263307.MomentLP.decode Rat n
                                    (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D) x))→
                              (∀
                                  (i:
                                    Fin
                                      (Lax263307.MomentLP.dimension n
                                        (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D))),
                                  Lax263307Proofs.NativeSignedArithmetic.Bounded
                                    (@HPow.hPow Nat Nat Nat
                                      (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                      ((2:Nat)) H)
                                    (x i))→
                                Nat.le
                                    (Nat.add n
                                      ((1:Nat)))
                                    T→
                                  Lax263307Proofs.NativeNearExecution.Bounds n
                                      (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D) D k
                                      (Lax263307.AlgorithmParameters.sparsity cfg.a cfg.K cfg.b n D)
                                      (@HPow.hPow Nat Nat Nat
                                        (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                        ((2:Nat)) H)
                                      (Nat.mul
                                        ((2:Nat)) H)
                                      T fuel S w cfg extent front→
                                    Nat.le
                                        (Lax263307Proofs.NativeUniformFlow.wordHeight n
                                          (Lax263307Proofs.NativeLargeResources.heightExponent cfg.b n
                                            (Lax263307.AlgorithmParameters.load cfg.b n D) k
                                            (Nat.mul
                                              ((2:Nat)) H))
                                          (@Lax263307Proofs.NativeSelectedNear.Program.code flow fp)
                                          (@Lax263307Proofs.NativeSelectedNear.Program.width flow fp)
                                          (@Lax263307Proofs.NativeSelectedNear.Program.time flow fp)
                                          (@Lax263307Proofs.NativeSelectedNear.Program.output flow fp))
                                        w→
                                      (∀ (a:String),
                                          @Membership.mem String (List String) (@List.instMembership String)
                                              Lax263307Proofs.NativeSeparatorContext.workspace a→
                                            Nat.le
                                              (Lax263307Proofs.NativeUniformFlow.spaceBound n
                                                (Lax263307Proofs.NativeLargeResources.heightExponent cfg.b n
                                                  (Lax263307.AlgorithmParameters.load cfg.b n D) k
                                                  (Nat.mul
                                                    ((2:Nat)) H))
                                                (@Lax263307Proofs.NativeSelectedNear.Program.time flow fp))
                                              (extent a))→
                                        ∀
                                          (child:
                                            (A:Finset (Fin n))→
                                              Nat→ Option (Finset (Fin (@Finset.card (Fin n) A)))),
                                          @Lax263307Proofs.NativeRecursiveSetup.Near n
                                            (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D) D k
                                            (Lax263307.AlgorithmParameters.sparsity cfg.a cfg.K cfg.b n D) cfg.b
                                            (Lax263307.AlgorithmParameters.load cfg.b n D) fuel S v
                                            (@HPow.hPow Nat Nat Nat
                                              (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                              ((2:Nat)) H)
                                            (Nat.mul
                                              ((2:Nat)) H)
                                            T w
                                            (Lax263307Proofs.NativeUniformFlow.spaceBound n
                                              (Lax263307Proofs.NativeLargeResources.heightExponent cfg.b n
                                                (Lax263307.AlgorithmParameters.load cfg.b n D) k
                                                (Nat.mul
                                                  ((2:Nat)) H))
                                              (@Lax263307Proofs.NativeSelectedNear.Program.time flow fp))
                                            (Lax263307Proofs.NativeSeparatorOutput.timeBound n
                                              (Lax263307Proofs.NativeLargeResources.heightExponent cfg.b n
                                                (Lax263307.AlgorithmParameters.load cfg.b n D) k
                                                (Nat.mul
                                                  ((2:Nat)) H))
                                              (@Lax263307Proofs.NativeSelectedNear.Program.code flow fp)
                                              (@Lax263307Proofs.NativeSelectedNear.Program.coeff flow fp)
                                              (@Lax263307Proofs.NativeSelectedNear.Program.time flow fp))
                                            childSteps childTime cfg G inst flow x extent front child
                                            (Lax263307Proofs.NativeRecursiveDomain.eligible C rootN
                                              (Nat.add
                                                (Nat.mul S
                                                  (@List.length String
                                                    (Lax263307Proofs.NativeCoreMachine.frameArrays cfg)))
                                                (@List.length String
                                                  (Lax263307Proofs.NativeCoreMachine.frameScalars cfg)))
                                              capacity):= @Lax263307Proofs.NativeSelectedNear.setup
