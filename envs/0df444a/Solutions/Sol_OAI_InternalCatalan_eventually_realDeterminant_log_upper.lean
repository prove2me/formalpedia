-- Prove2me | solution 1 for OAI.InternalCatalan.eventually_realDeterminant_log_upper
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T19:08:40.666028+00:00
-- url     : https://prove2.me/submissions/4acaa7cb-5c53-4aa0-aeeb-966c1cc1bdbd

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Filter.AtTopBot.Group
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_OAICatalanIrrationality
import Theorems.Thm_OAI_InternalCatalan_barrierCase2X_global_upper
import Theorems.Thm_OAI_InternalCatalan_barrierCase2Y_global_upper
import Theorems.Thm_OAI_InternalCatalan_barrier_case2_norm_rational_upper
import Theorems.Thm_OAI_InternalCatalan_realDeterminant_eventually_log_certificate_sup

section
-- module Solutions.OAICatalan.Catalan.Analysis.RealEnergyLogSeries
namespace OAI

noncomputable section
open Set

namespace InternalCatalan


theorem energy_hasSum_re_power_div {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => (z ^ k).re / (k : ℝ))
      (-Real.log ‖1 - z‖) := by
  simpa only [Complex.div_natCast_re, Complex.neg_re, Complex.log_re] using
    Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log hz)




theorem energy_hasSum_real_power_div {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    HasSum (fun k : ℕ => u ^ k / (k : ℝ)) (-Real.log (1 - u)) := by
  have huNorm : ‖(u : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using abs_lt.mpr hu
  have hnorm : ‖(1 : ℂ) - (u : ℂ)‖ = 1 - u := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hu.2)]
  simpa only [← Complex.ofReal_pow, Complex.ofReal_re, hnorm] using
    energy_hasSum_re_power_div huNorm






end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Polynomial.CentralCoefficients
namespace OAI

namespace InternalCatalan

section

open scoped BigOperators



@[simp] theorem centralCoeff_zero : centralCoeff 0 = 1 := by
  norm_num [centralCoeff]

@[simp] theorem centralCoeffKernel_zero : centralCoeffKernel 0 = 1 := by
  norm_num [centralCoeffKernel]





@[simp] theorem momentScalar_zero : momentScalar 0 = 2 := by
  norm_num [momentScalar]





@[simp] theorem boundaryMinus_zero : boundaryMinus 0 = 0 := rfl
@[simp] theorem boundaryMinus_one : boundaryMinus 1 = 2 := rfl
@[simp] theorem boundaryPlus_zero : boundaryPlus 0 = 0 := rfl
@[simp] theorem boundaryPlus_one : boundaryPlus 1 = 0 := rfl








@[simp] theorem momentRat_zero_right (i : ℕ) : momentRat i 0 = boundaryMinus i := by
  simp [momentRat]

@[simp] theorem momentRat_zero_left (j : ℕ) : momentRat 0 j = boundaryPlus j := by
  cases j with
  | zero => simp [momentRat]
  | succ j => simp [momentRat]






@[simp] theorem harmonicRat_zero (d : ℕ) : harmonicRat d 0 = 0 := by
  simp [harmonicRat]



@[simp] theorem zetaRat_diagonal (i : ℕ) : zetaRat i i = -harmonicRat 2 i := by
  simp [zetaRat]




end













end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.RealColumnDeterminant
namespace OAI

noncomputable section

namespace InternalCatalan

section

open Polynomial




@[simp] theorem reversedRow_zero (C : ℕ) : reversedRow C 0 = 0 := by
  simp [reversedRow]



































end

section

open scoped BigOperators









end

section

open Polynomial







variable {K : Type*} [Field K]




end

open Polynomial



end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Energy.BarrierFinitePotentialRat
namespace OAI

noncomputable section

namespace InternalCatalan

section









open Polynomial Filter
open scoped BigOperators










end

section

open scoped BigOperators

theorem barrierTrialNormSq_nil_eq_sum (cs : List ℤ) :
    barrierTrialNormSq (barrierTrial cs []) =
      ∑ k ∈ Finset.range cs.length,
        ((cs.getD k 0 : ℝ) / 100000000) ^ 2 / ((k + 1 : ℕ) : ℝ) := by
  unfold barrierTrialNormSq
  have heq (k : ℕ) : barrierTrial cs [] (k + 1) =
      (cs.getD k 0 : ℝ) / 100000000 := by
    simp [barrierTrial, barrierFiniteCoeff]
  simp_rw [heq]
  apply tsum_eq_sum
  intro k hk
  have hlen : cs.length ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
  rw [List.getD_eq_default cs 0 hlen]
  norm_num

theorem barrier_case1_norm_sharp_upper :
    barrierTrialNormSq barrierP1 + (1 / 2 : ℝ) * barrierTrialNormSq barrierV1 <
      (931985203901 / 1000000000000 : ℝ) := by
  change barrierTrialNormSq (barrierTrial barrierP1Finite []) +
      (1 / 2 : ℝ) * barrierTrialNormSq (barrierTrial barrierV1Finite []) < _
  rw [barrierTrialNormSq_nil_eq_sum, barrierTrialNormSq_nil_eq_sum]
  norm_num [barrierP1Finite, barrierV1Finite, Finset.sum_range_succ]

theorem barrier_case1_norm_coarse_upper :
    barrierTrialNormSq barrierP1 + (1 / 2 : ℝ) * barrierTrialNormSq barrierV1 <
      (9321 / 10000 : ℝ) := by
  exact barrier_case1_norm_sharp_upper.trans (by norm_num)


end
section

open Polynomial
open scoped BigOperators

theorem barrierTrialT_nil_eq_sum (cs : List ℤ) (x : ℝ) :
    barrierTrialT (barrierTrial cs []) x =
      ∑ k ∈ Finset.range cs.length,
        ((cs.getD k 0 : ℝ) / 100000000) *
          (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x / ((k + 1 : ℕ) : ℝ) := by
  unfold barrierTrialT
  have heq (k : ℕ) : barrierTrial cs [] (k + 1) =
      (cs.getD k 0 : ℝ) / 100000000 := by
    simp [barrierTrial, barrierFiniteCoeff]
  simp_rw [heq]
  apply tsum_eq_sum
  intro k hk
  have hlen : cs.length ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
  rw [List.getD_eq_default cs 0 hlen]
  norm_num

theorem barrierTrialS_nil_eq_sum (cs : List ℤ) (x : ℝ) :
    barrierTrialS (barrierTrial cs []) x =
      ∑ k ∈ Finset.range cs.length,
        ((cs.getD k 0 : ℝ) / 100000000) * x ^ (k + 1) / ((k + 1 : ℕ) : ℝ) := by
  unfold barrierTrialS
  have heq (k : ℕ) : barrierTrial cs [] (k + 1) =
      (cs.getD k 0 : ℝ) / 100000000 := by
    simp [barrierTrial, barrierFiniteCoeff]
  simp_rw [heq]
  apply tsum_eq_sum
  intro k hk
  have hlen : cs.length ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
  rw [List.getD_eq_default cs 0 hlen]
  norm_num

end

section

open Polynomial Set Filter
open scoped BigOperators



end

open Polynomial







open Polynomial
open scoped BigOperators

def barrierFiniteTRat (cs : List ℤ) (x : ℚ) : ℚ :=
  ∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℚ) / 100000000) *
    (Chebyshev.T ℚ ((k + 1 : ℕ) : ℤ)).eval x / ((k + 1 : ℕ) : ℚ)

def barrierFiniteSRat (cs : List ℤ) (x : ℚ) : ℚ :=
  ∑ k ∈ Finset.range cs.length,
    ((cs.getD k 0 : ℚ) / 100000000) * x ^ (k + 1) / ((k + 1 : ℕ) : ℚ)

theorem barrierTrialT_nil_eval_rat (cs : List ℤ) (x : ℚ) :
    barrierTrialT (barrierTrial cs []) (x : ℝ) = ((barrierFiniteTRat cs x : ℚ) : ℝ) := by
  have heval (n : ℤ) : (Chebyshev.T ℝ n).eval (x : ℝ) =
      (((Chebyshev.T ℚ n).eval x : ℚ) : ℝ) := by
    rw [← Chebyshev.map_T (Rat.castHom ℝ)]
    change ((Chebyshev.T ℚ n).map (Rat.castHom ℝ)).eval ((Rat.castHom ℝ) x) =
      (Rat.castHom ℝ) ((Chebyshev.T ℚ n).eval x)
    exact Polynomial.eval_map_apply (Rat.castHom ℝ) x
  rw [barrierTrialT_nil_eq_sum]
  unfold barrierFiniteTRat
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  rw [heval]

theorem barrierTrialS_nil_eval_rat (cs : List ℤ) (x : ℚ) :
    barrierTrialS (barrierTrial cs []) (x : ℝ) = ((barrierFiniteSRat cs x : ℚ) : ℝ) := by
  rw [barrierTrialS_nil_eq_sum]
  unfold barrierFiniteSRat
  push_cast
  rfl

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.RealEnergySupDual
namespace OAI

noncomputable section

namespace InternalCatalan

section

open Set




end

section

open Polynomial
open scoped BigOperators





end

section

open Polynomial Set
open scoped BigOperators






end

section

open Set
open scoped BigOperators







end

section

open scoped BigOperators





end

open Set
open scoped BigOperators






















open Set
open scoped BigOperators





theorem realEnergyRowTrialField_image_nonempty (k lam : ℝ) (p v : ℕ → ℝ) :
    (realEnergyRowTrialField k lam p v '' {x : ℝ | x ∈ Ico (-1 : ℝ) 1 ∧ x ≠ 0}).Nonempty := by
  refine ⟨realEnergyRowTrialField k lam p v (-1 / 2), -1 / 2, ?_, rfl⟩
  norm_num

theorem realEnergyColumnTrialField_image_nonempty (v : ℕ → ℝ) :
    (realEnergyColumnTrialField v '' Ioo (0 : ℝ) 1).Nonempty := by
  refine ⟨realEnergyColumnTrialField v (1 / 2), 1 / 2, ?_, rfl⟩
  norm_num




end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Energy.BarrierDescartesCoefficientDegree
namespace OAI

noncomputable section

namespace InternalCatalan

section

open Polynomial
open scoped BigOperators

def barrierDescartesTransform {R : Type*} [CommRing R] (p : R[X])
    (d : ℕ) (a b : R) : R[X] :=
  ∑ k ∈ Finset.range (d + 1),
    C (p.coeff k) * (C a + C b * X) ^ k * (1 + X) ^ (d - k)

theorem barrierDescartesTransform_eval {R : Type*} [Field R] (p : R[X])
    (d : ℕ) (a b t : R) (hd : p.natDegree ≤ d) (ht : 1 + t ≠ 0) :
    (barrierDescartesTransform p d a b).eval t =
      (1 + t) ^ d * p.eval ((a + b * t) / (1 + t)) := by
  unfold barrierDescartesTransform
  rw [eval_finsetSum, eval_eq_sum_range' (Nat.lt_succ_of_le hd), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkd : k ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hp : (1 + t) ^ (d - k) = (1 + t) ^ d / (1 + t) ^ k := by
    apply (eq_div_iff (pow_ne_zero k ht)).2
    rw [← pow_add, Nat.sub_add_cancel hkd]
  simp only [eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_one]
  rw [hp, div_pow]
  ring

theorem barrierDescartesTransform_eval_eq_zero_iff {R : Type*} [Field R] (p : R[X])
    (d : ℕ) (a b t : R) (hd : p.natDegree ≤ d) (ht : 1 + t ≠ 0) :
    (barrierDescartesTransform p d a b).eval t = 0 ↔
      p.eval ((a + b * t) / (1 + t)) = 0 := by
  rw [barrierDescartesTransform_eval p d a b t hd ht]
  simp [pow_ne_zero d ht]

theorem barrierMobius_inverse {a b x : ℝ} (hx : x ∈ Set.Ioo a b) :
    0 < (x - a) / (b - x) ∧
      (a + b * ((x - a) / (b - x))) / (1 + (x - a) / (b - x)) = x := by
  have hp : 0 < (x - a) / (b - x) :=
    div_pos (sub_pos.mpr hx.1) (sub_pos.mpr hx.2)
  have hb : b - x ≠ 0 := ne_of_gt (sub_pos.mpr hx.2)
  have h1 : 1 + (x - a) / (b - x) ≠ 0 := ne_of_gt (by linarith)
  refine ⟨hp, ?_⟩
  apply (div_eq_iff h1).2
  field_simp [hb]
  ring

theorem barrierDescartesTransform_root_of_interval (p : ℝ[X]) (d : ℕ)
    {a b x : ℝ} (hd : p.natDegree ≤ d) (hx : x ∈ Set.Ioo a b)
    (hp : p.eval x = 0) :
    0 < (x - a) / (b - x) ∧
      (barrierDescartesTransform p d a b).eval ((x - a) / (b - x)) = 0 := by
  obtain ⟨ht, heq⟩ := barrierMobius_inverse hx
  refine ⟨ht, ?_⟩
  apply (barrierDescartesTransform_eval_eq_zero_iff p d a b _ hd
    (ne_of_gt (by linarith))).2
  rw [heq]
  exact hp





end

section

open Polynomial

theorem barrierDescartes_interval_roots_card_le (p : ℝ[X]) (d : ℕ) (a b : ℝ)
    (hd : p.natDegree ≤ d)
    (hne : barrierDescartesTransform p d a b ≠ 0)
    (s : Finset ℝ) (hs : ∀ x ∈ s, x ∈ Set.Ioo a b ∧ p.eval x = 0) :
    s.card ≤ (barrierDescartesTransform p d a b).signVariations := by
  classical
  let Q := barrierDescartesTransform p d a b
  let t := (Q.roots.filter (fun x => 0 < x)).toFinset
  have hcard : s.card ≤ t.card := by
    apply Finset.card_le_card_of_injOn (fun x : ℝ => (x - a) / (b - x))
    · intro x hx
      obtain ⟨hpos, hroot⟩ := barrierDescartesTransform_root_of_interval p d hd
        (hs x hx).1 (hs x hx).2
      apply Multiset.mem_toFinset.mpr
      exact Multiset.mem_filter.mpr
        ⟨(Polynomial.mem_roots hne).mpr hroot, hpos⟩
    · intro x hx y hy hxy
      change (x - a) / (b - x) = (y - a) / (b - y) at hxy
      have hix := (barrierMobius_inverse (hs x hx).1).2
      have hiy := (barrierMobius_inverse (hs y hy).1).2
      calc
        x = (a + b * ((x - a) / (b - x))) / (1 + (x - a) / (b - x)) := hix.symm
        _ = (a + b * ((y - a) / (b - y))) / (1 + (y - a) / (b - y)) := by rw [hxy]
        _ = y := hiy
  have htcard : t.card ≤ Q.roots.countP (fun x => 0 < x) := by
    simpa only [t, Multiset.countP_eq_card_filter] using
      Multiset.toFinset_card_le (Q.roots.filter (fun x => 0 < x))
  exact hcard.trans (htcard.trans (Polynomial.roots_countP_pos_le_signVariations Q))

end

section

open Filter Polynomial
open scoped Topology





end

open Polynomial
open scoped BigOperators


end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.FirstBarrier.BarrierCaseOneRootExistence
namespace OAI

noncomputable section

namespace InternalCatalan

open Polynomial

theorem rationalPolynomial_root_mem_Ioo_of_eval_mul_neg (p : ℚ[X])
    {a b : ℚ} (hab : a < b) (hs : p.eval a * p.eval b < 0) :
    ∃ x : ℝ, x ∈ Set.Ioo (a : ℝ) (b : ℝ) ∧
      (p.map (Rat.castHom ℝ)).eval x = 0 := by
  have heval (q : ℚ) :
      (p.map (Rat.castHom ℝ)).eval (q : ℝ) = ((p.eval q : ℚ) : ℝ) := by
    change (p.map (Rat.castHom ℝ)).eval ((Rat.castHom ℝ) q) =
      (Rat.castHom ℝ) (p.eval q)
    exact Polynomial.eval_map_apply (Rat.castHom ℝ) q
  have hab' : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  have hs' : (p.map (Rat.castHom ℝ)).eval (a : ℝ) *
      (p.map (Rat.castHom ℝ)).eval (b : ℝ) < 0 := by
    simp only [heval]
    exact_mod_cast hs
  have hc : ContinuousOn (fun x : ℝ => (p.map (Rat.castHom ℝ)).eval x)
      (Set.Icc (a : ℝ) (b : ℝ)) := (p.map (Rat.castHom ℝ)).continuousOn
  rcases mul_neg_iff.mp hs' with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have hz : (0 : ℝ) ∈ Set.Ioo
        ((p.map (Rat.castHom ℝ)).eval (b : ℝ))
        ((p.map (Rat.castHom ℝ)).eval (a : ℝ)) := ⟨hb, ha⟩
    rcases (intermediate_value_Ioo' hab'.le hc) hz with ⟨x, hx, hroot⟩
    exact ⟨x, hx, hroot⟩
  · have hz : (0 : ℝ) ∈ Set.Ioo
        ((p.map (Rat.castHom ℝ)).eval (a : ℝ))
        ((p.map (Rat.castHom ℝ)).eval (b : ℝ)) := ⟨ha, hb⟩
    rcases (intermediate_value_Ioo hab'.le hc) hz with ⟨x, hx, hroot⟩
    exact ⟨x, hx, hroot⟩

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.FirstBarrier.BarrierCaseOneDescartesX0
namespace OAI

noncomputable section

namespace InternalCatalan

section

open Polynomial
open scoped BigOperators

def barrierFiniteUDerivative (cs : List ℤ) : ℚ[X] :=
  ∑ k ∈ Finset.range cs.length,
    C ((cs.getD k 0 : ℚ) / 100000000) * Chebyshev.U ℚ (k : ℤ)

def barrierFinitePowerDerivative (cs : List ℤ) : ℚ[X] :=
  ∑ k ∈ Finset.range cs.length,
    C ((cs.getD k 0 : ℚ) / 100000000) * X ^ k

def barrierCase1QX : ℚ[X] := X * (1 - X) * (1 + X ^ 2) ^ 2

def barrierCase1QY : ℚ[X] := X * (1 - X)

def barrierCase1AX : ℚ[X] :=
  C (19 / 48) * (1 - X) * (1 + X ^ 2) ^ 2 -
    C (1 / 12) * X * (1 + X ^ 2) ^ 2 -
    C (41 / 24) * X ^ 2 * (1 - X) * (1 + X ^ 2) -
    C (4 * (247405979 / 100000000)) * X ^ 2 * (1 - X) -
    C 2 * barrierCase1QX * barrierFiniteUDerivative barrierP1Finite -
    barrierCase1QX * barrierFinitePowerDerivative barrierV1Finite

def barrierCase1AY : ℚ[X] :=
  C (7 / 48) * (1 - X) - C (1 / 12) * X +
    C 2 * barrierCase1QY * barrierFiniteUDerivative barrierV1Finite

def barrierCase1XDerivativeFormula (x : ℝ) : ℝ :=
  (19 / 48) / x - (1 / 12) / (1 - x) - (41 / 24) * x / (1 + x ^ 2) -
    4 * barrierLambda1 * x / (1 + x ^ 2) ^ 2 -
    2 * (barrierFiniteUDerivative barrierP1Finite).eval₂ (Rat.castHom ℝ) x -
    (barrierFinitePowerDerivative barrierV1Finite).eval₂ (Rat.castHom ℝ) x

def barrierCase1YDerivativeFormula (x : ℝ) : ℝ :=
  (7 / 48) / x - (1 / 12) / (1 - x) +
    2 * (barrierFiniteUDerivative barrierV1Finite).eval₂ (Rat.castHom ℝ) x

theorem barrierCase1QX_eval_ne_zero {x : ℝ} (h0 : x ≠ 0) (h1 : x ≠ 1) :
    barrierCase1QX.eval₂ (Rat.castHom ℝ) x ≠ 0 := by
  have hd : 1 + x ^ 2 ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < 1 + x ^ 2)
  simpa [barrierCase1QX, eval₂_pow] using
    mul_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr (Ne.symm h1))) (pow_ne_zero 2 hd)

theorem barrierCase1QY_eval_ne_zero {x : ℝ} (h0 : x ≠ 0) (h1 : x ≠ 1) :
    barrierCase1QY.eval₂ (Rat.castHom ℝ) x ≠ 0 := by
  simpa [barrierCase1QY] using mul_ne_zero h0 (sub_ne_zero.mpr (Ne.symm h1))

theorem barrierCase1AX_clears_denominator {x : ℝ} (h0 : x ≠ 0) (h1 : x ≠ 1) :
    barrierCase1AX.eval₂ (Rat.castHom ℝ) x =
      barrierCase1QX.eval₂ (Rat.castHom ℝ) x * barrierCase1XDerivativeFormula x := by
  have hd : 1 + x ^ 2 ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < 1 + x ^ 2)
  have ho : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  simp only [barrierCase1AX, barrierCase1QX, barrierCase1XDerivativeFormula,
    barrierLambda1, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_C, eval₂_X,
    eval₂_one, eval₂_ofNat, map_div₀, map_mul, map_ofNat, map_one]
  field_simp [h0, ho, hd]

theorem barrierCase1AY_clears_denominator {x : ℝ} (h0 : x ≠ 0) (h1 : x ≠ 1) :
    barrierCase1AY.eval₂ (Rat.castHom ℝ) x =
      barrierCase1QY.eval₂ (Rat.castHom ℝ) x * barrierCase1YDerivativeFormula x := by
  have ho : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  simp only [barrierCase1AY, barrierCase1QY, barrierCase1YDerivativeFormula,
    eval₂_sub, eval₂_add, eval₂_mul, eval₂_C, eval₂_X,
    eval₂_one, eval₂_ofNat, map_div₀, map_ofNat, map_one]
  field_simp [h0, ho]

end

section

open Polynomial

def barrierCase1AXExplicit : ℚ[X] :=
  C (19/48) +
    C (-27654673/60000000) * X ^ 1 +
    C (-2660802911/300000000) * X ^ 2 +
    C (246612221/20000000) * X ^ 3 +
    C (198644883/6250000) * X ^ 4 +
    C (-9182425759/300000000) * X ^ 5 +
    C (-320848639/10000000) * X ^ 6 +
    C (252958279/10000000) * X ^ 7 +
    C (-4542019331/50000000) * X ^ 8 +
    C (8873559613/100000000) * X ^ 9 +
    C (3723872963/100000000) * X ^ 10 +
    C (-3407762831/100000000) * X ^ 11 +
    C (3242106693/50000000) * X ^ 12 +
    C (-6401402757/100000000) * X ^ 13

def barrierCase1AYExplicit : ℚ[X] :=
  C (7/48) +
    C (-131721511/37500000) * X ^ 1 +
    C (91528151/6250000) * X ^ 2 +
    C (3975799/2500000) * X ^ 3 +
    C (-208633661/3125000) * X ^ 4 +
    C (1596719/50000) * X ^ 5 +
    C (170059219/1562500) * X ^ 6 +
    C (-29059541/390625) * X ^ 7 +
    C (-43803919/781250) * X ^ 8 +
    C (16992389/390625) * X ^ 9

private theorem barrier_U_3 :
    Chebyshev.U ℚ 3 = 2 * X * Chebyshev.U ℚ 2 - Chebyshev.U ℚ 1 := by
  simpa only [Int.reduceAdd] using Chebyshev.U_add_two ℚ 1

private theorem barrier_U_4 :
    Chebyshev.U ℚ 4 = 2 * X * Chebyshev.U ℚ 3 - Chebyshev.U ℚ 2 := by
  simpa only [Int.reduceAdd] using Chebyshev.U_add_two ℚ 2

private theorem barrier_U_5 :
    Chebyshev.U ℚ 5 = 2 * X * Chebyshev.U ℚ 4 - Chebyshev.U ℚ 3 := by
  simpa only [Int.reduceAdd] using Chebyshev.U_add_two ℚ 3

private theorem barrier_U_6 :
    Chebyshev.U ℚ 6 = 2 * X * Chebyshev.U ℚ 5 - Chebyshev.U ℚ 4 := by
  simpa only [Int.reduceAdd] using Chebyshev.U_add_two ℚ 4

private theorem barrier_U_7 :
    Chebyshev.U ℚ 7 = 2 * X * Chebyshev.U ℚ 6 - Chebyshev.U ℚ 5 := by
  simpa only [Int.reduceAdd] using Chebyshev.U_add_two ℚ 5

theorem barrierCase1AX_eq_explicit : barrierCase1AX = barrierCase1AXExplicit := by
  apply Polynomial.funext
  intro x
  norm_num [barrierCase1AX, barrierCase1AXExplicit, barrierCase1QX,
    barrierCase1QY, barrierFiniteUDerivative, barrierFinitePowerDerivative,
    barrierP1Finite, barrierV1Finite, Finset.sum_range_succ,
    eval_finsetSum, Chebyshev.U_two, barrier_U_3, barrier_U_4,
    barrier_U_5, barrier_U_6, barrier_U_7]
  ring

theorem barrierCase1AX_natDegree : barrierCase1AX.natDegree = 13 := by
  rw [barrierCase1AX_eq_explicit]
  unfold barrierCase1AXExplicit
  compute_degree!

theorem barrierCase1AY_eq_explicit : barrierCase1AY = barrierCase1AYExplicit := by
  apply Polynomial.funext
  intro x
  norm_num [barrierCase1AY, barrierCase1AYExplicit, barrierCase1QX,
    barrierCase1QY, barrierFiniteUDerivative, barrierFinitePowerDerivative,
    barrierP1Finite, barrierV1Finite, Finset.sum_range_succ,
    eval_finsetSum, Chebyshev.U_two, barrier_U_3, barrier_U_4,
    barrier_U_5, barrier_U_6, barrier_U_7]
  ring

theorem barrierCase1AY_natDegree : barrierCase1AY.natDegree = 9 := by
  rw [barrierCase1AY_eq_explicit]
  unfold barrierCase1AYExplicit
  compute_degree!



def barrierCase1XBrackets : List ℤ :=
  [-9917299785, -2259572153, 2543808026, 4437270259, 6348298970]

theorem barrierCase1AX_bracket_signs (m : ℤ) (hm : m ∈ barrierCase1XBrackets) :
    barrierCase1AX.eval (barrierBracketLeft m) *
      barrierCase1AX.eval (barrierBracketRight m) < 0 := by
  rw [barrierCase1AX_eq_explicit]
  simp only [barrierCase1XBrackets, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  <;> norm_num [barrierCase1AXExplicit, barrierBracketLeft, barrierBracketRight, eval_pow]

theorem barrierCase1X_bracket_domain (m : ℤ) (hm : m ∈ barrierCase1XBrackets) :
    -1 < barrierBracketLeft m ∧ barrierBracketRight m < 1 ∧
      (barrierBracketRight m < 0 ∨ 0 < barrierBracketLeft m) := by
  simp only [barrierCase1XBrackets, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  <;> norm_num [barrierBracketLeft, barrierBracketRight]

def barrierCase1YBrackets : List ℤ :=
  [532669786, 2504239325, 5701738806, 7966939383, 9454490138]

theorem barrierCase1AY_bracket_signs (m : ℤ) (hm : m ∈ barrierCase1YBrackets) :
    barrierCase1AY.eval (barrierBracketLeft m) *
      barrierCase1AY.eval (barrierBracketRight m) < 0 := by
  rw [barrierCase1AY_eq_explicit]
  simp only [barrierCase1YBrackets, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  <;> norm_num [barrierCase1AYExplicit, barrierBracketLeft, barrierBracketRight, eval_pow]

theorem barrierCase1Y_bracket_domain (m : ℤ) (hm : m ∈ barrierCase1YBrackets) :
    0 < barrierBracketLeft m ∧ barrierBracketRight m < 1 := by
  simp only [barrierCase1YBrackets, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  <;> norm_num [barrierBracketLeft, barrierBracketRight]

def barrierCase1AYTransformExplicit : ℝ[X] :=
  C (7/48) +
    C (-82502761/37500000) * X ^ 1 +
    C (-153864091/18750000) * X ^ 2 +
    C (674992019/37500000) * X ^ 3 +
    C (337427861/4687500) * X ^ 4 +
    C (52708561/7500000) * X ^ 5 +
    C (-266783927/3750000) * X ^ 6 +
    C (107903701/7500000) * X ^ 7 +
    C (15916019/18750000) * X ^ 8 +
    C (-1/12) * X ^ 9

theorem barrierCase1AY_transform_eq_explicit :
    barrierDescartesTransform (barrierCase1AY.map (Rat.castHom ℝ)) 9 0 1 =
      barrierCase1AYTransformExplicit := by
  apply Polynomial.funext
  intro x
  norm_num [barrierDescartesTransform, barrierCase1AY_eq_explicit,
    barrierCase1AYExplicit, barrierCase1AYTransformExplicit,
    Finset.sum_range_succ, eval_finsetSum, eval_pow, coeff_C_mul, coeff_X_pow, coeff_X]
  ring

theorem barrierCase1AY_transform_signVariations :
    (barrierDescartesTransform (barrierCase1AY.map (Rat.castHom ℝ)) 9 0 1).signVariations = 5 := by
  rw [barrierCase1AY_transform_eq_explicit]
  have hd : barrierCase1AYTransformExplicit.degree = 9 := by
    unfold barrierCase1AYTransformExplicit
    compute_degree!
  rw [signVariations, coeffList, hd]
  norm_num [barrierCase1AYTransformExplicit,
    List.range_succ, List.destutter, List.destutter', sign_apply,
    coeff_C_mul, coeff_X_pow, coeff_X]


end

section

theorem barrierCase1AX_subdivision_nonzero :
    barrierCase1AX.eval (-1) ≠ 0 ∧ barrierCase1AX.eval (-1 / 2) ≠ 0 ∧
      barrierCase1AX.eval 0 ≠ 0 ∧ barrierCase1AX.eval (1 / 2) ≠ 0 ∧
      barrierCase1AX.eval 1 ≠ 0 := by
  rw [barrierCase1AX_eq_explicit]
  norm_num [barrierCase1AXExplicit, Polynomial.eval_pow]


open Polynomial
open scoped BigOperators

def barrierCase1AXCoefficient (k : ℕ) : ℚ :=
  ([19/48, -27654673/60000000, -2660802911/300000000, 246612221/20000000, 198644883/6250000, -9182425759/300000000, -320848639/10000000, 252958279/10000000, -4542019331/50000000, 8873559613/100000000, 3723872963/100000000, -3407762831/100000000, 3242106693/50000000, -6401402757/100000000] : List ℚ).getD k 0

theorem barrierCase1AX_coeff_small (k : ℕ) (hk : k < 14) :
    barrierCase1AX.coeff k = barrierCase1AXCoefficient k := by
  interval_cases k
  <;> rw [barrierCase1AX_eq_explicit]
  <;> norm_num [barrierCase1AXExplicit, barrierCase1AXCoefficient,
    coeff_C_mul, coeff_X_pow, coeff_X]

theorem barrierCase1AX_transform_eval (a b x : ℝ) :
    (barrierDescartesTransform (barrierCase1AX.map (Rat.castHom ℝ)) 13 a b).eval x =
      ∑ k ∈ Finset.range 14,
        ((barrierCase1AXCoefficient k : ℚ) : ℝ) * (a + b * x) ^ k * (1 + x) ^ (13 - k) := by
  unfold barrierDescartesTransform
  rw [eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Polynomial.coeff_map, barrierCase1AX_coeff_small k (Finset.mem_range.mp hk)]
  simp only [eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_one]
  rfl

end

theorem barrierBracketLeft_lt_right (m : ℤ) :
    barrierBracketLeft m < barrierBracketRight m := by
  unfold barrierBracketLeft barrierBracketRight
  apply div_lt_div_of_pos_right _ (by norm_num : (0 : ℚ) < 10000000000)
  push_cast
  linarith

theorem barrierCase1AX_root_in_each_bracket (m : ℤ) (hm : m ∈ barrierCase1XBrackets) :
    ∃ x : ℝ, x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) ∧
      (barrierCase1AX.map (Rat.castHom ℝ)).eval x = 0 := by
  exact rationalPolynomial_root_mem_Ioo_of_eval_mul_neg barrierCase1AX
    (barrierBracketLeft_lt_right m) (barrierCase1AX_bracket_signs m hm)

theorem barrierCase1AY_root_in_each_bracket (m : ℤ) (hm : m ∈ barrierCase1YBrackets) :
    ∃ x : ℝ, x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) ∧
      (barrierCase1AY.map (Rat.castHom ℝ)).eval x = 0 := by
  exact rationalPolynomial_root_mem_Ioo_of_eval_mul_neg barrierCase1AY
    (barrierBracketLeft_lt_right m) (barrierCase1AY_bracket_signs m hm)

open Polynomial

def barrierCase1AXTransform0Explicit : ℝ[X] :=
  C (197396341 / 37500000) +
    C (-41373586421 / 150000000) * X ^ 1 +
    C (-7836353153 / 3750000) * X ^ 2 +
    C (-828479578847 / 120000000) * X ^ 3 +
    C (-3279246739423 / 240000000) * X ^ 4 +
    C (-87449292655397 / 4800000000) * X ^ 5 +
    C (-41679500981699 / 2400000000) * X ^ 6 +
    C (-58739170281629 / 4800000000) * X ^ 7 +
    C (-7786668227467 / 1200000000) * X ^ 8 +
    C (-133002937907977 / 51200000000) * X ^ 9 +
    C (-118601317890961 / 153600000000) * X ^ 10 +
    C (-33203272271481 / 204800000000) * X ^ 11 +
    C (-8794089445937 / 409600000000) * X ^ 12 +
    C (-3292884383081 / 2457600000000) * X ^ 13

theorem barrierCase1AX_transform0_eq_explicit :
    barrierDescartesTransform (barrierCase1AX.map (Rat.castHom ℝ)) 13 (-1) (-1 / 2) =
      barrierCase1AXTransform0Explicit := by
  apply Polynomial.funext
  intro x
  rw [barrierCase1AX_transform_eval]
  norm_num [barrierCase1AXCoefficient, barrierCase1AXTransform0Explicit,
    Finset.sum_range_succ, eval_pow]
  ring

open Polynomial

def barrierCase1AXTransform1Explicit : ℝ[X] :=
  C (-3292884383081 / 2457600000000) +
    C (-8212614321121 / 614400000000) * X ^ 1 +
    C (-13289192880343 / 204800000000) * X ^ 2 +
    C (-19680190814197 / 102400000000) * X ^ 3 +
    C (-18611893427857 / 51200000000) * X ^ 4 +
    C (-16476547481449 / 38400000000) * X ^ 5 +
    C (-5106428303839 / 19200000000) * X ^ 6 +
    C (9121431887 / 384000000) * X ^ 7 +
    C (1988423816251 / 9600000000) * X ^ 8 +
    C (19834078543 / 100000000) * X ^ 9 +
    C (81989107001 / 800000000) * X ^ 10 +
    C (37707757849 / 1200000000) * X ^ 11 +
    C (645154673 / 120000000) * X ^ 12 +
    C (19 / 48) * X ^ 13

theorem barrierCase1AX_transform1_eq_explicit :
    barrierDescartesTransform (barrierCase1AX.map (Rat.castHom ℝ)) 13 (-1 / 2) (0) =
      barrierCase1AXTransform1Explicit := by
  apply Polynomial.funext
  intro x
  rw [barrierCase1AX_transform_eval]
  norm_num [barrierCase1AXCoefficient, barrierCase1AXTransform1Explicit,
    Finset.sum_range_succ, eval_pow]
  ring

def barrierCase1AXTransform2Explicit : ℝ[X] :=
  C (19 / 48) +
    C (196615109 / 40000000) * X ^ 1 +
    C (31070636329 / 1200000000) * X ^ 2 +
    C (60119116971 / 800000000) * X ^ 3 +
    C (76660107233 / 600000000) * X ^ 4 +
    C (1111514856533 / 9600000000) * X ^ 5 +
    C (127932804871 / 9600000000) * X ^ 6 +
    C (-1874949014717 / 19200000000) * X ^ 7 +
    C (-4686595639121 / 38400000000) * X ^ 8 +
    C (-11050376940053 / 153600000000) * X ^ 9 +
    C (-6607368253423 / 307200000000) * X ^ 10 +
    C (-1338397959119 / 614400000000) * X ^ 11 +
    C (194202312139 / 614400000000) * X ^ 12 +
    C (151932441073 / 2457600000000) * X ^ 13

theorem barrierCase1AX_transform2_eq_explicit :
    barrierDescartesTransform (barrierCase1AX.map (Rat.castHom ℝ)) 13 (0) (1 / 2) =
      barrierCase1AXTransform2Explicit := by
  apply Polynomial.funext
  intro x
  rw [barrierCase1AX_transform_eval]
  norm_num [barrierCase1AXCoefficient, barrierCase1AXTransform2Explicit,
    Finset.sum_range_succ, eval_pow]
  ring

def barrierCase1AXTransform3Explicit : ℝ[X] :=
  C (151932441073 / 2457600000000) +
    C (1586717109671 / 1228800000000) * X ^ 1 +
    C (5851476953239 / 614400000000) * X ^ 2 +
    C (2425740911911 / 76800000000) * X ^ 3 +
    C (4594095868667 / 153600000000) * X ^ 4 +
    C (-5153765194747 / 38400000000) * X ^ 5 +
    C (-2783183411353 / 4800000000) * X ^ 6 +
    C (-2656223354401 / 2400000000) * X ^ 7 +
    C (-5991394151383 / 4800000000) * X ^ 8 +
    C (-42883475647 / 50000000) * X ^ 9 +
    C (-8021241613 / 24000000) * X ^ 10 +
    C (-2870130291 / 50000000) * X ^ 11 +
    C (-36667881 / 50000000) * X ^ 12 +
    C (-1 / 3) * X ^ 13

theorem barrierCase1AX_transform3_eq_explicit :
    barrierDescartesTransform (barrierCase1AX.map (Rat.castHom ℝ)) 13 (1 / 2) (1) =
      barrierCase1AXTransform3Explicit := by
  apply Polynomial.funext
  intro x
  rw [barrierCase1AX_transform_eval]
  norm_num [barrierCase1AXCoefficient, barrierCase1AXTransform3Explicit,
    Finset.sum_range_succ, eval_pow]
  ring

theorem barrierCase1AY_interval_roots_card_le (s : Finset ℝ)
    (hs : ∀ x ∈ s, x ∈ Set.Ioo (0 : ℝ) 1 ∧
      (barrierCase1AY.map (Rat.castHom ℝ)).eval x = 0) :
    s.card ≤ 5 := by
  have hd : (barrierCase1AY.map (Rat.castHom ℝ)).natDegree ≤ 9 := by
    calc
      _ ≤ barrierCase1AY.natDegree := Polynomial.natDegree_map_le
      _ = 9 := barrierCase1AY_natDegree
  have hne : barrierDescartesTransform
      (barrierCase1AY.map (Rat.castHom ℝ)) 9 0 1 ≠ 0 := by
    intro hz
    have h := barrierCase1AY_transform_signVariations
    rw [hz, Polynomial.signVariations_zero] at h
    norm_num at h
  simpa only [barrierCase1AY_transform_signVariations] using
    barrierDescartes_interval_roots_card_le
      (barrierCase1AY.map (Rat.castHom ℝ)) 9 0 1 hd hne s hs

private theorem barrierCase1Y_bracket_subset_interval {m : ℤ}
    (hm : m ∈ barrierCase1YBrackets) {x : ℝ}
    (hx : x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ)) :
    x ∈ Set.Ioo (0 : ℝ) 1 := by
  obtain ⟨ha, hb⟩ := barrierCase1Y_bracket_domain m hm
  have ha' : (0 : ℝ) < (barrierBracketLeft m : ℝ) := by exact_mod_cast ha
  have hb' : (barrierBracketRight m : ℝ) < (1 : ℝ) := by exact_mod_cast hb
  exact ⟨ha'.trans hx.1, hx.2.trans hb'⟩

private theorem barrierCase1Y_brackets_disjoint {m n : ℤ}
    (hm : m ∈ barrierCase1YBrackets) (hn : n ∈ barrierCase1YBrackets)
    (hmn : m ≠ n) {x : ℝ}
    (hx : x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ))
    (hy : x ∈ Set.Ioo (barrierBracketLeft n : ℝ) (barrierBracketRight n : ℝ)) :
    False := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  simp only [barrierCase1YBrackets, List.mem_cons, List.not_mem_nil, or_false] at hm hn
  rcases hm with rfl | rfl | rfl | rfl | rfl
  <;> rcases hn with rfl | rfl | rfl | rfl | rfl
  all_goals try exact hmn rfl
  all_goals norm_num [barrierBracketLeft, barrierBracketRight] at hx0 hx1 hy0 hy1
  all_goals linarith

private def barrierCase1YChosenRoot (m : ℤ) : ℝ :=
  if hm : m ∈ barrierCase1YBrackets then
    Classical.choose (barrierCase1AY_root_in_each_bracket m hm)
  else 0

private theorem barrierCase1YChosenRoot_spec (m : ℤ)
    (hm : m ∈ barrierCase1YBrackets) :
    barrierCase1YChosenRoot m ∈
        Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) ∧
      (barrierCase1AY.map (Rat.castHom ℝ)).eval (barrierCase1YChosenRoot m) = 0 := by
  simpa only [barrierCase1YChosenRoot, dif_pos hm] using
    Classical.choose_spec (barrierCase1AY_root_in_each_bracket m hm)

private def barrierCase1YChosenRoots : Finset ℝ := by
  classical
  exact barrierCase1YBrackets.toFinset.image barrierCase1YChosenRoot

private theorem barrierCase1YChosenRoots_card : barrierCase1YChosenRoots.card = 5 := by
  classical
  have hinj : Set.InjOn barrierCase1YChosenRoot
      (↑barrierCase1YBrackets.toFinset : Set ℤ) := by
    intro m hm n hn heq
    have hm' : m ∈ barrierCase1YBrackets := List.mem_toFinset.mp hm
    have hn' : n ∈ barrierCase1YBrackets := List.mem_toFinset.mp hn
    by_contra hmn
    exact barrierCase1Y_brackets_disjoint hm' hn' hmn
      (barrierCase1YChosenRoot_spec m hm').1
      (by simpa only [heq] using (barrierCase1YChosenRoot_spec n hn').1)
  unfold barrierCase1YChosenRoots
  rw [Finset.card_image_of_injOn hinj]
  norm_num [barrierCase1YBrackets]

private theorem barrierCase1YChosenRoots_spec {x : ℝ}
    (hx : x ∈ barrierCase1YChosenRoots) :
    x ∈ Set.Ioo (0 : ℝ) 1 ∧ (barrierCase1AY.map (Rat.castHom ℝ)).eval x = 0 := by
  classical
  change x ∈ barrierCase1YBrackets.toFinset.image barrierCase1YChosenRoot at hx
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
  have hm' : m ∈ barrierCase1YBrackets := List.mem_toFinset.mp hm
  have hr := barrierCase1YChosenRoot_spec m hm'
  exact ⟨barrierCase1Y_bracket_subset_interval hm' hr.1, hr.2⟩

private theorem barrierCase1AY_root_mem_chosen {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hr : (barrierCase1AY.map (Rat.castHom ℝ)).eval x = 0) :
    x ∈ barrierCase1YChosenRoots := by
  classical
  by_contra hnot
  have hb : (insert x barrierCase1YChosenRoots).card ≤ 5 := by
    apply barrierCase1AY_interval_roots_card_le
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact ⟨hx, hr⟩
    · exact barrierCase1YChosenRoots_spec hy
  rw [Finset.card_insert_of_notMem hnot, barrierCase1YChosenRoots_card] at hb
  norm_num at hb

theorem barrierCase1AY_roots_exhausted {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hr : (barrierCase1AY.map (Rat.castHom ℝ)).eval x = 0) :
    ∃ m ∈ barrierCase1YBrackets,
      x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) := by
  classical
  have hmem := barrierCase1AY_root_mem_chosen hx hr
  change x ∈ barrierCase1YBrackets.toFinset.image barrierCase1YChosenRoot at hmem
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hmem
  have hm' : m ∈ barrierCase1YBrackets := List.mem_toFinset.mp hm
  exact ⟨m, hm', (barrierCase1YChosenRoot_spec m hm').1⟩


theorem barrierCase1AX_transform0_signVariations :
    (barrierDescartesTransform (barrierCase1AX.map (Rat.castHom ℝ)) 13 (-1) (-1 / 2)).signVariations = 1 := by
  rw [barrierCase1AX_transform0_eq_explicit]
  have hd : barrierCase1AXTransform0Explicit.degree = 13 := by
    unfold barrierCase1AXTransform0Explicit
    compute_degree!
  rw [signVariations, coeffList, hd]
  norm_num [barrierCase1AXTransform0Explicit,
    List.range_succ, List.destutter, List.destutter', sign_apply,
    coeff_C_mul, coeff_X_pow, coeff_X]


end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Energy.BarrierGlobalMaxReduction
namespace OAI

noncomputable section

namespace InternalCatalan.GlobalMaxReduction

open Set Filter
open scoped Topology

theorem le_on_Icc_of_critical_le {f : ℝ → ℝ} {a b M : ℝ}
    (hcont : ContinuousOn f (Icc a b))
    (ha : f a ≤ M) (hb : f b ≤ M)
    (hcritical : ∀ c ∈ Ioo a b, deriv f c = 0 → f c ≤ M) :
    ∀ x ∈ Icc a b, f x ≤ M := by
  intro x hx
  obtain ⟨c, hc, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨x, hx⟩ hcont
  have hcM : f c ≤ M := by
    by_cases hca : c = a
    · simpa only [hca] using ha
    by_cases hcb : c = b
    · simpa only [hcb] using hb
    have hcint : c ∈ Ioo a b :=
      ⟨lt_of_le_of_ne hc.1 (Ne.symm hca), lt_of_le_of_ne hc.2 hcb⟩
    have hlocal : IsLocalMax f c :=
      hmax.isLocalMax (Icc_mem_nhds hcint.1 hcint.2)
    exact hcritical c hcint hlocal.deriv_eq_zero
  exact (hmax hx).trans hcM

theorem exists_left_cutoff {f : ℝ → ℝ} {a x M : ℝ}
    (hlim : Tendsto f (𝓝[>] a) atBot) (hax : a < x) :
    ∃ l ∈ Ioo a x, f l ≤ M := by
  have hinterval : ∀ᶠ l in 𝓝[>] a, l ∈ Ioo a x := Ioo_mem_nhdsGT hax
  exact (hinterval.and (hlim.eventually (eventually_le_atBot M))).exists

theorem exists_right_cutoff {f : ℝ → ℝ} {x b M : ℝ}
    (hlim : Tendsto f (𝓝[<] b) atBot) (hxb : x < b) :
    ∃ r ∈ Ioo x b, f r ≤ M := by
  have hinterval : ∀ᶠ r in 𝓝[<] b, r ∈ Ioo x b := Ioo_mem_nhdsLT hxb
  exact (hinterval.and (hlim.eventually (eventually_le_atBot M))).exists

theorem le_on_Ioo_of_limits_of_critical_le {f : ℝ → ℝ} {a b M : ℝ}
    (hcont : ContinuousOn f (Ioo a b))
    (hleft : Tendsto f (𝓝[>] a) atBot)
    (hright : Tendsto f (𝓝[<] b) atBot)
    (hcritical : ∀ c ∈ Ioo a b, deriv f c = 0 → f c ≤ M) :
    ∀ x ∈ Ioo a b, f x ≤ M := by
  intro x hx
  obtain ⟨l, hl, hlM⟩ := exists_left_cutoff (M := M) hleft hx.1
  obtain ⟨r, hr, hrM⟩ := exists_right_cutoff (M := M) hright hx.2
  have hsub : Icc l r ⊆ Ioo a b := by
    intro z hz
    exact ⟨lt_of_lt_of_le hl.1 hz.1, lt_of_le_of_lt hz.2 hr.2⟩
  exact le_on_Icc_of_critical_le (hcont.mono hsub) hlM hrM
    (fun c hc hd => hcritical c (hsub ⟨hc.1.le, hc.2.le⟩) hd)
    x ⟨hl.2.le, hr.1.le⟩

theorem le_on_Ico_of_limit_of_critical_le {f : ℝ → ℝ} {a b M : ℝ}
    (hcont : ContinuousOn f (Ico a b))
    (ha : f a ≤ M)
    (hright : Tendsto f (𝓝[<] b) atBot)
    (hcritical : ∀ c ∈ Ioo a b, deriv f c = 0 → f c ≤ M) :
    ∀ x ∈ Ico a b, f x ≤ M := by
  intro x hx
  obtain ⟨r, hr, hrM⟩ := exists_right_cutoff (M := M) hright hx.2
  have hsub : Icc a r ⊆ Ico a b := by
    intro z hz
    exact ⟨hz.1, lt_of_le_of_lt hz.2 hr.2⟩
  exact le_on_Icc_of_critical_le (hcont.mono hsub) ha hrM
    (fun c hc hd => hcritical c ⟨hc.1, hc.2.trans hr.2⟩ hd)
    x ⟨hx.1, hr.1.le⟩

theorem le_on_Ioo_of_stationary_cover {f : ℝ → ℝ} {a b M : ℝ} {S : Set ℝ}
    (hcont : ContinuousOn f (Ioo a b))
    (hleft : Tendsto f (𝓝[>] a) atBot)
    (hright : Tendsto f (𝓝[<] b) atBot)
    (hcover : ∀ c ∈ Ioo a b, deriv f c = 0 → c ∈ S)
    (hvalues : ∀ c ∈ S, f c ≤ M) :
    ∀ x ∈ Ioo a b, f x ≤ M := by
  exact le_on_Ioo_of_limits_of_critical_le hcont hleft hright
    (fun c hc hd => hvalues c (hcover c hc hd))

theorem le_on_two_components_of_stationary_cover
    {f : ℝ → ℝ} {a c b M : ℝ} {S : Set ℝ}
    (hcontLeft : ContinuousOn f (Ico a c))
    (hcontRight : ContinuousOn f (Ioo c b))
    (ha : f a ≤ M)
    (hcLeft : Tendsto f (𝓝[<] c) atBot)
    (hcRight : Tendsto f (𝓝[>] c) atBot)
    (hbLeft : Tendsto f (𝓝[<] b) atBot)
    (hcover : ∀ x ∈ Ioo a c ∪ Ioo c b, deriv f x = 0 → x ∈ S)
    (hvalues : ∀ x ∈ S, f x ≤ M) :
    ∀ x ∈ Ico a c ∪ Ioo c b, f x ≤ M := by
  intro x hx
  rcases hx with hx | hx
  · exact le_on_Ico_of_limit_of_critical_le hcontLeft ha hcLeft
      (fun z hz hd => hvalues z (hcover z (Or.inl hz) hd)) x hx
  · exact le_on_Ioo_of_limits_of_critical_le hcontRight hcRight hbLeft
      (fun z hz hd => hvalues z (hcover z (Or.inr hz) hd)) x hx

end InternalCatalan.GlobalMaxReduction

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.FirstBarrier.BarrierCaseOnePointLogInputs
namespace OAI

noncomputable section
namespace InternalCatalan.Case1PointData

def FixedLogNormalization (s : ℝ) (m : ℤ) (y : ℚ) : Prop :=
  s = (2 : ℝ) ^ m * (y : ℝ) ∧
    (y : ℝ) ∈ Set.Icc (1 : ℝ) 2 ∧ |(m : ℝ)| ≤ 100

def X0 : ℚ := (-1983459957 / 2000000000)


theorem X0_normalizations :
    FixedLogNormalization |(X0 : ℝ)| (-1) (1983459957 / 1000000000) ∧
    FixedLogNormalization (1 - (X0 : ℝ)) (0) (3983459957 / 2000000000) ∧
    FixedLogNormalization (1 + (X0 : ℝ) ^ 2) (0) (7934113401022441849 / 4000000000000000000) := by
  norm_num [FixedLogNormalization, X0, Set.mem_Icc]

def X1 : ℚ := (-2259572153 / 10000000000)


theorem X1_normalizations :
    FixedLogNormalization |(X1 : ℝ)| (-3) (2259572153 / 1250000000) ∧
    FixedLogNormalization (1 - (X1 : ℝ)) (0) (12259572153 / 10000000000) ∧
    FixedLogNormalization (1 + (X1 : ℝ) ^ 2) (0) (105105666314613055409 / 100000000000000000000) := by
  norm_num [FixedLogNormalization, X1, Set.mem_Icc]

def X2 : ℚ := (1271904013 / 5000000000)


theorem X2_normalizations :
    FixedLogNormalization |(X2 : ℝ)| (-2) (1271904013 / 1250000000) ∧
    FixedLogNormalization (1 - (X2 : ℝ)) (-1) (3728095987 / 2500000000) ∧
    FixedLogNormalization (1 + (X2 : ℝ) ^ 2) (0) (26617739818285504169 / 25000000000000000000) := by
  norm_num [FixedLogNormalization, X2, Set.mem_Icc]

def X3 : ℚ := (4437270259 / 10000000000)


theorem X3_normalizations :
    FixedLogNormalization |(X3 : ℝ)| (-2) (4437270259 / 2500000000) ∧
    FixedLogNormalization (1 - (X3 : ℝ)) (-1) (5562729741 / 5000000000) ∧
    FixedLogNormalization (1 + (X3 : ℝ) ^ 2) (0) (119689367351405927081 / 100000000000000000000) := by
  norm_num [FixedLogNormalization, X3, Set.mem_Icc]

def X4 : ℚ := (634829897 / 1000000000)


theorem X4_normalizations :
    FixedLogNormalization |(X4 : ℝ)| (-1) (634829897 / 500000000) ∧
    FixedLogNormalization (1 - (X4 : ℝ)) (-2) (365170103 / 250000000) ∧
    FixedLogNormalization (1 + (X4 : ℝ) ^ 2) (0) (1403008998125030609 / 1000000000000000000) := by
  norm_num [FixedLogNormalization, X4, Set.mem_Icc]

def X5 : ℚ := -1


theorem X5_normalizations :
    FixedLogNormalization |(X5 : ℝ)| (0) 1 ∧
    FixedLogNormalization (1 - (X5 : ℝ)) (1) 1 ∧
    FixedLogNormalization (1 + (X5 : ℝ) ^ 2) (1) 1 := by
  norm_num [FixedLogNormalization, X5, Set.mem_Icc]







def Y0 : ℚ := (266334893 / 5000000000)


theorem Y0_normalizations :
    FixedLogNormalization (Y0 : ℝ) (-5) (266334893 / 156250000) ∧
    FixedLogNormalization (1 - (Y0 : ℝ)) (-1) (4733665107 / 2500000000) := by
  norm_num [FixedLogNormalization, Y0, Set.mem_Icc]

def Y1 : ℚ := (100169573 / 400000000)


theorem Y1_normalizations :
    FixedLogNormalization (Y1 : ℝ) (-2) (100169573 / 100000000) ∧
    FixedLogNormalization (1 - (Y1 : ℝ)) (-1) (299830427 / 200000000) := by
  norm_num [FixedLogNormalization, Y1, Set.mem_Icc]

def Y2 : ℚ := (2850869403 / 5000000000)


theorem Y2_normalizations :
    FixedLogNormalization (Y2 : ℝ) (-1) (2850869403 / 2500000000) ∧
    FixedLogNormalization (1 - (Y2 : ℝ)) (-2) (2149130597 / 1250000000) := by
  norm_num [FixedLogNormalization, Y2, Set.mem_Icc]

def Y3 : ℚ := (7966939383 / 10000000000)


theorem Y3_normalizations :
    FixedLogNormalization (Y3 : ℝ) (-1) (7966939383 / 5000000000) ∧
    FixedLogNormalization (1 - (Y3 : ℝ)) (-3) (2033060617 / 1250000000) := by
  norm_num [FixedLogNormalization, Y3, Set.mem_Icc]

def Y4 : ℚ := (4727245069 / 5000000000)


theorem Y4_normalizations :
    FixedLogNormalization (Y4 : ℝ) (-1) (4727245069 / 2500000000) ∧
    FixedLogNormalization (1 - (Y4 : ℝ)) (-5) (272754931 / 156250000) := by
  norm_num [FixedLogNormalization, Y4, Set.mem_Icc]

end InternalCatalan.Case1PointData

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Energy.BarrierLogRatConstants
namespace OAI

noncomputable section

namespace InternalCatalan

section

open scoped BigOperators

def barrierLogH (y : ℝ) : ℝ :=
  2 * ∑ j ∈ Finset.range 18,
    ((y - 1) / (y + 1)) ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ)

theorem barrier_hasSum_odd_log {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun k : ℕ => 2 * q ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ))
      (Real.log (1 + q) - Real.log (1 - q)) := by
  let f : ℕ → ℝ := fun k => q ^ k / (k : ℝ) - (-q) ^ k / (k : ℝ)
  have hq : q ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, hq1⟩
  have hnq : -q ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hbase : HasSum f (Real.log (1 + q) - Real.log (1 - q)) := by
    convert (energy_hasSum_real_power_div hq).sub
      (energy_hasSum_real_power_div hnq) using 1
    all_goals first
      | rfl
      | (simp only [sub_neg_eq_add]
         ring)
  have heven (k : ℕ) : f (2 * k) = 0 := by
    simp [f, pow_mul]
  have hodd (k : ℕ) : f (2 * k + 1) =
      2 * q ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ) := by
    simp only [f, pow_add, pow_mul, pow_one, neg_sq]
    ring
  have hi : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    intro i j hij
    change 2 * i + 1 = 2 * j + 1 at hij
    omega
  have hs : Summable
      (fun k : ℕ => 2 * q ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)) := by
    have hcomp := hbase.summable.comp_injective hi
    change Summable (fun k : ℕ => f (2 * k + 1)) at hcomp
    simpa only [hodd] using hcomp
  have he : HasSum (fun k => f (2 * k)) 0 := by
    simpa only [heven] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
  have ho : HasSum (fun k => f (2 * k + 1))
      (∑' k : ℕ, 2 * q ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)) := by
    simpa only [hodd] using hs.hasSum
  have heq : (∑' k : ℕ, 2 * q ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)) =
      Real.log (1 + q) - Real.log (1 - q) := by
    simpa only [zero_add] using (he.even_add_odd ho).unique hbase
  rw [← heq]
  exact hs.hasSum

theorem barrier_hasSum_scaled_log {y : ℝ} (hy : 1 ≤ y) :
    HasSum (fun k : ℕ => 2 * ((y - 1) / (y + 1)) ^ (2 * k + 1) /
      ((2 * k + 1 : ℕ) : ℝ)) (Real.log y) := by
  let q := (y - 1) / (y + 1)
  have hd : 0 < y + 1 := by linarith
  have hq0 : 0 ≤ q := div_nonneg (sub_nonneg.mpr hy) hd.le
  have hq1 : q < 1 := (div_lt_one hd).2 (by linarith)
  have hp : 1 + q ≠ 0 := ne_of_gt (by linarith)
  have hn : 1 - q ≠ 0 := ne_of_gt (by linarith)
  have heq : (1 + q) / (1 - q) = y := by
    apply (div_eq_iff hn).2
    dsimp [q]
    field_simp [ne_of_gt hd]
    ring
  have hlog : Real.log (1 + q) - Real.log (1 - q) = Real.log y := by
    rw [← Real.log_div hp hn, heq]
  simpa only [hlog] using barrier_hasSum_odd_log hq0 hq1

private theorem barrier_odd_log_shift_le_geometric {q : ℝ} (hq0 : 0 ≤ q)
    (m k : ℕ) :
    2 * q ^ (2 * (k + m) + 1) / ((2 * (k + m) + 1 : ℕ) : ℝ) ≤
      (2 * q ^ (2 * m + 1) / ((2 * m + 1 : ℕ) : ℝ)) * (q ^ 2) ^ k := by
  have hden0 : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by positivity
  have hden : ((2 * m + 1 : ℕ) : ℝ) ≤ ((2 * (k + m) + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.le_add_left m k)) 1
  have hnum : 0 ≤ 2 * q ^ (2 * (k + m) + 1) :=
    mul_nonneg (by norm_num) (pow_nonneg hq0 _)
  have hexp : 2 * (k + m) + 1 = (2 * m + 1) + 2 * k := by ring
  calc
    _ ≤ 2 * q ^ (2 * (k + m) + 1) / ((2 * m + 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_left hnum hden0 hden
    _ = (2 * q ^ (2 * m + 1) / ((2 * m + 1 : ℕ) : ℝ)) * (q ^ 2) ^ k := by
      rw [hexp, pow_add, pow_mul]
      ring

theorem barrier_odd_log_remainder_bounds {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (m : ℕ) :
    0 ≤ (Real.log (1 + q) - Real.log (1 - q)) -
        ∑ k ∈ Finset.range m, 2 * q ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ) ∧
      (Real.log (1 + q) - Real.log (1 - q)) -
          (∑ k ∈ Finset.range m, 2 * q ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)) ≤
        2 * q ^ (2 * m + 1) / (((2 * m + 1 : ℕ) : ℝ) * (1 - q ^ 2)) := by
  have hseries := barrier_hasSum_odd_log hq0 hq1
  have htail : HasSum
      (fun k : ℕ => 2 * q ^ (2 * (k + m) + 1) / ((2 * (k + m) + 1 : ℕ) : ℝ))
      ((Real.log (1 + q) - Real.log (1 - q)) -
        ∑ k ∈ Finset.range m, 2 * q ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)) := by
    exact (hasSum_nat_add_iff'
      (f := fun k : ℕ => 2 * q ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)) m).2 hseries
  have hq2 : q ^ 2 < 1 := by
    simpa only [pow_two, one_mul] using mul_self_lt_mul_self hq0 hq1
  have hq2abs : |q ^ 2| < 1 := by
    simpa only [abs_of_nonneg (sq_nonneg q)] using hq2
  have hgeom := (hasSum_geometric_of_abs_lt_one hq2abs).mul_left
    (2 * q ^ (2 * m + 1) / ((2 * m + 1 : ℕ) : ℝ))
  have hupper := hasSum_le (fun k => barrier_odd_log_shift_le_geometric hq0 m k)
    htail hgeom
  constructor
  · exact hasSum_le (fun k => by positivity) hasSum_zero htail
  · calc
      _ ≤ (2 * q ^ (2 * m + 1) / ((2 * m + 1 : ℕ) : ℝ)) * (1 - q ^ 2)⁻¹ := hupper
      _ = 2 * q ^ (2 * m + 1) / (((2 * m + 1 : ℕ) : ℝ) * (1 - q ^ 2)) := by
        rw [← div_eq_mul_inv, div_div]

theorem barrier_odd_log_remainder_bounds_eighteen {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    0 ≤ (Real.log (1 + q) - Real.log (1 - q)) -
        ∑ k ∈ Finset.range 18, 2 * q ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ) ∧
      (Real.log (1 + q) - Real.log (1 - q)) -
          (∑ k ∈ Finset.range 18, 2 * q ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)) ≤
        2 * q ^ 37 / (37 * (1 - q ^ 2)) := by
  simpa only [Nat.reduceMul, Nat.reduceAdd, Nat.cast_ofNat] using
    barrier_odd_log_remainder_bounds hq0 hq1 18

def barrierLogHError : ℝ := 2 * (1 / 3 : ℝ) ^ 37 / (37 * (1 - 1 / 9))

theorem barrier_log_parameter_bounds {y : ℝ} (hy : y ∈ Set.Icc (1 : ℝ) 2) :
    0 ≤ (y - 1) / (y + 1) ∧ (y - 1) / (y + 1) ≤ 1 / 3 := by
  have hd : 0 < y + 1 := by linarith [hy.1]
  constructor
  · exact div_nonneg (sub_nonneg.mpr hy.1) hd.le
  · apply (div_le_iff₀ hd).2
    linarith [hy.2]

theorem barrier_logH_remainder {y : ℝ} (hy : y ∈ Set.Icc (1 : ℝ) 2) :
    0 ≤ Real.log y - barrierLogH y ∧
      Real.log y - barrierLogH y ≤
        2 * ((y - 1) / (y + 1)) ^ 37 /
          (37 * (1 - ((y - 1) / (y + 1)) ^ 2)) := by
  let q := (y - 1) / (y + 1)
  obtain ⟨hq0, hqthird⟩ := barrier_log_parameter_bounds hy
  have hq1 : q < 1 := lt_of_le_of_lt hqthird (by norm_num)
  have hlog : Real.log (1 + q) - Real.log (1 - q) = Real.log y :=
    (barrier_hasSum_odd_log hq0 hq1).unique (barrier_hasSum_scaled_log hy.1)
  have hsum : (∑ k ∈ Finset.range 18,
      2 * q ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)) = barrierLogH y := by
    simp only [barrierLogH, Finset.mul_sum, mul_div_assoc, q]
  have h := barrier_odd_log_remainder_bounds_eighteen hq0 hq1
  rw [hlog, hsum] at h
  exact h

theorem barrier_logH_remainder_uniform {y : ℝ} (hy : y ∈ Set.Icc (1 : ℝ) 2) :
    0 ≤ Real.log y - barrierLogH y ∧
      Real.log y - barrierLogH y ≤ barrierLogHError := by
  obtain ⟨hlo, hhi⟩ := barrier_logH_remainder hy
  obtain ⟨hq0, hqthird⟩ := barrier_log_parameter_bounds hy
  let q := (y - 1) / (y + 1)
  have hpow : q ^ 37 ≤ (1 / 3 : ℝ) ^ 37 := pow_le_pow_left₀ hq0 hqthird 37
  have hsq : q ^ 2 ≤ (1 / 9 : ℝ) := by
    have h := pow_le_pow_left₀ hq0 hqthird 2
    norm_num at h
    exact h
  have hd : (0 : ℝ) < 37 * (1 - q ^ 2) := by linarith
  refine ⟨hlo, hhi.trans ?_⟩
  calc
    2 * q ^ 37 / (37 * (1 - q ^ 2)) ≤
        2 * (1 / 3 : ℝ) ^ 37 / (37 * (1 - q ^ 2)) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num)) hd.le
    _ ≤ 2 * (1 / 3 : ℝ) ^ 37 / (37 * (1 - 1 / 9)) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
    _ = barrierLogHError := rfl

theorem barrier_logH_error_101_lt :
    101 * barrierLogHError < (1 / 1000000000000000 : ℝ) := by
  norm_num [barrierLogHError]

end

section

def barrierScaledLogApprox (m : ℤ) (y : ℝ) : ℝ :=
  (m : ℝ) * barrierLogH 2 + barrierLogH y

theorem barrier_scaled_log_abs_error (m : ℤ) {y : ℝ}
    (hy : y ∈ Set.Icc (1 : ℝ) 2) :
    |Real.log ((2 : ℝ) ^ m * y) - barrierScaledLogApprox m y| ≤
      (|(m : ℝ)| + 1) * barrierLogHError := by
  have hypos : 0 < y := lt_of_lt_of_le (by norm_num) hy.1
  have h2 := barrier_logH_remainder_uniform (y := 2) ⟨by norm_num, le_rfl⟩
  have he := barrier_logH_remainder_uniform hy
  rw [Real.log_mul (zpow_ne_zero m (by norm_num)) (ne_of_gt hypos), Real.log_zpow]
  unfold barrierScaledLogApprox
  calc
    |(m : ℝ) * Real.log 2 + Real.log y - ((m : ℝ) * barrierLogH 2 + barrierLogH y)| =
        |(m : ℝ) * (Real.log 2 - barrierLogH 2) + (Real.log y - barrierLogH y)| := by
      congr 1
      ring
    _ ≤ |(m : ℝ) * (Real.log 2 - barrierLogH 2)| + |Real.log y - barrierLogH y| := by
      simpa only [Real.norm_eq_abs] using norm_add_le
        ((m : ℝ) * (Real.log 2 - barrierLogH 2)) (Real.log y - barrierLogH y)
    _ = |(m : ℝ)| * (Real.log 2 - barrierLogH 2) + (Real.log y - barrierLogH y) := by
      rw [abs_mul, abs_of_nonneg h2.1, abs_of_nonneg he.1]
    _ ≤ |(m : ℝ)| * barrierLogHError + barrierLogHError :=
      add_le_add (mul_le_mul_of_nonneg_left h2.2 (abs_nonneg _)) he.2
    _ = (|(m : ℝ)| + 1) * barrierLogHError := by ring

theorem barrier_scaled_log_abs_error_lt (m : ℤ) {y : ℝ}
    (hy : y ∈ Set.Icc (1 : ℝ) 2) (hm : |(m : ℝ)| ≤ 100) :
    |Real.log ((2 : ℝ) ^ m * y) - barrierScaledLogApprox m y| <
      (1 / 1000000000000000 : ℝ) := by
  have he : 0 ≤ barrierLogHError := by unfold barrierLogHError; positivity
  calc
    _ ≤ (|(m : ℝ)| + 1) * barrierLogHError := barrier_scaled_log_abs_error m hy
    _ ≤ 101 * barrierLogHError := mul_le_mul_of_nonneg_right (by linarith) he
    _ < (1 / 1000000000000000 : ℝ) := barrier_logH_error_101_lt

theorem barrier_log_two_lower : (693146 / 1000000 : ℝ) < Real.log 2 := by
  have h := (barrier_logH_remainder (y := 2) (by constructor <;> norm_num)).1
  have hfinite : (693146 / 1000000 : ℝ) < barrierLogH 2 := by
    norm_num [barrierLogH, Finset.sum_range_succ]
  linarith







open scoped BigOperators

def barrierLogHRat (y : ℚ) : ℚ :=
  2 * ∑ j ∈ Finset.range 18,
    ((y - 1) / (y + 1)) ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℚ)

def barrierScaledLogRat (m : ℤ) (y : ℚ) : ℚ :=
  (m : ℚ) * barrierLogHRat 2 + barrierLogHRat y

theorem barrierLogHRat_cast (y : ℚ) :
    ((barrierLogHRat y : ℚ) : ℝ) = barrierLogH (y : ℝ) := by
  unfold barrierLogHRat barrierLogH
  push_cast
  rfl

theorem barrierScaledLogRat_cast (m : ℤ) (y : ℚ) :
    ((barrierScaledLogRat m y : ℚ) : ℝ) = barrierScaledLogApprox m (y : ℝ) := by
  unfold barrierScaledLogRat barrierScaledLogApprox
  push_cast
  rw [barrierLogHRat_cast, barrierLogHRat_cast]
  norm_num

theorem barrier_fixed_log_abs_error {s : ℝ} {m : ℤ} {y : ℚ}
    (h : Case1PointData.FixedLogNormalization s m y) :
    |Real.log s - ((barrierScaledLogRat m y : ℚ) : ℝ)| <
      (1 / 1000000000000000 : ℝ) := by
  rcases h with ⟨hs, hy, hm⟩
  rw [hs, barrierScaledLogRat_cast]
  exact barrier_scaled_log_abs_error_lt m hy hm

end

section

theorem barrier_two_coarse_total_sharp_lt :
    -(11 / 16 : ℝ) * Real.log 2 + 77844 / 100000 - 98399 / 100000 -
      160890 / 100000 + 48 / 1000000 < -(2290939875 / 1000000000 : ℝ) := by
  linarith [barrier_log_two_lower]

theorem barrier_one_coarse_total_sharp_lt :
    -(11 / 16 : ℝ) * Real.log 2 + 9321 / 10000 - 13244 / 10000 -
      14280 / 10000 + 48 / 1000000 < -(2296789875 / 1000000000 : ℝ) := by
  linarith [barrier_log_two_lower]


open scoped BigOperators









end




end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Energy.BarrierFinitePotentialDerivatives
namespace OAI

noncomputable section

namespace InternalCatalan

open Polynomial
open scoped BigOperators

private theorem barrierFiniteT_term_hasDerivAt (a : ℝ) (k : ℕ) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => a * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval y /
        ((k + 1 : ℕ) : ℝ))
      (a * (Chebyshev.U ℝ (k : ℤ)).eval x) x := by
  have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hindex : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by simp
  have ht : HasDerivAt
      (fun y : ℝ => (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval y)
      (((k + 1 : ℕ) : ℝ) * (Chebyshev.U ℝ (k : ℤ)).eval x) x := by
    simpa only [Chebyshev.T_derivative_eq_U, eval_mul, eval_intCast,
      hindex, Int.cast_natCast, eval_natCast] using
      (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).hasDerivAt x
  apply ((ht.const_mul a).div_const ((k + 1 : ℕ) : ℝ)).congr_deriv
  field_simp [hk]

private theorem barrierFiniteS_term_hasDerivAt (a : ℝ) (k : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => a * y ^ (k + 1) / ((k + 1 : ℕ) : ℝ))
      (a * x ^ k) x := by
  have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hp : HasDerivAt (fun y : ℝ => y ^ (k + 1))
      (((k + 1 : ℕ) : ℝ) * x ^ k) x := by
    simpa only [Nat.add_sub_cancel] using hasDerivAt_pow (k + 1) x
  apply ((hp.const_mul a).div_const ((k + 1 : ℕ) : ℝ)).congr_deriv
  field_simp [hk]

theorem barrierTrialT_nil_hasDerivAt (cs : List ℤ) (x : ℝ) :
    HasDerivAt (barrierTrialT (barrierTrial cs []))
      ((barrierFiniteUDerivative cs).eval₂ (Rat.castHom ℝ) x) x := by
  have hf : barrierTrialT (barrierTrial cs []) =
      (fun y : ℝ => ∑ k ∈ Finset.range cs.length,
        ((cs.getD k 0 : ℝ) / 100000000) *
          (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval y / ((k + 1 : ℕ) : ℝ)) := by
    funext y
    exact barrierTrialT_nil_eq_sum cs y
  have hd : (barrierFiniteUDerivative cs).eval₂ (Rat.castHom ℝ) x =
      ∑ k ∈ Finset.range cs.length,
        ((cs.getD k 0 : ℝ) / 100000000) * (Chebyshev.U ℝ (k : ℤ)).eval x := by
    simp only [barrierFiniteUDerivative, eval₂_finsetSum, eval₂_mul,
      eval₂_C, map_div₀, map_intCast, map_ofNat]
    simp only [eval₂_eq_eval_map, Chebyshev.map_U]
  rw [hf, hd]
  exact HasDerivAt.fun_sum (fun k _ =>
    barrierFiniteT_term_hasDerivAt ((cs.getD k 0 : ℝ) / 100000000) k x)

theorem barrierTrialS_nil_hasDerivAt (cs : List ℤ) (x : ℝ) :
    HasDerivAt (barrierTrialS (barrierTrial cs []))
      ((barrierFinitePowerDerivative cs).eval₂ (Rat.castHom ℝ) x) x := by
  have hf : barrierTrialS (barrierTrial cs []) =
      (fun y : ℝ => ∑ k ∈ Finset.range cs.length,
        ((cs.getD k 0 : ℝ) / 100000000) * y ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) := by
    funext y
    exact barrierTrialS_nil_eq_sum cs y
  have hd : (barrierFinitePowerDerivative cs).eval₂ (Rat.castHom ℝ) x =
      ∑ k ∈ Finset.range cs.length,
        ((cs.getD k 0 : ℝ) / 100000000) * x ^ k := by
    simp only [barrierFinitePowerDerivative, eval₂_finsetSum, eval₂_mul,
      eval₂_C, eval₂_X_pow, map_div₀, map_intCast, map_ofNat]
  rw [hf, hd]
  exact HasDerivAt.fun_sum (fun k _ =>
    barrierFiniteS_term_hasDerivAt ((cs.getD k 0 : ℝ) / 100000000) k x)

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.FirstBarrier.BarrierCaseOneBracketHeight
namespace OAI

noncomputable section

namespace InternalCatalan

section

def barrierCase1X (x : ℝ) : ℝ :=
  realEnergyField 1 x + barrierLambda1 * realEnergyCaseField x -
    2 * barrierTrialT barrierP1 x - barrierTrialS barrierV1 x

def barrierCase1Y (x : ℝ) : ℝ :=
  realEnergyColumnField x + 2 * barrierTrialT barrierV1 x

private theorem barrier_realEnergyField_one_hasDerivAt {x : ℝ}
    (h0 : x ≠ 0) (h1 : x ≠ 1) :
    HasDerivAt (realEnergyField 1)
      ((19 / 48 : ℝ) / x - (1 / 12 : ℝ) / (1 - x) -
        (41 / 24 : ℝ) * x / (1 + x ^ 2)) x := by
  have ho : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hd : 1 + x ^ 2 ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < 1 + x ^ 2)
  have hl0 : HasDerivAt (fun y : ℝ => Real.log |y|) (1 / x) x := by
    simpa only [Real.log_abs, one_div] using Real.hasDerivAt_log h0
  have hl1 : HasDerivAt (fun y : ℝ => Real.log (1 - y))
      (-1 / (1 - x)) x :=
    ((hasDerivAt_id x).const_sub (1 : ℝ)).log ho
  have hp : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).const_add (1 : ℝ)
  have hl2 := hp.log hd
  have hh := ((hl0.const_mul (19 / 48 : ℝ)).add
    (hl1.const_mul (1 / 12 : ℝ))).sub
    (hl2.const_mul ((1 : ℝ) / 2 + 17 / 48))
  unfold realEnergyField
  apply hh.congr_deriv
  field_simp [h0, ho, hd]
  ring

private theorem barrier_realEnergyColumnField_hasDerivAt {x : ℝ}
    (h0 : x ≠ 0) (h1 : x ≠ 1) :
    HasDerivAt realEnergyColumnField
      ((7 / 48 : ℝ) / x - (1 / 12 : ℝ) / (1 - x)) x := by
  have ho : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hl0 : HasDerivAt Real.log (1 / x) x := by
    simpa only [one_div] using Real.hasDerivAt_log h0
  have hl1 : HasDerivAt (fun y : ℝ => Real.log (1 - y))
      (-1 / (1 - x)) x :=
    ((hasDerivAt_id x).const_sub (1 : ℝ)).log ho
  have hh := (hl0.const_mul (7 / 48 : ℝ)).add (hl1.const_mul (1 / 12 : ℝ))
  unfold realEnergyColumnField
  apply hh.congr_deriv
  field_simp [h0, ho]
  ring

private theorem barrier_realEnergyCaseField_hasDerivAt (x : ℝ) :
    HasDerivAt realEnergyCaseField (-4 * x / (1 + x ^ 2) ^ 2) x := by
  have hd : 1 + x ^ 2 ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < 1 + x ^ 2)
  have hp : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have hq : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x :=
    hp.const_add (1 : ℝ)
  have hh := ((hp.const_mul (2 : ℝ)).fun_div hq hd).const_sub (1 / 6 : ℝ)
  unfold realEnergyCaseField
  apply hh.congr_deriv
  field_simp [hd]
  ring

theorem barrierCase1X_hasDerivAt {x : ℝ} (h0 : x ≠ 0) (h1 : x ≠ 1) :
    HasDerivAt barrierCase1X (barrierCase1XDerivativeFormula x) x := by
  have ht : HasDerivAt (barrierTrialT barrierP1)
      ((barrierFiniteUDerivative barrierP1Finite).eval₂ (Rat.castHom ℝ) x) x := by
    simpa only [barrierP1] using barrierTrialT_nil_hasDerivAt barrierP1Finite x
  have hs : HasDerivAt (barrierTrialS barrierV1)
      ((barrierFinitePowerDerivative barrierV1Finite).eval₂ (Rat.castHom ℝ) x) x := by
    simpa only [barrierV1] using barrierTrialS_nil_hasDerivAt barrierV1Finite x
  have hh := (((barrier_realEnergyField_one_hasDerivAt h0 h1).add
    ((barrier_realEnergyCaseField_hasDerivAt x).const_mul barrierLambda1)).sub
    (ht.const_mul (2 : ℝ))).sub hs
  unfold barrierCase1X
  apply hh.congr_deriv
  unfold barrierCase1XDerivativeFormula
  ring

theorem barrierCase1Y_hasDerivAt {x : ℝ} (h0 : x ≠ 0) (h1 : x ≠ 1) :
    HasDerivAt barrierCase1Y (barrierCase1YDerivativeFormula x) x := by
  have ht : HasDerivAt (barrierTrialT barrierV1)
      ((barrierFiniteUDerivative barrierV1Finite).eval₂ (Rat.castHom ℝ) x) x := by
    simpa only [barrierV1] using barrierTrialT_nil_hasDerivAt barrierV1Finite x
  have hh := (barrier_realEnergyColumnField_hasDerivAt h0 h1).add (ht.const_mul (2 : ℝ))
  unfold barrierCase1Y
  apply hh.congr_deriv
  unfold barrierCase1YDerivativeFormula
  rfl

end

namespace Case1Height
open Polynomial
open scoped BigOperators

theorem abs_U_eval_le (k : ℕ) {x : ℝ} (hx : |x| ≤ 1) :
    |(Chebyshev.U ℝ (k : ℤ)).eval x| ≤ (k : ℝ) + 1 := by
  have h := Chebyshev.abs_iterate_derivative_T_real_le ((k : ℤ) + 1) 1 hx
  simp only [Function.iterate_one] at h
  rw [Chebyshev.derivative_T_eval_one] at h
  rw [Chebyshev.T_derivative_eq_U, eval_mul, eval_intCast] at h
  have hi : (k : ℤ) + 1 - 1 = (k : ℤ) := by ring
  rw [hi, abs_mul] at h
  have hn : (((k : ℤ) + 1 : ℤ) : ℝ) = (k : ℝ) + 1 := by norm_num
  rw [hn] at h
  have hp : 0 < (k : ℝ) + 1 := by positivity
  rw [abs_of_pos hp] at h
  exact le_of_mul_le_mul_left (by simpa only [sq] using h) hp

theorem finiteU_abs_le_mass (cs : List ℤ) {x : ℝ} (hx : |x| ≤ 1) :
    |(barrierFiniteUDerivative cs).eval₂ (Rat.castHom ℝ) x| ≤
      ∑ k ∈ Finset.range cs.length,
        |(cs.getD k 0 : ℝ) / 100000000| * ((k : ℝ) + 1) := by
  have hd : (barrierFiniteUDerivative cs).eval₂ (Rat.castHom ℝ) x =
      ∑ k ∈ Finset.range cs.length,
        ((cs.getD k 0 : ℝ) / 100000000) * (Chebyshev.U ℝ (k : ℤ)).eval x := by
    simp only [barrierFiniteUDerivative, eval₂_finsetSum, eval₂_mul,
      eval₂_C, map_div₀, map_intCast, map_ofNat]
    simp only [eval₂_eq_eval_map, Chebyshev.map_U]
  rw [hd]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro k _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_U_eval_le k hx) (abs_nonneg _)

theorem finitePower_abs_le_mass (cs : List ℤ) {x : ℝ} (hx : |x| ≤ 1) :
    |(barrierFinitePowerDerivative cs).eval₂ (Rat.castHom ℝ) x| ≤
      ∑ k ∈ Finset.range cs.length, |(cs.getD k 0 : ℝ) / 100000000| := by
  have hd : (barrierFinitePowerDerivative cs).eval₂ (Rat.castHom ℝ) x =
      ∑ k ∈ Finset.range cs.length,
        ((cs.getD k 0 : ℝ) / 100000000) * x ^ k := by
    simp only [barrierFinitePowerDerivative, eval₂_finsetSum, eval₂_mul,
      eval₂_C, eval₂_X_pow, map_div₀, map_intCast, map_ofNat]
  rw [hd]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro k _
  rw [abs_mul, abs_pow]
  exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg x) hx)
    (abs_nonneg ((cs.getD k 0 : ℝ) / 100000000))).trans_eq (mul_one _)

theorem actual_finite_bounds {x : ℝ} (hx : |x| ≤ 1) :
    |(barrierFiniteUDerivative barrierP1Finite).eval₂ (Rat.castHom ℝ) x| ≤ 36 ∧
    |(barrierFiniteUDerivative barrierV1Finite).eval₂ (Rat.castHom ℝ) x| ≤ 36 ∧
    |(barrierFinitePowerDerivative barrierV1Finite).eval₂ (Rat.castHom ℝ) x| ≤ 8 := by
  refine ⟨(finiteU_abs_le_mass barrierP1Finite hx).trans ?_,
    (finiteU_abs_le_mass barrierV1Finite hx).trans ?_,
    (finitePower_abs_le_mass barrierV1Finite hx).trans ?_⟩
  all_goals norm_num [barrierP1Finite, barrierV1Finite, Finset.sum_range_succ]

private theorem abs_div_le_const {a b C : ℝ} (hb : 0 < |b|)
    (h : |a| ≤ C * |b|) : |a / b| ≤ C := by
  rw [abs_div]
  exact (div_le_iff₀ hb).2 h

private theorem abs_sub_le_pair (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  simpa only [Real.norm_eq_abs] using norm_sub_le a b

private theorem abs_five_sub_le (a b c d e g : ℝ) :
    |a - b - c - d - e - g| ≤ |a| + |b| + |c| + |d| + |e| + |g| := by
  have h1 := abs_sub_le_pair a b
  have h2 := abs_sub_le_pair (a - b) c
  have h3 := abs_sub_le_pair (a - b - c) d
  have h4 := abs_sub_le_pair (a - b - c - d) e
  have h5 := abs_sub_le_pair (a - b - c - d - e) g
  linarith

theorem actual_X_deriv_abs_le {x : ℝ} (hx : |x| ≤ 1)
    (hxmargin : (1 / 100 : ℝ) ≤ |x|)
    (hgap : (1 / 100 : ℝ) ≤ 1 - x) :
    |deriv barrierCase1X x| ≤ 100000 := by
  have hxpos : 0 < |x| := lt_of_lt_of_le (by norm_num) hxmargin
  have hgpos : 0 < 1 - x := lt_of_lt_of_le (by norm_num) hgap
  have h0 : x ≠ 0 := abs_pos.mp hxpos
  have h1 : x ≠ 1 := by intro h; subst x; norm_num at hgap
  obtain ⟨hpu, _, hvp⟩ := actual_finite_bounds hx
  have hd : 0 < 1 + x ^ 2 := by positivity
  have hd1 : 1 ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg x]
  have hd2 : 1 ≤ (1 + x ^ 2) ^ 2 := by nlinarith [sq_nonneg (x ^ 2)]
  have hA : |(19 / 48 : ℝ) / x| ≤ 40 := by
    apply abs_div_le_const hxpos
    norm_num
    linarith
  have hB : |(1 / 12 : ℝ) / (1 - x)| ≤ 9 := by
    apply abs_div_le_const (abs_pos.mpr (ne_of_gt hgpos))
    rw [abs_of_pos hgpos]
    norm_num
    linarith
  have hC : |(41 / 24 : ℝ) * x / (1 + x ^ 2)| ≤ 2 := by
    apply abs_div_le_const (abs_pos.mpr (ne_of_gt hd))
    rw [abs_mul, abs_of_pos hd]
    norm_num
    nlinarith
  have hD : |4 * barrierLambda1 * x / (1 + x ^ 2) ^ 2| ≤ 10 := by
    apply abs_div_le_const (abs_pos.mpr (ne_of_gt (sq_pos_of_pos hd)))
    rw [abs_mul, abs_of_pos (sq_pos_of_pos hd)]
    norm_num [barrierLambda1]
    nlinarith
  have hE : |2 * (barrierFiniteUDerivative barrierP1Finite).eval₂ (Rat.castHom ℝ) x| ≤ 72 := by
    rw [abs_mul]
    norm_num
    linarith
  rw [(barrierCase1X_hasDerivAt h0 h1).deriv]
  unfold barrierCase1XDerivativeFormula
  exact (abs_five_sub_le _ _ _ _ _ _).trans (by linarith)

theorem actual_Y_deriv_abs_le {x : ℝ} (hx : |x| ≤ 1)
    (hxmargin : (1 / 100 : ℝ) ≤ |x|)
    (hgap : (1 / 100 : ℝ) ≤ 1 - x) :
    |deriv barrierCase1Y x| ≤ 100000 := by
  have hxpos : 0 < |x| := lt_of_lt_of_le (by norm_num) hxmargin
  have hgpos : 0 < 1 - x := lt_of_lt_of_le (by norm_num) hgap
  have h0 : x ≠ 0 := abs_pos.mp hxpos
  have h1 : x ≠ 1 := by intro h; subst x; norm_num at hgap
  obtain ⟨_, hvu, _⟩ := actual_finite_bounds hx
  have hA : |(7 / 48 : ℝ) / x| ≤ 15 := by
    apply abs_div_le_const hxpos
    norm_num
    linarith
  have hB : |(1 / 12 : ℝ) / (1 - x)| ≤ 9 := by
    apply abs_div_le_const (abs_pos.mpr (ne_of_gt hgpos))
    rw [abs_of_pos hgpos]
    norm_num
    linarith
  have hC : |2 * (barrierFiniteUDerivative barrierV1Finite).eval₂ (Rat.castHom ℝ) x| ≤ 72 := by
    rw [abs_mul]
    norm_num
    linarith
  rw [(barrierCase1Y_hasDerivAt h0 h1).deriv]
  unfold barrierCase1YDerivativeFormula
  have hab := abs_sub_le_pair ((7 / 48 : ℝ) / x) ((1 / 12 : ℝ) / (1 - x))
  have habc := abs_add_le (((7 / 48 : ℝ) / x) - ((1 / 12 : ℝ) / (1 - x)))
    (2 * (barrierFiniteUDerivative barrierV1Finite).eval₂ (Rat.castHom ℝ) x)
  linarith

end Case1Height

section

open Set Filter
open scoped Topology

private theorem barrier_atBot_add_finite {l : Filter ℝ} {f g : ℝ → ℝ} {c : ℝ}
    (hf : Tendsto f l atBot) (hg : Tendsto g l (𝓝 c)) :
    Tendsto (fun x => f x + g x) l atBot := by
  have hb : ∀ᶠ x in l, g x ≤ c + 1 :=
    ((tendsto_order.mp hg).2 (c + 1) (by linarith)).mono (fun _ hx => hx.le)
  exact tendsto_atBot_add_right_of_ge' l (c + 1) hf hb

private theorem barrier_log_one_sub_tendsto :
    Tendsto (fun x : ℝ => Real.log (1 - x)) (𝓝[<] 1) atBot := by
  have hc : Continuous (fun x : ℝ => 1 - x) := continuous_const.sub continuous_id
  have ht : Tendsto (fun x : ℝ => 1 - x) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using (hc.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      change x < 1 at hx
      change 0 < 1 - x
      exact sub_pos.mpr hx
  exact Real.tendsto_log_nhdsGT_zero.comp ht

private def barrierCase1XRegular (x : ℝ) : ℝ :=
  -(41 / 48 : ℝ) * Real.log (1 + x ^ 2) +
    barrierLambda1 * realEnergyCaseField x -
    2 * barrierTrialT barrierP1 x - barrierTrialS barrierV1 x

private theorem barrierCase1XRegular_continuousAt (x : ℝ) :
    ContinuousAt barrierCase1XRegular x := by
  have hp : ContinuousAt (fun y : ℝ => 1 + y ^ 2) x :=
    continuousAt_const.add (continuousAt_id.pow 2)
  have hd : 1 + x ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hc : ContinuousAt realEnergyCaseField x := by
    unfold realEnergyCaseField
    exact continuousAt_const.sub
      ((continuousAt_const.mul (continuousAt_id.pow 2)).div hp hd)
  have ht : ContinuousAt (barrierTrialT barrierP1) x := by
    simpa only [barrierP1] using
      (barrierTrialT_nil_hasDerivAt barrierP1Finite x).continuousAt
  have hs : ContinuousAt (barrierTrialS barrierV1) x := by
    simpa only [barrierV1] using
      (barrierTrialS_nil_hasDerivAt barrierV1Finite x).continuousAt
  exact ((((hp.log hd).const_mul (-(41 / 48 : ℝ))).add
    (hc.const_mul barrierLambda1)).sub (ht.const_mul 2)).sub hs

private theorem barrierCase1V1T_continuousAt (x : ℝ) :
    ContinuousAt (barrierTrialT barrierV1) x := by
  simpa only [barrierV1] using
    (barrierTrialT_nil_hasDerivAt barrierV1Finite x).continuousAt

private theorem barrierCase1X_split (x : ℝ) :
    barrierCase1X x = (19 / 48 : ℝ) * Real.log |x| +
      (1 / 12 : ℝ) * Real.log (1 - x) + barrierCase1XRegular x := by
  unfold barrierCase1X realEnergyField barrierCase1XRegular
  ring

private theorem barrierCase1X_zero_remainder :
    ContinuousAt (fun x : ℝ => (1 / 12 : ℝ) * Real.log (1 - x) +
      barrierCase1XRegular x) 0 := by
  have hl : ContinuousAt (fun x : ℝ => Real.log (1 - x)) 0 :=
    (continuousAt_const.sub continuousAt_id).log (by norm_num)
  exact (hl.const_mul (1 / 12 : ℝ)).add (barrierCase1XRegular_continuousAt 0)

private theorem barrierCase1X_one_remainder :
    ContinuousAt (fun x : ℝ => (19 / 48 : ℝ) * Real.log |x| +
      barrierCase1XRegular x) 1 := by
  have hl : ContinuousAt (fun x : ℝ => Real.log |x|) 1 := by
    simpa only [Real.log_abs] using (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0))
  exact (hl.const_mul (19 / 48 : ℝ)).add (barrierCase1XRegular_continuousAt 1)

theorem barrierCase1X_tendsto_zero_left :
    Tendsto barrierCase1X (𝓝[<] 0) atBot := by
  have hl : Tendsto (fun x : ℝ => (19 / 48 : ℝ) * Real.log |x|)
      (𝓝[<] 0) atBot := by
    simpa only [Real.log_abs] using
      (Tendsto.const_mul_atBot (by norm_num : (0 : ℝ) < 19 / 48)
        Real.tendsto_log_nhdsLT_zero)
  have hh := barrier_atBot_add_finite hl
    (barrierCase1X_zero_remainder.tendsto.mono_left nhdsWithin_le_nhds)
  convert hh using 1
  funext x
  rw [barrierCase1X_split]
  ring

theorem barrierCase1X_tendsto_zero_right :
    Tendsto barrierCase1X (𝓝[>] 0) atBot := by
  have hl : Tendsto (fun x : ℝ => (19 / 48 : ℝ) * Real.log |x|)
      (𝓝[>] 0) atBot := by
    simpa only [Real.log_abs] using
      (Tendsto.const_mul_atBot (by norm_num : (0 : ℝ) < 19 / 48)
        Real.tendsto_log_nhdsGT_zero)
  have hh := barrier_atBot_add_finite hl
    (barrierCase1X_zero_remainder.tendsto.mono_left nhdsWithin_le_nhds)
  convert hh using 1
  funext x
  rw [barrierCase1X_split]
  ring

theorem barrierCase1X_tendsto_one_left :
    Tendsto barrierCase1X (𝓝[<] 1) atBot := by
  have hl := Tendsto.const_mul_atBot (by norm_num : (0 : ℝ) < 1 / 12)
    barrier_log_one_sub_tendsto
  have hh := barrier_atBot_add_finite hl
    (barrierCase1X_one_remainder.tendsto.mono_left nhdsWithin_le_nhds)
  convert hh using 1
  funext x
  rw [barrierCase1X_split]
  ring

theorem barrierCase1Y_tendsto_zero_right :
    Tendsto barrierCase1Y (𝓝[>] 0) atBot := by
  have hl := Tendsto.const_mul_atBot (by norm_num : (0 : ℝ) < 7 / 48)
    Real.tendsto_log_nhdsGT_zero
  have hr : ContinuousAt (fun x : ℝ => (1 / 12 : ℝ) * Real.log (1 - x) +
      2 * barrierTrialT barrierV1 x) 0 := by
    have hlog : ContinuousAt (fun x : ℝ => Real.log (1 - x)) 0 :=
      (continuousAt_const.sub continuousAt_id).log (by norm_num)
    exact (hlog.const_mul (1 / 12 : ℝ)).add
      ((barrierCase1V1T_continuousAt 0).const_mul 2)
  have hh := barrier_atBot_add_finite hl (hr.tendsto.mono_left nhdsWithin_le_nhds)
  convert hh using 1
  funext x
  unfold barrierCase1Y realEnergyColumnField
  ring

theorem barrierCase1Y_tendsto_one_left :
    Tendsto barrierCase1Y (𝓝[<] 1) atBot := by
  have hl := Tendsto.const_mul_atBot (by norm_num : (0 : ℝ) < 1 / 12)
    barrier_log_one_sub_tendsto
  have hr : ContinuousAt (fun x : ℝ => (7 / 48 : ℝ) * Real.log x +
      2 * barrierTrialT barrierV1 x) 1 := by
    exact ((Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).const_mul
      (7 / 48 : ℝ)).add ((barrierCase1V1T_continuousAt 1).const_mul 2)
  have hh := barrier_atBot_add_finite hl (hr.tendsto.mono_left nhdsWithin_le_nhds)
  convert hh using 1
  funext x
  unfold barrierCase1Y realEnergyColumnField
  ring


end

def barrierCase1XRat (x : ℚ) : ℚ :=
  (247405979 / 100000000 : ℚ) * (1 / 6 - 2 * x ^ 2 / (1 + x ^ 2)) -
    2 * barrierFiniteTRat barrierP1Finite x - barrierFiniteSRat barrierV1Finite x

def barrierCase1YRat (x : ℚ) : ℚ :=
  2 * barrierFiniteTRat barrierV1Finite x

theorem barrierCase1X_eval_rat (x : ℚ) :
    barrierCase1X (x : ℝ) =
      (19 / 48 : ℝ) * Real.log |(x : ℝ)| +
        (1 / 12 : ℝ) * Real.log (1 - (x : ℝ)) -
        (41 / 48 : ℝ) * Real.log (1 + (x : ℝ) ^ 2) +
        ((barrierCase1XRat x : ℚ) : ℝ) := by
  unfold barrierCase1X barrierP1 barrierV1
  rw [barrierTrialT_nil_eval_rat, barrierTrialS_nil_eval_rat]
  unfold realEnergyField realEnergyCaseField barrierCase1XRat barrierLambda1
  push_cast
  ring

theorem barrierCase1Y_eval_rat (x : ℚ) :
    barrierCase1Y (x : ℝ) =
      (7 / 48 : ℝ) * Real.log (x : ℝ) +
        (1 / 12 : ℝ) * Real.log (1 - (x : ℝ)) +
        ((barrierCase1YRat x : ℚ) : ℝ) := by
  unfold barrierCase1Y barrierV1
  rw [barrierTrialT_nil_eval_rat]
  unfold realEnergyColumnField barrierCase1YRat
  push_cast
  ring

theorem barrierCase1X_deriv_eq_zero_iff {x : ℝ} (h0 : x ≠ 0) (h1 : x ≠ 1) :
    deriv barrierCase1X x = 0 ↔ (barrierCase1AX.map (Rat.castHom ℝ)).eval x = 0 := by
  rw [(barrierCase1X_hasDerivAt h0 h1).deriv, Polynomial.eval_map,
    barrierCase1AX_clears_denominator h0 h1]
  simp [barrierCase1QX_eval_ne_zero h0 h1]

theorem barrierCase1Y_deriv_eq_zero_iff {x : ℝ} (h0 : x ≠ 0) (h1 : x ≠ 1) :
    deriv barrierCase1Y x = 0 ↔ (barrierCase1AY.map (Rat.castHom ℝ)).eval x = 0 := by
  rw [(barrierCase1Y_hasDerivAt h0 h1).deriv, Polynomial.eval_map,
    barrierCase1AY_clears_denominator h0 h1]
  simp [barrierCase1QY_eval_ne_zero h0 h1]



open Set

namespace Case1Height

theorem X_closed_bracket_margins (m : ℤ) (hm : m ∈ barrierCase1XBrackets)
    {x : ℝ} (hx : x ∈ Icc (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ)) :
    |x| ≤ 1 ∧ (1 / 100 : ℝ) ≤ |x| ∧ (1 / 100 : ℝ) ≤ 1 - x := by
  simp only [barrierCase1XBrackets, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  all_goals
    norm_num [barrierBracketLeft, barrierBracketRight, Set.mem_Icc] at hx
    refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩, ?_, ?_⟩
    · rcases le_total x 0 with hn | hp
      · rw [abs_of_nonpos hn]
        linarith
      · rw [abs_of_nonneg hp]
        linarith
    · linarith

theorem Y_closed_bracket_margins (m : ℤ) (hm : m ∈ barrierCase1YBrackets)
    {x : ℝ} (hx : x ∈ Icc (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ)) :
    |x| ≤ 1 ∧ (1 / 100 : ℝ) ≤ |x| ∧ (1 / 100 : ℝ) ≤ 1 - x := by
  simp only [barrierCase1YBrackets, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  all_goals
    norm_num [barrierBracketLeft, barrierBracketRight, Set.mem_Icc] at hx
    refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩, ?_, ?_⟩
    · rcases le_total x 0 with hn | hp
      · rw [abs_of_nonpos hn]
        linarith
      · rw [abs_of_nonneg hp]
        linarith
    · linarith

private theorem regular_of_margins {x : ℝ}
    (hx : (1 / 100 : ℝ) ≤ |x|) (hgap : (1 / 100 : ℝ) ≤ 1 - x) :
    x ≠ 0 ∧ x ≠ 1 := by
  constructor
  · exact abs_pos.mp (lt_of_lt_of_le (by norm_num) hx)
  · intro h
    subst x
    norm_num at hgap

theorem abs_sub_le_on_Icc {f : ℝ → ℝ} {a b C x : ℝ}
    (hdiff : ∀ y ∈ Icc a b, DifferentiableAt ℝ f y)
    (hbound : ∀ y ∈ Icc a b, |deriv f y| ≤ C)
    (hx : x ∈ Icc a b) : |f x - f a| ≤ C * |x - a| := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hx.1.trans hx.2⟩
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y hy => (hdiff y hy).hasDerivAt.hasDerivWithinAt)
      (fun y hy => by simpa only [Real.norm_eq_abs] using hbound y hy)
      (convex_Icc a b) ha hx

theorem actual_bracket_width (m : ℤ) :
    (barrierBracketRight m : ℝ) - (barrierBracketLeft m : ℝ) =
      (2 / 10000000000 : ℝ) := by
  norm_num [barrierBracketLeft, barrierBracketRight]
  ring

private theorem height_of_abs_variation {f : ℝ → ℝ} {m : ℤ} {x : ℝ}
    (hx : x ∈ Icc (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ))
    (hvar : |f x - f (barrierBracketLeft m : ℝ)| ≤
      100000 * |x - (barrierBracketLeft m : ℝ)|) :
    f x ≤ f (barrierBracketLeft m : ℝ) + (2 / 100000 : ℝ) := by
  have hdist : |x - (barrierBracketLeft m : ℝ)| ≤
      (barrierBracketRight m : ℝ) - (barrierBracketLeft m : ℝ) := by
    rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]
    exact sub_le_sub_right hx.2 _
  have he : |f x - f (barrierBracketLeft m : ℝ)| ≤ (2 / 100000 : ℝ) := by
    calc
      _ ≤ 100000 * |x - (barrierBracketLeft m : ℝ)| := hvar
      _ ≤ 100000 * ((barrierBracketRight m : ℝ) - (barrierBracketLeft m : ℝ)) :=
        mul_le_mul_of_nonneg_left hdist (by norm_num)
      _ = (2 / 100000 : ℝ) := by rw [actual_bracket_width]; norm_num
  have hs := (le_abs_self (f x - f (barrierBracketLeft m : ℝ))).trans he
  linarith

end Case1Height

theorem barrierCase1X_bracket_height (m : ℤ) (hm : m ∈ barrierCase1XBrackets)
    {x : ℝ} (hx : x ∈ Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ)) :
    barrierCase1X x ≤ barrierCase1X (barrierBracketLeft m : ℝ) + (2 / 100000 : ℝ) := by
  have hxcc : x ∈ Icc (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) :=
    ⟨hx.1.le, hx.2.le⟩
  apply Case1Height.height_of_abs_variation hxcc
  apply Case1Height.abs_sub_le_on_Icc
  · intro y hy
    obtain ⟨_, hy0, hy1⟩ := Case1Height.X_closed_bracket_margins m hm hy
    obtain ⟨h0, h1⟩ := Case1Height.regular_of_margins hy0 hy1
    exact (barrierCase1X_hasDerivAt h0 h1).differentiableAt
  · intro y hy
    obtain ⟨hyabs, hy0, hy1⟩ := Case1Height.X_closed_bracket_margins m hm hy
    exact Case1Height.actual_X_deriv_abs_le hyabs hy0 hy1
  · exact hxcc

theorem barrierCase1Y_bracket_height (m : ℤ) (hm : m ∈ barrierCase1YBrackets)
    {x : ℝ} (hx : x ∈ Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ)) :
    barrierCase1Y x ≤ barrierCase1Y (barrierBracketLeft m : ℝ) + (2 / 100000 : ℝ) := by
  have hxcc : x ∈ Icc (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) :=
    ⟨hx.1.le, hx.2.le⟩
  apply Case1Height.height_of_abs_variation hxcc
  apply Case1Height.abs_sub_le_on_Icc
  · intro y hy
    obtain ⟨_, hy0, hy1⟩ := Case1Height.Y_closed_bracket_margins m hm hy
    obtain ⟨h0, h1⟩ := Case1Height.regular_of_margins hy0 hy1
    exact (barrierCase1Y_hasDerivAt h0 h1).differentiableAt
  · intro y hy
    obtain ⟨hyabs, hy0, hy1⟩ := Case1Height.Y_closed_bracket_margins m hm hy
    exact Case1Height.actual_Y_deriv_abs_le hyabs hy0 hy1
  · exact hxcc

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.FirstBarrier.BarrierCaseOnePointY1
namespace OAI


noncomputable section
namespace InternalCatalan
open Polynomial

private theorem barrier_T_3 :
    Chebyshev.T ℚ 3 = 2 * X * Chebyshev.T ℚ 2 - Chebyshev.T ℚ 1 := by
  simpa only [Int.reduceAdd] using Chebyshev.T_add_two ℚ 1

private theorem barrier_T_4 :
    Chebyshev.T ℚ 4 = 2 * X * Chebyshev.T ℚ 3 - Chebyshev.T ℚ 2 := by
  simpa only [Int.reduceAdd] using Chebyshev.T_add_two ℚ 2

private theorem barrier_T_5 :
    Chebyshev.T ℚ 5 = 2 * X * Chebyshev.T ℚ 4 - Chebyshev.T ℚ 3 := by
  simpa only [Int.reduceAdd] using Chebyshev.T_add_two ℚ 3

private theorem barrier_T_6 :
    Chebyshev.T ℚ 6 = 2 * X * Chebyshev.T ℚ 5 - Chebyshev.T ℚ 4 := by
  simpa only [Int.reduceAdd] using Chebyshev.T_add_two ℚ 4

private theorem barrier_T_7 :
    Chebyshev.T ℚ 7 = 2 * X * Chebyshev.T ℚ 6 - Chebyshev.T ℚ 5 := by
  simpa only [Int.reduceAdd] using Chebyshev.T_add_two ℚ 5

private theorem barrier_T_8 :
    Chebyshev.T ℚ 8 = 2 * X * Chebyshev.T ℚ 7 - Chebyshev.T ℚ 6 := by
  simpa only [Int.reduceAdd] using Chebyshev.T_add_two ℚ 6

def barrierCase1TPExplicit (x : ℚ) : ℚ :=
  (1120821349 / 2400000000 : ℚ) +
    (2202187 / 5000000 : ℚ) * x ^ 1 +
    (-31132013 / 50000000 : ℚ) * x ^ 2 +
    (-50767033 / 75000000 : ℚ) * x ^ 3 +
    (-203194679 / 50000000 : ℚ) * x ^ 4 +
    (986599 / 3906250 : ℚ) * x ^ 5 +
    (5902457 / 750000 : ℚ) * x ^ 6 +
    (285123 / 5468750 : ℚ) * x ^ 7 +
    (-24939103 / 6250000 : ℚ) * x ^ 8

theorem barrierCase1TP_eq_explicit (x : ℚ) :
    barrierFiniteTRat barrierP1Finite x = barrierCase1TPExplicit x := by
  norm_num [barrierFiniteTRat, barrierP1Finite, barrierCase1TPExplicit,
    Finset.sum_range_succ, Chebyshev.T_two, barrier_T_3, barrier_T_4,
    barrier_T_5, barrier_T_6, barrier_T_7, barrier_T_8]
  ring

def barrierCase1TVExplicit (x : ℚ) : ℚ :=
  (-1005408749 / 2400000000 : ℚ) +
    (-41042587 / 25000000 : ℚ) * x ^ 1 +
    (28402743 / 10000000 : ℚ) * x ^ 2 +
    (16189271 / 7500000 : ℚ) * x ^ 3 +
    (-336320967 / 50000000 : ℚ) * x ^ 4 +
    (-34182773 / 15625000 : ℚ) * x ^ 5 +
    (67938223 / 9375000 : ℚ) * x ^ 6 +
    (9819141 / 10937500 : ℚ) * x ^ 7 +
    (-16992389 / 6250000 : ℚ) * x ^ 8

theorem barrierCase1TV_eq_explicit (x : ℚ) :
    barrierFiniteTRat barrierV1Finite x = barrierCase1TVExplicit x := by
  norm_num [barrierFiniteTRat, barrierV1Finite, barrierCase1TVExplicit,
    Finset.sum_range_succ, Chebyshev.T_two, barrier_T_3, barrier_T_4,
    barrier_T_5, barrier_T_6, barrier_T_7, barrier_T_8]
  ring

def barrierCase1SVExplicit (x : ℚ) : ℚ :=
  (-3596521 / 4000000 : ℚ) * x ^ 1 +
    (1321857 / 5000000 : ℚ) * x ^ 2 +
    (45168341 / 300000000 : ℚ) * x ^ 3 +
    (-30708629 / 400000000 : ℚ) * x ^ 4 +
    (-19269841 / 500000000 : ℚ) * x ^ 5 +
    (530033 / 9375000 : ℚ) * x ^ 6 +
    (9819141 / 700000000 : ℚ) * x ^ 7 +
    (-16992389 / 800000000 : ℚ) * x ^ 8

theorem barrierCase1SV_eq_explicit (x : ℚ) :
    barrierFiniteSRat barrierV1Finite x = barrierCase1SVExplicit x := by
  norm_num [barrierFiniteSRat, barrierV1Finite, barrierCase1SVExplicit,
    Finset.sum_range_succ, Chebyshev.T_two, barrier_T_3, barrier_T_4,
    barrier_T_5, barrier_T_6, barrier_T_7, barrier_T_8]
  ring

end InternalCatalan




namespace InternalCatalan

def barrierCase1XApproxRat (x : ℚ) (m0 m1 m2 : ℤ) (y0 y1 y2 : ℚ) : ℚ :=
  (19 / 48 : ℚ) * barrierScaledLogRat m0 y0 +
    (1 / 12 : ℚ) * barrierScaledLogRat m1 y1 -
    (41 / 48 : ℚ) * barrierScaledLogRat m2 y2 + barrierCase1XRat x

def barrierCase1YApproxRat (x : ℚ) (m0 m1 : ℤ) (y0 y1 : ℚ) : ℚ :=
  (7 / 48 : ℚ) * barrierScaledLogRat m0 y0 +
    (1 / 12 : ℚ) * barrierScaledLogRat m1 y1 + barrierCase1YRat x

theorem barrierCase1X_approx_error (x : ℚ) (m0 m1 m2 : ℤ) (y0 y1 y2 : ℚ)
    (h0 : Case1PointData.FixedLogNormalization |(x : ℝ)| m0 y0)
    (h1 : Case1PointData.FixedLogNormalization (1 - (x : ℝ)) m1 y1)
    (h2 : Case1PointData.FixedLogNormalization (1 + (x : ℝ) ^ 2) m2 y2) :
    |barrierCase1X (x : ℝ) -
      ((barrierCase1XApproxRat x m0 m1 m2 y0 y1 y2 : ℚ) : ℝ)| <
      (2 / 1000000000000000 : ℝ) := by
  have he0 := abs_lt.mp (barrier_fixed_log_abs_error h0)
  have he1 := abs_lt.mp (barrier_fixed_log_abs_error h1)
  have he2 := abs_lt.mp (barrier_fixed_log_abs_error h2)
  rw [barrierCase1X_eval_rat]
  unfold barrierCase1XApproxRat
  push_cast
  apply abs_lt.mpr
  constructor <;> linarith [he0.1, he0.2, he1.1, he1.2, he2.1, he2.2]

theorem barrierCase1Y_approx_error (x : ℚ) (m0 m1 : ℤ) (y0 y1 : ℚ)
    (h0 : Case1PointData.FixedLogNormalization (x : ℝ) m0 y0)
    (h1 : Case1PointData.FixedLogNormalization (1 - (x : ℝ)) m1 y1) :
    |barrierCase1Y (x : ℝ) -
      ((barrierCase1YApproxRat x m0 m1 y0 y1 : ℚ) : ℝ)| <
      (1 / 1000000000000000 : ℝ) := by
  have he0 := abs_lt.mp (barrier_fixed_log_abs_error h0)
  have he1 := abs_lt.mp (barrier_fixed_log_abs_error h1)
  rw [barrierCase1Y_eval_rat]
  unfold barrierCase1YApproxRat
  push_cast
  apply abs_lt.mpr
  constructor <;> linarith [he0.1, he0.2, he1.1, he1.2]





open Case1PointData

private theorem barrierCase1X0_approx_upper :
    barrierCase1XApproxRat X0 (-1) (0) (0) (1983459957 / 1000000000) (3983459957 / 2000000000) (7934113401022441849 / 4000000000000000000) <
      (-13244 / 10000 - 2 / 1000000000000000 : ℚ) := by
  unfold barrierCase1XApproxRat barrierCase1XRat
  rw [barrierCase1TP_eq_explicit, barrierCase1SV_eq_explicit]
  norm_num [X0, barrierCase1TPExplicit, barrierCase1TVExplicit,
    barrierCase1SVExplicit, barrierScaledLogRat, barrierLogHRat, Finset.sum_range_succ]

theorem barrierCase1X0_lt : barrierCase1X (X0 : ℝ) < (-13244 / 10000 : ℝ) := by
  have he := abs_lt.mp (barrierCase1X_approx_error X0 (-1) (0) (0) (1983459957 / 1000000000) (3983459957 / 2000000000) (7934113401022441849 / 4000000000000000000)
    X0_normalizations.1 X0_normalizations.2.1 X0_normalizations.2.2)
  have ha : ((barrierCase1XApproxRat X0 (-1) (0) (0) (1983459957 / 1000000000) (3983459957 / 2000000000) (7934113401022441849 / 4000000000000000000) : ℚ) : ℝ) <
      (-13244 / 10000 - 2 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase1X0_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith [he.2]

end InternalCatalan




namespace InternalCatalan
open Case1PointData

private theorem barrierCase1X1_approx_upper :
    barrierCase1XApproxRat X1 (-3) (0) (0) (2259572153 / 1250000000) (12259572153 / 10000000000) (105105666314613055409 / 100000000000000000000) <
      (-13244 / 10000 - 2 / 1000000000000000 : ℚ) := by
  unfold barrierCase1XApproxRat barrierCase1XRat
  rw [barrierCase1TP_eq_explicit, barrierCase1SV_eq_explicit]
  norm_num [X1, barrierCase1TPExplicit, barrierCase1TVExplicit,
    barrierCase1SVExplicit, barrierScaledLogRat, barrierLogHRat, Finset.sum_range_succ]

theorem barrierCase1X1_lt : barrierCase1X (X1 : ℝ) < (-13244 / 10000 : ℝ) := by
  have he := abs_lt.mp (barrierCase1X_approx_error X1 (-3) (0) (0) (2259572153 / 1250000000) (12259572153 / 10000000000) (105105666314613055409 / 100000000000000000000)
    X1_normalizations.1 X1_normalizations.2.1 X1_normalizations.2.2)
  have ha : ((barrierCase1XApproxRat X1 (-3) (0) (0) (2259572153 / 1250000000) (12259572153 / 10000000000) (105105666314613055409 / 100000000000000000000) : ℚ) : ℝ) <
      (-13244 / 10000 - 2 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase1X1_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith [he.2]

end InternalCatalan




namespace InternalCatalan
open Case1PointData

private theorem barrierCase1X2_approx_upper :
    barrierCase1XApproxRat X2 (-2) (-1) (0) (1271904013 / 1250000000) (3728095987 / 2500000000) (26617739818285504169 / 25000000000000000000) <
      (-13244 / 10000 - 2 / 1000000000000000 : ℚ) := by
  unfold barrierCase1XApproxRat barrierCase1XRat
  rw [barrierCase1TP_eq_explicit, barrierCase1SV_eq_explicit]
  norm_num [X2, barrierCase1TPExplicit, barrierCase1TVExplicit,
    barrierCase1SVExplicit, barrierScaledLogRat, barrierLogHRat, Finset.sum_range_succ]

theorem barrierCase1X2_lt : barrierCase1X (X2 : ℝ) < (-13244 / 10000 : ℝ) := by
  have he := abs_lt.mp (barrierCase1X_approx_error X2 (-2) (-1) (0) (1271904013 / 1250000000) (3728095987 / 2500000000) (26617739818285504169 / 25000000000000000000)
    X2_normalizations.1 X2_normalizations.2.1 X2_normalizations.2.2)
  have ha : ((barrierCase1XApproxRat X2 (-2) (-1) (0) (1271904013 / 1250000000) (3728095987 / 2500000000) (26617739818285504169 / 25000000000000000000) : ℚ) : ℝ) <
      (-13244 / 10000 - 2 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase1X2_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith [he.2]

end InternalCatalan




namespace InternalCatalan
open Case1PointData

private theorem barrierCase1X3_approx_upper :
    barrierCase1XApproxRat X3 (-2) (-1) (0) (4437270259 / 2500000000) (5562729741 / 5000000000) (119689367351405927081 / 100000000000000000000) <
      (-13244 / 10000 - 2 / 1000000000000000 : ℚ) := by
  unfold barrierCase1XApproxRat barrierCase1XRat
  rw [barrierCase1TP_eq_explicit, barrierCase1SV_eq_explicit]
  norm_num [X3, barrierCase1TPExplicit, barrierCase1TVExplicit,
    barrierCase1SVExplicit, barrierScaledLogRat, barrierLogHRat, Finset.sum_range_succ]

theorem barrierCase1X3_lt : barrierCase1X (X3 : ℝ) < (-13244 / 10000 : ℝ) := by
  have he := abs_lt.mp (barrierCase1X_approx_error X3 (-2) (-1) (0) (4437270259 / 2500000000) (5562729741 / 5000000000) (119689367351405927081 / 100000000000000000000)
    X3_normalizations.1 X3_normalizations.2.1 X3_normalizations.2.2)
  have ha : ((barrierCase1XApproxRat X3 (-2) (-1) (0) (4437270259 / 2500000000) (5562729741 / 5000000000) (119689367351405927081 / 100000000000000000000) : ℚ) : ℝ) <
      (-13244 / 10000 - 2 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase1X3_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith [he.2]

end InternalCatalan




namespace InternalCatalan
open Case1PointData

private theorem barrierCase1X4_approx_upper :
    barrierCase1XApproxRat X4 (-1) (-2) (0) (634829897 / 500000000) (365170103 / 250000000) (1403008998125030609 / 1000000000000000000) <
      (-13244 / 10000 - 2 / 1000000000000000 : ℚ) := by
  unfold barrierCase1XApproxRat barrierCase1XRat
  rw [barrierCase1TP_eq_explicit, barrierCase1SV_eq_explicit]
  norm_num [X4, barrierCase1TPExplicit, barrierCase1TVExplicit,
    barrierCase1SVExplicit, barrierScaledLogRat, barrierLogHRat, Finset.sum_range_succ]

theorem barrierCase1X4_lt : barrierCase1X (X4 : ℝ) < (-13244 / 10000 : ℝ) := by
  have he := abs_lt.mp (barrierCase1X_approx_error X4 (-1) (-2) (0) (634829897 / 500000000) (365170103 / 250000000) (1403008998125030609 / 1000000000000000000)
    X4_normalizations.1 X4_normalizations.2.1 X4_normalizations.2.2)
  have ha : ((barrierCase1XApproxRat X4 (-1) (-2) (0) (634829897 / 500000000) (365170103 / 250000000) (1403008998125030609 / 1000000000000000000) : ℚ) : ℝ) <
      (-13244 / 10000 - 2 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase1X4_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith [he.2]

end InternalCatalan




namespace InternalCatalan
open Case1PointData

private theorem barrierCase1X5_approx_upper :
    barrierCase1XApproxRat X5 (0) (1) (1) (1) (1) (1) <
      (-13244 / 10000 - 2 / 1000000000000000 : ℚ) := by
  unfold barrierCase1XApproxRat barrierCase1XRat
  rw [barrierCase1TP_eq_explicit, barrierCase1SV_eq_explicit]
  norm_num [X5, barrierCase1TPExplicit, barrierCase1TVExplicit,
    barrierCase1SVExplicit, barrierScaledLogRat, barrierLogHRat, Finset.sum_range_succ]

theorem barrierCase1X5_lt : barrierCase1X (X5 : ℝ) < (-13244 / 10000 : ℝ) := by
  have he := abs_lt.mp (barrierCase1X_approx_error X5 (0) (1) (1) (1) (1) (1)
    X5_normalizations.1 X5_normalizations.2.1 X5_normalizations.2.2)
  have ha : ((barrierCase1XApproxRat X5 (0) (1) (1) (1) (1) (1) : ℚ) : ℝ) <
      (-13244 / 10000 - 2 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase1X5_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith [he.2]

end InternalCatalan




namespace InternalCatalan
open Case1PointData



end InternalCatalan




namespace InternalCatalan
open Case1PointData



end InternalCatalan




namespace InternalCatalan
open Case1PointData

private theorem barrierCase1Y0_approx_upper :
    barrierCase1YApproxRat Y0 (-5) (-1)
      (266334893 / 156250000) (4733665107 / 2500000000) <
      (-14280 / 10000 - 1 / 1000000000000000 : ℚ) := by
  unfold barrierCase1YApproxRat barrierCase1YRat
  rw [barrierCase1TV_eq_explicit]
  norm_num [Y0, barrierCase1TVExplicit, barrierScaledLogRat,
    barrierLogHRat, Finset.sum_range_succ]

theorem barrierCase1Y0_lt : barrierCase1Y (Y0 : ℝ) < (-14280 / 10000 : ℝ) := by
  have he := abs_lt.mp (barrierCase1Y_approx_error Y0 (-5) (-1)
    (266334893 / 156250000) (4733665107 / 2500000000)
    Y0_normalizations.1 Y0_normalizations.2)
  have ha : ((barrierCase1YApproxRat Y0 (-5) (-1)
      (266334893 / 156250000) (4733665107 / 2500000000) : ℚ) : ℝ) <
      (-14280 / 10000 - 1 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase1Y0_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith [he.2]

end InternalCatalan




namespace InternalCatalan
open Case1PointData

private theorem barrierCase1Y1_approx_upper :
    barrierCase1YApproxRat Y1 (-2) (-1) (100169573 / 100000000) (299830427 / 200000000) <
      (-14280 / 10000 - 1 / 1000000000000000 : ℚ) := by
  unfold barrierCase1YApproxRat barrierCase1YRat
  rw [barrierCase1TV_eq_explicit]
  norm_num [Y1, barrierCase1TPExplicit, barrierCase1TVExplicit,
    barrierCase1SVExplicit, barrierScaledLogRat, barrierLogHRat, Finset.sum_range_succ]

theorem barrierCase1Y1_lt : barrierCase1Y (Y1 : ℝ) < (-14280 / 10000 : ℝ) := by
  have he := abs_lt.mp (barrierCase1Y_approx_error Y1 (-2) (-1) (100169573 / 100000000) (299830427 / 200000000)
    Y1_normalizations.1 Y1_normalizations.2)
  have ha : ((barrierCase1YApproxRat Y1 (-2) (-1) (100169573 / 100000000) (299830427 / 200000000) : ℚ) : ℝ) <
      (-14280 / 10000 - 1 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase1Y1_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith [he.2]

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.FirstBarrier.BarrierCaseOneGlobalBounds
namespace OAI


noncomputable section
namespace InternalCatalan
open Polynomial

theorem barrierCase1AX_transform1_signVariations :
    (barrierDescartesTransform (barrierCase1AX.map (Rat.castHom ℝ)) 13 (-1 / 2) (0)).signVariations = 1 := by
  rw [barrierCase1AX_transform1_eq_explicit]
  have hd : barrierCase1AXTransform1Explicit.degree = 13 := by
    unfold barrierCase1AXTransform1Explicit
    compute_degree!
  rw [signVariations, coeffList, hd]
  norm_num [barrierCase1AXTransform1Explicit,
    List.range_succ, List.destutter, List.destutter', sign_apply,
    coeff_C_mul, coeff_X_pow, coeff_X]


end InternalCatalan




namespace InternalCatalan
open Polynomial

theorem barrierCase1AX_transform2_signVariations :
    (barrierDescartesTransform (barrierCase1AX.map (Rat.castHom ℝ)) 13 (0) (1 / 2)).signVariations = 2 := by
  rw [barrierCase1AX_transform2_eq_explicit]
  have hd : barrierCase1AXTransform2Explicit.degree = 13 := by
    unfold barrierCase1AXTransform2Explicit
    compute_degree!
  rw [signVariations, coeffList, hd]
  norm_num [barrierCase1AXTransform2Explicit,
    List.range_succ, List.destutter, List.destutter', sign_apply,
    coeff_C_mul, coeff_X_pow, coeff_X]


end InternalCatalan




namespace InternalCatalan
open Polynomial

theorem barrierCase1AX_transform3_signVariations :
    (barrierDescartesTransform (barrierCase1AX.map (Rat.castHom ℝ)) 13 (1 / 2) (1)).signVariations = 1 := by
  rw [barrierCase1AX_transform3_eq_explicit]
  have hd : barrierCase1AXTransform3Explicit.degree = 13 := by
    unfold barrierCase1AXTransform3Explicit
    compute_degree!
  rw [signVariations, coeffList, hd]
  norm_num [barrierCase1AXTransform3Explicit,
    List.range_succ, List.destutter, List.destutter', sign_apply,
    coeff_C_mul, coeff_X_pow, coeff_X]


end InternalCatalan






namespace InternalCatalan

open Polynomial

private theorem barrierCase1AX_mapped_natDegree_le :
    (barrierCase1AX.map (Rat.castHom ℝ)).natDegree ≤ 13 := by
  calc
    _ ≤ barrierCase1AX.natDegree := Polynomial.natDegree_map_le
    _ = 13 := barrierCase1AX_natDegree

theorem barrierCase1AX_interval0_roots_card_le (s : Finset ℝ)
    (hs : ∀ x ∈ s, x ∈ Set.Ioo (-1) (-1 / 2) ∧
      (barrierCase1AX.map (Rat.castHom ℝ)).eval x = 0) :
    s.card ≤ 1 := by
  have hne : barrierDescartesTransform
      (barrierCase1AX.map (Rat.castHom ℝ)) 13 (-1) (-1 / 2) ≠ 0 := by
    intro hz
    have h := barrierCase1AX_transform0_signVariations
    rw [hz, Polynomial.signVariations_zero] at h
    norm_num at h
  simpa only [barrierCase1AX_transform0_signVariations] using
    barrierDescartes_interval_roots_card_le
      (barrierCase1AX.map (Rat.castHom ℝ)) 13 (-1) (-1 / 2)
      barrierCase1AX_mapped_natDegree_le hne s hs

theorem barrierCase1AX_interval1_roots_card_le (s : Finset ℝ)
    (hs : ∀ x ∈ s, x ∈ Set.Ioo (-1 / 2) 0 ∧
      (barrierCase1AX.map (Rat.castHom ℝ)).eval x = 0) :
    s.card ≤ 1 := by
  have hne : barrierDescartesTransform
      (barrierCase1AX.map (Rat.castHom ℝ)) 13 (-1 / 2) 0 ≠ 0 := by
    intro hz
    have h := barrierCase1AX_transform1_signVariations
    rw [hz, Polynomial.signVariations_zero] at h
    norm_num at h
  simpa only [barrierCase1AX_transform1_signVariations] using
    barrierDescartes_interval_roots_card_le
      (barrierCase1AX.map (Rat.castHom ℝ)) 13 (-1 / 2) 0
      barrierCase1AX_mapped_natDegree_le hne s hs

theorem barrierCase1AX_interval2_roots_card_le (s : Finset ℝ)
    (hs : ∀ x ∈ s, x ∈ Set.Ioo 0 (1 / 2) ∧
      (barrierCase1AX.map (Rat.castHom ℝ)).eval x = 0) :
    s.card ≤ 2 := by
  have hne : barrierDescartesTransform
      (barrierCase1AX.map (Rat.castHom ℝ)) 13 0 (1 / 2) ≠ 0 := by
    intro hz
    have h := barrierCase1AX_transform2_signVariations
    rw [hz, Polynomial.signVariations_zero] at h
    norm_num at h
  simpa only [barrierCase1AX_transform2_signVariations] using
    barrierDescartes_interval_roots_card_le
      (barrierCase1AX.map (Rat.castHom ℝ)) 13 0 (1 / 2)
      barrierCase1AX_mapped_natDegree_le hne s hs

theorem barrierCase1AX_interval3_roots_card_le (s : Finset ℝ)
    (hs : ∀ x ∈ s, x ∈ Set.Ioo (1 / 2) 1 ∧
      (barrierCase1AX.map (Rat.castHom ℝ)).eval x = 0) :
    s.card ≤ 1 := by
  have hne : barrierDescartesTransform
      (barrierCase1AX.map (Rat.castHom ℝ)) 13 (1 / 2) 1 ≠ 0 := by
    intro hz
    have h := barrierCase1AX_transform3_signVariations
    rw [hz, Polynomial.signVariations_zero] at h
    norm_num at h
  simpa only [barrierCase1AX_transform3_signVariations] using
    barrierDescartes_interval_roots_card_le
      (barrierCase1AX.map (Rat.castHom ℝ)) 13 (1 / 2) 1
      barrierCase1AX_mapped_natDegree_le hne s hs

private theorem barrierCase1AX_map_eval_rat_ne_zero (q : ℚ)
    (hq : barrierCase1AX.eval q ≠ 0) :
    (barrierCase1AX.map (Rat.castHom ℝ)).eval (q : ℝ) ≠ 0 := by
  have heval : (barrierCase1AX.map (Rat.castHom ℝ)).eval (q : ℝ) =
      ((barrierCase1AX.eval q : ℚ) : ℝ) := by
    change (barrierCase1AX.map (Rat.castHom ℝ)).eval ((Rat.castHom ℝ) q) =
      (Rat.castHom ℝ) (barrierCase1AX.eval q)
    exact Polynomial.eval_map_apply (Rat.castHom ℝ) q
  rw [heval]
  exact_mod_cast hq

private theorem barrierCase1AX_root_subdivision {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo (0 : ℝ) 1)
    (hr : (barrierCase1AX.map (Rat.castHom ℝ)).eval x = 0) :
    x ∈ Set.Ioo (-1 : ℝ) (-1 / 2) ∨ x ∈ Set.Ioo (-1 / 2 : ℝ) 0 ∨
      x ∈ Set.Ioo (0 : ℝ) (1 / 2) ∨ x ∈ Set.Ioo (1 / 2 : ℝ) 1 := by
  have hn : (barrierCase1AX.map (Rat.castHom ℝ)).eval (-1 / 2 : ℝ) ≠ 0 := by
    simpa using barrierCase1AX_map_eval_rat_ne_zero (-1 / 2)
      barrierCase1AX_subdivision_nonzero.2.1
  have hp : (barrierCase1AX.map (Rat.castHom ℝ)).eval (1 / 2 : ℝ) ≠ 0 := by
    simpa using barrierCase1AX_map_eval_rat_ne_zero (1 / 2)
      barrierCase1AX_subdivision_nonzero.2.2.2.1
  have hxne : x ≠ (-1 / 2 : ℝ) := by
    intro heq
    exact hn (by simpa only [heq] using hr)
  have hxpe : x ≠ (1 / 2 : ℝ) := by
    intro heq
    exact hp (by simpa only [heq] using hr)
  rcases hx with hx | hx
  · rcases lt_or_gt_of_ne hxne with hlt | hgt
    · exact Or.inl ⟨hx.1, hlt⟩
    · exact Or.inr (Or.inl ⟨hgt, hx.2⟩)
  · rcases lt_or_gt_of_ne hxpe with hlt | hgt
    · exact Or.inr (Or.inr (Or.inl ⟨hx.1, hlt⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hgt, hx.2⟩))

theorem barrierCase1AX_domain_roots_card_le (s : Finset ℝ)
    (hs : ∀ x ∈ s, x ∈ Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo (0 : ℝ) 1 ∧
      (barrierCase1AX.map (Rat.castHom ℝ)).eval x = 0) :
    s.card ≤ 5 := by
  classical
  let s0 := s.filter (fun x => x ∈ Set.Ioo (-1 : ℝ) (-1 / 2))
  let s1 := s.filter (fun x => x ∈ Set.Ioo (-1 / 2 : ℝ) 0)
  let s2 := s.filter (fun x => x ∈ Set.Ioo (0 : ℝ) (1 / 2))
  let s3 := s.filter (fun x => x ∈ Set.Ioo (1 / 2 : ℝ) 1)
  have h0 : s0.card ≤ 1 := by
    apply barrierCase1AX_interval0_roots_card_le
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact ⟨hx'.2, (hs x hx'.1).2⟩
  have h1 : s1.card ≤ 1 := by
    apply barrierCase1AX_interval1_roots_card_le
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact ⟨hx'.2, (hs x hx'.1).2⟩
  have h2 : s2.card ≤ 2 := by
    apply barrierCase1AX_interval2_roots_card_le
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact ⟨hx'.2, (hs x hx'.1).2⟩
  have h3 : s3.card ≤ 1 := by
    apply barrierCase1AX_interval3_roots_card_le
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact ⟨hx'.2, (hs x hx'.1).2⟩
  have hcover : s ⊆ s0 ∪ (s1 ∪ (s2 ∪ s3)) := by
    intro x hx
    have hparts := barrierCase1AX_root_subdivision (hs x hx).1 (hs x hx).2
    simp only [Finset.mem_union]
    rcases hparts with hx0 | hx1 | hx2 | hx3
    · exact Or.inl (Finset.mem_filter.mpr ⟨hx, hx0⟩)
    · exact Or.inr (Or.inl (Finset.mem_filter.mpr ⟨hx, hx1⟩))
    · exact Or.inr (Or.inr (Or.inl (Finset.mem_filter.mpr ⟨hx, hx2⟩)))
    · exact Or.inr (Or.inr (Or.inr (Finset.mem_filter.mpr ⟨hx, hx3⟩)))
  calc
    s.card ≤ (s0 ∪ (s1 ∪ (s2 ∪ s3))).card := Finset.card_le_card hcover
    _ ≤ s0.card + (s1 ∪ (s2 ∪ s3)).card := Finset.card_union_le _ _
    _ ≤ s0.card + (s1.card + (s2 ∪ s3).card) :=
      Nat.add_le_add_left (Finset.card_union_le _ _) _
    _ ≤ s0.card + (s1.card + (s2.card + s3.card)) :=
      Nat.add_le_add_left (Nat.add_le_add_left (Finset.card_union_le _ _) _) _
    _ ≤ 1 + (1 + (2 + 1)) := Nat.add_le_add h0 (Nat.add_le_add h1 (Nat.add_le_add h2 h3))
    _ = 5 := rfl

private theorem barrierCase1X_bracket_subset_domain {m : ℤ}
    (hm : m ∈ barrierCase1XBrackets) {x : ℝ}
    (hx : x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ)) :
    x ∈ Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo (0 : ℝ) 1 := by
  obtain ⟨ha, hb, hzero⟩ := barrierCase1X_bracket_domain m hm
  have ha' : (-1 : ℝ) < (barrierBracketLeft m : ℝ) := by exact_mod_cast ha
  have hb' : (barrierBracketRight m : ℝ) < (1 : ℝ) := by exact_mod_cast hb
  rcases hzero with hneg | hpos
  · have hn' : (barrierBracketRight m : ℝ) < (0 : ℝ) := by exact_mod_cast hneg
    exact Or.inl ⟨ha'.trans hx.1, hx.2.trans hn'⟩
  · have hp' : (0 : ℝ) < (barrierBracketLeft m : ℝ) := by exact_mod_cast hpos
    exact Or.inr ⟨hp'.trans hx.1, hx.2.trans hb'⟩

private theorem barrierCase1X_brackets_disjoint {m n : ℤ}
    (hm : m ∈ barrierCase1XBrackets) (hn : n ∈ barrierCase1XBrackets)
    (hmn : m ≠ n) {x : ℝ}
    (hx : x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ))
    (hy : x ∈ Set.Ioo (barrierBracketLeft n : ℝ) (barrierBracketRight n : ℝ)) :
    False := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  simp only [barrierCase1XBrackets, List.mem_cons, List.not_mem_nil, or_false] at hm hn
  rcases hm with rfl | rfl | rfl | rfl | rfl
  <;> rcases hn with rfl | rfl | rfl | rfl | rfl
  all_goals try exact hmn rfl
  all_goals norm_num [barrierBracketLeft, barrierBracketRight] at hx0 hx1 hy0 hy1
  all_goals linarith

private def barrierCase1XChosenRoot (m : ℤ) : ℝ :=
  if hm : m ∈ barrierCase1XBrackets then
    Classical.choose (barrierCase1AX_root_in_each_bracket m hm)
  else 0

private theorem barrierCase1XChosenRoot_spec (m : ℤ)
    (hm : m ∈ barrierCase1XBrackets) :
    barrierCase1XChosenRoot m ∈
        Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) ∧
      (barrierCase1AX.map (Rat.castHom ℝ)).eval (barrierCase1XChosenRoot m) = 0 := by
  simpa only [barrierCase1XChosenRoot, dif_pos hm] using
    Classical.choose_spec (barrierCase1AX_root_in_each_bracket m hm)

private def barrierCase1XChosenRoots : Finset ℝ := by
  classical
  exact barrierCase1XBrackets.toFinset.image barrierCase1XChosenRoot

private theorem barrierCase1XChosenRoots_card : barrierCase1XChosenRoots.card = 5 := by
  classical
  have hinj : Set.InjOn barrierCase1XChosenRoot
      (↑barrierCase1XBrackets.toFinset : Set ℤ) := by
    intro m hm n hn heq
    have hm' : m ∈ barrierCase1XBrackets := List.mem_toFinset.mp hm
    have hn' : n ∈ barrierCase1XBrackets := List.mem_toFinset.mp hn
    by_contra hmn
    exact barrierCase1X_brackets_disjoint hm' hn' hmn
      (barrierCase1XChosenRoot_spec m hm').1
      (by simpa only [heq] using (barrierCase1XChosenRoot_spec n hn').1)
  unfold barrierCase1XChosenRoots
  rw [Finset.card_image_of_injOn hinj]
  norm_num [barrierCase1XBrackets]

private theorem barrierCase1XChosenRoots_spec {x : ℝ}
    (hx : x ∈ barrierCase1XChosenRoots) :
    x ∈ Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo (0 : ℝ) 1 ∧ (barrierCase1AX.map (Rat.castHom ℝ)).eval x = 0 := by
  classical
  change x ∈ barrierCase1XBrackets.toFinset.image barrierCase1XChosenRoot at hx
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
  have hm' : m ∈ barrierCase1XBrackets := List.mem_toFinset.mp hm
  have hr := barrierCase1XChosenRoot_spec m hm'
  exact ⟨barrierCase1X_bracket_subset_domain hm' hr.1, hr.2⟩

private theorem barrierCase1AX_root_mem_chosen {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo (0 : ℝ) 1)
    (hr : (barrierCase1AX.map (Rat.castHom ℝ)).eval x = 0) :
    x ∈ barrierCase1XChosenRoots := by
  classical
  by_contra hnot
  have hb : (insert x barrierCase1XChosenRoots).card ≤ 5 := by
    apply barrierCase1AX_domain_roots_card_le
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact ⟨hx, hr⟩
    · exact barrierCase1XChosenRoots_spec hy
  rw [Finset.card_insert_of_notMem hnot, barrierCase1XChosenRoots_card] at hb
  norm_num at hb

theorem barrierCase1AX_roots_exhausted {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo (0 : ℝ) 1)
    (hr : (barrierCase1AX.map (Rat.castHom ℝ)).eval x = 0) :
    ∃ m ∈ barrierCase1XBrackets,
      x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) := by
  classical
  have hmem := barrierCase1AX_root_mem_chosen hx hr
  change x ∈ barrierCase1XBrackets.toFinset.image barrierCase1XChosenRoot at hmem
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hmem
  have hm' : m ∈ barrierCase1XBrackets := List.mem_toFinset.mp hm
  exact ⟨m, hm', (barrierCase1XChosenRoot_spec m hm').1⟩


end InternalCatalan




namespace InternalCatalan
open Set

theorem barrierCase1X_le_of_bracket_bounds (M : ℝ)
    (hneg : barrierCase1X (-1) ≤ M)
    (hbr : ∀ m ∈ barrierCase1XBrackets, ∀ x ∈
      Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ),
      barrierCase1X x ≤ M) :
    ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo (0 : ℝ) 1, barrierCase1X x ≤ M := by
  apply GlobalMaxReduction.le_on_two_components_of_stationary_cover
    (S := {x | ∃ m ∈ barrierCase1XBrackets,
      x ∈ Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ)})
  · intro x hx
    exact (barrierCase1X_hasDerivAt (by linarith [hx.2])
      (by linarith [hx.2])).continuousAt.continuousWithinAt
  · intro x hx
    exact (barrierCase1X_hasDerivAt (by linarith [hx.1])
      (by linarith [hx.2])).continuousAt.continuousWithinAt
  · exact hneg
  · exact barrierCase1X_tendsto_zero_left
  · exact barrierCase1X_tendsto_zero_right
  · exact barrierCase1X_tendsto_one_left
  · intro x hx hd
    have h0 : x ≠ 0 := by rcases hx with hx | hx <;> linarith [hx.1, hx.2]
    have h1 : x ≠ 1 := by rcases hx with hx | hx <;> linarith [hx.1, hx.2]
    exact barrierCase1AX_roots_exhausted hx ((barrierCase1X_deriv_eq_zero_iff h0 h1).1 hd)
  · rintro x ⟨m, hm, hx⟩
    exact hbr m hm x hx

theorem barrierCase1Y_le_of_bracket_bounds (M : ℝ)
    (hbr : ∀ m ∈ barrierCase1YBrackets, ∀ x ∈
      Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ),
      barrierCase1Y x ≤ M) :
    ∀ x ∈ Ioo (0 : ℝ) 1, barrierCase1Y x ≤ M := by
  apply GlobalMaxReduction.le_on_Ioo_of_stationary_cover
    (S := {x | ∃ m ∈ barrierCase1YBrackets,
      x ∈ Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ)})
  · intro x hx
    exact (barrierCase1Y_hasDerivAt (by linarith [hx.1])
      (by linarith [hx.2])).continuousAt.continuousWithinAt
  · exact barrierCase1Y_tendsto_zero_right
  · exact barrierCase1Y_tendsto_one_left
  · intro x hx hd
    exact barrierCase1AY_roots_exhausted hx ((barrierCase1Y_deriv_eq_zero_iff
      (by linarith [hx.1]) (by linarith [hx.2])).1 hd)
  · rintro x ⟨m, hm, hx⟩
    exact hbr m hm x hx

end InternalCatalan




namespace InternalCatalan
open Polynomial
















end InternalCatalan




namespace InternalCatalan
open Case1PointData

private theorem barrierCase1Y2_approx_upper :
    barrierCase1YApproxRat Y2 (-1) (-2) (2850869403 / 2500000000) (2149130597 / 1250000000) <
      (-14280 / 10000 - 1 / 1000000000000000 : ℚ) := by
  unfold barrierCase1YApproxRat barrierCase1YRat
  rw [barrierCase1TV_eq_explicit]
  norm_num [Y2, barrierCase1TPExplicit, barrierCase1TVExplicit,
    barrierCase1SVExplicit, barrierScaledLogRat, barrierLogHRat, Finset.sum_range_succ]

theorem barrierCase1Y2_lt : barrierCase1Y (Y2 : ℝ) < (-14280 / 10000 : ℝ) := by
  have he := abs_lt.mp (barrierCase1Y_approx_error Y2 (-1) (-2) (2850869403 / 2500000000) (2149130597 / 1250000000)
    Y2_normalizations.1 Y2_normalizations.2)
  have ha : ((barrierCase1YApproxRat Y2 (-1) (-2) (2850869403 / 2500000000) (2149130597 / 1250000000) : ℚ) : ℝ) <
      (-14280 / 10000 - 1 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase1Y2_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith [he.2]

end InternalCatalan




namespace InternalCatalan
open Case1PointData

private theorem barrierCase1Y3_approx_upper :
    barrierCase1YApproxRat Y3 (-1) (-3) (7966939383 / 5000000000) (2033060617 / 1250000000) <
      (-14280 / 10000 - 1 / 1000000000000000 : ℚ) := by
  unfold barrierCase1YApproxRat barrierCase1YRat
  rw [barrierCase1TV_eq_explicit]
  norm_num [Y3, barrierCase1TPExplicit, barrierCase1TVExplicit,
    barrierCase1SVExplicit, barrierScaledLogRat, barrierLogHRat, Finset.sum_range_succ]

theorem barrierCase1Y3_lt : barrierCase1Y (Y3 : ℝ) < (-14280 / 10000 : ℝ) := by
  have he := abs_lt.mp (barrierCase1Y_approx_error Y3 (-1) (-3) (7966939383 / 5000000000) (2033060617 / 1250000000)
    Y3_normalizations.1 Y3_normalizations.2)
  have ha : ((barrierCase1YApproxRat Y3 (-1) (-3) (7966939383 / 5000000000) (2033060617 / 1250000000) : ℚ) : ℝ) <
      (-14280 / 10000 - 1 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase1Y3_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith [he.2]

end InternalCatalan




namespace InternalCatalan
open Case1PointData

private theorem barrierCase1Y4_approx_upper :
    barrierCase1YApproxRat Y4 (-1) (-5) (4727245069 / 2500000000) (272754931 / 156250000) <
      (-14280 / 10000 - 1 / 1000000000000000 : ℚ) := by
  unfold barrierCase1YApproxRat barrierCase1YRat
  rw [barrierCase1TV_eq_explicit]
  norm_num [Y4, barrierCase1TPExplicit, barrierCase1TVExplicit,
    barrierCase1SVExplicit, barrierScaledLogRat, barrierLogHRat, Finset.sum_range_succ]

theorem barrierCase1Y4_lt : barrierCase1Y (Y4 : ℝ) < (-14280 / 10000 : ℝ) := by
  have he := abs_lt.mp (barrierCase1Y_approx_error Y4 (-1) (-5) (4727245069 / 2500000000) (272754931 / 156250000)
    Y4_normalizations.1 Y4_normalizations.2)
  have ha : ((barrierCase1YApproxRat Y4 (-1) (-5) (4727245069 / 2500000000) (272754931 / 156250000) : ℚ) : ℝ) <
      (-14280 / 10000 - 1 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase1Y4_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith [he.2]

end InternalCatalan




namespace InternalCatalan

theorem barrierCase1X_bracket_left_lt (m : ℤ)
    (hm : m ∈ barrierCase1XBrackets) :
    barrierCase1X (barrierBracketLeft m : ℝ) < (-13244 / 10000 : ℝ) := by
  simp only [barrierCase1XBrackets, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  · convert barrierCase1X0_lt using 1
    norm_num [barrierBracketLeft, Case1PointData.X0]
  · convert barrierCase1X1_lt using 1
    norm_num [barrierBracketLeft, Case1PointData.X1]
  · convert barrierCase1X2_lt using 1
    norm_num [barrierBracketLeft, Case1PointData.X2]
  · convert barrierCase1X3_lt using 1
    norm_num [barrierBracketLeft, Case1PointData.X3]
  · convert barrierCase1X4_lt using 1
    norm_num [barrierBracketLeft, Case1PointData.X4]
theorem barrierCase1Y_bracket_left_lt (m : ℤ)
    (hm : m ∈ barrierCase1YBrackets) :
    barrierCase1Y (barrierBracketLeft m : ℝ) < (-14280 / 10000 : ℝ) := by
  simp only [barrierCase1YBrackets, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  · convert barrierCase1Y0_lt using 1
    norm_num [barrierBracketLeft, Case1PointData.Y0]
  · convert barrierCase1Y1_lt using 1
    norm_num [barrierBracketLeft, Case1PointData.Y1]
  · convert barrierCase1Y2_lt using 1
    norm_num [barrierBracketLeft, Case1PointData.Y2]
  · convert barrierCase1Y3_lt using 1
    norm_num [barrierBracketLeft, Case1PointData.Y3]
  · convert barrierCase1Y4_lt using 1
    norm_num [barrierBracketLeft, Case1PointData.Y4]

theorem barrierCase1X_neg_one_lt : barrierCase1X (-1) < (-13244 / 10000 : ℝ) := by
  simpa [Case1PointData.X5] using barrierCase1X5_lt






theorem barrierCase1X_global_upper {x : ℝ}
    (hx : -1 ≤ x ∧ x < 1 ∧ x ≠ 0) :
    barrierCase1X x ≤ (-13244 / 10000 : ℝ) + 24 / 1000000 := by
  have hbound := barrierCase1X_le_of_bracket_bounds
    ((-13244 / 10000 : ℝ) + 24 / 1000000)
    (by linarith [barrierCase1X_neg_one_lt])
    (by
      intro m hm y hy
      have hp := barrierCase1X_bracket_left_lt m hm
      have hh := barrierCase1X_bracket_height m hm hy
      linarith)
  apply hbound x
  by_cases hneg : x < 0
  · exact Or.inl ⟨hx.1, hneg⟩
  · exact Or.inr ⟨by rcases hx with ⟨_, _, hx0⟩; rcases lt_or_gt_of_ne hx0 with h | h <;> linarith,
      hx.2.1⟩

theorem barrierCase1Y_global_upper {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    barrierCase1Y x ≤ (-14280 / 10000 : ℝ) + 24 / 1000000 := by
  apply barrierCase1Y_le_of_bracket_bounds
    ((-14280 / 10000 : ℝ) + 24 / 1000000) _ x hx
  intro m hm y hy
  have hp := barrierCase1Y_bracket_left_lt m hm
  have hh := barrierCase1Y_bracket_height m hm hy
  linarith

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoNorm
namespace OAI


noncomputable section
namespace InternalCatalan


theorem barrier_case2_norm_coarse_upper :
    2 * barrierTrialNormSq barrierP2 + (1 / 2 : ℝ) * barrierTrialNormSq barrierV2 <
      (77844 / 100000 : ℝ) :=
  lt_of_le_of_lt barrier_case2_norm_rational_upper (by norm_num)

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.RealDeterminantUpper
namespace OAI


noncomputable section
open Filter
open scoped Topology

namespace InternalCatalan









end InternalCatalan

end



noncomputable section
open Set Filter
open scoped BigOperators

namespace InternalCatalan



end InternalCatalan

end



noncomputable section
open Set Filter
open scoped BigOperators

namespace InternalCatalan




end InternalCatalan

end



noncomputable section
open Set Filter

namespace InternalCatalan

private theorem barrier_case1_row_sup_upper :
    realEnergyRowTrialSup 1 barrierLambda1 barrierP1 barrierV1 ≤
      (-13244 / 10000 : ℝ) + 24 / 1000000 := by
  unfold realEnergyRowTrialSup
  refine csSup_le (realEnergyRowTrialField_image_nonempty _ _ _ _) ?_
  rintro y ⟨x, hx, rfl⟩
  simpa [realEnergyRowTrialField, barrierCase1X] using
    barrierCase1X_global_upper ⟨hx.1.1, hx.1.2, hx.2⟩

private theorem barrier_case1_column_sup_upper :
    realEnergyColumnTrialSup barrierV1 ≤ (-14280 / 10000 : ℝ) + 24 / 1000000 := by
  unfold realEnergyColumnTrialSup
  refine csSup_le (realEnergyColumnTrialField_image_nonempty _) ?_
  rintro y ⟨x, hx, rfl⟩
  simpa only [realEnergyColumnTrialField, barrierCase1Y] using barrierCase1Y_global_upper hx

private theorem barrier_case2_row_sup_upper :
    realEnergyRowTrialSup 2 0 barrierP2 barrierV2 ≤
      (-98399 / 100000 : ℝ) + 24 / 1000000 := by
  unfold realEnergyRowTrialSup
  refine csSup_le (realEnergyRowTrialField_image_nonempty _ _ _ _) ?_
  rintro y ⟨x, hx, rfl⟩
  simpa [realEnergyRowTrialField, barrierCase2X, barrierLambda2,
    show (2 : ℝ) * 2 = 4 by norm_num] using
    barrierCase2X_global_upper ⟨hx.1.1, hx.1.2, hx.2⟩

private theorem barrier_case2_column_sup_upper :
    realEnergyColumnTrialSup barrierV2 ≤ (-160890 / 100000 : ℝ) + 24 / 1000000 := by
  unfold realEnergyColumnTrialSup
  refine csSup_le (realEnergyColumnTrialField_image_nonempty _) ?_
  rintro y ⟨x, hx, rfl⟩
  simpa only [realEnergyColumnTrialField, barrierCase2Y] using barrierCase2Y_global_upper hx

theorem realDeterminantCaseOneDual_sharp_lt :
    realEnergyDualConstant 1 barrierP1 barrierV1
      (realEnergyRowTrialSup 1 barrierLambda1 barrierP1 barrierV1)
      (realEnergyColumnTrialSup barrierV1) < -(2296789875 / 1000000000 : ℝ) := by
  unfold realEnergyDualConstant
  nlinarith only [barrier_case1_norm_coarse_upper, barrier_case1_row_sup_upper,
    barrier_case1_column_sup_upper, barrier_one_coarse_total_sharp_lt]

theorem realDeterminantCaseTwoDual_sharp_lt :
    realEnergyDualConstant 2 barrierP2 barrierV2
      (realEnergyRowTrialSup 2 0 barrierP2 barrierV2)
      (realEnergyColumnTrialSup barrierV2) < -(2290939875 / 1000000000 : ℝ) := by
  unfold realEnergyDualConstant
  nlinarith only [barrier_case2_norm_coarse_upper, barrier_case2_row_sup_upper,
    barrier_case2_column_sup_upper, barrier_two_coarse_total_sharp_lt]

theorem realDeterminantCertificateSupBound_sharp_lt :
    realDeterminantCertificateSupBound < -(2290939875 / 1000000000 : ℝ) := by
  unfold realDeterminantCertificateSupBound
  apply max_lt
  · exact lt_trans realDeterminantCaseOneDual_sharp_lt (by norm_num)
  · exact realDeterminantCaseTwoDual_sharp_lt

theorem realDeterminantCertificateSupBound_lt :
    realDeterminantCertificateSupBound < -(22909 / 10000 : ℝ) :=
  lt_trans realDeterminantCertificateSupBound_sharp_lt (by norm_num)



theorem eventually_realDeterminant_log_upper :
    ∀ᶠ N : ℕ in atTop, determinant N ≠ 0 →
      Real.log |determinant N| / (n N : ℝ) ^ 2 - Real.log 2 / 2 <
        -(22909 / 10000 : ℝ) := by
  have hd : 0 < (-(22909 / 10000 : ℝ) - realDeterminantCertificateSupBound) / 2 := by
    linarith [realDeterminantCertificateSupBound_lt]
  filter_upwards [realDeterminant_eventually_log_certificate_sup hd] with N hN
  intro hnonzero
  have hupper := hN hnonzero
  linarith [realDeterminantCertificateSupBound_lt]

end InternalCatalan

end

end OAI

end

section
open OAI.InternalCatalan
open Set Filter

theorem solution :
    ∀ᶠ N : ℕ in atTop, determinant N ≠ 0 →
      Real.log |determinant N| / (n N : ℝ) ^ 2 - Real.log 2 / 2 <
        -(22909 / 10000 : ℝ) := by
  first
  | exact @OAI.InternalCatalan.eventually_realDeterminant_log_upper
  | (apply OAI.InternalCatalan.eventually_realDeterminant_log_upper <;> assumption)

end
