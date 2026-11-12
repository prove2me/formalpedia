-- Prove2me | solution 1 for OAI.Erdos970.NumberTheoryLean.ScaledOriginalTail.actual_uniform_scaled_tail_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:08:34.187548+00:00
-- url     : https://prove2.me/submissions/29c260bd-d512-4e96-8073-978eea5f68fb

import Batteries.Tactic.Lemma
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Group.Support
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompMap
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.Bound
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Lattice
import Definitions.Def_OAIQ247J010
import Theorems.Thm_OAI_Erdos970_NumberTheoryLean_GrowingFarTail_source_growing_far_tail_jb247
import Theorems.Thm_OAI_Erdos970_NumberTheoryLean_SourceCouplingRate_source_coupling_rate_jb247
import Theorems.Thm_OAI_Erdos970_NumberTheoryLean_SourceSuccessfulTail_source_successful_tail_jb247

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FiniteHistorySupport
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.Erdos970.NumberTheoryLean.ReferenceBenchmarkDecay.benchmark_even_below_two
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.FinitePathGeometry

open Set
open DerivativeWeights TransitionKernels

theorem nextGap_div_ratio {r t : ℝ} (ht : 0 < t) : nextGap r t / t = nextExponent r t := by
  unfold nextGap nextExponent
  field_simp

theorem nextGap_eq_cost {r t : ℝ} (ht : 0 < t) : nextGap r t = r * Real.exp (-cost t) := by
  have hx : 0 < 1 + 1 / t := by positivity
  unfold cost nextGap
  rw [Real.exp_neg, Real.exp_log hx]
  field_simp

theorem finalGap_eq_cost {i : Side} {s r : ℝ} {ts : List ℝ}
    (hs : Valid i s) (ht : Admissible i s ts) :
    finalGap r ts = r * Real.exp (-pathCost ts) := by
  induction ts generalizing i s r with
  | nil => simp [finalGap, pathCost]
  | cons t ts ih =>
    have hv := valid_next hs ht.1
    rw [finalGap, ih hv ht.2, nextGap_eq_cost (valid_pos hv), pathCost,
      neg_add, Real.exp_add]
    ring

end NumberTheoryLean.FinitePathGeometry



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_WeightIntegrals
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.Erdos970.NumberTheoryLean.ReferenceBenchmarkDecay.benchmark_even_below_two
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.TwoStepDensityBounds

open Set
open DerivativeWeights WeightFutureIntegrals FinitePathGeometry

theorem weight_antitone {i : Side} {s t : ℝ} (hs : Valid i s) (ht : Valid i t) (hst : s ≤ t) :
    weight i t ≤ weight i s := by
  cases i with
  | even =>
    exact phiEven_strictAntiOn.antitoneOn
      (by change 1 < s; dsimp [Valid] at hs <;> linarith)
      (by change 1 < t; dsimp [Valid] at ht <;> linarith) hst
  | odd => exact phiOdd_antitone hst

end NumberTheoryLean.TwoStepDensityBounds

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_InverseWeightGrowth
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.Erdos970.NumberTheoryLean.ReferenceBenchmarkDecay.benchmark_even_below_two
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.WeightGlobalBounds

open Filter Set
open scoped Topology
open LinearSieveFunctions BuchstabBridge DerivativeWeights WeightTailBounds

theorem weights_global_logDeriv_bound : ∃ C : ℝ, 0 < C ∧
    (∀ s : ℝ, 198 / 100 ≤ s →
      |deriv phiEven s / phiEven s| ≤ C * (1 + s) ^ 3) ∧
    (∀ s : ℝ, 3 < s → |deriv phiOdd s / phiOdd s| ≤ C * (1 + s) ^ 3) := by
  obtain ⟨C, hC, he, ho⟩ := weights_global_ratio_bound
  refine ⟨4 * C, by positivity, ?_, ?_⟩
  · intro s hs
    have hs1 : 1 < s := by linarith
    have hcoeff : s / (s - 1) ^ 2 ≤ 4 * (1 + s) := by
      apply (div_le_iff₀ (sq_pos_of_pos (by linarith))).mpr
      have hsq : (1 : ℝ) / 4 ≤ (s - 1) ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hsq (show 0 ≤ 4 * (1 + s) by linarith)]
    have hr0 : 0 ≤ phiOdd (s - 1) / phiEven s :=
      (div_pos (phiOdd_pos _) (phiEven_pos hs1)).le
    have hn : 0 ≤ -deriv phiEven s / phiEven s := by rw [even_logDeriv_eq hs1]; positivity
    have habs : |deriv phiEven s / phiEven s| = -deriv phiEven s / phiEven s := by
      rw [abs_of_nonpos (by rw [neg_div] at hn; linarith)]
      ring
    rw [habs, even_logDeriv_eq hs1]
    calc
      _ ≤ (4 * (1 + s)) * (C * (1 + s) ^ 2) := mul_le_mul hcoeff (he s hs) hr0 (by linarith)
      _ = _ := by ring
  · intro s hs
    have hcoeff : s / (s - 1) ^ 2 ≤ 4 * (1 + s) := by
      apply (div_le_iff₀ (sq_pos_of_pos (by linarith))).mpr
      have hsq : 1 ≤ (s - 1) ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hsq (show 0 ≤ 4 * (1 + s) by linarith)]
    have hr : phiEven (s - 1) / phiOdd s ≤ C * (1 + s) ^ 2 := by
      have h := ho s (by linarith)
      rwa [max_eq_right (show 2 ≤ s - 1 by linarith)] at h
    have hr0 : 0 ≤ phiEven (s - 1) / phiOdd s :=
      (div_pos (phiEven_pos (by linarith)) (phiOdd_pos s)).le
    have hn : 0 ≤ -deriv phiOdd s / phiOdd s := by rw [odd_logDeriv_eq hs]; positivity
    have habs : |deriv phiOdd s / phiOdd s| = -deriv phiOdd s / phiOdd s := by
      rw [abs_of_nonpos (by rw [neg_div] at hn; linarith)]
      ring
    rw [habs, odd_logDeriv_eq hs]
    calc
      _ ≤ (4 * (1 + s)) * (C * (1 + s) ^ 2) := mul_le_mul hcoeff hr hr0 (by linarith)
      _ = _ := by ring

theorem interval_abs_bound {H d : ℝ → ℝ} {a b B : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn H (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt H (d t) t)
    (hb : ∀ t ∈ Ioo a b, |d t| ≤ B) : |H b - H a| ≤ B * (b - a) := by
  rcases eq_or_lt_of_le hab with h | h
  · subst b
    simp
  · obtain ⟨t, ht, heq⟩ := exists_deriv_eq_slope H h hc
      (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    rw [(hd t ht).deriv] at heq
    have hbound := hb t ht
    rw [heq, abs_div, abs_of_pos (sub_pos.mpr h)] at hbound
    exact (div_le_iff₀ (sub_pos.mpr h)).mp hbound

theorem phiOdd_max_three (s : ℝ) : phiOdd (max 3 s) = phiOdd s := by
  by_cases hs : s ≤ 3
  · rw [max_eq_left hs, phiOdd_initial le_rfl, phiOdd_initial hs]
  · rw [max_eq_right (le_of_not_ge hs)]

theorem weights_log_lipschitz : ∃ C : ℝ, 0 < C ∧ ∀ S : ℝ, 3 ≤ S →
    (∀ u v : ℝ, 198 / 100 ≤ u → 198 / 100 ≤ v → u ≤ S → v ≤ S →
      |Real.log (phiEven u) - Real.log (phiEven v)| ≤ C * (1 + S) ^ 3 * |u - v|) ∧
    (∀ u v : ℝ, 95 / 100 ≤ u → 95 / 100 ≤ v → u ≤ S → v ≤ S →
      |Real.log (phiOdd u) - Real.log (phiOdd v)| ≤ C * (1 + S) ^ 3 * |u - v|) := by
  obtain ⟨C, hC, he, ho⟩ := weights_global_logDeriv_bound
  refine ⟨C, hC, ?_⟩
  intro S hS
  have he_ordered : ∀ u v : ℝ, 198 / 100 ≤ u → u ≤ v → v ≤ S →
      |Real.log (phiEven v) - Real.log (phiEven u)| ≤ C * (1 + S) ^ 3 * (v - u) := by
    intro u v hu huv hv
    apply interval_abs_bound huv
    · intro t ht
      have ht1 : 1 < t := by linarith [ht.1]
      exact ((phiEven_continuousAt ht1).log (ne_of_gt (phiEven_pos ht1))).continuousWithinAt
    · intro t ht
      exact ((phiEven_hasDerivAt (by linarith [ht.1])).differentiableAt.hasDerivAt.log
        (ne_of_gt (phiEven_pos (by linarith [ht.1]))))
    · intro t ht
      have h := he t (by linarith [ht.1])
      apply le_trans h
      apply mul_le_mul_of_nonneg_left _ hC.le
      gcongr <;> linarith [ht.1, ht.2]
  have ho_ordered : ∀ u v : ℝ, 3 ≤ u → u ≤ v → v ≤ S →
      |Real.log (phiOdd v) - Real.log (phiOdd u)| ≤ C * (1 + S) ^ 3 * (v - u) := by
    intro u v hu huv hv
    apply interval_abs_bound huv
    · intro t _
      exact (phiOdd_continuous.continuousAt.log (ne_of_gt (phiOdd_pos t))).continuousWithinAt
    · intro t ht
      exact ((phiOdd_hasDerivAt (by linarith [ht.1])).differentiableAt.hasDerivAt.log
        (ne_of_gt (phiOdd_pos t)))
    · intro t ht
      have h := ho t (by linarith [ht.1])
      apply le_trans h
      apply mul_le_mul_of_nonneg_left _ hC.le
      gcongr <;> linarith [ht.1, ht.2]
  constructor
  · intro u v hu hv huS hvS
    rcases le_total u v with huv | hvu
    · rw [abs_sub_comm (Real.log (phiEven u)), abs_sub_comm u, abs_of_nonneg (sub_nonneg.mpr huv)]
      exact he_ordered u v hu huv hvS
    · rw [abs_of_nonneg (sub_nonneg.mpr hvu)]
      exact he_ordered v u hv hvu huS
  · have ho_clamped : ∀ u v : ℝ, u ≤ v → v ≤ S →
        |Real.log (phiOdd v) - Real.log (phiOdd u)| ≤ C * (1 + S) ^ 3 * (v - u) := by
      intro u v huv hvS
      have hmax : max 3 u ≤ max 3 v := max_le_max_left 3 huv
      have hdiff : max 3 v - max 3 u ≤ v - u := by
        by_cases hu : u ≤ 3
        · rw [max_eq_left hu]
          by_cases hv : v ≤ 3
          · rw [max_eq_left hv]
            linarith
          · rw [max_eq_right (le_of_not_ge hv)]
            linarith
        · rw [max_eq_right (le_of_not_ge hu), max_eq_right (show 3 ≤ v by linarith)]
      have h := ho_ordered (max 3 u) (max 3 v) (le_max_left _ _) hmax (max_le hS hvS)
      rw [phiOdd_max_three, phiOdd_max_three] at h
      exact le_trans h (mul_le_mul_of_nonneg_left hdiff (by positivity))
    intro u v _ _ huS hvS
    rcases le_total u v with huv | hvu
    · rw [abs_sub_comm (Real.log (phiOdd u)), abs_sub_comm u, abs_of_nonneg (sub_nonneg.mpr huv)]
      exact ho_clamped u v huv hvS
    · rw [abs_of_nonneg (sub_nonneg.mpr hvu)]
      exact ho_clamped v u hvu huS

end NumberTheoryLean.WeightGlobalBounds

end

section

namespace NumberTheoryLean.InverseWeightGrowth
open FinitePathGeometry DerivativeWeights WeightGlobalBounds

private theorem reference_valid (i : Side) : Valid i (reference i) := by
  cases i <;> norm_num [reference,Valid]

private theorem reference_bounds (i : Side) : 0 ≤ reference i ∧ reference i ≤ 3 := by
  cases i <;> norm_num [reference]

theorem inverse_weight_quartic : ∃ A C : ℝ, 0 < A ∧ 0 < C ∧
    ∀ i : Side, ∀ t : ℝ, Valid i t →
      1/weight i t ≤ A*Real.exp (C*(1+t)^4) := by
  obtain ⟨L,hL,hlocal⟩ := weights_log_lipschitz
  let A : ℝ := 1/weight .even 2 + 1/weight .odd 1
  have hE : 0 < 1/weight .even 2 := one_div_pos.mpr (weight_pos (by norm_num [Valid]))
  have hO : 0 < 1/weight .odd 1 := one_div_pos.mpr (weight_pos (by norm_num [Valid]))
  have hA : 0 < A := add_pos hE hO
  refine ⟨A,192*L,hA,by positivity,?_⟩
  intro i t ht
  have ht0 := valid_pos ht
  have hr := reference_valid i
  have hr0 := (reference_bounds i).1
  have hr3 := (reference_bounds i).2
  let S : ℝ := t+3
  have hS : 3 ≤ S := by dsimp [S] <;> linarith
  have htS : t ≤ S := by dsimp [S] <;> linarith
  have hrS : reference i ≤ S := by dsimp [S] <;> linarith
  have hlog : |Real.log (weight i (reference i))-Real.log (weight i t)| ≤
      L*(1+S)^3*|reference i-t| := by
    cases i with
    | even => exact (hlocal S hS).1 _ _ hr ht hrS htS
    | odd => exact (hlocal S hS).2 _ _ hr ht hrS htS
  have hdist : |reference i-t| ≤ 3*(1+t) := by
    calc
      _ ≤ |reference i|+|t| := abs_sub _ _
      _ = reference i+t := by rw [abs_of_nonneg hr0,abs_of_nonneg ht0.le]
      _ ≤ _ := by linarith
  have hSbound : 1+S ≤ 4*(1+t) := by dsimp [S] <;> linarith
  have hmajor : L*(1+S)^3*|reference i-t| ≤ (192*L)*(1+t)^4 := by
    calc
      _ ≤ L*(4*(1+t))^3*(3*(1+t)) := mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hSbound 3) hL.le)
        hdist (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hdifference : Real.log (weight i (reference i))-Real.log (weight i t) ≤
      (192*L)*(1+t)^4 := ((le_abs_self _).trans hlog).trans hmajor
  have hexp := Real.exp_le_exp.mpr hdifference
  rw [Real.exp_sub,Real.exp_log (weight_pos hr),Real.exp_log (weight_pos ht)] at hexp
  have hreference : 1/weight i (reference i) ≤ A := by
    cases i <;> dsimp [reference,A] <;> linarith
  calc
    _ = (1/weight i (reference i))*(weight i (reference i)/weight i t) := by
      field_simp [(weight_pos hr).ne']
    _ ≤ (1/weight i (reference i))*Real.exp ((192*L)*(1+t)^4) :=
      mul_le_mul_of_nonneg_left hexp (one_div_nonneg.mpr (weight_pos hr).le)
    _ ≤ _ := mul_le_mul_of_nonneg_right hreference (Real.exp_pos _).le

theorem inverse_weight_below_cutoff : ∃ A C : ℝ, 0 < A ∧ 0 < C ∧
    ∀ K : ℝ, ∀ i : Side, ∀ t : ℝ, Valid i t → t ≤ K →
      1/weight i t ≤ A*Real.exp (C*(1+K)^4) := by
  obtain ⟨A,C,hA,hC,h⟩ := inverse_weight_quartic
  refine ⟨A,C,hA,hC,?_⟩
  intro K i t ht htK
  have ht0 := valid_pos ht
  exact (h i t ht).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith : 0 ≤ 1+t) (by linarith : 1+t ≤ 1+K) 4) hC.le)) hA.le)

end NumberTheoryLean.InverseWeightGrowth

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_LowStateHorizon
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.LowStateHorizon

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostGrouping
open ArrivalKernelGeometry RegeneratingInverseBands HarmonicWeightKernel

 theorem cost_ge_inv_add_one {t : ℝ} (ht : 0 < t) : 1 / (t + 1) ≤ cost t := by
  have hx : 0 < 1 + 1 / t := by positivity
  have h := Real.one_sub_inv_le_log_of_pos hx
  have heq : 1 - (1 + 1 / t)⁻¹ = 1 / (t + 1) := by
    field_simp [ht.ne', hx.ne', show t + 1 ≠ 0 by linarith]
    ring
  rw [heq] at h
  exact h

theorem source_horizon_log_cube {B : ℝ} (hB : 2 ≤ Real.log B) :
    ((sourceHorizon ((Real.log B) ^ 2) B : ℕ) : ℝ) ≤ 5 * (Real.log B) ^ 3 := by
  let x := Real.log B
  have hx : 2 ≤ x := hB
  have hpos : 0 ≤ (x ^ 2 + 1) * (x + 2) := by positivity
  have hc := (Nat.ceil_lt_add_one hpos).le
  change ((⌈(x ^ 2 + 1) * (x + 2)⌉₊ + 1 : ℕ) : ℝ) ≤ 5 * x ^ 3
  push_cast
  have h2 : 0 ≤ (x - 2) * x := mul_nonneg (by linarith) (by linarith)
  have h3 : 0 ≤ (x - 2) * x ^ 2 := mul_nonneg (by linarith) (sq_nonneg x)
  nlinarith

end NumberTheoryLean.LowStateHorizon

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeRatioBins
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSingletonClassChainState _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.PrimeTiltPrefixes

open _root_.Erdos970.Set
open FinitePathGeometry PrimeTiltGeometry ErdosPrimeInputs.HarmonicPrimeMeasure
open ErdosPrimeInputs.PrimePrefixMass

theorem ratios_admissible {w ell S s r cap : ℝ} {i : Side} {closed : Bool} {ps : List ℕ}
    (hpath : PrimeAdmissible w ell S i s r cap closed ps) : Admissible i s (primeRatios w r ps) := by
  classical
  induction ps generalizing i s r cap closed with
  | nil => trivial
  | cons p ps ih =>
    rcases hpath with ⟨hp,hps⟩
    exact ⟨(Finset.mem_filter.mp hp).2.2.2.1, ih hps⟩

theorem primeFinalGap_eq {w ell S s r cap : ℝ} {i : Side} {closed : Bool} {ps : List ℕ}
    (hell : 0 ≤ ell) (hr : 0 < r) (hs : Valid i s)
    (hpath : PrimeAdmissible w ell S i s r cap closed ps) :
    primeFinalGap w r ps = finalGap r (primeRatios w r ps) := by
  induction ps generalizing i s r cap closed with
  | nil => rfl
  | cons p ps ih =>
    rcases hpath with ⟨hp,hps⟩
    simp only [primeFinalGap, primeRatios, finalGap]
    rw [nextGap_childRatio hr (child_exponent_positive hell hp) (valid_pos (child_valid hs hp))]
    exact ih (child_gap_positive hell hr hs hp) (child_valid hs hp) hps

end NumberTheoryLean.PrimeTiltPrefixes

end

section

namespace NumberTheoryLean.PrimeHistories

open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open FinitePathGeometry PrimeTiltGeometry PrimeTiltPrefixes
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem terminal_append (w : ℝ) (z : Node) (ps qs : List ℕ) :
    terminal w z (ps++qs) = terminal w (terminal w z ps) qs := by
  exact List.foldl_append

namespace History

variable {w ell S : ℝ} {start : Node}

theorem append_node (h : History w ell S start) (p : ℕ) (hp : p ∈ nodeChildren w ell S h.node) :
    (h.append p hp).node = step w h.node p := by
  change terminal w start (h.primes ++ [p]) = _
  rw [terminal_append, terminal_cons, terminal_nil]
  rfl

end History
end NumberTheoryLean.PrimeHistories

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeGridGeometry
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.OAI.Erdos970.NumberTheoryLean.ReferenceBenchmarkDecay.benchmark_even_below_two
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace NumberTheoryLean.PrimeKilledChain

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry PrimeTiltGeometry PrimeHistories PrimeRowNormalization

 theorem normalizationRate_pos : 0 < normalizationRate :=
  (Classical.choose_spec (Classical.choose_spec retained_row_mass_one_add)).1

end NumberTheoryLean.PrimeKilledChain



namespace NumberTheoryLean.PrimeCompactVisits

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeTiltGeometry

variable {w ell S : ℝ} {start : Node}

theorem visit_nonneg (K : ℝ) (z : ChainState w ell S start) : 0 ≤ visit K z := by
  cases z with
  | none => exact le_rfl
  | some h => simp only [visit]; split_ifs <;> norm_num

theorem potential_nonneg {K : ℝ} (hK : 0 ≤ K) (hell : 0 ≤ ell)
    (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (z : ChainState w ell S start) :
    0 ≤ potential K z := by
  cases z with
  | none => exact le_rfl
  | some h =>
    have hg : 0 < h.node.gap := terminal_gap_positive hell hr hs h.admissible
    exact add_nonneg (le_min hg.le hK) zero_le_one

theorem potential_le {K : ℝ} (hK : 0 ≤ K) (z : ChainState w ell S start) :
    potential K z ≤ K+1 := by
  cases z with
  | none => change (0:ℝ) ≤ K+1; linarith
  | some h => exact add_le_add_left (min_le_right _ _) 1

theorem visit_le_potential {K : ℝ} (hK : 0 ≤ K) (hell : 0 ≤ ell)
    (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (z : ChainState w ell S start) :
    visit K z ≤ potential K z := by
  cases z with
  | none => exact le_rfl
  | some h =>
    have hg : 0 < h.node.gap := terminal_gap_positive hell hr hs h.admissible
    simp only [visit,potential]
    split_ifs with hle
    · rw [min_eq_left hle]; linarith
    · exact add_nonneg (le_min hg.le hK) zero_le_one

theorem child_potential_drift {K : ℝ} (hell : 1 ≤ ell)
    (h : History w ell S start) (p : ℕ) (hp : p ∈ nodeChildren w ell S h.node) :
    visit K (some h) + potential K (some (h.append p hp)) ≤ potential K (some h) := by
  classical
  have he : ell < ErdosPrimeInputs.HarmonicPrimeMeasure.primeExponent w p :=
    (Finset.mem_filter.mp hp).2.1
  simp only [visit,potential,History.append_node,step]
  split_ifs with hle
  · rw [min_eq_left hle]
    have hm := min_le_left (h.node.gap-ErdosPrimeInputs.HarmonicPrimeMeasure.primeExponent w p) K
    linarith
  · rw [min_eq_right (le_of_not_ge hle)]
    have hm := min_le_right (h.node.gap-ErdosPrimeInputs.HarmonicPrimeMeasure.primeExponent w p) K
    linarith

variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell)
    (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
    (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

include hell hr hs in

theorem actual_row_drift_ae {K : ℝ} (hK : 0 ≤ K) (z : ChainState w ell S start) :
    ∀ᵐ y ∂chain w ell S start z, visit K z + potential K y ≤ potential K z := by
  classical
  cases z with
  | none =>
    rw [chain_none]
    exact (ae_dirac_iff (by trivial)).mpr (by simp [visit,potential])
  | some h =>
    have hdead : visit K (some h) + potential K (none : ChainState w ell S start) ≤ potential K (some h) := by
      simpa only [potential,add_zero] using visit_le_potential hK (by linarith : 0 ≤ ell) hr hs (some h)
    have hchild := child_potential_drift (K := K) hell h
    apply ae_iff.mpr
    simp [chain_some,completedLaw,liveLaw,hdead,hchild]

include hw hell hS0 hS hr hs hsS

theorem actual_row_drift {K : ℝ} (hK : 0 ≤ K) (z : ChainState w ell S start) :
    ENNReal.ofReal (visit K z) + (∫⁻ y, ENNReal.ofReal (potential K y) ∂chain w ell S start z) ≤
      ENNReal.ofReal (potential K z) := by
  let := chain_isMarkov hw hell hS0 hS hr hs hsS
  have hp := actual_row_drift_ae hell hr hs hK z
  have hnon := potential_nonneg (w := w) (S := S) hK (by linarith : 0 ≤ ell) hr hs
  calc
    _ = ∫⁻ y, ENNReal.ofReal (visit K z) + ENNReal.ofReal (potential K y) ∂chain w ell S start z := by
      rw [lintegral_add_left measurable_const,lintegral_const,measure_univ,mul_one]
    _ ≤ ∫⁻ _y, ENNReal.ofReal (potential K z) ∂chain w ell S start z := by
      apply lintegral_mono_ae
      filter_upwards [hp] with y hy
      rw [← ENNReal.ofReal_add (visit_nonneg K z) (hnon y)]
      exact ENNReal.ofReal_le_ofReal hy
    _ = _ := by rw [lintegral_const,measure_univ,mul_one]

end NumberTheoryLean.PrimeCompactVisits



namespace NumberTheoryLean.PrimeHistoryHorizon

open _root_.Set _root_.Finset
open _root_.Erdos970.Set
open FinitePathGeometry PrimeTiltGeometry PrimeTiltPrefixes PrimeHistories
open LowStateHorizon ErdosPrimeInputs.HarmonicPrimeMeasure

theorem valid_ratio_lower {i : Side} {t : ℝ} (ht : Valid i t) : (19/20 : ℝ) ≤ t := by
  cases i <;> dsimp [Valid] at ht <;> linarith

theorem prime_cost_lower {w ell S s r cap : ℝ} {i : Side} {closed : Bool} {ps : List ℕ}
    (hs : Valid i s) (hpath : PrimeAdmissible w ell S i s r cap closed ps) :
    (ps.length : ℝ)/(S+1) ≤ pathCost (primeRatios w r ps) := by
  classical
  induction ps generalizing i s r cap closed with
  | nil => simp [primeRatios,pathCost]
  | cons p ps ih =>
    rcases hpath with ⟨hp,hrest⟩
    have ht := valid_pos (child_valid hs hp)
    have htS : childRatio w r p ≤ S := (Finset.mem_filter.mp hp).2.2.2.2
    have hc : 1/(S+1) ≤ cost (childRatio w r p) :=
      (one_div_le_one_div_of_le (by linarith : 0 < childRatio w r p+1) (by linarith)).trans
        (cost_ge_inv_add_one ht)
    have hih := ih (child_valid hs hp) hrest
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, add_div, primeRatios, pathCost]
    linarith

theorem prime_gap_cost {w ell S s r cap : ℝ} {i : Side} {closed : Bool} {ps : List ℕ}
    (hell : 0 ≤ ell) (hr : 0 < r) (hs : Valid i s)
    (hpath : PrimeAdmissible w ell S i s r cap closed ps) :
    primeFinalGap w r ps = r * Real.exp (-pathCost (primeRatios w r ps)) := by
  rw [primeFinalGap_eq hell hr hs hpath, finalGap_eq_cost hs (ratios_admissible hpath)]

theorem prime_final_gap_lower {w ell S s r cap : ℝ} {i : Side} {closed : Bool} {ps : List ℕ}
    (hell : 0 < ell) (hr : 0 < r) (hs : Valid i s)
    (hpath : PrimeAdmissible w ell S i s r cap closed ps) (hne : ps ≠ []) :
    (19/20 : ℝ)*ell < primeFinalGap w r ps := by
  classical
  induction ps generalizing i s r cap closed with
  | nil => exact False.elim (hne rfl)
  | cons p ps ih =>
    rcases hpath with ⟨hp,hrest⟩
    cases ps with
    | nil =>
      have hx : ell < primeExponent w p := (Finset.mem_filter.mp hp).2.1
      have hx0 : 0 < primeExponent w p := hell.trans hx
      have ht := valid_ratio_lower (child_valid hs hp)
      have heq : r-primeExponent w p = childRatio w r p * primeExponent w p := by
        unfold childRatio
        field_simp
      change (19/20 : ℝ)*ell < r-primeExponent w p
      calc
        _ < (19/20 : ℝ)*primeExponent w p := mul_lt_mul_of_pos_left hx (by norm_num)
        _ ≤ childRatio w r p * primeExponent w p := mul_le_mul_of_nonneg_right ht hx0.le
        _ = _ := heq.symm
    | cons q qs =>
      exact ih (child_gap_positive hell.le hr hs hp) (child_valid hs hp) hrest (by simp)

theorem prime_source_horizon {w ell S s r cap B : ℝ} {i : Side} {closed : Bool} {ps : List ℕ}
    (hell : 1 ≤ ell) (hS : 0 ≤ S) (hr : 0 < r) (hs : Valid i s)
    (hpath : PrimeAdmissible w ell S i s r cap closed ps) (hB : 0 < B) (hsize : r ≤ (23/10 : ℝ)*B) :
    ps.length < sourceHorizon S B := by
  by_cases hne : ps = []
  · subst ps
    unfold sourceHorizon
    simp
  · have hell0 : 0 < ell := by linarith
    have hgap := prime_final_gap_lower hell0 hr hs hpath hne
    have hl := Real.log_lt_log (mul_pos (by norm_num : (0 : ℝ) < 19/20) hell0) hgap
    rw [prime_gap_cost hell0.le hr hs hpath,
      Real.log_mul hr.ne' (Real.exp_pos _).ne', Real.log_exp] at hl
    have hc := prime_cost_lower hs hpath
    have hlogR := Real.log_le_log hr hsize
    rw [Real.log_mul (by norm_num : (23/10 : ℝ) ≠ 0) hB.ne'] at hlogR
    have hlog23 : Real.log (23/10 : ℝ) ≤ 13/10 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 23/10)
      norm_num at h
      exact h
    have hlog19 : (-1/19 : ℝ) ≤ Real.log (19/20 : ℝ) := by
      have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 19/20)
      norm_num at h
      linarith
    have hlogell : Real.log (19/20 : ℝ) ≤ Real.log ((19/20 : ℝ)*ell) :=
      Real.log_le_log (by norm_num) (by nlinarith)
    have hn : (ps.length : ℝ)/(S+1) < Real.log B+2 := by linarith
    have hmul := (div_lt_iff₀ (by linarith : 0 < S+1)).mp hn
    have hceil := Nat.le_ceil ((S+1)*(Real.log B+2))
    have hreal : (ps.length : ℝ) < (sourceHorizon S B : ℝ) := by
      unfold sourceHorizon
      push_cast
      nlinarith
    exact_mod_cast hreal

theorem history_length_lt {w ell S B : ℝ} {start : Node}
    (hell : 1 ≤ ell) (hS : 0 ≤ S) (hr : 0 < start.gap) (hs : Valid start.side start.ratio)
    (hB : 0 < B) (hsize : start.gap ≤ (23/10 : ℝ)*B) (h : History w ell S start) :
    h.primes.length < sourceHorizon S B :=
  prime_source_horizon hell hS hr hs h.admissible hB hsize

end NumberTheoryLean.PrimeHistoryHorizon



namespace NumberTheoryLean.PrimeCorrectionFactor

open _root_.Filter _root_.Set
open _root_.Erdos970.Filter _root_.Erdos970.Set
open scoped Topology
open FinitePathGeometry PrimeHistories PrimeHistoryHorizon PrimeKilledChain LowStateHorizon

theorem correctionBudget_tendsto_zero (d : ℝ) : Tendsto (correctionBudget d) atTop (𝓝 0) := by
  have ht : Tendsto (fun x : ℝ => 5*d^3*x^6*Real.exp (-normalizationRate*x)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (6 : ℝ) normalizationRate normalizationRate_pos).const_mul (5*d^3)
    simpa only [Real.rpow_ofNat, mul_assoc, mul_zero] using h
  have hi : Tendsto (fun w : ℝ => 5*d^3*(Real.log w)^3*epsilon w) atTop (𝓝 0) := by
    apply Tendsto.congr' _ (ht.comp (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop))
    filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (0 : ℝ))] with w hw
    have hp : (Real.sqrt (Real.log w))^6 = (Real.log w)^3 := by
      calc
        _ = ((Real.sqrt (Real.log w))^2)^3 := by ring
        _ = _ := by rw [Real.sq_sqrt hw]
    simp only [Function.comp_apply, epsilon, hp]
  have h := ((Real.continuous_exp.tendsto (0 : ℝ)).comp hi).sub_const 1
  change Tendsto (fun w : ℝ => Real.exp (5*d^3*(Real.log w)^3*epsilon w)-1) atTop (𝓝 0)
  simpa only [Function.comp_apply, Real.exp_zero, sub_self] using h

theorem correction_le_budget {d w B : ℝ} (hB : 2 ≤ Real.log B) (hcomp : Real.log B ≤ d*Real.log w) (n : ℕ)
    (hn : n ≤ sourceHorizon ((Real.log B)^2) B) :
    0 ≤ (1+epsilon w)^n-1 ∧ (1+epsilon w)^n-1 ≤ correctionBudget d w := by
  have hpow1 : 1 ≤ (1+epsilon w)^n := one_le_pow₀ (by linarith [epsilon_pos w])
  have hN := source_horizon_log_cube hB
  have hnR : (n : ℝ) ≤ (sourceHorizon ((Real.log B)^2) B : ℝ) := by exact_mod_cast hn
  have hcube : (Real.log B)^3 ≤ (d*Real.log w)^3 := pow_le_pow_left₀ (by linarith) hcomp 3
  have hnum : (n : ℝ) ≤ 5*d^3*(Real.log w)^3 := by nlinarith [hN,hnR]
  have hbase : 1+epsilon w ≤ Real.exp (epsilon w) := by
    simpa only [add_comm] using Real.add_one_le_exp (epsilon w)
  have hp : (1+epsilon w)^n ≤ (Real.exp (epsilon w))^n := pow_le_pow_left₀ (by linarith [epsilon_pos w]) hbase n
  rw [← Real.exp_nat_mul] at hp
  have he : Real.exp ((n : ℝ)*epsilon w) ≤ Real.exp (5*d^3*(Real.log w)^3*epsilon w) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hnum (epsilon_pos w).le)
  exact ⟨sub_nonneg.mpr hpow1, sub_le_sub_right (hp.trans he) 1⟩

theorem history_correction {d w ell B : ℝ} {start : Node}
    (hlogB : 2 ≤ Real.log B)
    (hcomp : Real.log B ≤ d*Real.log w) (hell : 1 ≤ ell) (hr : 0 < start.gap)
    (hs : Valid start.side start.ratio) (hB : 0 < B) (hsize : start.gap ≤ (23/10 : ℝ)*B)
    (h : History w ell ((Real.log B)^2) start) :
    0 ≤ (1+epsilon w)^h.primes.length-1 ∧
      (1+epsilon w)^h.primes.length-1 ≤ correctionBudget d w :=
  correction_le_budget hlogB hcomp h.primes.length
    (history_length_lt hell (sq_nonneg _) hr hs hB hsize h).le

end NumberTheoryLean.PrimeCorrectionFactor



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_CemeteryHistoryLaw
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.CemeteryKernel

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

theorem complete_isMarkov (K : Kernel α α) (hK : ∀ x, K x univ ≤ 1) : IsMarkovKernel (complete K) := by
  constructor
  intro z
  constructor
  cases z with
  | inl x =>
    rw [complete_live, liveRow_apply, Measure.add_apply, Measure.map_apply measurable_inl MeasurableSet.univ,
      Set.preimage_univ, Measure.smul_apply]
    simp only [measure_univ, smul_eq_mul, mul_one]
    exact add_tsub_cancel_of_le (hK x)
  | inr u =>
    cases u
    change Measure.dirac (dead : Space α) univ = 1
    exact measure_univ

end NumberTheoryLean.CemeteryKernel

end

section

namespace NumberTheoryLean.CemeteryHistoryMap

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open CemeteryKernel FiniteHistoryTransport

variable {X : Type*} [MeasurableSpace X]
variable (K : Kernel X X) [IsMarkovKernel K] {E : Set X} (hE : MeasurableSet E)

instance restricted_complete_markov : IsMarkovKernel (complete (K.restrict hE)) := by
  apply complete_isMarkov
  intro x
  rw [Kernel.restrict_apply,Measure.restrict_apply_univ]
  exact (measure_mono (subset_univ E)).trans_eq (measure_univ (μ := K x))

end NumberTheoryLean.CemeteryHistoryMap

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_CompletedParentInterval
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ContinuousKilledBins

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PairedCostGrouping ArrivalKernelGeometry
open LowStateHorizon RegeneratingInverseBands KernelDensityBridge ContinuousRatioBins

instance continuousChain_isMarkov (v ell S : ℝ) : IsMarkovKernel (continuousChain v ell S) := by
  apply CemeteryKernel.complete_isMarkov
  intro z
  rw [lowKernel, Kernel.restrict_apply, Measure.restrict_apply_univ]
  calc
    _ ≤ costKernel z univ := measure_mono (subset_univ _)
    _ = 1 := measure_univ

end NumberTheoryLean.ContinuousKilledBins

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeCompactWeights
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.PrimeBinMembership

open _root_.Set _root_.Finset
open FinitePathGeometry PrimeTiltGeometry PrimeTiltPrefixes PrimeHistories
open PrimeRatioBins NormalizedPrimeBins PrimeKilledChain
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem step_consistent {w ell S : ℝ} {z : Node} {p : ℕ} (hell : 0 ≤ ell)
    (hr : 0 < z.gap) (hs : Valid z.side z.ratio) (hp : p ∈ nodeChildren w ell S z) :
    Consistent (step w z p) := by
  have hx := child_exponent_positive hell hp
  have ht := valid_pos (child_valid hs hp)
  change primeExponent w p = (z.gap-primeExponent w p)/childRatio w z.gap p
  rw [← nextGap_childRatio hr hx ht, nextGap_div_ratio ht, nextExponent_childRatio hr hx]

theorem terminal_consistent {w ell S : ℝ} {z : Node} {ps : List ℕ} (hell : 0 ≤ ell)
    (hr : 0 < z.gap) (hs : Valid z.side z.ratio) (hz : Consistent z) (hp : allowed w ell S z ps) :
    Consistent (terminal w z ps) := by
  induction ps generalizing z with
  | nil => exact hz
  | cons p ps ih =>
    rcases (allowed_cons w ell S z p ps).mp hp with ⟨hc,ht⟩
    exact ih (child_gap_positive hell hr hs hc) (child_valid hs hc) (step_consistent hell hr hs hc) ht

theorem history_consistent {w ell S : ℝ} {start : Node} (hell : 0 ≤ ell)
    (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hc : Consistent start)
    (h : History w ell S start) : Consistent h.node :=
  terminal_consistent hell hr hs hc h.admissible

end NumberTheoryLean.PrimeBinMembership

end

section

namespace NumberTheoryLean.PrimeCompactWeights

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeCompactVisits
open PrimeCorrectionFactor PrimeBinMembership PrimeTiltGeometry DerivativeWeights

theorem terminal_cutoff_lower {w ell S : ℝ} {start : Node} {ps : List ℕ}
    (hc : ell ≤ start.cutoff) (hp : allowed w ell S start ps) : ell ≤ (terminal w start ps).cutoff := by
  classical
  induction ps generalizing start with
  | nil => exact hc
  | cons p ps ih =>
    obtain ⟨hchild,htail⟩ := (allowed_cons w ell S start p ps).mp hp
    have hlo : ell < ErdosPrimeInputs.HarmonicPrimeMeasure.primeExponent w p :=
      (Finset.mem_filter.mp hchild).2.1
    exact ih hlo.le htail

theorem history_ratio_le_gap {w ell S : ℝ} {start : Node}
    (hell : 1 ≤ ell) (hr : 0 < start.gap) (hs : Valid start.side start.ratio)
    (hc : Consistent start) (hcut : ell ≤ start.cutoff) (h : History w ell S start) :
    h.node.ratio ≤ h.node.gap := by
  have hv : 0 < h.node.ratio := valid_pos (terminal_valid hs h.admissible)
  have hn : Consistent h.node := history_consistent (by linarith) hr hs hc h
  have hlow : ell ≤ h.node.cutoff := terminal_cutoff_lower hcut h.admissible
  change h.node.cutoff = h.node.gap/h.node.ratio at hn
  have he := (eq_div_iff hv.ne').mp hn
  nlinarith

end NumberTheoryLean.PrimeCompactWeights

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_ActualCouplingUpdates
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Finset
open scoped BigOperators
namespace Erdos970Dependency.MaximalCoupling

variable {ι : Type*} [Fintype ι]
attribute [local instance] Classical.propDecidable

omit [Fintype ι] in
theorem common_nonneg {a b : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (i : ι) :
    0 ≤ common a b i := le_min (ha i) (hb i)

omit [Fintype ι] in
theorem leftRemainder_nonneg (a b : ι → ℝ) (i : ι) : 0 ≤ leftRemainder a b i :=
  sub_nonneg.mpr (min_le_left _ _)
omit [Fintype ι] in
theorem rightRemainder_nonneg (a b : ι → ℝ) (i : ι) : 0 ≤ rightRemainder a b i :=
  sub_nonneg.mpr (min_le_right _ _)

theorem sum_leftRemainder {a b : ι → ℝ} (ha : ∑ i, a i = 1) :
    ∑ i, leftRemainder a b i = residual a b := by simp only [leftRemainder, sum_sub_distrib, ha, residual]
theorem sum_rightRemainder {a b : ι → ℝ} (hb : ∑ i, b i = 1) :
    ∑ i, rightRemainder a b i = residual a b := by simp only [rightRemainder, sum_sub_distrib, hb, residual]

theorem residual_nonneg {a b : ι → ℝ} (ha : ∑ i, a i = 1) : 0 ≤ residual a b := by
  rw [← sum_leftRemainder ha]
  exact sum_nonneg (fun i _ => leftRemainder_nonneg a b i)

theorem leftRemainder_zero {a b : ι → ℝ} (ha : ∑ i, a i = 1) (hr : residual a b = 0) (i : ι) :
    leftRemainder a b i = 0 := by
  have h := single_le_sum (fun j _ => leftRemainder_nonneg a b j) (mem_univ i)
  rw [sum_leftRemainder ha, hr] at h
  exact le_antisymm h (leftRemainder_nonneg a b i)

theorem matrix_nonneg {a b : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hsa : ∑ i, a i = 1) (i j : ι) : 0 ≤ matrix a b i j := by
  unfold matrix
  apply add_nonneg
  · split_ifs <;> first | exact common_nonneg ha hb i | exact le_rfl
  · split_ifs
    · exact le_rfl
    · exact div_nonneg (mul_nonneg (leftRemainder_nonneg a b i) (rightRemainder_nonneg a b j)) (residual_nonneg hsa)

theorem row_sum {a b : ι → ℝ} (ha : ∑ i, a i = 1) (hb : ∑ i, b i = 1) (i : ι) :
    ∑ j, matrix a b i j = a i := by
  classical
  by_cases hr : residual a b = 0
  · have hz := leftRemainder_zero ha hr i
    simp only [matrix, ite_eq_left hr, add_zero]
    simp only [sum_ite_eq, mem_univ, ite_true, if_true]
    unfold leftRemainder at hz
    linarith
  · simp only [matrix, ite_eq_right hr, sum_add_distrib]
    rw [sum_ite_eq]
    simp only [mem_univ, ite_true, if_true]
    rw [← sum_div, ← mul_sum, sum_rightRemainder hb]
    rw [mul_div_cancel_right₀ _ hr]
    unfold leftRemainder
    ring

end Erdos970Dependency.MaximalCoupling

end

section

namespace NumberTheoryLean.KernelBinConditioning

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]

theorem conditional_apply (K : Kernel α β) {B : Set β} (hB : MeasurableSet B) (default : β) (x : α) :
    conditional K hB default x = if K x B = 0 then Measure.dirac default else (K x B)⁻¹ • (K x).restrict B := rfl

instance conditional_isMarkov (K : Kernel α β) [IsMarkovKernel K] {B : Set β}
    (hB : MeasurableSet B) (default : β) : IsMarkovKernel (conditional K hB default) := by
  constructor
  intro x
  constructor
  classical
  rw [conditional_apply]
  by_cases hx : K x B = 0
  · rw [ite_eq_left hx]
    exact measure_univ
  · rw [ite_eq_right hx, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel hx (measure_ne_top _ _)

theorem weighted_conditional (K : Kernel α β) [IsMarkovKernel K] {B : Set β}
    (hB : MeasurableSet B) (default : β) (x : α) :
    (K x B) • conditional K hB default x = (K x).restrict B := by
  classical
  rw [conditional_apply]
  by_cases hx : K x B = 0
  · rw [ite_eq_left hx, hx, zero_smul]
    exact (Measure.restrict_eq_zero.mpr hx).symm
  · rw [ite_eq_right hx, smul_smul, ENNReal.mul_inv_cancel hx (measure_ne_top _ _), one_smul]

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem labelMass_measurable (K : Kernel α β) {label : β → ι} (hl : Measurable label) (i : ι) :
    Measurable (fun x => labelMass K label x i) :=
  ENNReal.measurable_toReal.comp (K.measurable_coe (hl (measurableSet_singleton i)))

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
theorem labelMass_nonneg (K : Kernel α β) (label : β → ι) (x : α) (i : ι) :
    0 ≤ labelMass K label x i := ENNReal.toReal_nonneg

variable [Fintype ι]

theorem labelMass_sum (K : Kernel α β) [IsMarkovKernel K] {label : β → ι}
    (hl : Measurable label) (x : α) : ∑ i, labelMass K label x i = 1 := by
  have h := sum_measure_preimage_singleton (μ := K x) (Finset.univ : Finset ι)
    (fun i _ => hl (measurableSet_singleton i))
  simp only [Finset.coe_univ, Set.preimage_univ, measure_univ] at h
  have hr := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _), ENNReal.toReal_one] at hr
  exact hr

theorem conditional_mixture (K : Kernel α β) [IsMarkovKernel K] {label : β → ι}
    (hl : Measurable label) (default : β) (x : α) :
    (∑ i, (K x (label ⁻¹' {i})) • conditional K (hl (measurableSet_singleton i)) default x) = K x := by
  simp_rw [weighted_conditional]
  apply Measure.ext
  intro B hB
  rw [Measure.finsetSum_apply]
  simp_rw [Measure.restrict_apply hB]
  have h := sum_measure_preimage_singleton (μ := (K x).restrict B) (Finset.univ : Finset ι)
    (fun i _ => hl (measurableSet_singleton i))
  simp only [Finset.coe_univ, Set.preimage_univ, Measure.restrict_apply_univ] at h
  have heq : ∀ i : ι, (K x).restrict B (label ⁻¹' {i}) = K x (B ∩ label ⁻¹' {i}) := by
    intro i
    rw [Measure.restrict_apply (hl (measurableSet_singleton i)), Set.inter_comm]
  simp_rw [heq] at h
  exact h

end NumberTheoryLean.KernelBinConditioning

end

section

namespace NumberTheoryLean.KernelCouplingWeights

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open KernelBinConditioning Erdos970Dependency.MaximalCoupling
attribute [local instance] Classical.propDecidable

variable {α β γ ι : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem weight_measurable (K : Kernel α β) (L : Kernel α γ) {f : β → ι} {g : γ → ι}
    (hf : Measurable f) (hg : Measurable g) (i j : ι) : Measurable (fun x => weight K L f g x i j) := by
  classical
  have ha := labelMass_measurable K hf
  have hb := labelMass_measurable L hg
  have hc (i : ι) : Measurable (fun x => common (labelMass K f x) (labelMass L g x) i) := (ha i).min (hb i)
  have hr : Measurable (fun x => residual (labelMass K f x) (labelMass L g x)) :=
    measurable_const.sub (Finset.measurable_sum univ (fun i _ => hc i))
  have hl : Measurable (fun x => leftRemainder (labelMass K f x) (labelMass L g x) i) := (ha i).sub (hc i)
  have hh : Measurable (fun x => rightRemainder (labelMass K f x) (labelMass L g x) j) := (hb j).sub (hc j)
  have hd : Measurable (fun x => if i = j then common (labelMass K f x) (labelMass L g x) i else 0) := by
    by_cases hij : i = j
    · simpa only [ite_eq_left hij] using hc i
    · simp only [ite_eq_right hij]
      exact measurable_const
  exact hd.add (Measurable.ite (measurableSet_eq_fun hr measurable_const) measurable_const ((hl.mul hh).div hr))

theorem weight_joint_measurable (K : Kernel α β) (L : Kernel α γ) {f : β → ι} {g : γ → ι}
    (hf : Measurable f) (hg : Measurable g) (i j : ι) :
    Measurable (Function.uncurry (fun (x : α) (_ : β × γ) => ENNReal.ofReal (weight K L f g x i j))) :=
  (ENNReal.measurable_ofReal.comp (weight_measurable K L hf hg i j)).comp measurable_fst

variable (K : Kernel α β) (L : Kernel α γ) [IsMarkovKernel K] [IsMarkovKernel L]
variable {f : β → ι} {g : γ → ι} (hf : Measurable f) (hg : Measurable g)
include hf hg

omit hg [IsMarkovKernel L] in
theorem weight_nonnegative (x : α) (i j : ι) : 0 ≤ weight K L f g x i j :=
  matrix_nonneg (labelMass_nonneg K f x) (labelMass_nonneg L g x) (labelMass_sum K hf x) i j

theorem weight_row (x : α) (i : ι) : ∑ j, weight K L f g x i j = labelMass K f x i :=
  row_sum (labelMass_sum K hf x) (labelMass_sum L hg x) i

theorem weight_row_ofReal (x : α) (i : ι) :
    ∑ j, ENNReal.ofReal (weight K L f g x i j) = K x (f ⁻¹' {i}) := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => weight_nonnegative K L (g := g) hf x i j), weight_row K L hf hg]
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

theorem weight_total_ofReal (x : α) : ∑ i, ∑ j, ENNReal.ofReal (weight K L f g x i j) = 1 := by
  simp_rw [weight_row_ofReal K L hf hg]
  have h := sum_measure_preimage_singleton (μ := K x) (Finset.univ : Finset ι)
    (fun i _ => hf (measurableSet_singleton i))
  simpa only [Finset.coe_univ, Set.preimage_univ, measure_univ] using h

end NumberTheoryLean.KernelCouplingWeights

end

section

namespace NumberTheoryLean.KernelCouplingLift

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open KernelBinConditioning KernelCouplingWeights

variable {α β γ ι : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
variable (K : Kernel α β) (L : Kernel α γ) [IsMarkovKernel K] [IsMarkovKernel L]
variable {f : β → ι} {g : γ → ι} (hf : Measurable f) (hg : Measurable g) (dβ : β) (dγ : γ)

theorem component_apply (i j : ι) (x : α) :
    component K L hf hg dβ dγ i j x = ENNReal.ofReal (weight K L f g x i j) •
      (conditional K (hf (measurableSet_singleton i)) dβ x).prod
        (conditional L (hg (measurableSet_singleton j)) dγ x) := by
  rw [component, Kernel.withDensity_apply _ (weight_joint_measurable K L hf hg i j) x,
    Kernel.prod_apply, withDensity_const]

theorem coupled_apply_set (x : α) {B : Set (β × γ)} (hB : MeasurableSet B) :
    coupled K L hf hg dβ dγ x B = ∑ i, ∑ j, ENNReal.ofReal (weight K L f g x i j) *
      ((conditional K (hf (measurableSet_singleton i)) dβ x).prod
        (conditional L (hg (measurableSet_singleton j)) dγ x)) B := by
  rw [coupled, Kernel.sum_apply' _ _ hB, tsum_fintype, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [component_apply, Measure.smul_apply, smul_eq_mul]

instance coupled_isMarkov : IsMarkovKernel (coupled K L hf hg dβ dγ) := by
  constructor
  intro x
  constructor
  rw [coupled_apply_set K L hf hg dβ dγ x MeasurableSet.univ]
  simp only [measure_univ, mul_one]
  exact weight_total_ofReal K L hf hg x

theorem coupled_map_fst (x : α) :
    (coupled K L hf hg dβ dγ x).map Prod.fst = K x := by
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply measurable_fst hB, coupled_apply_set K L hf hg dβ dγ x (measurable_fst hB)]
  have hpre : (Prod.fst ⁻¹' B : Set (β × γ)) = B ×ˢ univ := by ext p; simp
  rw [hpre]
  simp only [Measure.prod_prod, measure_univ, mul_one]
  simp_rw [← Finset.sum_mul, weight_row_ofReal K L hf hg]
  have h := congrArg (fun μ : Measure β => μ B) (conditional_mixture K hf dβ x)
  simpa only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul] using h

end NumberTheoryLean.KernelCouplingLift

end

section

namespace NumberTheoryLean.ActualProcessCoupling

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ContinuousKilledBins MeshRatioLabels KernelCouplingLift KernelBinConditioning

instance continuousParent_isMarkov (w ell S : ℝ) (start : Node) (v : ℝ) :
    IsMarkovKernel (continuousParent w ell S start v) := by unfold continuousParent; infer_instance

variable {w ell S : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
variable (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

instance jointKernel_isMarkov (v mesh : ℝ) : IsMarkovKernel (jointKernel hw hell hS0 hS hr hs hsS v mesh) := by
  let := chain_isMarkov hw hell hS0 hS hr hs hsS
  unfold jointKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem jointKernel_left (v mesh : ℝ) (p : ChainState w ell S start) (z : CemeteryKernel.Space CostState) :
    (jointKernel hw hell hS0 hS hr hs hsS v mesh (p,z)).map Prod.fst = chain w ell S start p := by
  let := chain_isMarkov hw hell hS0 hS hr hs hsS
  exact coupled_map_fst (primeParent w ell S start) (continuousParent w ell S start v)
    (primeLabel_measurable w ell S mesh start) (continuousLabel_measurable S mesh)
    none CemeteryKernel.dead (p,z)

end NumberTheoryLean.ActualProcessCoupling

end

section

namespace NumberTheoryLean.ActualCouplingFinite

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ContinuousKilledBins PrimeChainHorizon LowStateHorizon

section Generic
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable (K : Kernel α α) (L : Kernel β β)
variable {f : α → β} (hf : Measurable f)

include hf

theorem map_power_of_step (hstep : ∀ x, (K x).map f = L (f x)) (n : ℕ) (x : α) :
    ((K^n) x).map f = (L^n) (f x) := by
  let P : Kernel α β := Kernel.deterministic f hf
  have hinter : P ∘ₖ K = L ∘ₖ P := by
    rw [show P = Kernel.deterministic f hf from rfl, Kernel.deterministic_comp_eq_map,
      Kernel.comp_deterministic_eq_comap]
    ext x : 1
    rw [Kernel.map_apply _ hf,Kernel.comap_apply]
    exact hstep x
  have hpow : ∀ n, P ∘ₖ (K^n) = (L^n) ∘ₖ P := by
    intro n
    induction n with
    | zero =>
      change P ∘ₖ (Kernel.id : Kernel α α) = Kernel.id ∘ₖ P
      rw [Kernel.comp_id,Kernel.id_comp]
    | succ n ih =>
      have hp : K^(n+1) = (K^n) ∘ₖ K := pow_succ _ _
      have hq : L^(n+1) = (L^n) ∘ₖ L := pow_succ _ _
      rw [hp,hq,← Kernel.comp_assoc,ih,Kernel.comp_assoc,hinter,← Kernel.comp_assoc]
  have h := hpow n
  rw [show P = Kernel.deterministic f hf from rfl,Kernel.deterministic_comp_eq_map,
    Kernel.comp_deterministic_eq_comap] at h
  have hx := congrArg (fun M : Kernel α β => M x) h
  rwa [Kernel.map_apply _ hf,Kernel.comap_apply] at hx
end Generic

variable {w ell S : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
variable (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

instance jointKernel_pow_markov (v mesh : ℝ) (n : ℕ) :
    IsMarkovKernel ((jointKernel hw hell hS0 hS hr hs hsS v mesh)^n) := by
  induction n with
  | zero => change IsMarkovKernel (Kernel.id : Kernel (JointState w ell S start) (JointState w ell S start)); infer_instance
  | succ n ih =>
    let := ih
    have hp : (jointKernel hw hell hS0 hS hr hs hsS v mesh)^(n+1) =
      (jointKernel hw hell hS0 hS hr hs hsS v mesh) ∘ₖ ((jointKernel hw hell hS0 hS hr hs hsS v mesh)^n) := pow_succ' _ _
    rw [hp]
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem joint_power_left (v mesh : ℝ) (n : ℕ) (q : JointState w ell S start) :
    (((jointKernel hw hell hS0 hS hr hs hsS v mesh)^n) q).map Prod.fst =
      ((chain w ell S start)^n) q.1 := by
  let := chain_isMarkov hw hell hS0 hS hr hs hsS
  exact map_power_of_step _ _ measurable_fst
    (fun x => jointKernel_left hw hell hS0 hS hr hs hsS v mesh x.1 x.2) n q

instance jointPathLaw_probability (v mesh : ℝ) (z : CostState) (n : ℕ) :
    IsProbabilityMeasure (jointPathLaw hw hell hS0 hS hr hs hsS v mesh z n) := by
  unfold jointPathLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem jointPathLaw_prime (v mesh : ℝ) (z : CostState) (n : ℕ) :
    (jointPathLaw hw hell hS0 hS hr hs hsS v mesh z n).map Prod.fst = pathLaw w ell S start n :=
  joint_power_left hw hell hS0 hS hr hs hsS v mesh n (some History.empty,.inl z)

end NumberTheoryLean.ActualCouplingFinite

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FlaggedSourceStart
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.PersistentFailureFlag

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open ActualCouplingFinite

variable {α : Type*} [MeasurableSpace α]

theorem badBit_measurable {Bad : α → Prop} (hBad : MeasurableSet {x | Bad x}) : Measurable (badBit Bad) := by
  classical
  exact Measurable.ite hBad measurable_const measurable_const

theorem update_measurable {Bad : α → Prop} (hBad : MeasurableSet {x | Bad x}) : Measurable (update Bad) := by
  have hor : Measurable (fun p : Bool × Bool => p.1 || p.2) := measurable_of_countable _
  exact measurable_snd.prodMk (hor.comp ((measurable_snd.comp measurable_fst).prodMk
    ((badBit_measurable hBad).comp measurable_snd)))

instance marked_isMarkov (K : Kernel α α) [IsMarkovKernel K]
    {Bad : α → Prop} (hBad : MeasurableSet {x | Bad x}) : IsMarkovKernel (marked K hBad) := by
  unfold marked
  exact Kernel.IsMarkovKernel.map _ (update_measurable hBad)

theorem marked_apply (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (z : FlagState α) {B : Set (FlagState α)} (hB : MeasurableSet B) :
    marked K hBad z B = K z.1 {y | (y,z.2 || badBit Bad y) ∈ B} := by
  rw [marked,Kernel.map_apply' _ (update_measurable hBad) _ hB,
    Kernel.prod_apply' _ _ _ ((update_measurable hBad) hB),Kernel.id_apply]
  rw [lintegral_dirac']
  · rfl
  · exact measurable_measure_prodMk_left ((update_measurable hBad) hB)

theorem row_update_measurable {Bad : α → Prop} (hBad : MeasurableSet {x | Bad x}) (b : Bool) :
    Measurable (fun y : α => (y,b || badBit Bad y)) := by
  have hor : Measurable (fun p : Bool × Bool => p.1 || p.2) := measurable_of_countable _
  exact measurable_id.prodMk (hor.comp (measurable_const.prodMk (badBit_measurable hBad)))

theorem marked_eq_map (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (z : FlagState α) :
    marked K hBad z = (K z.1).map (fun y => (y,z.2 || badBit Bad y)) := by
  apply Measure.ext
  intro B hB
  rw [marked_apply K hBad z hB,Measure.map_apply (row_update_measurable hBad z.2) hB]
  rfl

theorem marked_map (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (z : FlagState α) : (marked K hBad z).map Prod.fst = K z.1 := by
  rw [marked_eq_map K hBad z,Measure.map_map (f:=fun y => (y,z.2 || badBit Bad y))
    (g:=Prod.fst) measurable_fst (row_update_measurable hBad z.2)]
  exact Measure.map_id

theorem failed_measurable : MeasurableSet (failed (α:=α)) :=
  measurable_snd (measurableSet_singleton true)

theorem marked_failed_true (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (x : α) : marked K hBad (x,true) failed = 1 := by
  rw [marked_apply K hBad (x,true) failed_measurable]
  simp [failed]

instance marked_pow_markov (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (n : ℕ) : IsMarkovKernel ((marked K hBad)^n) := by
  induction n with
  | zero => change IsMarkovKernel (Kernel.id : Kernel (FlagState α) (FlagState α)); infer_instance
  | succ n ih =>
    let := ih
    have hp : (marked K hBad)^(n+1) = (marked K hBad) ∘ₖ ((marked K hBad)^n) := pow_succ' _ _
    rw [hp]
    first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply update_measurable <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem marked_power_map (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (n : ℕ) (z : FlagState α) :
    (((marked K hBad)^n) z).map Prod.fst = (K^n) z.1 :=
  map_power_of_step (marked K hBad) K measurable_fst (marked_map K hBad) n z

instance law_probability (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (x : α) (n : ℕ) : IsProbabilityMeasure (law K hBad x n) := by
  unfold law
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end NumberTheoryLean.PersistentFailureFlag



namespace NumberTheoryLean.FlaggedSourceStart

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ActualCouplingFinite ActualFlagInvariant PersistentFailureFlag
open RegeneratingInverseBands ContinuousKilledBins

variable {w ell S : ℝ} {start : Node}

variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
variable (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

instance sourceLaw_probability (mesh : ℝ) (n : ℕ) :
    IsProbabilityMeasure (sourceLaw hw hell hS0 hS hr hs hsS mesh n) := by
  unfold sourceLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem sourceLaw_joint (mesh : ℝ) (n : ℕ) :
    (sourceLaw hw hell hS0 hS hr hs hsS mesh n).map Prod.fst =
      jointPathLaw hw hell hS0 hS hr hs hsS (Real.log start.gap) mesh (sourceCostState hs) n :=
  marked_power_map _ (mismatch_measurable mesh) n (sourceJoint w ell S start hs,false)

theorem sourceLaw_prime (mesh : ℝ) (n : ℕ) :
    (sourceLaw hw hell hS0 hS hr hs hsS mesh n).map (fun q => q.1.1) = pathLaw w ell S start n := by
  calc
    _ = ((sourceLaw hw hell hS0 hS hr hs hsS mesh n).map Prod.fst).map Prod.fst :=
      (Measure.map_map (f:=Prod.fst) (g:=Prod.fst) measurable_fst measurable_fst).symm
    _ = _ := by rw [sourceLaw_joint,jointPathLaw_prime]

end NumberTheoryLean.FlaggedSourceStart


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_ExponentialMesh
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ExponentialMesh

open _root_.Set _root_.Filter
open scoped Topology

theorem log_pow_sqrt (n : ℕ) {w : ℝ} (hw : 0 ≤ Real.log w) :
    (Real.sqrt (Real.log w))^(2*n) = (Real.log w)^n := by
  rw [pow_mul,Real.sq_sqrt hw]

theorem log_power_exp_tendsto (C : ℝ) (n : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun w : ℝ => C*(Real.log w)^n*Real.exp (-c*Real.sqrt (Real.log w))) atTop (𝓝 0) := by
  have hbase : Tendsto (fun x : ℝ => C*x^(2*n)*Real.exp (-c*x)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((2*n:ℕ):ℝ) c hc).const_mul C
    simpa only [Real.rpow_natCast,mul_zero,mul_assoc] using h
  apply Tendsto.congr' _ (hbase.comp (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop))
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (0:ℝ))] with w hw
  simp only [Function.comp_apply,log_pow_sqrt n hw]

end NumberTheoryLean.ExponentialMesh

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourceMarginalRate
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.UniformBudgetRate

open _root_.Set _root_.Filter
open scoped Topology
open UniformFailureBudget ExponentialMesh BudgetPolynomialBound PrimeKilledChain

theorem source_scale_bound {d w B : ℝ} (hW : d^2 ≤ Real.log w)
    (hB : 2 ≤ Real.log B) (hcomp : Real.log B ≤ d*Real.log w) :
    (Real.log B)^2 ≤ (Real.log w)^3 ∧
      (LowStateHorizon.sourceHorizon ((Real.log B)^2) B:ℝ) ≤ 5*d^3*(Real.log w)^3 := by
  have hlog : 0 ≤ Real.log w := (sq_nonneg d).trans hW
  have hpow₂ := pow_le_pow_left₀ (show 0 ≤ Real.log B by linarith) hcomp 2
  have hpow₃ := pow_le_pow_left₀ (show 0 ≤ Real.log B by linarith) hcomp 3
  have hmul := mul_le_mul_of_nonneg_right hW (sq_nonneg (Real.log w))
  have hN := LowStateHorizon.source_horizon_log_cube hB
  constructor <;> nlinarith

end NumberTheoryLean.UniformBudgetRate

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_PrimeExponentialTail
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ExponentialMeshTail

open _root_.Finset

theorem quadratic_exp_majorant {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) :
    r^2*Real.exp (-c*r) ≤ (8/c^2)*Real.exp (-c*r/2) := by
  have h := Real.pow_div_factorial_le_exp (x := c*r/2) (by positivity) 2
  norm_num only [Nat.factorial_succ,Nat.factorial_zero,Nat.cast_one,Nat.cast_ofNat] at h
  have hc2 : 0 < c^2 := sq_pos_of_pos hc
  have hp : r^2 ≤ (8/c^2)*Real.exp (c*r/2) := by
    have hh : r^2 ≤ 8*Real.exp (c*r/2)/c^2 := (le_div_iff₀ hc2).mpr (by nlinarith [h])
    convert hh using 1 <;> first | rfl | ring
  calc
    _ ≤ ((8/c^2)*Real.exp (c*r/2))*Real.exp (-c*r) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc,← Real.exp_add]; congr 2; ring

end NumberTheoryLean.ExponentialMeshTail

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_SourceCompactCoupling
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.CouplingData

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ActualFlagInvariant KernelCouplingLift PersistentFailureFlag

variable {w ell S : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
variable (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem sourceLaw_eq (mesh : ℝ) (n : ℕ) :
    FlaggedSourceStart.sourceLaw hw hell hS0 hS hr hs hsS mesh n = sourceLaw w ell S start hs mesh n := rfl

include hw hell hS0 hS hr hsS in

theorem source_prime (mesh : ℝ) (n : ℕ) :
    (sourceLaw w ell S start hs mesh n).map (fun q => q.1.1) = pathLaw w ell S start n := by
  rw [← sourceLaw_eq hw hell hS0 hS hr hs hsS]
  exact FlaggedSourceStart.sourceLaw_prime hw hell hS0 hS hr hs hsS mesh n

end NumberTheoryLean.CouplingData

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_FlaggedOccupationBound
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.FlaggedOccupationBound

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open PersistentFailureFlag

variable {α : Type*} [MeasurableSpace α]

theorem selected_measurable {f : α → ℝ≥0∞} (hf : Measurable f) : Measurable (selected f) :=
  (hf.comp measurable_fst).indicator failed_measurable

theorem selected_integral_le {f : α → ℝ≥0∞} {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hf : ∀ x,f x ≤ C) (μ : Measure (FlagState α)) :
    (∫⁻ z,selected f z ∂μ) ≤ C*μ failed := by
  calc
    _ ≤ ∫⁻ z,C*failed.indicator (fun _ => (1:ℝ≥0∞)) z ∂μ := by
      apply lintegral_mono
      rintro ⟨x,b⟩
      cases b <;> simp [selected,failed,hf x]
    _ = _ := by
      rw [lintegral_const_mul' _ _ hC,lintegral_indicator failed_measurable,setLIntegral_const,one_mul]

theorem selected_true_integral (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) {f : α → ℝ≥0∞} (hf : Measurable f) (x : α) :
    (∫⁻ z,selected f z ∂marked K hBad (x,true)) = ∫⁻ y,f y ∂K x := by
  rw [marked_eq_map K hBad (x,true),lintegral_map (selected_measurable hf)
    (row_update_measurable hBad true)]
  simp only [Bool.true_or,selected_true]

theorem selected_row (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) {q V : α → ℝ≥0∞} (hV : Measurable V)
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hbound : ∀ x,V x ≤ C)
    (hdrift : ∀ x,q x+(∫⁻ y,V y ∂K x) ≤ V x) (z : FlagState α) :
    selected q z+(∫⁻ y,selected V y ∂marked K hBad z)+
      C*failed.indicator (fun _ => (1:ℝ≥0∞)) z ≤
        selected V z+C*marked K hBad z failed := by
  rcases z with ⟨x,b⟩
  cases b with
  | false =>
    simpa [selected,failed] using selected_integral_le hC hbound (marked K hBad (x,false))
  | true =>
    rw [selected_true,selected_true,selected_true_integral K hBad hV,marked_failed_true]
    simpa [failed] using add_le_add_left (hdrift x) C

theorem law_selected_step (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) {q V : α → ℝ≥0∞} (hq : Measurable q) (hV : Measurable V)
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hbound : ∀ x,V x ≤ C)
    (hdrift : ∀ x,q x+(∫⁻ y,V y ∂K x) ≤ V x) (x : α) (n : ℕ) :
    (∫⁻ z,selected q z ∂law K hBad x n)+
      (∫⁻ z,selected V z ∂law K hBad x (n+1))+C*law K hBad x n failed ≤
        (∫⁻ z,selected V z ∂law K hBad x n)+C*law K hBad x (n+1) failed := by
  have hp : (marked K hBad)^(n+1) = marked K hBad ∘ₖ ((marked K hBad)^n) := pow_succ' _ _
  have hnext : (∫⁻ z,selected V z ∂law K hBad x (n+1)) =
      ∫⁻ z,∫⁻ y,selected V y ∂marked K hBad z ∂law K hBad x n := by
    unfold law
    rw [hp,Kernel.lintegral_comp _ _ _ (selected_measurable hV)]
  have hfail : law K hBad x (n+1) failed = ∫⁻ z,marked K hBad z failed ∂law K hBad x n := by
    unfold law
    rw [hp,Kernel.comp_apply' _ _ _ failed_measurable]
  have hi := lintegral_mono (μ := law K hBad x n) (selected_row K hBad hV hC hbound hdrift)
  have hinner : Measurable (fun z => ∫⁻ y,selected V y ∂marked K hBad z) := (selected_measurable hV).lintegral_kernel
  rw [lintegral_add_left (f := fun z => selected q z+(∫⁻ y,selected V y ∂marked K hBad z))
      ((selected_measurable hq).add hinner),
    lintegral_add_left (selected_measurable hq),
    lintegral_add_left (selected_measurable hV),
    lintegral_const_mul' _ _ hC,lintegral_const_mul' _ _ hC,
    lintegral_indicator failed_measurable,setLIntegral_const,one_mul] at hi
  rw [← hnext,← hfail] at hi
  exact hi

theorem finite_selected_occupation (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) {q V : α → ℝ≥0∞} (hq : Measurable q) (hV : Measurable V)
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hbound : ∀ x,V x ≤ C)
    (hdrift : ∀ x,q x+(∫⁻ y,V y ∂K x) ≤ V x) (x : α) (N : ℕ) :
    (∑ n ∈ range N, ∫⁻ z,selected q z ∂law K hBad x n) ≤ C*law K hBad x N failed := by
  have hstrong : ∀ N : ℕ,
      (∑ n ∈ range N, ∫⁻ z,selected q z ∂law K hBad x n)+
        (∫⁻ z,selected V z ∂law K hBad x N) ≤ C*law K hBad x N failed := by
    intro N
    induction N with
    | zero =>
      simp only [sum_range_zero,zero_add,law,pow_zero]
      change (∫⁻ z,selected V z ∂Measure.dirac (x,false)) ≤ C*Measure.dirac (x,false) failed
      rw [lintegral_dirac' _ (selected_measurable hV),selected_false]
      exact zero_le
    | succ N ih =>
      rw [sum_range_succ,add_assoc]
      have hd : C*law K hBad x N failed ≠ ∞ := ENNReal.mul_ne_top hC (measure_ne_top _ _)
      apply (ENNReal.add_le_add_iff_right hd).mp
      calc
        _ = (∑ n ∈ range N, ∫⁻ z,selected q z ∂law K hBad x n)+
            ((∫⁻ z,selected q z ∂law K hBad x N)+
             (∫⁻ z,selected V z ∂law K hBad x (N+1))+C*law K hBad x N failed) := by ac_rfl
        _ ≤ (∑ n ∈ range N, ∫⁻ z,selected q z ∂law K hBad x n)+
            ((∫⁻ z,selected V z ∂law K hBad x N)+C*law K hBad x (N+1) failed) :=
          add_le_add_right (law_selected_step K hBad hq hV hC hbound hdrift x N) _
        _ ≤ C*law K hBad x N failed+C*law K hBad x (N+1) failed := by
          rw [← add_assoc]
          exact add_le_add_left ih _
        _ = _ := add_comm _ _
  exact (le_add_right le_rfl).trans (hstrong N)

end NumberTheoryLean.FlaggedOccupationBound

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_ActualFlaggedCompact
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ActualFlaggedCompact

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain ActualProcessCoupling
open PrimeCompactVisits FlaggedOccupationBound PersistentFailureFlag ActualFlagInvariant

variable {w ell S : ℝ} {start : Node}

theorem compactVisit_measurable (K : ℝ) : Measurable (compactVisit (w:=w) (ell:=ell) (S:=S) (start:=start) K) :=
  (measurable_of_countable (fun p : ChainState w ell S start => ENNReal.ofReal (visit K p))).comp measurable_fst

theorem compactPotential_measurable (K : ℝ) : Measurable (compactPotential (w:=w) (ell:=ell) (S:=S) (start:=start) K) :=
  (measurable_of_countable (fun p : ChainState w ell S start => ENNReal.ofReal (potential K p))).comp measurable_fst

variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
    (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem joint_compact_drift {K : ℝ} (hK : 0 ≤ K) (v mesh : ℝ) (z : JointState w ell S start) :
    compactVisit K z+(∫⁻ y,compactPotential K y ∂jointKernel hw hell hS0 hS hr hs hsS v mesh z) ≤
      compactPotential K z := by
  have hmeas : Measurable (fun p : ChainState w ell S start => ENNReal.ofReal (potential K p)) := measurable_of_countable _
  have heq : (∫⁻ y,compactPotential K y ∂jointKernel hw hell hS0 hS hr hs hsS v mesh z) =
      ∫⁻ p,ENNReal.ofReal (potential K p) ∂chain w ell S start z.1 := by
    rw [← jointKernel_left hw hell hS0 hS hr hs hsS v mesh z.1 z.2,
      lintegral_map hmeas measurable_fst]
    rfl
  rw [heq]
  exact actual_row_drift hw hell hS0 hS hr hs hsS hK z.1

include hw hell hS0 hS hr hsS in

theorem actual_flagged_compact_visits {K : ℝ} (hK : 0 ≤ K) (mesh : ℝ) (N : ℕ) :
    (∑ n ∈ range N, ∫⁻ z,selected (compactVisit K) z ∂CouplingData.sourceLaw w ell S start hs mesh n) ≤
      ENNReal.ofReal (K+1)*CouplingData.sourceLaw w ell S start hs mesh N failed := by
  have hbound : ∀ z : JointState w ell S start,compactPotential K z ≤ ENNReal.ofReal (K+1) :=
    fun z => ENNReal.ofReal_le_ofReal (potential_le hK z.1)
  have h := finite_selected_occupation
    (jointKernel hw hell hS0 hS hr hs hsS (Real.log start.gap) mesh)
    (mismatch_measurable mesh) (compactVisit_measurable K) (compactPotential_measurable K)
    ENNReal.ofReal_ne_top hbound
    (joint_compact_drift hw hell hS0 hS hr hs hsS hK (Real.log start.gap) mesh)
    (FlaggedSourceStart.sourceJoint w ell S start hs) N
  exact h

end NumberTheoryLean.ActualFlaggedCompact

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_GrowingFarTail
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.InverseWeightGrowth
open _root_.Filter
open scoped Topology

theorem quartic_log_scale_absorption {C kappa : ℝ} (hC : 0 ≤ C) (hkappa : 0 < kappa) :
    ∀ᶠ w : ℝ in atTop,
      Real.exp (C*(1+(Real.log w)^((1 : ℝ)/10))^4) *
        Real.exp (-kappa*Real.sqrt (Real.log w)) ≤
          Real.exp (-(kappa/2)*Real.sqrt (Real.log w)) := by
  have hk : Tendsto (fun w : ℝ => (Real.log w)^((1 : ℝ)/10)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/10)).comp Real.tendsto_log_atTop
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    hk.eventually (eventually_ge_atTop (max 1 (32*C/kappa)))] with w hlog hcut
  let k : ℝ := (Real.log w)^((1 : ℝ)/10)
  have hk1 : 1 ≤ k := (le_max_left _ _).trans hcut
  have hk0 : 0 ≤ k := by linarith
  have hcoef : 16*C ≤ (kappa/2)*k := by
    have h := (div_le_iff₀ hkappa).mp ((le_max_right _ _).trans hcut)
    nlinarith
  have hsqrt : Real.sqrt (Real.log w) = k^5 := by
    rw [Real.sqrt_eq_rpow]
    dsimp [k]
    rw [← Real.rpow_mul_natCast (by linarith : 0 ≤ Real.log w)]
    norm_num
  have hmajor : C*(1+k)^4 ≤ (kappa/2)*Real.sqrt (Real.log w) := by
    calc
      _ ≤ C*(2*k)^4 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by linarith) (by linarith : 1+k ≤ 2*k) 4) hC
      _ = (16*C)*k^4 := by ring
      _ ≤ ((kappa/2)*k)*k^4 := mul_le_mul_of_nonneg_right hcoef (pow_nonneg hk0 _)
      _ = _ := by rw [hsqrt]; ring
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  change C*(1+k)^4 + -kappa*Real.sqrt (Real.log w) ≤ _
  nlinarith

end NumberTheoryLean.InverseWeightGrowth

end

section

namespace NumberTheoryLean.ModerateFailedReward

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeBinMembership
open PrimeCompactVisits PrimeCompactWeights ActualProcessCoupling
open FlaggedOccupationBound ActualFlaggedCompact PersistentFailureFlag
open DerivativeWeights ExponentialMeshTail InverseWeightGrowth

variable {w ell S : ℝ} {start : Node}

theorem exponential_quartic_absorbs_linear {C K : ℝ} (hK : 0 ≤ K) :
    Real.exp (C*(1+K)^4)*(K+1) ≤ Real.exp ((C+1)*(1+K)^4) := by
  have hp : K ≤ (1+K)^4 := by nlinarith [pow_nonneg hK 3,pow_nonneg hK 4]
  have hlin : K+1 ≤ Real.exp ((1+K)^4) := (Real.add_one_le_exp K).trans (Real.exp_le_exp.mpr hp)
  calc
    _ ≤ Real.exp (C*(1+K)^4)*Real.exp ((1+K)^4) := mul_le_mul_of_nonneg_left hlin (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem moderate_reward_envelope : ∃ A C : ℝ,0 < A ∧ 0 < C ∧
    ∀ w ell S : ℝ,∀ start : Node,1 ≤ ell → 0 < start.gap → Valid start.side start.ratio →
      Consistent start → ell ≤ start.cutoff → ∀ c : ℝ,0 < c → ∀ K : ℝ,
      ∀ z : ChainState w ell S start,
        moderateReward c K z ≤ ENNReal.ofReal ((8*A/c^2)*Real.exp (C*(1+K)^4))*ENNReal.ofReal (visit K z) := by
  obtain ⟨A,C,hA,hC,hbound⟩ := inverse_weight_below_cutoff
  refine ⟨A,C,hA,hC,?_⟩
  intro w ell S start hell hr hs hcons hcut c hc K z
  cases z with
  | none => simp [moderateReward,visit]
  | some h =>
    by_cases hh : h.node.gap ≤ K
    · have hg : 0 < h.node.gap := terminal_gap_positive (by linarith) hr hs h.admissible
      have hv : Valid h.node.side h.node.ratio := terminal_valid hs h.admissible
      have htK := (history_ratio_le_gap hell hr hs hcons hcut h).trans hh
      have hinv := hbound K h.node.side h.node.ratio hv htK
      have hraw : h.node.gap^2*Real.exp (-c*h.node.gap) ≤ 8/c^2 := by
        refine (quadratic_exp_majorant hc hg.le).trans ?_
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.mpr (by nlinarith : -c*h.node.gap/2 ≤ 0)) (show 0 ≤ 8/c^2 by positivity)
      have hφ := weight_pos hv
      have hreal : h.node.gap^2*Real.exp (-c*h.node.gap)/weight h.node.side h.node.ratio ≤
          (8*A/c^2)*Real.exp (C*(1+K)^4) := by
        calc
          _ = (h.node.gap^2*Real.exp (-c*h.node.gap))*(1/weight h.node.side h.node.ratio) := by ring
          _ ≤ (8/c^2)*(A*Real.exp (C*(1+K)^4)) := mul_le_mul hraw hinv (by positivity) (by positivity)
          _ = _ := by ring
      simp only [moderateReward,visit,ite_eq_left hh,ENNReal.ofReal_one,mul_one]
      exact ENNReal.ofReal_le_ofReal hreal
    · simp [moderateReward,visit,hh]

theorem actual_moderate_failed_sum : ∃ A C : ℝ,0 < A ∧ 0 < C ∧
    ∀ w ell S : ℝ,∀ start : Node,∀ _hw : normalizationThreshold ≤ w,
      ∀ _hell : 1 ≤ ell,∀ _hS0 : 0 ≤ S,∀ _hS : S ≤ (Real.log w)^3,
      ∀ _hr : 0 < start.gap,∀ hs : Valid start.side start.ratio,∀ _hsS : start.ratio ≤ S,
      Consistent start → ell ≤ start.cutoff → ∀ c : ℝ,0 < c → ∀ K : ℝ,0 ≤ K →
      ∀ mesh : ℝ,∀ N : ℕ,
        (∑ n ∈ range N,∫⁻ z,selected (fun q : JointState w ell S start => moderateReward c K q.1) z
          ∂CouplingData.sourceLaw w ell S start hs mesh n) ≤
          ENNReal.ofReal ((8*A/c^2)*Real.exp (C*(1+K)^4))*
            CouplingData.sourceLaw w ell S start hs mesh N failed := by
  obtain ⟨A,C,hA,hC,hbound⟩ := moderate_reward_envelope
  refine ⟨A,C+1,hA,by linarith,?_⟩
  intro w ell S start hw hell hS0 hS hr hs hsS hcons hcut c hc K hK mesh N
  let D := (8*A/c^2)*Real.exp (C*(1+K)^4)
  have hD : 0 ≤ D := by dsimp [D] <;> positivity
  have hpoint : ∀ z : FlagState (JointState w ell S start),
      selected (fun q => moderateReward c K q.1) z ≤ ENNReal.ofReal D*selected (compactVisit K) z := by
    rintro ⟨q,b⟩
    cases b with
    | false => simp only [selected_false,mul_zero,le_refl]
    | true =>
      simpa only [selected_true,compactVisit] using hbound w ell S start hell hr hs hcons hcut c hc K q.1
  have hsum : (∑ n ∈ range N,∫⁻ z,selected (fun q : JointState w ell S start => moderateReward c K q.1) z
      ∂CouplingData.sourceLaw w ell S start hs mesh n) ≤
      ENNReal.ofReal D*(∑ n ∈ range N,∫⁻ z,selected (compactVisit K) z ∂CouplingData.sourceLaw w ell S start hs mesh n) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n _hn
    calc
      _ ≤ ∫⁻ z,ENNReal.ofReal D*selected (compactVisit K) z ∂CouplingData.sourceLaw w ell S start hs mesh n := lintegral_mono hpoint
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hlinear := exponential_quartic_absorbs_linear (C:=C) hK
  refine hsum.trans ?_
  calc
    _ ≤ ENNReal.ofReal D*(ENNReal.ofReal (K+1)*CouplingData.sourceLaw w ell S start hs mesh N failed) :=
      mul_le_mul_of_nonneg_left (actual_flagged_compact_visits hw hell hS0 hS hr hs hsS hK mesh N) zero_le
    _ ≤ _ := by
      rw [← mul_assoc,← ENNReal.ofReal_mul hD]
      apply mul_le_mul_of_nonneg_right _ zero_le
      apply ENNReal.ofReal_le_ofReal
      dsimp [D]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hlinear (show 0 ≤ 8*A/c^2 by positivity)

end NumberTheoryLean.ModerateFailedReward

end

section

namespace NumberTheoryLean.SourceModerateFailure

open _root_.Set _root_.Filter _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeBinMembership
open ActualProcessCoupling PersistentFailureFlag FlaggedOccupationBound
open ModerateFailedReward SourceCouplingRate InverseWeightGrowth UniformBudgetRate
open ExponentialMesh LowStateHorizon

theorem source_moderate_failure : ∃ κ₀ A : ℝ,0 < κ₀ ∧ 0 < A ∧
    ∀ κ : ℝ,0 < κ → κ ≤ κ₀ → ∀ d : ℝ,0 < d → ∃ w₀ : ℝ,1 < w₀ ∧
      ∀ w : ℝ,w₀ ≤ w → ∀ ell B : ℝ,∀ start : Node,∀ hs : Valid start.side start.ratio,
        1 ≤ ell → ell ≤ B → 0 < B → 2 ≤ Real.log B → Real.log B ≤ d*Real.log w →
        0 < start.gap → start.ratio ≤ 23/10 → Consistent start → start.cutoff = B →
        let S := (Real.log B)^2
        let N := sourceHorizon S B
        ∀ c : ℝ,0 < c →
          (∑ n ∈ range N,∫⁻ z,selected (fun q : JointState w ell S start => moderateReward c (growingCutoff w) q.1) z
            ∂CouplingData.sourceLaw w ell S start hs (mesh κ w) n) ≤
              ENNReal.ofReal ((A/c^2)*Real.exp (-(κ/4)*Real.sqrt (Real.log w))) := by
  obtain ⟨κ₀,hκ₀,hrate⟩ := source_coupling_rate_jb247
  obtain ⟨A,C,hA,hC,hmod⟩ := actual_moderate_failed_sum
  refine ⟨κ₀,8*A,hκ₀,by positivity,?_⟩
  intro κ hκ hκle d hd
  obtain ⟨wF,hwF,hrate⟩ := hrate κ hκ hκle d hd
  have hevent := (quartic_log_scale_absorption hC.le (show 0 < κ/2 by linarith)).and
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (d^2)))
  obtain ⟨wAux,hwAux⟩ := eventually_atTop.mp hevent
  refine ⟨max wF (max normalizationThreshold wAux),hwF.trans_le (le_max_left _ _),?_⟩
  intro w hw ell B start hs hell hellB hB hlogB hcomp hr h23 hcons hcut
  dsimp only
  intro c hc
  let S := (Real.log B)^2
  let N := sourceHorizon S B
  have hnorm : normalizationThreshold ≤ w := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hw
  have hwe := hwAux w ((le_trans (le_max_right _ _) (le_max_right _ _)).trans hw)
  have hscale := source_scale_bound hwe.2 hlogB hcomp
  have hS0 : 0 ≤ S := sq_nonneg _
  have hS3 : 3 ≤ S := by dsimp [S] <;> nlinarith
  have hsS : start.ratio ≤ S := by linarith
  have hlog : 0 ≤ Real.log w := (sq_nonneg d).trans hwe.2
  have hcut0 : 0 ≤ growingCutoff w := Real.rpow_nonneg hlog _
  have hsize : start.gap ≤ (23/10:ℝ)*B := by
    have he : start.cutoff = start.gap/start.ratio := hcons
    rw [hcut] at he
    have hh := (eq_div_iff (valid_pos hs).ne').mp he
    nlinarith
  have hfailed := ((hrate w ((le_max_left _ _).trans hw) ell B start hs hell hB hlogB hcomp hr h23 hcons hsize).1 N le_rfl).1
  have hm := hmod w ell S start hnorm hell hS0 hscale.1 hr hs hsS hcons (by rwa [hcut])
    c hc (growingCutoff w) hcut0 (mesh κ w) N
  have hcoef : 0 ≤ 8*A/c^2 := by positivity
  refine hm.trans ?_
  calc
    _ ≤ ENNReal.ofReal ((8*A/c^2)*Real.exp (C*(1+growingCutoff w)^4))*
        ENNReal.ofReal (Real.exp (-(κ/2)*Real.sqrt (Real.log w))) :=
      mul_le_mul_of_nonneg_left hfailed zero_le
    _ = ENNReal.ofReal ((8*A/c^2)*(Real.exp (C*(1+growingCutoff w)^4)*
        Real.exp (-(κ/2)*Real.sqrt (Real.log w)))) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have habsorb : Real.exp (C*(1+growingCutoff w)^4)*Real.exp (-(κ/2)*Real.sqrt (Real.log w)) ≤
          Real.exp (-(κ/4)*Real.sqrt (Real.log w)) := by
        simpa only [growingCutoff,div_div,show (2:ℝ)*2 = 4 by norm_num] using hwe.1
      exact mul_le_mul_of_nonneg_left habsorb hcoef

end NumberTheoryLean.SourceModerateFailure

end

section

namespace NumberTheoryLean.GrowingFarTail

open _root_.Set _root_.Filter _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeBinMembership
open PrimeExponentialTail SourceModerateFailure LowStateHorizon

theorem growingCutoff_tendsto : Tendsto growingCutoff atTop atTop :=
  (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/10)).comp Real.tendsto_log_atTop

theorem log_cube_growing_exp_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (fun w : ℝ => (Real.log w)^3*Real.exp (-c*growingCutoff w)) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => x^30*Real.exp (-c*x)) atTop (𝓝 0) := by
    simpa only [Real.rpow_ofNat] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (30:ℝ) c hc
  apply Tendsto.congr' _ (h.comp growingCutoff_tendsto)
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (0:ℝ))] with w hw
  have hp : growingCutoff w^30 = (Real.log w)^3 := by
    unfold growingCutoff
    rw [← Real.rpow_mul_natCast hw]
    norm_num
  simp only [Function.comp_apply,hp]

theorem farBudget_tendsto_zero (C d : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (farBudget C c d) atTop (𝓝 0) := by
  have h := (log_cube_growing_exp_tendsto (show 0 < c/4 by linarith)).const_mul (5*d^3*(C*(8/c^2)*(1+4/c)))
  simp only [mul_zero] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext w
  unfold farBudget
  ring

end NumberTheoryLean.GrowingFarTail

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_SuccessfulTailTransport
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SuccessfulTailTransport

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling PersistentFailureFlag ActualFlagInvariant
open RegeneratingInverseBands InvariantInverseWeights ArrivalKernelGeometry
open ContinuousArrivalSupport ContinuousCompletedOccupation
open ContinuousKilledBins CostPrefixTransport

variable {w ell S : ℝ} {start : Node}

theorem cleanReward_measurable (c K : ℝ) : Measurable (cleanReward (w:=w) (ell:=ell) (S:=S) (start:=start) c K) := by
  apply Measurable.ite (measurable_snd (measurableSet_singleton false))
  · exact (measurable_of_countable (PrimeExponentialTail.tailReward c K)).comp (measurable_fst.comp measurable_fst)
  · exact measurable_const

end NumberTheoryLean.SuccessfulTailTransport

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeTailSplit
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.InitialPrimeTail

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain DerivativeWeights
open PrimeExponentialTail ExponentialMeshTail SuccessfulTailTransport

theorem initialConstant_pos : 0 < initialConstant :=
  div_pos (by norm_num) (weight_pos (by norm_num [Valid]))

theorem initialBudget_tendsto_zero {c : ℝ} (hc : 0 < c) : Tendsto (initialBudget c) atTop (𝓝 0) := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (0:ℝ) (c/2) (by linarith : 0 < c/2)
  have h' := h.const_mul (initialConstant/c^2)
  change Tendsto (fun B : ℝ => (initialConstant/c^2)*Real.exp (-(c/2)*B)) atTop (𝓝 0)
  simpa only [Real.rpow_zero,one_mul,mul_zero] using h'

theorem initial_tail_integral (w ell S c K : ℝ) (start : Node) :
    (∫⁻ z,tailReward c K z ∂pathLaw w ell S start 0) =
      tailReward c K (some (History.empty : History w ell S start)) := by
  change (∫⁻ z,tailReward c K z ∂Measure.dirac (some History.empty)) = _
  rw [lintegral_dirac' _ (measurable_of_countable _)]

theorem clean_initial_integral (w ell S c K mesh : ℝ) (start : Node) (hs : Valid start.side start.ratio) :
    (∫⁻ z,cleanReward c K z ∂CouplingData.sourceLaw w ell S start hs mesh 0) =
      tailReward c K (some (History.empty : History w ell S start)) := by
  change (∫⁻ z,cleanReward c K z ∂Measure.dirac (FlaggedSourceStart.sourceJoint w ell S start hs,false)) = _
  rw [lintegral_dirac' _ (cleanReward_measurable c K)]
  rfl

theorem source_initial_tail {w ell S B c K : ℝ} {start : Node}
    (hc : 0 < c) (hB : 0 < B) (hsize : B ≤ start.gap)
    (hi : start.side = .even) (h199 : 199/100 ≤ start.ratio) (h23 : start.ratio ≤ 23/10) :
    tailReward c K (some (History.empty : History w ell S start)) ≤ ENNReal.ofReal (initialBudget c B) := by
  have hr : 0 < start.gap := hB.trans_le hsize
  have hs : Valid start.side start.ratio := by rw [hi]; change 198/100 ≤ start.ratio; linarith
  have hφ := weight_pos hs
  have hφend : 0 < weight .even (23/10) := weight_pos (by norm_num [Valid])
  have hmono : weight .even (23/10) ≤ weight start.side start.ratio := by
    rw [hi]
    exact TwoStepDensityBounds.weight_antitone (by change 198/100 ≤ start.ratio; linarith) (by norm_num [Valid]) h23
  have hinv := one_div_le_one_div_of_le hφend hmono
  have hraw := quadratic_exp_majorant hc hr.le
  have hexp : Real.exp (-c*start.gap/2) ≤ Real.exp (-(c/2)*B) := Real.exp_le_exp.mpr (by nlinarith)
  have hbound : start.gap^2*Real.exp (-c*start.gap)/weight start.side start.ratio ≤ initialBudget c B := by
    calc
      _ = (start.gap^2*Real.exp (-c*start.gap))*(1/weight start.side start.ratio) := by ring
      _ ≤ ((8/c^2)*Real.exp (-c*start.gap/2))*(1/weight .even (23/10)) :=
        mul_le_mul hraw hinv (by positivity) (by positivity)
      _ ≤ ((8/c^2)*Real.exp (-(c/2)*B))*(1/weight .even (23/10)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp (by positivity)) (by positivity)
      _ = _ := by unfold initialBudget initialConstant; ring
  change (if K < start.gap then ENNReal.ofReal _ else 0) ≤ _
  split_ifs
  · exact ENNReal.ofReal_le_ofReal hbound
  · exact zero_le

end NumberTheoryLean.InitialPrimeTail

end

section


namespace NumberTheoryLean.PrimeTailSplit

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain ActualProcessCoupling
open PersistentFailureFlag FlaggedOccupationBound PrimeExponentialTail
open SuccessfulTailTransport ModerateFailedReward InitialPrimeTail

variable {w ell S : ℝ} {start : Node}

theorem tail_split_pointwise (c K T : ℝ) (q : FlagState (JointState w ell S start)) :
    tailReward c K q.1.1 ≤ cleanReward c K q+
      selected (fun p : JointState w ell S start => moderateReward c T p.1) q+tailReward c T q.1.1 := by
  rcases q with ⟨⟨p,y⟩,b⟩
  cases b with
  | false =>
    simp only [cleanReward,selected_false,add_zero]
    exact le_add_of_nonneg_right zero_le
  | true =>
    simp only [cleanReward,Bool.true_eq_false,ite_false, if_false,selected_true,zero_add]
    cases p with
    | none => simp [tailReward,moderateReward]
    | some h =>
      by_cases hK : K < h.node.gap
      · rw [tailReward,ite_eq_left hK]
        by_cases hT : h.node.gap ≤ T
        · simp only [moderateReward,PrimeCompactVisits.visit,ite_eq_left hT,ENNReal.ofReal_one,mul_one]
          exact le_add_of_nonneg_right zero_le
        · rw [tailReward,ite_eq_left (lt_of_not_ge hT)]
          exact le_add_of_nonneg_left zero_le
      · rw [tailReward,ite_eq_right hK]
        exact zero_le

theorem finite_le_initial_plus_successors (a : ℕ → ℝ≥0∞) (N : ℕ) :
    (∑ n ∈ range N,a n) ≤ a 0+∑ n ∈ range N,a (n+1) := by
  calc
    _ ≤ ∑ n ∈ range (N+1),a n := by rw [Finset.sum_range_succ]; exact le_add_of_nonneg_right zero_le
    _ = _ := by rw [Finset.sum_range_succ']; exact add_comm _ _

private theorem add_tail_bounds {a b c x y p q : ℝ≥0∞}
    (ha : a ≤ x + p) (hc : c ≤ y + q) : a + b + c ≤ x + y + p + b + q := by
  calc
    _ ≤ (x + p) + b + (y + q) := add_le_add (add_le_add ha (le_refl b)) hc
    _ = _ := by ac_rfl

variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
    (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

include hw hell hS0 hS hr hsS in

theorem actual_finite_tail_split (c K T mesh : ℝ) (N : ℕ) :
    (∑ n ∈ range N,∫⁻ z,tailReward c K z ∂pathLaw w ell S start n) ≤
      tailReward c K (some (History.empty : History w ell S start))+
      tailReward c T (some (History.empty : History w ell S start))+
      (∑ n ∈ range N,∫⁻ q,cleanReward c K q ∂CouplingData.sourceLaw w ell S start hs mesh (n+1))+
      (∑ n ∈ range N,∫⁻ q,selected (fun p : JointState w ell S start => moderateReward c T p.1) q
        ∂CouplingData.sourceLaw w ell S start hs mesh n)+
      (∑ n ∈ range N,∫⁻ z,tailReward c T z ∂pathLaw w ell S start (n+1)) := by
  have htail (R : ℝ) : Measurable (tailReward (w:=w) (ell:=ell) (S:=S) (start:=start) c R) := measurable_of_countable _
  have hmod : Measurable (fun p : JointState w ell S start => moderateReward c T p.1) :=
    (measurable_of_countable (moderateReward c T)).comp measurable_fst
  have hone : ∀ n : ℕ,(∫⁻ z,tailReward c K z ∂pathLaw w ell S start n) ≤
      (∫⁻ q,cleanReward c K q ∂CouplingData.sourceLaw w ell S start hs mesh n)+
      (∫⁻ q,selected (fun p : JointState w ell S start => moderateReward c T p.1) q
        ∂CouplingData.sourceLaw w ell S start hs mesh n)+
      (∫⁻ z,tailReward c T z ∂pathLaw w ell S start n) := by
    intro n
    have he := CouplingData.source_prime hw hell hS0 hS hr hs hsS mesh n
    rw [← he,lintegral_map (g:=fun q : FlagState (JointState w ell S start) => q.1.1)
      (htail K) (measurable_fst.comp measurable_fst)]
    have h := lintegral_mono (μ:=CouplingData.sourceLaw w ell S start hs mesh n) (tail_split_pointwise c K T)
    rw [lintegral_add_left (f:=fun q : FlagState (JointState w ell S start) => cleanReward c K q+selected (fun p : JointState w ell S start => moderateReward c T p.1) q)
        ((cleanReward_measurable c K).add (selected_measurable hmod)),
      lintegral_add_left (cleanReward_measurable c K)] at h
    rw [← lintegral_map (g:=fun q : FlagState (JointState w ell S start) => q.1.1)
      (htail T) (measurable_fst.comp measurable_fst),he] at h
    rw [he]
    exact h
  have hclean := finite_le_initial_plus_successors
    (fun n => ∫⁻ q,cleanReward c K q ∂CouplingData.sourceLaw w ell S start hs mesh n) N
  rw [clean_initial_integral] at hclean
  have hfar := finite_le_initial_plus_successors (fun n => ∫⁻ z,tailReward c T z ∂pathLaw w ell S start n) N
  rw [initial_tail_integral] at hfar
  have hsum := Finset.sum_le_sum (s:=range N) (fun n _ => hone n)
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib] at hsum
  exact hsum.trans (add_tail_bounds hclean hfar)

end NumberTheoryLean.PrimeTailSplit

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ScaledOriginalTail
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SourceTailBudget

open _root_.Set _root_.Filter _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeBinMembership
open PrimeExponentialTail PrimeTailSplit InitialPrimeTail
open SourceSuccessfulTail SourceModerateFailure GrowingFarTail ExponentialMesh
open UniformBudgetRate LowStateHorizon

theorem failureBudget_tendsto_zero (A c : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (failureBudget A c κ) atTop (𝓝 0) := by
  change Tendsto (fun w : ℝ => (A/c^2)*Real.exp (-(κ/4)*Real.sqrt (Real.log w))) atTop (𝓝 0)
  simpa only [pow_zero,mul_one] using log_power_exp_tendsto (A/c^2) 0 (show 0 < κ/4 by linarith)

theorem source_tail_budget : ∃ κ₀ A C : ℝ,0 < κ₀ ∧ 0 < A ∧ 0 < C ∧
    ∀ κ : ℝ,0 < κ → κ ≤ κ₀ → ∀ d c : ℝ,0 < d → 0 < c →
      ∃ b : ℕ → ℝ≥0∞,Tendsto b atTop (𝓝 0) ∧ ∃ w₀ : ℝ,1 < w₀ ∧
      ∀ w : ℝ,w₀ ≤ w → ∀ ell B : ℝ,∀ start : Node,∀ _hs : Valid start.side start.ratio,
        1 ≤ ell → ell ≤ B → 0 < B → 2 ≤ Real.log B → Real.log B ≤ d*Real.log w →
        0 < start.gap → start.side = .even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff = B →
        let S := (Real.log B)^2
        let N := sourceHorizon S B
        ∀ M : ℕ,(∑ n ∈ range N,∫⁻ z,tailReward c (3*((M:ℝ)+1)) z ∂pathLaw w ell S start n) ≤
          ENNReal.ofReal (2*initialBudget c B)+b M+
          ENNReal.ofReal (failureBudget A c κ w)+ENNReal.ofReal (farBudget C c d w) := by
  obtain ⟨κM,A,hκM,hA,hmoderate⟩ := source_moderate_failure
  obtain ⟨κF,C,hκF,hC,hfar⟩ := source_growing_far_tail_jb247
  refine ⟨min κM κF,A,C,lt_min hκM hκF,hA,hC,?_⟩
  intro κ hκ hκle d c hd hc
  obtain ⟨wM,hwM,hmoderate⟩ := hmoderate κ hκ (hκle.trans (min_le_left _ _)) d hd
  obtain ⟨wF,hwF,hfar⟩ := hfar κ hκ (hκle.trans (min_le_right _ _)) d hd
  obtain ⟨b,hb,wC,hwC,hclean⟩ := source_successful_tail_jb247 κ d c hκ hd hc
  obtain ⟨wScale,hwScale⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (d^2)))
  let w₀ := max (max wM wF) (max wC (max normalizationThreshold wScale))
  refine ⟨b,hb,w₀,hwM.trans_le ((le_max_left _ _).trans (le_max_left _ _)),?_⟩
  intro w hw ell B start hs hell hellB hB hlogB hcomp hr hi h199 h23 hcons hcut
  dsimp only
  intro M
  let S := (Real.log B)^2
  let N := sourceHorizon S B
  have hwM' : wM ≤ w := (le_trans (le_max_left _ _) (le_max_left _ _)).trans hw
  have hwF' : wF ≤ w := (le_trans (le_max_right _ _) (le_max_left _ _)).trans hw
  have hwC' : wC ≤ w := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hw
  have hnorm : normalizationThreshold ≤ w :=
    (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)).trans hw
  have hwScale' : wScale ≤ w :=
    (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)).trans hw
  have hscale := source_scale_bound (hwScale w hwScale') hlogB hcomp
  have hS0 : 0 ≤ S := sq_nonneg _
  have hS3 : 3 ≤ S := by dsimp [S] <;> nlinarith
  have hsS : start.ratio ≤ S := by linarith
  have hsize : B ≤ start.gap := by
    have he : start.cutoff = start.gap/start.ratio := hcons
    rw [hcut] at he
    have hh := (eq_div_iff (valid_pos hs).ne').mp he
    nlinarith
  have hsplit := actual_finite_tail_split hnorm hell hS0 hscale.1 hr hs hsS c (3*((M:ℝ)+1))
    (growingCutoff w) (mesh κ w) N
  have hinitK := source_initial_tail (w:=w) (ell:=ell) (S:=S) (K:=3*((M:ℝ)+1)) hc hB hsize hi h199 h23
  have hinitT := source_initial_tail (w:=w) (ell:=ell) (S:=S) (K:=growingCutoff w) hc hB hsize hi h199 h23
  have hsuccess := hclean w hwC' ell B start hs hell hB hlogB hcomp hr hi h199 h23 M
  have hfailed := hmoderate w hwM' ell B start hs hell hellB hB hlogB hcomp hr h23 hcons hcut c hc
  have hfarther := hfar w hwF' ell B start hell hellB hB hlogB hcomp hr hi h199 h23 hcons hcut c hc
  have hI : 0 ≤ initialBudget c B := by unfold initialBudget; have h0 := initialConstant_pos; positivity
  have hIadd : ENNReal.ofReal (initialBudget c B)+ENNReal.ofReal (initialBudget c B) =
      ENNReal.ofReal (2*initialBudget c B) := by
    rw [← ENNReal.ofReal_add hI hI]
    congr 1
    ring
  have hbound := add_le_add (add_le_add (add_le_add (add_le_add hinitK hinitT) hsuccess) hfailed) hfarther
  rw [hIadd] at hbound
  exact hsplit.trans hbound

end NumberTheoryLean.SourceTailBudget

end

section

namespace NumberTheoryLean.SourceUniformTail

open _root_.Set _root_.Filter _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeBinMembership
open PrimeExponentialTail SourceTailBudget InitialPrimeTail GrowingFarTail LowStateHorizon

theorem four_quarters {ε : ℝ} (hε : 0 ≤ ε) :
    ENNReal.ofReal (ε/4)+ENNReal.ofReal (ε/4)+ENNReal.ofReal (ε/4)+ENNReal.ofReal (ε/4) = ENNReal.ofReal ε := by
  have hq : 0 ≤ ε/4 := by positivity
  rw [← ENNReal.ofReal_add hq hq,← ENNReal.ofReal_add (by positivity) hq,
    ← ENNReal.ofReal_add (by positivity) hq]
  congr 1
  ring

theorem actual_uniform_inverse_tail (d c ε : ℝ) (hd : 0 < d) (hc : 0 < c) (hε : 0 < ε) :
    ∃ M₀ : ℕ,∃ B₀ w₀ : ℝ,0 < B₀ ∧ 1 < w₀ ∧
      ∀ M : ℕ,M₀ ≤ M → ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w →
      ∀ ell : ℝ,1 ≤ ell → ell ≤ B → Real.log B ≤ d*Real.log w →
      ∀ start : Node,start.side = .even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff = B →
        let S := (Real.log B)^2
        let N := sourceHorizon S B
        (∑ n ∈ range N,∫⁻ z,tailReward c (3*((M:ℝ)+1)) z ∂pathLaw w ell S start n) ≤ ENNReal.ofReal ε := by
  obtain ⟨κ₀,A,C,hκ₀,hA,hC,hsource⟩ := source_tail_budget
  let κ := κ₀/2
  have hκ : 0 < κ := by dsimp [κ] <;> positivity
  have hκle : κ ≤ κ₀ := by dsimp [κ] <;> linarith
  obtain ⟨b,hb,wP,hwP,hsource⟩ := hsource κ hκ hκle d c hd hc
  have hδ : 0 < ε/4 := by positivity
  obtain ⟨M₀,hM₀⟩ := eventually_atTop.mp (hb.eventually (eventually_le_nhds (ENNReal.ofReal_pos.mpr hδ)))
  have hinit : Tendsto (fun B : ℝ => 2*initialBudget c B) atTop (𝓝 0) := by
    simpa only [mul_zero] using (initialBudget_tendsto_zero hc).const_mul 2
  obtain ⟨Baux,hBaux⟩ := eventually_atTop.mp (hinit.eventually (eventually_le_nhds hδ))
  obtain ⟨wFail,hwFail⟩ := eventually_atTop.mp
    ((failureBudget_tendsto_zero A c hκ).eventually (eventually_le_nhds hδ))
  obtain ⟨wFar,hwFar⟩ := eventually_atTop.mp
    ((farBudget_tendsto_zero C d hc).eventually (eventually_le_nhds hδ))
  let B₀ := max (Real.exp 2) Baux
  let w₀ := max wP (max wFail wFar)
  refine ⟨M₀,B₀,w₀,(Real.exp_pos 2).trans_le (le_max_left _ _),hwP.trans_le (le_max_left _ _),?_⟩
  intro M hM B w hB hw ell hell hellB hcomp start hi h199 h23 hcons hcut
  dsimp only
  have hBexp : Real.exp 2 ≤ B := (le_max_left _ _).trans hB
  have hBpos : 0 < B := (Real.exp_pos 2).trans_le hBexp
  have hlogB : 2 ≤ Real.log B := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 2) hBexp
  have hs : Valid start.side start.ratio := by rw [hi]; change 198/100 ≤ start.ratio; linarith
  have hr : 0 < start.gap := by
    have he : start.cutoff = start.gap/start.ratio := hcons
    rw [hcut] at he
    have hh := (eq_div_iff (valid_pos hs).ne').mp he
    rw [← hh]
    exact mul_pos hBpos (valid_pos hs)
  have hbudget := hsource w ((le_max_left _ _).trans hw) ell B start hs hell hellB hBpos hlogB hcomp hr hi h199 h23 hcons hcut M
  have hI := ENNReal.ofReal_le_ofReal (hBaux B ((le_max_right _ _).trans hB))
  have hF := ENNReal.ofReal_le_ofReal (hwFail w ((le_trans (le_max_left _ _) (le_max_right _ _)).trans hw))
  have hG := ENNReal.ofReal_le_ofReal (hwFar w ((le_trans (le_max_right _ _) (le_max_right _ _)).trans hw))
  have hsum := add_le_add (add_le_add (add_le_add hI (hM₀ M hM)) hF) hG
  rw [four_quarters hε.le] at hsum
  exact hbudget.trans hsum

end NumberTheoryLean.SourceUniformTail

end

section

namespace NumberTheoryLean.ScaledOriginalTail

open _root_.Set _root_.Filter _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeBinMembership DerivativeWeights
open PrimeCompactWeights PrimeCorrectionFactor PrimeExponentialTail SourceUniformTail LowStateHorizon

theorem prefactorBound_pos : 0 < prefactorBound :=
  mul_pos (by norm_num) (weight_pos (by norm_num [Valid]))

theorem scaled_reward_prefactor {w ell S B c : ℝ} {start : Node}
    (hB : 0 ≤ B) (hr : 0 < start.gap) (hsize : B ≤ start.gap)
    (hs : Valid start.side start.ratio) (hi : start.side = .even) (h199 : 199/100 ≤ start.ratio)
    (h : History w ell S start) (hcorr : (1+epsilon w)^h.primes.length ≤ 2) :
    scaledWeight w B start (some h)*Real.exp (-c*h.node.gap) ≤
      prefactorBound*(h.node.gap^2*Real.exp (-c*h.node.gap)/weight h.node.side h.node.ratio) := by
  have hφ := weight_pos hs
  have hφg := weight_pos (terminal_valid hs h.admissible)
  have hφ0 : 0 < weight .even (199/100) := weight_pos (by norm_num [Valid])
  have hinit : weight start.side start.ratio ≤ weight .even (199/100) := by
    rw [hi]
    exact TwoStepDensityBounds.weight_antitone (by norm_num [Valid]) (hi ▸ hs) h199
  have hrat : B/start.gap ≤ 1 := (div_le_one hr).mpr hsize
  have hrat0 : 0 ≤ B/start.gap := div_nonneg hB hr.le
  have hrat2 : (B/start.gap)^2 ≤ 1 := by nlinarith
  have hcorr0 := pow_nonneg (normalizer_pos w).le h.primes.length
  have hcoef : ((B/start.gap)^2*(1+epsilon w)^h.primes.length)*weight start.side start.ratio ≤ prefactorBound := by
    have hh : (B/start.gap)^2*(1+epsilon w)^h.primes.length ≤ 2 :=
      (mul_le_mul hrat2 hcorr hcorr0 zero_le_one).trans_eq (one_mul 2)
    exact mul_le_mul hh hinit hφ.le (by norm_num)
  calc
    _ = (((B/start.gap)^2*(1+epsilon w)^h.primes.length)*weight start.side start.ratio)*
        (h.node.gap^2*Real.exp (-c*h.node.gap)/weight h.node.side h.node.ratio) := by
      unfold scaledWeight
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (by positivity)

theorem source_scaled_tail_envelope {d w ell B c K : ℝ} {start : Node}
    (hB : 0 < B) (hell : 1 ≤ ell) (hlogB : 2 ≤ Real.log B) (hcomp : Real.log B ≤ d*Real.log w)
    (hbudget : correctionBudget d w ≤ 1)
    (hi : start.side = .even) (h199 : 199/100 ≤ start.ratio) (h23 : start.ratio ≤ 23/10)
    (hcons : Consistent start) (hcut : start.cutoff = B)
    (z : ChainState w ell ((Real.log B)^2) start) :
    scaledTail c K w B start z ≤ ENNReal.ofReal prefactorBound*tailReward c K z := by
  have hs : Valid start.side start.ratio := by rw [hi]; change 198/100 ≤ start.ratio; linarith
  have he : B*start.ratio = start.gap := by
    have hh : start.cutoff = start.gap/start.ratio := hcons
    rw [hcut] at hh
    exact (eq_div_iff (valid_pos hs).ne').mp hh
  have hr : 0 < start.gap := by rw [← he]; exact mul_pos hB (valid_pos hs)
  have hsize : B ≤ start.gap := by nlinarith
  have hupper : start.gap ≤ (23/10:ℝ)*B := by nlinarith
  cases z with
  | none => simp [scaledTail,tailReward]
  | some h =>
    have hcorrection : (1+epsilon w)^h.primes.length ≤ 2 := by
      have hh := (history_correction hlogB hcomp hell hr hs hB hupper h).2
      linarith
    have hbound := scaled_reward_prefactor (c:=c) hB.le hr hsize hs hi h199 h hcorrection
    by_cases hh : K < h.node.gap
    · rw [scaledTail,tailReward,ite_eq_left hh,ite_eq_left hh,← ENNReal.ofReal_mul prefactorBound_pos.le]
      exact ENNReal.ofReal_le_ofReal hbound
    · simp [scaledTail,tailReward,hh]

theorem actual_uniform_scaled_tail_jb247_oai (d c ε : ℝ) (hd : 0 < d) (hc : 0 < c) (hε : 0 < ε) :
    ∃ M₀ : ℕ,∃ B₀ w₀ : ℝ,0 < B₀ ∧ 1 < w₀ ∧
      ∀ M : ℕ,M₀ ≤ M → ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w →
      ∀ ell : ℝ,1 ≤ ell → ell ≤ B → Real.log B ≤ d*Real.log w →
      ∀ start : Node,start.side = .even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff = B →
        let S := (Real.log B)^2
        let N := sourceHorizon S B
        (∑ n ∈ range N,∫⁻ z,scaledTail c (3*((M:ℝ)+1)) w B start z ∂pathLaw w ell S start n) ≤ ENNReal.ofReal ε := by
  have hD := prefactorBound_pos
  obtain ⟨M₀,BR,wR,hBR,hwR,hraw⟩ := actual_uniform_inverse_tail d c (ε/prefactorBound) hd hc (div_pos hε hD)
  obtain ⟨wCorr,hwCorr⟩ := eventually_atTop.mp
    ((correctionBudget_tendsto_zero d).eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1)))
  refine ⟨M₀,max BR (Real.exp 2),max wR wCorr,hBR.trans_le (le_max_left _ _),hwR.trans_le (le_max_left _ _),?_⟩
  intro M hM B w hB hw ell hell hellB hcomp start hi h199 h23 hcons hcut
  dsimp only
  let S := (Real.log B)^2
  let N := sourceHorizon S B
  have hBR' : BR ≤ B := (le_max_left _ _).trans hB
  have hBpos : 0 < B := hBR.trans_le hBR'
  have hlogB : 2 ≤ Real.log B := by
    have hh : Real.exp 2 ≤ B := (le_max_right _ _).trans hB
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 2) hh
  have hbudget := hwCorr w ((le_max_right _ _).trans hw)
  have hb := hraw M hM B w hBR' ((le_max_left _ _).trans hw) ell hell hellB hcomp start hi h199 h23 hcons hcut
  have hpoint := source_scaled_tail_envelope (c:=c) (K:=3*((M:ℝ)+1)) hBpos hell hlogB hcomp hbudget hi h199 h23 hcons hcut
  calc
    _ ≤ ∑ n ∈ range N,ENNReal.ofReal prefactorBound*(∫⁻ z,tailReward c (3*((M:ℝ)+1)) z ∂pathLaw w ell S start n) := by
      apply Finset.sum_le_sum
      intro n _hn
      calc
        _ ≤ ∫⁻ z,ENNReal.ofReal prefactorBound*tailReward c (3*((M:ℝ)+1)) z ∂pathLaw w ell S start n := lintegral_mono hpoint
        _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal prefactorBound*ENNReal.ofReal (ε/prefactorBound) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hb zero_le
    _ = _ := by
      rw [← ENNReal.ofReal_mul hD.le]
      congr 1
      field_simp

end NumberTheoryLean.ScaledOriginalTail

end

end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.NumberTheoryLean.ScaledOriginalTail.actual_uniform_scaled_tail_jb247_oai := @OAI.Erdos970.NumberTheoryLean.ScaledOriginalTail.actual_uniform_scaled_tail_jb247_oai
