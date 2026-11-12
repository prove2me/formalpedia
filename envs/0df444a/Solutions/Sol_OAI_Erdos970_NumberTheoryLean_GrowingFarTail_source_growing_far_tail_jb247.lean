-- Prove2me | solution 1 for OAI.Erdos970.NumberTheoryLean.GrowingFarTail.source_growing_far_tail_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:04:22.592198+00:00
-- url     : https://prove2.me/submissions/faca22b0-6d05-403a-a503-8f89ca9e82b3

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

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FiniteHistorySupport
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.FinitePathGeometry

open Set
open DerivativeWeights TransitionKernels

theorem minRatio_ge_sub_one (i : Side) (s : ℝ) : s - 1 ≤ minRatio i s := by
  cases i with
  | even => exact le_rfl
  | odd => exact le_max_right _ _

theorem nextGap_div_ratio {r t : ℝ} (ht : 0 < t) : nextGap r t / t = nextExponent r t := by
  unfold nextGap nextExponent
  field_simp

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
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
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

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_LowStateHorizon
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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

section

namespace NumberTheoryLean.PrimeRatioBins

open _root_.Erdos970.Set
open FinitePathGeometry PrimeTiltGeometry PrimeTiltBounds
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimeEndpoints

theorem bin_log_width_bounds {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b-a)/(b+1) ≤ Real.log (b+1)-Real.log (a+1) ∧
      Real.log (b+1)-Real.log (a+1) ≤ (b-a)/(a+1) := by
  have ha1 : 0 < a+1 := by linarith
  have hb1 : 0 < b+1 := by linarith
  have hq := div_pos hb1 ha1
  have hl := Real.one_sub_inv_le_log_of_pos hq
  have hu := Real.log_le_sub_one_of_pos hq
  rw [Real.log_div hb1.ne' ha1.ne'] at hl hu
  have heL : 1-((b+1)/(a+1))⁻¹ = (b-a)/(b+1) := by field_simp <;> ring
  have heU : (b+1)/(a+1)-1 = (b-a)/(a+1) := by field_simp <;> ring
  rw [heL] at hl
  rw [heU] at hu
  exact ⟨hl,hu⟩

end NumberTheoryLean.PrimeRatioBins

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

variable (w ell S : ℝ) (start : Node)

variable {w ell S : ℝ} {start : Node}

theorem pathLaw_isProbability (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell)
    (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
    (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S) (n : ℕ) :
    IsProbabilityMeasure (pathLaw w ell S start n) := by
  let := chain_isMarkov hw hell hS0 hS hr hs hsS
  unfold pathLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end NumberTheoryLean.PrimeKilledChain



namespace NumberTheoryLean.PrimeChainHorizon

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain LowStateHorizon

variable {w ell S : ℝ} {start : Node}

theorem stage_measurable (n : ℕ) : MeasurableSet {z : ChainState w ell S start | stage n z} := trivial

theorem next_stage (n : ℕ) (z : ChainState w ell S start) (hz : stage n z) :
    ∀ᵐ y ∂chain w ell S start z, stage (n+1) y := by
  classical
  cases z with
  | none =>
    rw [chain_none]
    exact (ae_dirac_iff (stage_measurable (n+1))).mpr trivial
  | some h =>
    have hlen : h.primes.length = n := hz
    apply ae_iff.mpr
    simp [chain_some, completedLaw, liveLaw, stage, History.append_primes, hlen]

theorem pathLaw_stage (n : ℕ) : ∀ᵐ z ∂pathLaw w ell S start n, stage n z := by
  induction n with
  | zero =>
    change ∀ᵐ z ∂Measure.dirac (some (History.empty : History w ell S start)), stage 0 z
    exact (ae_dirac_iff (stage_measurable 0)).mpr rfl
  | succ n ih =>
    have hp : (chain w ell S start)^(n+1) = (chain w ell S start) ∘ₖ ((chain w ell S start)^n) := pow_succ' _ _
    change ∀ᵐ z ∂((chain w ell S start)^(n+1)) (some History.empty), stage (n+1) z
    rw [hp]
    apply Kernel.ae_comp_of_ae_ae (stage_measurable (n+1))
    filter_upwards [ih] with z hz
    exact next_stage n z hz

end NumberTheoryLean.PrimeChainHorizon



namespace NumberTheoryLean.PrimeSideSupport

open _root_.Set _root_.MeasureTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open FinitePathGeometry PrimeTiltGeometry PrimeHistories PrimeKilledChain PrimeChainHorizon

theorem sideAfter_flip (i : Side) (n : ℕ) : sideAfter i.flip n = (sideAfter i n).flip := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sideAfter,ih]

theorem terminal_side_after (w : ℝ) (z : Node) (ps : List ℕ) :
    (terminal w z ps).side = sideAfter z.side ps.length := by
  induction ps generalizing z with
  | nil => rfl
  | cons p ps ih =>
    rw [terminal_cons,ih,List.length_cons,sideAfter]
    exact sideAfter_flip z.side ps.length

theorem regular_step {w ell S : ℝ} {z : Node} (hz : Regular z) {p : ℕ}
    (hp : p ∈ nodeChildren w ell S z) : Regular (step w z p) := by
  classical
  have hlo := (Finset.mem_filter.mp hp).2.2.2.1
  cases hi : z.side with
  | even =>
    change regularLower z.side ≤ z.ratio at hz
    rw [hi,regularLower] at hz
    change minRatio z.side z.ratio ≤ childRatio w z.gap p at hlo
    rw [hi,minRatio] at hlo
    change regularLower z.side.flip ≤ childRatio w z.gap p
    rw [hi,Side.flip,regularLower]
    linarith
  | odd =>
    change minRatio z.side z.ratio ≤ childRatio w z.gap p at hlo
    rw [hi,minRatio] at hlo
    change regularLower z.side.flip ≤ childRatio w z.gap p
    rw [hi,Side.flip,regularLower]
    exact (le_max_left _ _).trans hlo

theorem two_step_regular {w ell S : ℝ} {z : Node} {p q : ℕ}
    (hp : p ∈ nodeChildren w ell S z) (hq : q ∈ nodeChildren w ell S (step w z p)) :
    Regular (step w (step w z p) q) := by
  classical
  have hlo := (Finset.mem_filter.mp hp).2.2.2.1
  have hlo' := (Finset.mem_filter.mp hq).2.2.2.1
  change minRatio z.side.flip (childRatio w z.gap p) ≤ childRatio w (step w z p).gap q at hlo'
  change regularLower z.side.flip.flip ≤ childRatio w (step w z p).gap q
  cases hi : z.side with
  | even =>
    rw [Side.flip,Side.flip,regularLower]
    rw [hi,Side.flip,minRatio] at hlo'
    exact (le_max_left _ _).trans hlo'
  | odd =>
    rw [Side.flip,Side.flip,regularLower]
    change minRatio z.side z.ratio ≤ childRatio w z.gap p at hlo
    rw [hi,minRatio] at hlo
    rw [hi,Side.flip,minRatio] at hlo'
    linarith [le_max_left (2:ℝ) (z.ratio-1)]

theorem terminal_regular_of_regular {w ell S : ℝ} {z : Node} {ps : List ℕ}
    (hz : Regular z) (hp : allowed w ell S z ps) : Regular (terminal w z ps) := by
  induction ps generalizing z with
  | nil => exact hz
  | cons p ps ih =>
    rcases (allowed_cons w ell S z p ps).mp hp with ⟨hchild,hpath⟩
    exact ih (regular_step hz hchild) hpath

theorem terminal_regular {w ell S : ℝ} {z : Node} {ps : List ℕ}
    (hp : allowed w ell S z ps) (hlen : 2 ≤ ps.length) : Regular (terminal w z ps) := by
  cases ps with
  | nil => simp at hlen
  | cons p ps =>
    cases ps with
    | nil => simp at hlen
    | cons q qs =>
      rcases (allowed_cons w ell S z p (q::qs)).mp hp with ⟨hp,hrest⟩
      rcases (allowed_cons w ell S (step w z p) q qs).mp hrest with ⟨hq,hrest⟩
      change Regular (terminal w (step w (step w z p) q) qs)
      exact terminal_regular_of_regular (two_step_regular hp hq) hrest

theorem weak_step {w ell S : ℝ} {z : Node} (hz : Valid z.side z.ratio) {p : ℕ}
    (hp : p ∈ nodeChildren w ell S z) : WeakRegular (step w z p) := by
  classical
  have hlo := (Finset.mem_filter.mp hp).2.2.2.1
  change minRatio z.side z.ratio ≤ childRatio w z.gap p at hlo
  change weakLower z.side.flip ≤ childRatio w z.gap p
  cases hi : z.side with
  | even =>
    rw [hi,Valid] at hz
    rw [hi,minRatio] at hlo
    rw [Side.flip,weakLower]
    linarith
  | odd =>
    rw [hi,minRatio] at hlo
    rw [Side.flip,weakLower]
    exact (le_max_left _ _).trans hlo

theorem terminal_weak {w ell S : ℝ} {z : Node} {ps : List ℕ}
    (hz : Valid z.side z.ratio) (hp : allowed w ell S z ps) (hne : ps ≠ []) :
    WeakRegular (terminal w z ps) := by
  induction ps generalizing z with
  | nil => exact False.elim (hne rfl)
  | cons p ps ih =>
    rcases (allowed_cons w ell S z p ps).mp hp with ⟨hchild,hpath⟩
    cases ps with
    | nil => exact weak_step hz hchild
    | cons q qs => exact ih (child_valid hz hchild) hpath (by simp)

theorem pathLaw_regular {w ell S : ℝ} {start : Node} (n : ℕ) (hn : 2 ≤ n) :
    ∀ᵐ p ∂pathLaw w ell S start n, match p with
      | none => True
      | some h => Regular h.node := by
  filter_upwards [pathLaw_stage (w:=w) (ell:=ell) (S:=S) (start:=start) n] with p hp
  cases p with
  | none => trivial
  | some h =>
    have heq : h.primes.length = n := hp
    exact terminal_regular h.admissible (by omega)

theorem pathLaw_weak {w ell S : ℝ} {start : Node} (hs : Valid start.side start.ratio)
    (n : ℕ) (hn : 1 ≤ n) :
    ∀ᵐ p ∂pathLaw w ell S start n, match p with
      | none => True
      | some h => WeakRegular h.node := by
  filter_upwards [pathLaw_stage (w:=w) (ell:=ell) (S:=S) (start:=start) n] with p hp
  cases p with
  | none => trivial
  | some h =>
    have heq : h.primes.length = n := hp
    apply terminal_weak hs h.admissible
    intro he
    simp [he] at heq
    omega

theorem pathLaw_side {w ell S : ℝ} {start : Node} (hi : start.side = .even) (n : ℕ) :
    ∀ᵐ p ∂pathLaw w ell S start n, match p with
      | none => True
      | some h => h.node.side = sideAfter .even n := by
  filter_upwards [pathLaw_stage (w:=w) (ell:=ell) (S:=S) (start:=start) n] with p hp
  cases p with
  | none => trivial
  | some h =>
    have heq : h.primes.length = n := hp
    change (terminal w start h.primes).side = _
    rw [terminal_side_after,heq,hi]

end NumberTheoryLean.PrimeSideSupport



namespace NumberTheoryLean.PrimeGridGeometry

open _root_.Set _root_.Erdos970.Set
open FinitePathGeometry PrimeHistories PrimeSideSupport

theorem width_nonneg (m : ℕ) : 0 ≤ width m := by unfold width; positivity

theorem width_pos {m : ℕ} (hm : 1 ≤ m) : 0 < width m := by
  apply one_div_pos.mpr
  exact_mod_cast (show 0 < m by omega)

theorem point_succ (m j : ℕ) : point m (j+1) = point m j+width m := by
  simp only [point,width,Nat.cast_add,Nat.cast_one,add_div]

theorem threshold_le_point {m : ℕ} (hm : 1 ≤ m) (k j : ℕ) :
    (k:ℝ) ≤ point m j ↔ k*m ≤ j := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  rw [point,le_div_iff₀ hm0]
  exact_mod_cast Iff.rfl

theorem index_from_upper {m j k : ℕ} {t : ℝ} (hm : 1 ≤ m)
    (hkt : (k:ℝ) ≤ t) (ht : t < point m (j+1)) : k*m ≤ j := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hdiv : (k:ℝ) < ((j+1:ℕ):ℝ)/(m:ℝ) := hkt.trans_lt ht
  have hmul := (lt_div_iff₀ hm0).mp hdiv
  have hn : k*m < j+1 := by exact_mod_cast hmul
  omega

theorem finite_grid_cover {m J : ℕ} {t : ℝ} (hm : 1 ≤ m) (ht : 0 ≤ t)
    (hJ : t < point m (J+1)) : ∃ j ≤ J, t ∈ Ico (point m j) (point m (j+1)) := by
  let j := ⌊t*(m:ℝ)⌋₊
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have htm : 0 ≤ t*(m:ℝ) := mul_nonneg ht hm0.le
  have hlo := Nat.floor_le htm
  have hhi := Nat.lt_floor_add_one (t*(m:ℝ))
  have hbound : (j:ℝ) < ((J+1:ℕ):ℝ) := by
    have h := (lt_div_iff₀ hm0).mp hJ
    exact hlo.trans_lt h
  have hj : j ≤ J := by
    have hnat : j < J+1 := by exact_mod_cast hbound
    omega
  refine ⟨j,hj,?_⟩
  constructor
  · exact (div_le_iff₀ hm0).mpr hlo
  · apply (lt_div_iff₀ hm0).mpr
    simpa only [Nat.cast_add,Nat.cast_one] using hhi

theorem incoming_grid_end {m : ℕ} (hmN : 1 ≤ m) (j : ℕ) :
    point m (j+m+2) = point m j+1+2*width m := by
  have hm : (m:ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  unfold point width
  push_cast
  field_simp

theorem regular_bin_domain {m j : ℕ} {z : Node} (hm : 1 ≤ m) (hz : Regular z)
    (hbin : z.ratio ∈ Ico (point m j) (point m (j+1))) :
    lowerIndex m z.side ≤ j ∧ Valid z.side (point m j) := by
  cases hi : z.side with
  | even =>
    change regularLower z.side ≤ z.ratio at hz
    rw [hi,regularLower] at hz
    have hj := index_from_upper hm (k:=2) hz hbin.2
    have ht : (2:ℝ) ≤ point m j := by simpa only [Nat.cast_ofNat] using (threshold_le_point hm 2 j).mpr hj
    rw [lowerIndex,Valid]
    exact ⟨hj,by linarith⟩
  | odd =>
    change regularLower z.side ≤ z.ratio at hz
    rw [hi,regularLower] at hz
    have hj := index_from_upper hm (k:=1) (by simpa only [Nat.cast_one] using hz) hbin.2
    have ht : (1:ℝ) ≤ point m j := by simpa only [Nat.cast_one] using (threshold_le_point hm 1 j).mpr hj
    rw [lowerIndex,Valid]
    exact ⟨by simpa using hj,by linarith⟩

theorem weak_bin_domain {m j : ℕ} {z : Node} (hm : 1 ≤ m) (hsmall : width m ≤ 1/100)
    (hz : WeakRegular z) (hbin : z.ratio ∈ Ico (point m j) (point m (j+1))) :
    Valid z.side (point m j) := by
  cases hi : z.side with
  | even =>
    change weakLower z.side ≤ z.ratio at hz
    rw [hi,weakLower] at hz
    have hj := index_from_upper hm (k:=2) hz hbin.2
    have ht : (2:ℝ) ≤ point m j := by simpa only [Nat.cast_ofNat] using (threshold_le_point hm 2 j).mpr hj
    rw [Valid]
    linarith
  | odd =>
    change weakLower z.side ≤ z.ratio at hz
    rw [hi,weakLower] at hz
    have ht := hbin.2
    rw [point_succ] at ht
    rw [Valid]
    linarith

end NumberTheoryLean.PrimeGridGeometry


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeCompactWeights
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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

namespace NumberTheoryLean.ActualPrimeBins

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeTiltGeometry PrimeTiltBounds PrimeHistories PrimeKilledChain
open PrimeBinMembership NormalizedPrimeBins PrimeRatioBins

variable {w ell S : ℝ} {start : Node}

theorem mem_liveBin_some (h : History w ell S start) (a b : ℝ) :
    some h ∈ liveBin a b ↔ a ≤ h.node.ratio ∧ h.node.ratio < b := Iff.rfl

theorem not_mem_liveBin_none (a b : ℝ) :
    (none : ChainState w ell S start) ∉ liveBin a b := by
  change ¬False
  exact not_false

theorem chain_live_bin_formula (h : History w ell S start) (a b : ℝ) :
    chain w ell S start (some h) (liveBin a b) =
      ∑ p ∈ nodeChildren w ell S h.node,
        if a ≤ childRatio w h.node.gap p ∧ childRatio w h.node.gap p < b then childProbability w ell S start h p else 0 := by
  classical
  simp only [chain_some, completedLaw, Measure.add_apply, liveLaw, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul, Measure.dirac_apply, Set.indicator, mem_liveBin_some, not_mem_liveBin_none, History.append_node, step,
    Pi.one_apply, mul_ite, mul_one, mul_zero, ite_false, if_false, add_zero]
  exact Finset.sum_attach _ (fun p : ℕ =>
    if a ≤ childRatio w h.node.gap p ∧ childRatio w h.node.gap p < b then childProbability w ell S start h p else 0)

end NumberTheoryLean.ActualPrimeBins

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_RetainedIntervalUpper
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.OAI.Erdos970.NumberTheoryLean.ReferenceBenchmarkDecay.benchmark_even_below_two
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.RetainedIntervalUpper

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeTiltGeometry PrimeTiltBounds PrimeTiltMonotone
open PrimeCumulativeBound PrimeRatioBins ContinuousRatioBins
open PrimeHistories PrimeKilledChain ContinuousKilledBins FinitePathMeasures
open LowStateHorizon ErdosPrimeInputs.HarmonicPrimeMeasure

theorem retained_subset_closed {w ell S s r cap a b : ℝ} {i : Side} {closed : Bool}
    (hw : 1 < w) (ha : 0 < a) (hab : a ≤ b) :
    retainedInterval w ell S i s r cap closed a b ⊆ closedBin w r a b := by
  classical
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hchild,hat,htb⟩
  have hprime := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hchild).1).2
  have hint := (closed_interval_iff (r:=r) ha hab (PrimeRatioBins.primeExponent_pos hw hprime)).mp ⟨hat,htb⟩
  apply Finset.mem_filter.mpr
  refine ⟨Nat.mem_primesLE.mpr ⟨?_,hprime⟩,hat,htb⟩
  have hp0 : (0:ℝ) < p := by exact_mod_cast hprime.pos
  have hreal : (p:ℝ) ≤ w^(r/(a+1)) := (exponent_le_iff hw hp0).mp hint.2
  exact (Nat.le_floor_iff (Real.rpow_pos_of_pos (by linarith : 0 < w) _).le).mpr hreal

theorem short_interval_lower_exponent {w ell S s r cap a b : ℝ} {i : Side} {closed : Bool}
    (hell : 1 ≤ ell) (hs : Valid i s) (ha : 0 < a) (hab : a ≤ b) (hwidth : b-a ≤ 1)
    (hne : (retainedInterval w ell S i s r cap closed a b).Nonempty) :
    (1/2:ℝ) ≤ r/(b+1) := by
  classical
  obtain ⟨p,hp⟩ := hne
  rcases Finset.mem_filter.mp hp with ⟨hchild,hat,htb⟩
  have ht0 := valid_pos (child_valid hs hchild)
  have hx : 1 < primeExponent w p := hell.trans_lt (Finset.mem_filter.mp hchild).2.1
  have hmul : (childRatio w r p+1)*primeExponent w p = r := by
    unfold childRatio
    field_simp
    ring
  have hrgt : childRatio w r p+1 < r := by nlinarith
  apply (le_div_iff₀ (by linarith : 0 < b+1)).mpr
  nlinarith

theorem closed_prime_error : ∃ c C w₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ r a b : ℝ, 0 < r → 0 < a → a ≤ b → 1/2 ≤ r/(b+1) →
      |closedMass w r a b-(Real.log (b+1)-Real.log (a+1))| ≤
        C*Real.exp (-c*Real.sqrt ((1/2:ℝ)*Real.log w)) := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,hbound⟩ := harmonic_prime_measure
  refine ⟨c,C,w₀,hc,hC,hw₀,?_⟩
  intro w hw r a b hr ha hab hlow
  have hw1 := hw₀.trans_le hw
  have hend : r/(b+1) ≤ r/(a+1) := div_le_div_of_nonneg_left hr.le (by linarith) (by linarith)
  have h := hbound w hw (r/(b+1)) (r/(a+1)) hlow hend true true
  rw [← closedMass_eq_harmonic hw1 ha hab,bin_log_width hr ha hab] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hlow (Real.log_pos hw1).le)) (by linarith)

end NumberTheoryLean.RetainedIntervalUpper


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_ConditionalPrimeBins
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.OAI.Erdos970.NumberTheoryLean.ReferenceBenchmarkDecay.benchmark_even_below_two
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.PrimeCompletedIntervalUpper

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeTiltGeometry PrimeHistories PrimeKilledChain
open RetainedIntervalUpper

variable {w ell S : ℝ} {start : Node}

theorem mem_closedLiveBin_some (h : History w ell S start) (a b : ℝ) :
    some h ∈ closedLiveBin a b ↔ a ≤ h.node.ratio ∧ h.node.ratio ≤ b := Iff.rfl

theorem not_mem_closedLiveBin_none (a b : ℝ) :
    (none : ChainState w ell S start) ∉ closedLiveBin a b := by
  change ¬False
  exact not_false

theorem chain_closedBin_formula (h : History w ell S start) (a b : ℝ) :
    chain w ell S start (some h) (closedLiveBin a b) =
      ∑ p ∈ nodeChildren w ell S h.node,
        if a ≤ childRatio w h.node.gap p ∧ childRatio w h.node.gap p ≤ b
        then childProbability w ell S start h p else 0 := by
  classical
  simp only [chain_some,completedLaw,Measure.add_apply,liveLaw,Measure.finsetSum_apply,
    Measure.smul_apply,smul_eq_mul,Measure.dirac_apply,Set.indicator,mem_closedLiveBin_some,
    not_mem_closedLiveBin_none,History.append_node,step,Pi.one_apply,mul_ite,mul_one,mul_zero,ite_false, if_false,add_zero]
  exact Finset.sum_attach _ (fun p : ℕ =>
    if a ≤ childRatio w h.node.gap p ∧ childRatio w h.node.gap p ≤ b
    then childProbability w ell S start h p else 0)

theorem chain_interval_le_tilt (h : History w ell S start) (hs : Valid h.node.side h.node.ratio) (a b : ℝ) :
    chain w ell S start (some h) (closedLiveBin a b) ≤
      ENNReal.ofReal (retainedIntervalTilt w ell S h.node.side h.node.ratio h.node.gap h.node.cutoff h.node.closed a b) := by
  classical
  rw [chain_closedBin_formula,← Finset.sum_filter]
  change (∑ p ∈ retainedInterval w ell S h.node.side h.node.ratio h.node.gap h.node.cutoff h.node.closed a b,
    childProbability w ell S start h p) ≤ _
  unfold retainedIntervalTilt
  rw [ENNReal.ofReal_sum_of_nonneg
    (s := retainedInterval w ell S h.node.side h.node.ratio h.node.gap h.node.cutoff h.node.closed a b)
    (f := fun p => primeTilt w h.node.gap h.node.side h.node.ratio p)
    (fun p hp => primeTilt_nonneg hs (Finset.mem_filter.mp hp).1)]
  apply Finset.sum_le_sum
  intro p hp
  apply ENNReal.ofReal_le_ofReal
  exact div_le_self (primeTilt_nonneg hs (Finset.mem_filter.mp hp).1) (by linarith [epsilon_pos w])

end NumberTheoryLean.PrimeCompletedIntervalUpper



namespace NumberTheoryLean.ConditionalPrimeBins

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeTiltGeometry PrimeTiltBounds PrimeTiltMonotone
open PrimeCumulativeBound PrimeRatioBins RetainedIntervalUpper PrimeCompletedIntervalUpper
open PrimeHistories PrimeKilledChain DerivativeWeights WeightFutureIntegrals

theorem multiplier_valid_antitone {i : Side} {s a t : ℝ} (hs : Valid i s)
    (ha : Valid i.flip a) (ht : Valid i.flip t) (hat : a ≤ t) :
    multiplier i s t ≤ multiplier i s a := by
  have ha0 := valid_pos ha
  have ht0 := valid_pos ht
  have hphi := TwoStepDensityBounds.weight_antitone ha ht hat
  have hq : (t+1)/t ≤ (a+1)/a := by
    rw [add_div,div_self ht0.ne',add_div,div_self ha0.ne']
    exact add_le_add_right (one_div_le_one_div_of_le ha0 hat) 1
  have hqt : 0 ≤ (t+1)/t := by positivity
  have hqa : 0 ≤ (a+1)/a := by positivity
  have hsq : ((t+1)/t)^2 ≤ ((a+1)/a)^2 := by nlinarith
  unfold multiplier
  apply div_le_div_of_nonneg_right _ (weight_pos hs).le
  exact mul_le_mul hsq hphi (weight_pos ht).le (sq_nonneg _)

theorem retained_tilt_le_multiplier {w ell S s r cap a b : ℝ} {i : Side} {closed : Bool}
    (hw : 1 < w) (hs : Valid i s) (ha : Valid i.flip a) (hab : a ≤ b) :
    retainedIntervalTilt w ell S i s r cap closed a b ≤ multiplier i s a*closedMass w r a b := by
  classical
  let A := retainedInterval w ell S i s r cap closed a b
  have hraw : (∑ p ∈ A,(p:ℝ)⁻¹) ≤ closedMass w r a b :=
    Finset.sum_le_sum_of_subset_of_nonneg (retained_subset_closed hw (valid_pos ha) hab)
      (fun p _ _ => inv_nonneg.mpr (Nat.cast_nonneg p))
  calc
    _ ≤ multiplier i s a*(∑ p ∈ A,(p:ℝ)⁻¹) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hchild,hat,_⟩
      have hm := multiplier_valid_antitone hs ha (child_valid hs hchild) hat
      rw [primeTilt_eq_multiplier,mul_comm (multiplier i s a)]
      exact mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr (Nat.cast_nonneg p))
    _ ≤ _ := mul_le_mul_of_nonneg_left hraw (multiplier_pos hs ha).le

theorem retained_conditional_bin : ∃ c C w₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ ell S : ℝ, ∀ i : Side, ∀ s r cap a h : ℝ, ∀ closed : Bool,
      1 ≤ ell → 0 < r → Valid i s → Valid i.flip a → 0 < h → h ≤ 1 →
      retainedIntervalTilt w ell S i s r cap closed a (a+h) ≤
        (1+C*(a+1)*Real.exp (-c*Real.sqrt ((1/2:ℝ)*Real.log w))/h)*
          h*W a*(weight i.flip a/weight i s) := by
  classical
  obtain ⟨c,C,w₀,hc,hC,hw₀,herror⟩ := closed_prime_error
  refine ⟨c,C,w₀,hc,hC,hw₀,?_⟩
  intro w hw ell S i s r cap a h closed hell hr hs ha hh hh1
  have ha0 := valid_pos ha
  have hma := (multiplier_pos hs ha).le
  let A := retainedInterval w ell S i s r cap closed a (a+h)
  let e := Real.exp (-c*Real.sqrt ((1/2:ℝ)*Real.log w))
  by_cases hne : A.Nonempty
  · have hlow := short_interval_lower_exponent hell hs ha0 (by linarith : a ≤ a+h)
      (by linarith : a+h-a ≤ 1) hne
    have herr := herror w hw r a (a+h) hr ha0 (by linarith) hlow
    have hlog := (bin_log_width_bounds ha0 (show a ≤ a+h by linarith)).2
    have hraw : closedMass w r a (a+h) ≤ h/(a+1)+C*e := by
      rw [add_sub_cancel_left] at hlog
      linarith [(abs_le.mp herr).2]
    calc
      _ ≤ multiplier i s a*closedMass w r a (a+h) := retained_tilt_le_multiplier (hw₀.trans_le hw) hs ha (by linarith)
      _ ≤ multiplier i s a*(h/(a+1)+C*e) := mul_le_mul_of_nonneg_left hraw hma
      _ = _ := by
        unfold multiplier W
        dsimp only [e]
        field_simp [hh.ne',ha0.ne',(weight_pos hs).ne']
  · have hempty : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    change (∑ p ∈ A,_) ≤ _
    rw [hempty,Finset.sum_empty]
    have hW := (W_pos ha0).le
    have hratio := (div_pos (weight_pos ha) (weight_pos hs)).le
    positivity

variable {w ell S : ℝ} {start : Node}

theorem actual_conditional_bin : ∃ c C w₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ ell S : ℝ, ∀ start : Node,
      1 ≤ ell → 0 < start.gap → Valid start.side start.ratio →
      ∀ g : History w ell S start, ∀ a h : ℝ, Valid g.node.side.flip a → 0 < h → h ≤ 1 →
      chain w ell S start (some g) (ActualPrimeBins.liveBin a (a+h)) ≤
        ENNReal.ofReal ((1+C*(a+1)*Real.exp (-c*Real.sqrt ((1/2:ℝ)*Real.log w))/h)*
          h*W a*(weight g.node.side.flip a/weight g.node.side g.node.ratio)) := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,hbound⟩ := retained_conditional_bin
  refine ⟨c,C,w₀,hc,hC,hw₀,?_⟩
  intro w hw ell S start hell hr hs g a h ha hh hh1
  have hv := terminal_valid hs g.admissible
  have hg := terminal_gap_positive (show 0 ≤ ell by linarith) hr hs g.admissible
  have hsubset : ActualPrimeBins.liveBin a (a+h) ⊆ (closedLiveBin (w:=w) (ell:=ell) (S:=S) (start:=start) a (a+h)) := by
    intro p hp
    cases p with
    | none => exact False.elim hp
    | some p => exact ⟨hp.1,hp.2.le⟩
  exact (measure_mono hsubset).trans ((chain_interval_le_tilt g hv a (a+h)).trans
    (ENNReal.ofReal_le_ofReal (hbound w hw ell S g.node.side g.node.ratio g.node.gap g.node.cutoff a h g.node.closed
      hell hg hv ha hh hh1)))

end NumberTheoryLean.ConditionalPrimeBins


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

theorem mesh_pos (κ w : ℝ) : 0 < mesh κ w := by
  apply one_div_pos.mpr
  exact_mod_cast Nat.ceil_pos.mpr (Real.exp_pos (κ*Real.sqrt (Real.log w)))

theorem mesh_upper (κ w : ℝ) : mesh κ w ≤ Real.exp (-κ*Real.sqrt (Real.log w)) := by
  have h := one_div_le_one_div_of_le (Real.exp_pos (κ*Real.sqrt (Real.log w)))
    (Nat.le_ceil (Real.exp (κ*Real.sqrt (Real.log w))))
  have he : 1/Real.exp (κ*Real.sqrt (Real.log w)) = Real.exp (-κ*Real.sqrt (Real.log w)) := by
    rw [one_div,← Real.exp_neg]
    congr 1
    ring
  exact h.trans_eq he

theorem mesh_reciprocal (κ w : ℝ) : 1/mesh κ w = (⌈Real.exp (κ*Real.sqrt (Real.log w))⌉₊:ℝ) := by
  unfold mesh
  simp

theorem reciprocal_upper {κ : ℝ} (hκ : 0 ≤ κ) (w : ℝ) :
    1/mesh κ w ≤ 2*Real.exp (κ*Real.sqrt (Real.log w)) := by
  rw [mesh_reciprocal]
  have hc := Nat.ceil_lt_add_one (Real.exp_pos (κ*Real.sqrt (Real.log w))).le
  have he : 1 ≤ Real.exp (κ*Real.sqrt (Real.log w)) := Real.one_le_exp_iff.mpr (by positivity)
  linarith

theorem mesh_le_one {κ : ℝ} (hκ : 0 ≤ κ) (w : ℝ) : mesh κ w ≤ 1 := by
  apply (mesh_upper κ w).trans
  apply Real.exp_le_one_iff.mpr
  nlinarith [Real.sqrt_nonneg (Real.log w)]

theorem half_sqrt_lower {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x/2 ≤ Real.sqrt ((1/2:ℝ)*x) := by
  apply (sq_le_sq₀ (by positivity : 0 ≤ Real.sqrt x/2) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (by positivity : 0 ≤ (1/2:ℝ)*x)]
  nlinarith [Real.sq_sqrt hx]

theorem prime_error_dominated {c κ w : ℝ} (hκ : 0 ≤ κ) (hc : 2*κ ≤ c) (hw : 0 ≤ Real.log w) :
    Real.exp (-c*Real.sqrt ((1/2:ℝ)*Real.log w)) ≤ Real.exp (-κ*Real.sqrt (Real.log w)) := by
  have hc0 : 0 ≤ c := by linarith
  have hhalf := half_sqrt_lower hw
  have hmul := mul_le_mul_of_nonneg_left hhalf hc0
  have hcmp := mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg (Real.log w))
  apply Real.exp_le_exp.mpr
  nlinarith

theorem prime_error_over_mesh {c κ w : ℝ} (hκ : 0 ≤ κ) (hc : 4*κ ≤ c) (hw : 0 ≤ Real.log w) :
    Real.exp (-c*Real.sqrt ((1/2:ℝ)*Real.log w))/mesh κ w ≤
      2*Real.exp (-κ*Real.sqrt (Real.log w)) := by
  have hp := prime_error_dominated (c:=c) (κ:=2*κ) (by positivity) (by linarith) hw
  have hr := reciprocal_upper hκ w
  have hm := mesh_pos κ w
  calc
    _ = Real.exp (-c*Real.sqrt ((1/2:ℝ)*Real.log w))*(1/mesh κ w) := by ring
    _ ≤ Real.exp (-(2*κ)*Real.sqrt (Real.log w))*(2*Real.exp (κ*Real.sqrt (Real.log w))) :=
      mul_le_mul hp hr (by positivity) (Real.exp_pos _).le
    _ = _ := by
      rw [show Real.exp (-(2*κ)*Real.sqrt (Real.log w))*(2*Real.exp (κ*Real.sqrt (Real.log w))) =
        2*(Real.exp (-(2*κ)*Real.sqrt (Real.log w))*Real.exp (κ*Real.sqrt (Real.log w))) by ring,
        ← Real.exp_add]
      congr 2
      ring

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

theorem log_power_exp_absorption (C : ℝ) (n : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ w : ℝ in atTop, C*(Real.log w)^n*Real.exp (-c*Real.sqrt (Real.log w)) ≤
      Real.exp (-(c/2)*Real.sqrt (Real.log w)) := by
  have ht := log_power_exp_tendsto C n (show 0 < c/2 by positivity)
  filter_upwards [ht.eventually (eventually_lt_nhds (by norm_num : (0:ℝ) < 1))] with w hw
  calc
    _ = (C*(Real.log w)^n*Real.exp (-(c/2)*Real.sqrt (Real.log w)))*
        Real.exp (-(c/2)*Real.sqrt (Real.log w)) := by
      rw [show -c*Real.sqrt (Real.log w) = -(c/2)*Real.sqrt (Real.log w)+-(c/2)*Real.sqrt (Real.log w) by ring,
        Real.exp_add]
      ring
    _ ≤ 1*Real.exp (-(c/2)*Real.sqrt (Real.log w)) := mul_le_mul_of_nonneg_right hw.le (Real.exp_pos _).le
    _ = _ := one_mul _

theorem exp_increment {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : Real.exp x-1 ≤ 3*x := by
  have h := Real.abs_exp_sub_one_le (x:=x) (by rw [abs_of_nonneg hx]; exact hx1)
  rw [abs_of_nonneg hx] at h
  linarith [le_abs_self (Real.exp x-1)]

end NumberTheoryLean.ExponentialMesh

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_HorizonMeshSmallness
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.HorizonMeshSmallness

open _root_.Set _root_.Filter
open scoped Topology
open UniformFailureBudget ExponentialMesh

theorem horizon_mesh_smallness {A D κ : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D) (hκ : 0 < κ) :
    ∀ᶠ w : ℝ in atTop, ∀ S : ℝ, 0 ≤ S → S ≤ (Real.log w)^3 → ∀ N : ℕ,
      (N:ℝ) ≤ A*(Real.log w)^3 →
      2*mesh κ w ≤ 1 ∧ 4*(N:ℝ)*mesh κ w ≤ 1 ∧ D*(1+S)^3*mesh κ w ≤ 1 ∧
        upperDisplacement S (mesh κ w) N+mesh κ w ≤ 1 := by
  filter_upwards [log_power_exp_absorption 2 0 hκ,
    log_power_exp_absorption (4*A) 3 hκ,
    log_power_exp_absorption (8*D) 9 hκ,
    log_power_exp_absorption (24*A+1) 6 hκ,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with w htwo hclockB hparentB hupperB hlog
  intro S hS hSP N hNP
  let x := Real.log w
  let e := Real.exp (-κ*Real.sqrt (Real.log w))
  let τ := mesh κ w
  have hx : 1 ≤ x := hlog
  have hx0 : 0 ≤ x := by linarith
  have hx3 : 1 ≤ x^3 := one_le_pow₀ hx
  have hx6 : 1 ≤ x^6 := one_le_pow₀ hx
  have hSp : S+1 ≤ 2*x^3 := by change S ≤ x^3 at hSP; linarith
  have he : 0 ≤ e := (Real.exp_pos _).le
  have hτ : 0 < τ := mesh_pos κ w
  have hτe : τ ≤ e := mesh_upper κ w
  have hsmall : Real.exp (-(κ/2)*Real.sqrt (Real.log w)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith [Real.sqrt_nonneg (Real.log w)]
  have htwo' : 2*τ ≤ 1 := by
    have ht : 2*e ≤ Real.exp (-(κ/2)*Real.sqrt (Real.log w)) := by
      simpa only [pow_zero,mul_one] using htwo
    exact (mul_le_mul_of_nonneg_left hτe (by norm_num)).trans (ht.trans hsmall)
  have hclock : 4*(N:ℝ)*τ ≤ 1 := by
    calc
      _ ≤ (4*(A*x^3))*e := mul_le_mul (by nlinarith : 4*(N:ℝ) ≤ 4*(A*x^3)) hτe hτ.le (by positivity)
      _ = (4*A)*x^3*e := by ring
      _ ≤ _ := hclockB.trans hsmall
  have hparent : D*(1+S)^3*τ ≤ 1 := by
    calc
      _ ≤ (D*(2*x^3)^3)*e := mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith : 1+S ≤ 2*x^3) 3) hD)
        hτe hτ.le (by positivity)
      _ = (8*D)*x^9*e := by ring
      _ ≤ _ := hparentB.trans hsmall
  have hU : upperDisplacement S τ N ≤ 24*A*x^6*e := by
    have hexp := exp_increment (show 0 ≤ 4*(N:ℝ)*τ by positivity) hclock
    have hNmul : 12*(N:ℝ)*τ ≤ 12*(A*x^3)*e :=
      mul_le_mul (by nlinarith : 12*(N:ℝ) ≤ 12*(A*x^3)) hτe hτ.le (by positivity)
    calc
      _ ≤ (S+1)*(12*(N:ℝ)*τ) := by
        unfold upperDisplacement
        apply mul_le_mul_of_nonneg_left _ (by linarith : 0 ≤ S+1)
        nlinarith
      _ ≤ (2*x^3)*(12*(A*x^3)*e) := mul_le_mul hSp hNmul (by positivity) (by positivity)
      _ = _ := by ring
  have he6 : e ≤ x^6*e := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hx6 he
  have hUpper : upperDisplacement S τ N+τ ≤ 1 := by
    calc
      _ ≤ (24*A+1)*x^6*e := by nlinarith
      _ ≤ _ := hupperB.trans hsmall
  exact ⟨htwo',hclock,hparent,hUpper⟩

end NumberTheoryLean.HorizonMeshSmallness

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_MarginalGrowth
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.MarginalGrowth

open _root_.Set _root_.Filter
open scoped Topology
open ExponentialMesh

theorem factor_pos (L κ w S : ℝ) : 0 < factor L κ w S := by
  have hm := mesh_pos κ w
  unfold factor
  positivity

theorem factor_exp_upper (L κ w S : ℝ) : factor L κ w S ≤
    Real.exp (Real.exp (-(κ/2)*Real.sqrt (Real.log w))+L*(1+S)^3*mesh κ w+20*mesh κ w) := by
  have hm := mesh_pos κ w
  have h1 : 1+Real.exp (-(κ/2)*Real.sqrt (Real.log w)) ≤ Real.exp (Real.exp (-(κ/2)*Real.sqrt (Real.log w))) := by
    simpa only [add_comm] using Real.add_one_le_exp (Real.exp (-(κ/2)*Real.sqrt (Real.log w)))
  have h2 : 1+20*mesh κ w ≤ Real.exp (20*mesh κ w) := by
    simpa only [add_comm] using Real.add_one_le_exp (20*mesh κ w)
  unfold factor
  rw [Real.exp_add,Real.exp_add]
  exact mul_le_mul (mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le) h2 (by positivity) (by positivity)

theorem factor_power_bounded {A L κ : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L) (hκ : 0 < κ) :
    ∀ᶠ w : ℝ in atTop, ∀ S : ℝ, 0 ≤ S → S ≤ (Real.log w)^3 → ∀ n : ℕ,
      (n:ℝ) ≤ A*(Real.log w)^3 → (factor L κ w S)^n ≤ 2 := by
  have ht := log_power_exp_tendsto (A*(21+8*L)) 12 (show 0 < κ/2 by positivity)
  filter_upwards [ht.eventually (eventually_lt_nhds (Real.log_pos (by norm_num : (1:ℝ) < 2))),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with w hsmall hlog
  intro S hS hSP n hn
  let e := Real.exp (-(κ/2)*Real.sqrt (Real.log w))
  let τ := mesh κ w
  let a := e+L*(1+S)^3*τ+20*τ
  have hτ : 0 < τ := mesh_pos κ w
  have he : 0 ≤ e := (Real.exp_pos _).le
  have hτe : τ ≤ e := by
    apply (mesh_upper κ w).trans
    apply Real.exp_le_exp.mpr
    nlinarith [Real.sqrt_nonneg (Real.log w)]
  have hp3 : 1 ≤ (Real.log w)^3 := one_le_pow₀ hlog
  have hp9 : 1 ≤ (Real.log w)^9 := one_le_pow₀ hlog
  have he9 : e ≤ (Real.log w)^9*e := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hp9 he
  have hSp : 1+S ≤ 2*(Real.log w)^3 := by linarith
  have hmid : L*(1+S)^3*τ ≤ 8*L*(Real.log w)^9*e := by
    calc
      _ ≤ (L*(2*(Real.log w)^3)^3)*e := mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hSp 3) hL) hτe hτ.le (by positivity)
      _ = _ := by ring
  have ha0 : 0 ≤ a := by dsimp [a] <;> positivity
  have ha : a ≤ (21+8*L)*(Real.log w)^9*e := by dsimp [a] <;> nlinarith
  have hna : (n:ℝ)*a ≤ (A*(21+8*L))*(Real.log w)^12*e := by
    calc
      _ ≤ (A*(Real.log w)^3)*((21+8*L)*(Real.log w)^9*e) := mul_le_mul hn ha ha0 (by positivity)
      _ = _ := by ring
  have hpow := pow_le_pow_left₀ (factor_pos L κ w S).le (factor_exp_upper L κ w S) n
  rw [← Real.exp_nat_mul] at hpow
  calc
    _ ≤ Real.exp ((n:ℝ)*a) := hpow
    _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr (hna.trans hsmall.le)
    _ = _ := Real.exp_log (by norm_num)

end NumberTheoryLean.MarginalGrowth

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_MeshStationary
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped BigOperators

namespace Erdos970Dependency.MeshStationary

theorem mesh_nonneg (m : ℕ) : 0 ≤ mesh m := by unfold mesh; positivity

theorem mesh_le_one (m : ℕ) (hm : 1 ≤ m) : mesh m ≤ 1 := by
  have h : (0 : ℝ) < m := by exact_mod_cast (show 0 < m from hm)
  exact (div_le_one h).mpr (by exact_mod_cast hm)

theorem mesh_mul (m : ℕ) (hm : 1 ≤ m) : (m : ℝ)*mesh m = 1 := by
  have h : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (show 0 < m from hm))
  simp [mesh,h]

theorem point_ge_one (m k : ℕ) (hm : 1 ≤ m) (hkm : m ≤ k) : 1 ≤ point m k := by
  have h := mul_le_mul_of_nonneg_right (show (m : ℝ) ≤ k by exact_mod_cast hkm) (mesh_nonneg m)
  rw [mesh_mul m hm] at h
  exact h

theorem point_ge_two (m j : ℕ) (hm : 1 ≤ m) (hj : 2*m ≤ j) : 2 ≤ point m j := by
  have h := mul_le_mul_of_nonneg_right (show (2 : ℝ)*m ≤ j by exact_mod_cast hj) (mesh_nonneg m)
  rw [mul_assoc,mesh_mul m hm,mul_one] at h
  exact h

theorem point_nonneg (m k : ℕ) : 0 ≤ point m k :=
  mul_nonneg (Nat.cast_nonneg _) (mesh_nonneg _)

theorem point_succ (m k : ℕ) : point m (k+1) = point m k+mesh m := by
  unfold point
  push_cast
  ring

theorem weight_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ weight u := by unfold weight; positivity

theorem weight_le_two {u : ℝ} (hu : 1 ≤ u) : weight u ≤ 2 := by
  unfold weight
  apply (div_le_iff₀ (by positivity : 0 < u^2)).mpr
  nlinarith [sq_nonneg (u-1)]

theorem weight_cost_le_twenty {t : ℝ} (ht : 2 ≤ t) : weight t*(6*t+14) ≤ 20 := by
  calc
    _ = ((t+1)*(6*t+14))/t^2 := by unfold weight; ring
    _ ≤ _ := (div_le_iff₀ (by positivity : 0 < t^2)).mpr (by nlinarith [sq_nonneg (t-2)])

theorem reciprocal_drop_le {u h : ℝ} (hu : 0 < u) (hh : 0 ≤ h) :
    1/u-1/(u+h) ≤ h/u^2 := by
  have hup : 0 < u+h := by linarith
  calc
    _ = h/(u*(u+h)) := by field_simp <;> ring
    _ ≤ _ := div_le_div_of_nonneg_left hh (by positivity) (by nlinarith)

theorem reciprocal_telescope (m lo hi : ℕ) (hlohi : lo ≤ hi) :
    (∑ k ∈ Finset.Icc lo hi, ((1 : ℝ) / point m k - (1 : ℝ) / point m (k+1))) =
      (1 : ℝ) / point m lo - (1 : ℝ) / point m (hi+1) := by
  simpa only [neg_sub_neg] using!
    Finset.sum_Icc_sub hlohi (fun k => -(1/point m k))

theorem even_row_count (m j : ℕ) (hm : 1 ≤ m) (hj : m ≤ j) :
    mesh m * ((Finset.Icc (2*m) (j+m+1)).card : ℝ) ≤ point m j-1+3*mesh m := by
  have hc : (Finset.Icc (2*m) (j+m+1)).card+m = j+2 := by
    rw [Nat.card_Icc]
    omega
  have hcr : ((Finset.Icc (2*m) (j+m+1)).card : ℝ)+(m : ℝ) = (j : ℝ)+2 := by
    exact_mod_cast hc
  have he := congrArg (fun x : ℝ => x*mesh m) hcr
  have hmul := mesh_mul m hm
  have hn := mesh_nonneg m
  unfold point
  nlinarith

end Erdos970Dependency.MeshStationary

end

section

open scoped BigOperators

namespace Erdos970Dependency.MeshStationary

theorem row_card (m j : ℕ) : (Finset.Icc m (j+m+1)).card = j+2 := by
  rw [Nat.card_Icc]
  omega

theorem point_last (m j : ℕ) (hm : 1 ≤ m) :
    point m (j+m+2) = point m j + 1 + 2*mesh m := by
  unfold point
  push_cast
  nlinarith [mesh_mul m hm]

theorem reciprocal_sum_lower (m j : ℕ) (hm : 1 ≤ m) :
    (1 : ℝ) - 1 / point m (j+m+2) ≤
      ∑ k ∈ Finset.Icc m (j+m+1), mesh m / (point m k)^2 := by
  have h : (∑ k ∈ Finset.Icc m (j+m+1),
      ((1 : ℝ) / point m k - (1 : ℝ) / point m (k+1))) ≤
      ∑ k ∈ Finset.Icc m (j+m+1), mesh m / (point m k)^2 := by
    apply Finset.sum_le_sum
    intro k hk
    rw [point_succ]
    exact reciprocal_drop_le
      (lt_of_lt_of_le zero_lt_one (point_ge_one m k hm (Finset.mem_Icc.mp hk).1))
      (mesh_nonneg m)
  rw [reciprocal_telescope m m (j+m+1) (by omega)] at h
  have hfirst : point m m = 1 := mesh_mul m hm
  simpa only [hfirst,div_one,show j+m+1+1 = j+m+2 by omega] using h

theorem leading_sum_le (m j : ℕ) (hm : 1 ≤ m) :
    (∑ k ∈ Finset.Icc m (j+m+1), mesh m * (1 - 1 / (point m k)^2)) ≤
      (point m j)^2 / (point m j+1) + 2*mesh m := by
  have ht := point_nonneg m j
  have hh := mesh_nonneg m
  have ht1 : 0 < point m j+1 := by linarith
  have hrec := reciprocal_sum_lower m j hm
  rw [point_last m j hm] at hrec
  have hinv : (1 : ℝ) / (point m j+1+2*mesh m) ≤ 1 / (point m j+1) :=
    div_le_div_of_nonneg_left (by norm_num) ht1 (by linarith)
  calc
    _ = (∑ _k ∈ Finset.Icc m (j+m+1),mesh m) -
        ∑ k ∈ Finset.Icc m (j+m+1), mesh m / (point m k)^2 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = point m j + 2*mesh m -
        ∑ k ∈ Finset.Icc m (j+m+1), mesh m / (point m k)^2 := by
      simp only [Finset.sum_const,row_card,nsmul_eq_mul,Nat.cast_add,Nat.cast_ofNat,point]
      ring
    _ ≤ point m j + 2*mesh m - (1 - 1 / (point m j+1+2*mesh m)) :=
      sub_le_sub_left hrec _
    _ ≤ point m j - 1 + 1 / (point m j+1) + 2*mesh m := by linarith
    _ = _ := by field_simp <;> ring

theorem correction_sum_le (m j : ℕ) (hm : 1 ≤ m) :
    (∑ k ∈ Finset.Icc m (j+m+1), mesh m * (3*mesh m*weight (point m k))) ≤
      6*mesh m*(point m j+2) := by
  have hh := mesh_nonneg m
  have hh1 := mesh_le_one m hm
  calc
    _ ≤ ∑ _k ∈ Finset.Icc m (j+m+1),mesh m*(3*mesh m*2) := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (weight_le_two (point_ge_one m k hm (Finset.mem_Icc.mp hk).1)) (by positivity))
        hh
    _ = 6*mesh m*(point m j+2*mesh m) := by
      simp only [Finset.sum_const,row_card,nsmul_eq_mul,Nat.cast_add,Nat.cast_ofNat,point]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem full_row_sum_le (m j : ℕ) (hm : 1 ≤ m) :
    (∑ k ∈ Finset.Icc m (j+m+1),
      mesh m * (1 - 1 / (point m k)^2 + 3*mesh m*weight (point m k))) ≤
      (point m j)^2 / (point m j+1) + 2*mesh m + 6*mesh m*(point m j+2) := by
  calc
    _ = (∑ k ∈ Finset.Icc m (j+m+1),mesh m*(1 - 1 / (point m k)^2)) +
        ∑ k ∈ Finset.Icc m (j+m+1),mesh m*(3*mesh m*weight (point m k)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ _ := add_le_add (leading_sum_le m j hm) (correction_sum_le m j hm)

end Erdos970Dependency.MeshStationary

end

section

open scoped BigOperators

namespace Erdos970Dependency.MeshStationary

theorem odd_row_weighted (m j : ℕ) (hm : 1 ≤ m) (hj : 2*m ≤ j) :
    weight (point m j) *
      (∑ k ∈ Finset.Icc m (j+m+1),
        mesh m * (1 - 1 / (point m k)^2 + 3*mesh m*weight (point m k))) ≤
      1 + 20*mesh m := by
  have ht2 := point_ge_two m j hm hj
  have ht0 : point m j ≠ 0 := by linarith
  have ht1 : point m j+1 ≠ 0 := by linarith
  have hW := weight_nonneg (point_nonneg m j)
  calc
    _ ≤ weight (point m j) *
        ((point m j)^2 / (point m j+1) + 2*mesh m + 6*mesh m*(point m j+2)) :=
      mul_le_mul_of_nonneg_left (full_row_sum_le m j hm) hW
    _ = 1 + mesh m * (weight (point m j)*(6*point m j+14)) := by
      unfold weight
      field_simp
      ring
    _ ≤ 1 + mesh m*20 := add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (weight_cost_le_twenty ht2) (mesh_nonneg m))
    _ = _ := by ring

theorem even_row_literal (m j : ℕ) (hm : 1 ≤ m) (hj : m ≤ j) :
    (1/(m : ℝ)) * ((Finset.Icc (2*m) (j+m+1)).card : ℝ) ≤
      (j : ℝ)/(m : ℝ) - 1 + 3/(m : ℝ) := by
  simpa only [mesh,point,div_eq_mul_inv,one_mul] using even_row_count m j hm hj

theorem odd_row_literal (m j : ℕ) (hm : 1 ≤ m) (hj : 2*m ≤ j) :
    (((j : ℝ)/(m : ℝ)+1)/((j : ℝ)/(m : ℝ))^2) *
      (∑ k ∈ Finset.Icc m (j+m+1),
        (1/(m : ℝ)) *
          (1 - 1 / ((k : ℝ)/(m : ℝ))^2 +
            (3/(m : ℝ))*(((k : ℝ)/(m : ℝ)+1)/((k : ℝ)/(m : ℝ))^2))) ≤
      1 + 20/(m : ℝ) := by
  simpa only [mesh,point,weight,div_eq_mul_inv,one_mul,mul_assoc] using
    odd_row_weighted m j hm hj

end Erdos970Dependency.MeshStationary

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_MarginalProfiles
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.OAI.Erdos970.NumberTheoryLean.ReferenceBenchmarkDecay.benchmark_even_below_two
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.MarginalProfiles

open _root_.Set _root_.Finset
open FinitePathGeometry PrimeSideSupport PrimeGridGeometry DerivativeWeights WeightFutureIntegrals

theorem index_regular {m j : ℕ} (hm : 1 ≤ m) (i : Side) (hj : lowerIndex m i ≤ j) :
    regularLower i ≤ point m j := by
  cases i with
  | even => simpa only [regularLower,Nat.cast_ofNat] using (threshold_le_point hm 2 j).mpr hj
  | odd => simpa only [regularLower,Nat.cast_one] using (threshold_le_point hm 1 j).mpr (by simpa only [lowerIndex,one_mul] using hj)

theorem index_valid {m j : ℕ} (hm : 1 ≤ m) (i : Side) (hj : lowerIndex m i ≤ j) :
    Valid i (point m j) := by
  have ht := index_regular hm i hj
  cases i <;> dsimp [Valid,regularLower] at * <;> linarith

theorem profile_nonneg (m : ℕ) {i : Side} {t : ℝ} (ht : regularLower i ≤ t) : 0 ≤ profile m i t := by
  cases i with
  | even => exact zero_le_one
  | odd =>
    have ht1 : 1 ≤ t := ht
    have ht0 : 0 < t := by linarith
    have hinv : 1/t^2 ≤ 1 := by
      simpa only [div_one] using one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1) (one_le_pow₀ ht1 : (1:ℝ) ≤ t^2)
    have hW := (W_pos ht0).le
    have hlead : 0 ≤ 1-1/t^2 := sub_nonneg.mpr hinv
    have hw := width_nonneg m
    change 0 ≤ 1-1/t^2+3*width m*W t
    positivity

theorem even_stationary_profile {m j : ℕ} (hm : 1 ≤ m) (hj : m ≤ j) :
    W (point m j)*(width m*((Finset.Icc (2*m) (j+m+1)).card:ℝ)) ≤ profile m .odd (point m j) := by
  have ht : (1:ℝ) ≤ point m j := by simpa only [Nat.cast_one] using (threshold_le_point hm 1 j).mpr (by simpa only [lowerIndex,one_mul] using hj)
  have ht0 : 0 < point m j := by linarith
  have hcount : width m*((Finset.Icc (2*m) (j+m+1)).card:ℝ) ≤ point m j-1+3*width m := by
    simpa only [width,point,div_eq_mul_inv,one_mul] using
      Erdos970Dependency.MeshStationary.even_row_literal m j hm hj
  calc
    _ ≤ W (point m j)*(point m j-1+3*width m) := mul_le_mul_of_nonneg_left hcount (W_pos ht0).le
    _ = _ := by unfold profile W; field_simp <;> ring

theorem odd_stationary_profile {m j : ℕ} (hm : 1 ≤ m) (hj : 2*m ≤ j) :
    W (point m j)*(∑ k ∈ Finset.Icc m (j+m+1),width m*profile m .odd (point m k)) ≤ 1+20*width m := by
  simpa only [width,point,profile,W,div_eq_mul_inv,one_mul,mul_assoc] using
    Erdos970Dependency.MeshStationary.odd_row_literal m j hm hj

theorem stationary_profile {m j : ℕ} (hm : 1 ≤ m) (i : Side) (hj : lowerIndex m i.flip ≤ j) :
    W (point m j)*(∑ k ∈ Finset.Icc (lowerIndex m i) (j+m+1),width m*profile m i (point m k)) ≤
      (1+20*width m)*profile m i.flip (point m j) := by
  cases i with
  | even =>
    have hj' : m ≤ j := hj
    have ht := index_regular hm .odd hj'
    have hp := profile_nonneg m ht
    have hsum : (∑ k ∈ Finset.Icc (2*m) (j+m+1),width m*profile m .even (point m k)) =
        width m*((Finset.Icc (2*m) (j+m+1)).card:ℝ) := by
      simp only [profile,mul_one,Finset.sum_const,nsmul_eq_mul]
      ring
    change W (point m j)*(∑ k ∈ Finset.Icc (2*m) (j+m+1),width m*profile m .even (point m k)) ≤
      (1+20*width m)*profile m .odd (point m j)
    rw [hsum]
    apply (even_stationary_profile hm hj').trans
    have hw := width_nonneg m
    have h := mul_nonneg (show 0 ≤ 20*width m by positivity) hp
    nlinarith
  | odd =>
    have hj' : 2*m ≤ j := hj
    simpa only [lowerIndex,Side.flip,profile,mul_one] using odd_stationary_profile hm hj'

theorem W_le_six {t : ℝ} (ht : (1/2:ℝ) ≤ t) : W t ≤ 6 := by
  have ht0 : 0 < t := by linarith
  unfold W
  apply (div_le_iff₀ (sq_pos_of_pos ht0)).mpr
  nlinarith [sq_nonneg (t-1/2)]

theorem W_initial_cost {t : ℝ} (ht : 2 ≤ t) : W t*(t+3) ≤ 4 := by
  have ht0 : 0 < t := by linarith
  calc
    _ = ((t+1)*(t+3))/t^2 := by unfold W; ring
    _ ≤ _ := (div_le_iff₀ (sq_pos_of_pos ht0)).mpr (by nlinarith [sq_nonneg (t-2)])

theorem first_row_sum {m j : ℕ} (hm : 1 ≤ m) (hj : 2*m ≤ j) (I : Finset ℕ)
    (hI : I ⊆ Finset.Icc 0 (j+m+1)) (hpoints : ∀ k ∈ I,(1/2:ℝ) ≤ point m k) :
    W (point m j)*(∑ k ∈ I,width m*W (point m k)) ≤ 24 := by
  have ht : (2:ℝ) ≤ point m j := by simpa only [Nat.cast_ofNat] using (threshold_le_point hm 2 j).mpr hj
  have hW := (W_pos (show 0 < point m j by linarith)).le
  have hw := width_nonneg m
  have hw1 : width m ≤ 1 := Erdos970Dependency.MeshStationary.mesh_le_one m hm
  have hc : I.card ≤ j+m+2 := by
    have h := Finset.card_le_card hI
    rw [Nat.card_Icc] at h
    omega
  have hcR : (I.card:ℝ) ≤ ((j+m+2:ℕ):ℝ) := by exact_mod_cast hc
  have hs : (∑ k ∈ I,width m*W (point m k)) ≤ 6*(point m j+3) := by
    calc
      _ ≤ ∑ _k ∈ I,width m*6 := Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left (W_le_six (hpoints k hk)) hw)
      _ = (6*width m)*(I.card:ℝ) := by rw [Finset.sum_const,nsmul_eq_mul]; ring
      _ ≤ (6*width m)*((j+m+2:ℕ):ℝ) := mul_le_mul_of_nonneg_left hcR (by positivity)
      _ = 6*point m (j+m+2) := by unfold point width; ring
      _ = 6*(point m j+1+2*width m) := by rw [incoming_grid_end hm j]
      _ ≤ _ := by linarith
  calc
    _ ≤ W (point m j)*(6*(point m j+3)) := mul_le_mul_of_nonneg_left hs hW
    _ = 6*(W (point m j)*(point m j+3)) := by ring
    _ ≤ 6*4 := mul_le_mul_of_nonneg_left (W_initial_cost ht) (by norm_num)
    _ = _ := by norm_num

end NumberTheoryLean.MarginalProfiles

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_FiniteBinIntegral
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.FiniteBinIntegral

open Set MeasureTheory
open scoped ENNReal

variable {α β : Type*} [MeasurableSpace α]

theorem integrate_bin_envelope (μ : Measure α) (I : Finset β) (B : β → Set α)
    (hB : ∀ k ∈ I,MeasurableSet (B k)) (C : β → ℝ) :
    (∫⁻ x,∑ k ∈ I, ENNReal.ofReal (C k)*((B k).indicator (fun _ => (1:ℝ≥0∞)) x) ∂μ) =
      ∑ k ∈ I,ENNReal.ofReal (C k)*μ (B k) := by
  rw [lintegral_finsetSum I (f := fun k x => ENNReal.ofReal (C k)*((B k).indicator (fun _ => (1:ℝ≥0∞)) x))
    (fun k hk => measurable_const.mul (measurable_const.indicator (hB k hk)))]
  apply Finset.sum_congr rfl
  intro k hk
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_indicator (hB k hk),setLIntegral_const,one_mul]

end NumberTheoryLean.FiniteBinIntegral

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_GridWeightComparison
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.OAI.Erdos970.NumberTheoryLean.ReferenceBenchmarkDecay.benchmark_even_below_two
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ConditionalBinRate

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ConditionalPrimeBins ExponentialMesh DerivativeWeights WeightFutureIntegrals

 theorem relative_error_rate {c C κ : ℝ} (hC : 0 ≤ C) (hκ : 0 < κ) (hc : 4*κ ≤ c) :
    ∀ᶠ w : ℝ in atTop, ∀ S : ℝ, 0 ≤ S → S ≤ (Real.log w)^3 →
      C*(S+1)*Real.exp (-c*Real.sqrt ((1/2:ℝ)*Real.log w))/mesh κ w ≤
        Real.exp (-(κ/2)*Real.sqrt (Real.log w)) := by
  filter_upwards [log_power_exp_absorption (4*C) 3 hκ,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with w hbound hlog
  intro S hS0 hS
  have hpow : 1 ≤ (Real.log w)^3 := one_le_pow₀ hlog
  have hSp : S+1 ≤ 2*(Real.log w)^3 := by linarith
  have herror := prime_error_over_mesh hκ.le hc (by linarith : 0 ≤ Real.log w)
  have hm := mesh_pos κ w
  calc
    _ = (C*(S+1))*(Real.exp (-c*Real.sqrt ((1/2:ℝ)*Real.log w))/mesh κ w) := by ring
    _ ≤ (C*(2*(Real.log w)^3))*(2*Real.exp (-κ*Real.sqrt (Real.log w))) := mul_le_mul
      (mul_le_mul_of_nonneg_left hSp hC) herror (by positivity) (by positivity)
    _ = (4*C)*(Real.log w)^3*Real.exp (-κ*Real.sqrt (Real.log w)) := by ring
    _ ≤ _ := hbound

theorem actual_conditional_bin_rate : ∃ κ₀ : ℝ, 0 < κ₀ ∧
    ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∃ w₀ : ℝ, 1 < w₀ ∧ ∀ w : ℝ, w₀ ≤ w →
      ∀ ell S : ℝ, 0 ≤ S → S ≤ (Real.log w)^3 → ∀ start : Node,
      1 ≤ ell → 0 < start.gap → Valid start.side start.ratio →
      ∀ g : History w ell S start, ∀ a : ℝ, Valid g.node.side.flip a → a ≤ S →
        chain w ell S start (some g) (ActualPrimeBins.liveBin a (a+mesh κ w)) ≤
          ENNReal.ofReal ((1+Real.exp (-(κ/2)*Real.sqrt (Real.log w)))*
            mesh κ w*W a*(weight g.node.side.flip a/weight g.node.side g.node.ratio)) := by
  obtain ⟨c,C,wR,hc,hC,hwR,hraw⟩ := actual_conditional_bin
  refine ⟨c/4,by positivity,?_⟩
  intro κ hκ hκc
  have hcκ : 4*κ ≤ c := by linarith
  obtain ⟨W₀,hW₀⟩ := eventually_atTop.mp (relative_error_rate hC.le hκ hcκ)
  refine ⟨max wR W₀,hwR.trans_le (le_max_left _ _),?_⟩
  intro w hw ell S hS0 hS start hell hr hs g a ha haS
  have hm := mesh_pos κ w
  have hrel := hW₀ w ((le_max_right _ _).trans hw) S hS0 hS
  have hb := hraw w ((le_max_left _ _).trans hw) ell S start hell hr hs g a (mesh κ w) ha hm (mesh_le_one hκ.le w)
  have hv : Valid g.node.side g.node.ratio := terminal_valid hs g.admissible
  have hW := (W_pos (valid_pos ha)).le
  have hratio : 0 ≤ weight g.node.side.flip a/weight g.node.side g.node.ratio :=
    (div_pos (weight_pos ha) (weight_pos hv)).le
  have hδ : C*(a+1)*Real.exp (-c*Real.sqrt ((1/2:ℝ)*Real.log w))/mesh κ w ≤
      Real.exp (-(κ/2)*Real.sqrt (Real.log w)) := by
    apply le_trans _ hrel
    apply div_le_div_of_nonneg_right _ hm.le
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith : a+1 ≤ S+1) hC.le) (Real.exp_pos _).le
  refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (add_le_add_right hδ 1) hm.le) hW) hratio

end NumberTheoryLean.ConditionalBinRate

end

section

namespace NumberTheoryLean.GridWeightComparison

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open WeightGlobalBounds ConditionalBinRate ExponentialMesh DerivativeWeights WeightFutureIntegrals

theorem weight_local_ratio : ∃ L : ℝ, 0 < L ∧ ∀ S : ℝ, 3 ≤ S → ∀ i : Side, ∀ u s h : ℝ,
    Valid i u → Valid i s → s ≤ S → u ≤ s → s ≤ u+h →
      weight i u/weight i s ≤ Real.exp (L*(1+S)^3*h) := by
  obtain ⟨L,hL,hbound⟩ := weights_log_lipschitz
  refine ⟨L,hL,?_⟩
  intro S hS i u s h hu hs hsS hus hsu
  have hlog : |Real.log (weight i u)-Real.log (weight i s)| ≤ L*(1+S)^3*|u-s| := by
    cases i with
    | even => exact (hbound S hS).1 u s hu hs (hus.trans hsS) hsS
    | odd => exact (hbound S hS).2 u s hu hs (hus.trans hsS) hsS
  have habs : |u-s| ≤ h := by
    rw [abs_sub_comm u s,abs_of_nonneg (sub_nonneg.mpr hus)]
    linarith
  have hdiff : Real.log (weight i u)-Real.log (weight i s) ≤ L*(1+S)^3*h :=
    ((le_abs_self _).trans hlog).trans (mul_le_mul_of_nonneg_left habs (by positivity))
  have he := Real.exp_le_exp.mpr hdiff
  rwa [Real.exp_sub,Real.exp_log (weight_pos hu),Real.exp_log (weight_pos hs)] at he

theorem actual_parent_bin_upper : ∃ κ₀ L : ℝ, 0 < κ₀ ∧ 0 < L ∧
    ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∃ w₀ : ℝ, 1 < w₀ ∧ ∀ w : ℝ, w₀ ≤ w →
      ∀ ell S : ℝ, 3 ≤ S → S ≤ (Real.log w)^3 → ∀ start : Node,
      1 ≤ ell → 0 < start.gap → Valid start.side start.ratio →
      ∀ g : History w ell S start, ∀ u a : ℝ,
      Valid g.node.side u → Valid g.node.side.flip a → g.node.ratio ≤ S → a ≤ S →
      u ≤ g.node.ratio → g.node.ratio ≤ u+mesh κ w →
        chain w ell S start (some g) (ActualPrimeBins.liveBin a (a+mesh κ w)) ≤
          ENNReal.ofReal ((1+Real.exp (-(κ/2)*Real.sqrt (Real.log w)))*
            Real.exp (L*(1+S)^3*mesh κ w)*mesh κ w*W a*(weight g.node.side.flip a/weight g.node.side u)) := by
  obtain ⟨κ₀,hκ₀,hconditional⟩ := actual_conditional_bin_rate
  obtain ⟨L,hL,hlocal⟩ := weight_local_ratio
  refine ⟨κ₀,L,hκ₀,hL,?_⟩
  intro κ hκ hκle
  obtain ⟨w₀,hw₀,hrow⟩ := hconditional κ hκ hκle
  refine ⟨w₀,hw₀,?_⟩
  intro w hw ell S hS3 hS start hell hr hs g u a hu ha hgS haS hus hsu
  have hgv : Valid g.node.side g.node.ratio := terminal_valid hs g.admissible
  have hratio := hlocal S hS3 g.node.side u g.node.ratio (mesh κ w) hu hgv hgS hus hsu
  have htarget : weight g.node.side.flip a/weight g.node.side g.node.ratio ≤
      (weight g.node.side.flip a/weight g.node.side u)*Real.exp (L*(1+S)^3*mesh κ w) := by
    have heq : weight g.node.side.flip a/weight g.node.side g.node.ratio =
        (weight g.node.side.flip a/weight g.node.side u)*(weight g.node.side u/weight g.node.side g.node.ratio) := by
      field_simp [(weight_pos hu).ne']
    rw [heq]
    exact mul_le_mul_of_nonneg_left hratio (div_pos (weight_pos ha) (weight_pos hu)).le
  have hm := mesh_pos κ w
  have hW := (W_pos (valid_pos ha)).le
  have hM : 0 ≤ (1+Real.exp (-(κ/2)*Real.sqrt (Real.log w)))*mesh κ w*W a := by positivity
  refine (hrow w hw ell S (by linarith) hS start hell hr hs g a ha haS).trans (ENNReal.ofReal_le_ofReal ?_)
  calc
    _ ≤ ((1+Real.exp (-(κ/2)*Real.sqrt (Real.log w)))*mesh κ w*W a)*
        ((weight g.node.side.flip a/weight g.node.side u)*Real.exp (L*(1+S)^3*mesh κ w)) :=
      mul_le_mul_of_nonneg_left htarget hM
    _ = _ := by ring

end NumberTheoryLean.GridWeightComparison

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeMarginalRecursion
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.PrimeGridKernel

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeTiltGeometry PrimeHistories PrimeKilledChain PrimeSideSupport PrimeGridGeometry

variable {w ell S : ℝ} {start : Node}

theorem mem_bin (g : History w ell S start) (m j : ℕ) :
    some g ∈ bin m j ↔ g.node.ratio ∈ Ico (point m j) (point m (j+1)) := Iff.rfl

theorem bin_measurable (m j : ℕ) : MeasurableSet (bin (w:=w) (ell:=ell) (S:=S) (start:=start) m j) := trivial

theorem row_none (m j : ℕ) : chain w ell S start none (bin m j) = 0 := by
  rw [chain_none,Measure.dirac_apply' _ (bin_measurable m j),
    indicator_of_notMem (show (none:ChainState w ell S start) ∉ bin m j from ActualPrimeBins.not_mem_liveBin_none _ _)]

theorem row_zero_of_large_parent (g : History w ell S start) (m j : ℕ)
    (hlarge : point m j+width m+1 ≤ g.node.ratio) :
    chain w ell S start (some g) (bin m j) = 0 := by
  classical
  rw [bin,point_succ,ActualPrimeBins.chain_live_bin_formula]
  apply Finset.sum_eq_zero
  intro p hp
  have hlo := (Finset.mem_filter.mp hp).2.2.2.1
  have hmin := minRatio_ge_sub_one g.node.side g.node.ratio
  have hnot : ¬(point m j ≤ childRatio w g.node.gap p ∧ childRatio w g.node.gap p < point m j+width m) := by
    rintro ⟨_,ht⟩
    linarith
  rw [ite_eq_right hnot]

theorem row_zero_above_grid (g : History w ell S start) {m : ℕ} (hm : 1 ≤ m) (j : ℕ)
    (hlarge : point m (j+m+2) ≤ g.node.ratio) :
    chain w ell S start (some g) (bin m j) = 0 := by
  apply row_zero_of_large_parent
  rw [incoming_grid_end hm j] at hlarge
  linarith [width_nonneg m]

theorem weak_parent_cover (g : History w ell S start) {m : ℕ} (hm : 1 ≤ m)
    (hsmall : width m ≤ 1/100) (j : ℕ) (hv : Valid g.node.side g.node.ratio) (hg : WeakRegular g.node)
    (hupper : g.node.ratio < point m (j+m+2)) :
    ∃ k ∈ weakIndices m j g.node.side, some g ∈ bin m k := by
  classical
  obtain ⟨k,hk,hbin⟩ := finite_grid_cover (J:=j+m+1) hm (valid_pos hv).le (by simpa only [Nat.add_assoc] using hupper)
  exact ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _,hk⟩,weak_bin_domain hm hsmall hg hbin⟩,hbin⟩

theorem regular_parent_cover (g : History w ell S start) {m : ℕ} (hm : 1 ≤ m)
    (j : ℕ) (hv : Valid g.node.side g.node.ratio) (hg : Regular g.node)
    (hupper : g.node.ratio < point m (j+m+2)) :
    ∃ k ∈ Finset.Icc (lowerIndex m g.node.side) (j+m+1),
      some g ∈ bin m k ∧ Valid g.node.side (point m k) := by
  obtain ⟨k,hk,hbin⟩ := finite_grid_cover (J:=j+m+1) hm (valid_pos hv).le (by simpa only [Nat.add_assoc] using hupper)
  have hdom := regular_bin_domain hm hg hbin
  exact ⟨k,Finset.mem_Icc.mpr ⟨hdom.1,hk⟩,hbin,hdom.2⟩

theorem mass_step (m n j : ℕ) :
    mass w ell S start m (n+1) j =
      ∫⁻ p,chain w ell S start p (bin m j) ∂pathLaw w ell S start n := by
  have hp : (chain w ell S start)^(n+1) = (chain w ell S start) ∘ₖ ((chain w ell S start)^n) := pow_succ' _ _
  change ((chain w ell S start)^(n+1)) (some History.empty) (bin m j) = _
  rw [hp]
  exact Kernel.comp_apply' _ _ _ (bin_measurable m j)

end NumberTheoryLean.PrimeGridKernel

end

section


namespace NumberTheoryLean.PrimeMarginalRecursion

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain PrimeSideSupport
open PrimeGridGeometry PrimeGridKernel GridWeightComparison ExponentialMesh FiniteBinIntegral
open DerivativeWeights

theorem weak_coverage {w ell S : ℝ} {start : Node} (hs : Valid start.side start.ratio)
    (hi : start.side = .even) {m : ℕ} (hm : 1 ≤ m) (hsmall : width m ≤ 1/100)
    (n : ℕ) (hn : 1 ≤ n) (j : ℕ) :
    ∀ᵐ p ∂pathLaw w ell S start n, coveredParents m j (sideAfter .even n) (weakIndices m j (sideAfter .even n)) p := by
  filter_upwards [pathLaw_side (w:=w) (ell:=ell) (S:=S) hi n,pathLaw_weak (w:=w) (ell:=ell) (S:=S) hs n hn] with p hside hweak
  cases p with
  | none => trivial
  | some g =>
    refine ⟨hside,?_⟩
    intro htop
    have hgv : Valid g.node.side g.node.ratio := terminal_valid hs g.admissible
    obtain ⟨k,hk,hbin⟩ := weak_parent_cover g hm hsmall j hgv hweak htop
    have hkV := weak_bin_domain hm hsmall hweak ((mem_bin g m k).mp hbin)
    exact ⟨k,by simpa only [hside] using hk,hbin,by simpa only [hside] using hkV⟩

theorem regular_coverage {w ell S : ℝ} {start : Node} (hs : Valid start.side start.ratio)
    (hi : start.side = .even) {m : ℕ} (hm : 1 ≤ m) (n : ℕ) (hn : 2 ≤ n) (j : ℕ) :
    ∀ᵐ p ∂pathLaw w ell S start n, coveredParents m j (sideAfter .even n)
      (Finset.Icc (lowerIndex m (sideAfter .even n)) (j+m+1)) p := by
  filter_upwards [pathLaw_side (w:=w) (ell:=ell) (S:=S) hi n,pathLaw_regular (w:=w) (ell:=ell) (S:=S) (start:=start) n hn] with p hside hreg
  cases p with
  | none => trivial
  | some g =>
    refine ⟨hside,?_⟩
    intro htop
    have hgv : Valid g.node.side g.node.ratio := terminal_valid hs g.admissible
    obtain ⟨k,hk,hbin,hkV⟩ := regular_parent_cover g hm j hgv hreg htop
    exact ⟨k,by simpa only [hside] using hk,hbin,by simpa only [hside] using hkV⟩

theorem covered_recursion : ∃ κ₀ L : ℝ, 0 < κ₀ ∧ 0 < L ∧
    ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∃ w₀ : ℝ, 1 < w₀ ∧ ∀ w : ℝ, w₀ ≤ w →
    ∀ ell S : ℝ, 3 ≤ S → S ≤ (Real.log w)^3 → ∀ start : Node,
      1 ≤ ell → 0 < start.gap → Valid start.side start.ratio → start.ratio ≤ S →
      ∀ m n j : ℕ, 1 ≤ m → width m = mesh κ w → ∀ i : Side, ∀ I : Finset ℕ,
      Valid i.flip (point m j) → point m j ≤ S →
      (∀ᵐ p ∂pathLaw w ell S start n, coveredParents m j i I p) →
      mass w ell S start m (n+1) j ≤
        ∑ k ∈ I,ENNReal.ofReal (entry L κ w S m i j k)*mass w ell S start m n k := by
  obtain ⟨κ₀,L,hκ₀,hL,hparent⟩ := actual_parent_bin_upper
  refine ⟨κ₀,L,hκ₀,hL,?_⟩
  intro κ hκ hκle
  obtain ⟨w₀,hw₀,hrow⟩ := hparent κ hκ hκle
  refine ⟨w₀,hw₀,?_⟩
  intro w hw ell S hS3 hS start hell hr hs hsS m n j hm hmesh i I hjV hjS hcover
  classical
  have hEnvelope : ∀ᵐ p ∂pathLaw w ell S start n,
      chain w ell S start p (bin m j) ≤
        ∑ k ∈ I,ENNReal.ofReal (entry L κ w S m i j k)*((bin m k).indicator (fun _ => (1:ℝ≥0∞)) p) := by
    filter_upwards [hcover] with p hp
    cases p with
    | none => rw [row_none]; exact zero_le
    | some g =>
      by_cases hhigh : point m (j+m+2) ≤ g.node.ratio
      · rw [row_zero_above_grid g hm j hhigh]
        exact zero_le
      · obtain ⟨k,hk,hbin,hkV⟩ := hp.2 (lt_of_not_ge hhigh)
        have hgu : Valid g.node.side (point m k) := by rwa [hp.1]
        have hga : Valid g.node.side.flip (point m j) := by rwa [hp.1]
        have hgn : g.node.ratio ≤ S := terminal_ratio_le hsS g.admissible
        have hgBin := (mem_bin g m k).mp hbin
        have hgb : g.node.ratio ≤ point m k+mesh κ w := by
          rw [point_succ,hmesh] at hgBin
          exact hgBin.2.le
        have hb := hrow w hw ell S hS3 hS start hell hr hs g (point m k) (point m j)
          hgu hga hgn hjS hgBin.1 hgb
        have hentry : chain w ell S start (some g) (bin m j) ≤ ENNReal.ofReal (entry L κ w S m i j k) := by
          simpa only [bin,point_succ,hmesh,entry,hp.1] using hb
        calc
          _ ≤ ENNReal.ofReal (entry L κ w S m i j k) := hentry
          _ = ENNReal.ofReal (entry L κ w S m i j k)*((bin m k).indicator (fun _ => (1:ℝ≥0∞)) (some g)) := by
            rw [indicator_of_mem hbin,mul_one]
          _ ≤ _ := Finset.single_le_sum (s:=I) (a:=k)
            (f:=fun l => ENNReal.ofReal (entry L κ w S m i j l)*((bin m l).indicator (fun _ => (1:ℝ≥0∞)) (some g)))
            (fun _ _ => zero_le) hk
  rw [mass_step]
  calc
    _ ≤ ∫⁻ p,∑ k ∈ I,ENNReal.ofReal (entry L κ w S m i j k)*((bin m k).indicator (fun _ => (1:ℝ≥0∞)) p)
        ∂pathLaw w ell S start n := lintegral_mono_ae hEnvelope
    _ = _ := integrate_bin_envelope (pathLaw w ell S start n) I (bin m)
      (fun k _ => bin_measurable m k) (entry L κ w S m i j)

end NumberTheoryLean.PrimeMarginalRecursion

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_MarginalTransport
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.OAI.Erdos970.NumberTheoryLean.ReferenceBenchmarkDecay.benchmark_even_below_two
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section


namespace NumberTheoryLean.MarginalTransport

open _root_.Set _root_.Finset _root_.MeasureTheory
open scoped ENNReal
open FinitePathGeometry PrimeGridGeometry PrimeGridKernel PrimeSideSupport
open PrimeMarginalRecursion MarginalProfiles ExponentialMesh DerivativeWeights

theorem rowFactor_pos (L κ w S : ℝ) : 0 < rowFactor L κ w S := by unfold rowFactor; positivity

theorem factor_eq_row (L κ w S : ℝ) :
    MarginalGrowth.factor L κ w S = rowFactor L κ w S*(1+20*mesh κ w) := rfl

theorem row_le_factor (L κ w S : ℝ) : rowFactor L κ w S ≤ MarginalGrowth.factor L κ w S := by
  rw [factor_eq_row]
  have hm := mesh_pos κ w
  have hR := rowFactor_pos L κ w S
  nlinarith

theorem entry_nonneg (L κ w S : ℝ) (m j k : ℕ) {i : Side}
    (hj : Valid i.flip (point m j)) (hk : Valid i (point m k)) : 0 ≤ entry L κ w S m i j k := by
  have hm := width_nonneg m
  have hW := (WeightFutureIntegrals.W_pos (valid_pos hj)).le
  have hr := (div_pos (weight_pos hj) (weight_pos hk)).le
  unfold entry
  positivity

theorem entry_cancel (L κ w S C : ℝ) (m n j k : ℕ) (i : Side) (F : ℝ → ℝ)
    (hk : Valid i (point m k)) :
    entry L κ w S m i j k*(C*(MarginalGrowth.factor L κ w S)^n*width m*weight i (point m k)*F (point m k)) =
      (C*(MarginalGrowth.factor L κ w S)^n*rowFactor L κ w S*width m*weight i.flip (point m j))*
        W (point m j)*(width m*F (point m k)) := by
  have heq : (weight i.flip (point m j)/weight i (point m k))*weight i (point m k) = weight i.flip (point m j) :=
    div_mul_cancel₀ _ (weight_pos hk).ne'
  calc
    _ = (C*(MarginalGrowth.factor L κ w S)^n*rowFactor L κ w S*width m*W (point m j)*width m*F (point m k))*
        ((weight i.flip (point m j)/weight i (point m k))*weight i (point m k)) := by unfold entry rowFactor; ring
    _ = _ := by rw [heq]; ring

theorem transport_sum (L κ w S C : ℝ) (m n j : ℕ) (i : Side) (I : Finset ℕ)
    (F : ℝ → ℝ) (μ : ℕ → ℝ≥0∞) (hC : 0 ≤ C) (hj : Valid i.flip (point m j))
    (hI : ∀ k ∈ I,Valid i (point m k)) (hF : ∀ k ∈ I,0 ≤ F (point m k))
    (hμ : ∀ k ∈ I,μ k ≤ ENNReal.ofReal (C*(MarginalGrowth.factor L κ w S)^n*width m*weight i (point m k)*F (point m k))) :
    (∑ k ∈ I,ENNReal.ofReal (entry L κ w S m i j k)*μ k) ≤
      ENNReal.ofReal ((C*(MarginalGrowth.factor L κ w S)^n*rowFactor L κ w S*width m*weight i.flip (point m j))*
        (W (point m j)*(∑ k ∈ I,width m*F (point m k)))) := by
  let scale := C*(MarginalGrowth.factor L κ w S)^n*rowFactor L κ w S*width m*weight i.flip (point m j)
  have hg := (MarginalGrowth.factor_pos L κ w S).le
  have hr := (rowFactor_pos L κ w S).le
  have hw := width_nonneg m
  have hp := (weight_pos hj).le
  have hWt := (WeightFutureIntegrals.W_pos (valid_pos hj)).le
  have hscale : 0 ≤ scale := by dsimp [scale] <;> positivity
  calc
    _ ≤ ∑ k ∈ I,ENNReal.ofReal (scale*W (point m j)*(width m*F (point m k))) := by
      apply Finset.sum_le_sum
      intro k hk
      calc
        _ ≤ ENNReal.ofReal (entry L κ w S m i j k)*
            ENNReal.ofReal (C*(MarginalGrowth.factor L κ w S)^n*width m*weight i (point m k)*F (point m k)) :=
          mul_le_mul_of_nonneg_left (hμ k hk) zero_le
        _ = _ := by
          rw [← ENNReal.ofReal_mul (entry_nonneg L κ w S m j k hj (hI k hk))]
          exact congrArg ENNReal.ofReal (entry_cancel L κ w S C m n j k i F (hI k hk))
    _ = ENNReal.ofReal ((scale*W (point m j))*(∑ k ∈ I,width m*F (point m k))) := by
      rw [Finset.mul_sum,ENNReal.ofReal_sum_of_nonneg (s:=I)
        (f:=fun k => scale*W (point m j)*(width m*F (point m k)))
        (fun k hk => mul_nonneg (mul_nonneg hscale hWt) (mul_nonneg hw (hF k hk)))]
    _ = _ := by congr 1; ring

theorem profile_step (L κ w S C : ℝ) {m : ℕ} (hm : 1 ≤ m) (hmesh : width m = mesh κ w)
    (n j : ℕ) (i : Side) (μ : ℕ → ℝ≥0∞) (hC : 0 ≤ C) (hj : lowerIndex m i.flip ≤ j)
    (hμ : ∀ k,lowerIndex m i ≤ k → μ k ≤
      ENNReal.ofReal (C*(MarginalGrowth.factor L κ w S)^n*width m*weight i (point m k)*profile m i (point m k))) :
    (∑ k ∈ Finset.Icc (lowerIndex m i) (j+m+1),ENNReal.ofReal (entry L κ w S m i j k)*μ k) ≤
      ENNReal.ofReal (C*(MarginalGrowth.factor L κ w S)^(n+1)*width m*weight i.flip (point m j)*profile m i.flip (point m j)) := by
  have hjV := index_valid hm i.flip hj
  have ht := transport_sum L κ w S C m n j i (Finset.Icc (lowerIndex m i) (j+m+1)) (profile m i) μ hC hjV
    (fun k hk => index_valid hm i (Finset.mem_Icc.mp hk).1)
    (fun k hk => profile_nonneg m (index_regular hm i (Finset.mem_Icc.mp hk).1))
    (fun k hk => hμ k (Finset.mem_Icc.mp hk).1)
  have hg := (MarginalGrowth.factor_pos L κ w S).le
  have hr := (rowFactor_pos L κ w S).le
  have hw := width_nonneg m
  have hp := (weight_pos hjV).le
  have hscale : 0 ≤ C*(MarginalGrowth.factor L κ w S)^n*rowFactor L κ w S*width m*weight i.flip (point m j) := by positivity
  refine ht.trans (ENNReal.ofReal_le_ofReal ?_)
  calc
    _ ≤ (C*(MarginalGrowth.factor L κ w S)^n*rowFactor L κ w S*width m*weight i.flip (point m j))*
        ((1+20*width m)*profile m i.flip (point m j)) := mul_le_mul_of_nonneg_left (stationary_profile hm i hj) hscale
    _ = _ := by rw [pow_succ,factor_eq_row,← hmesh]; ring

theorem first_to_second (L κ w S C : ℝ) {m : ℕ} (hm : 1 ≤ m)
    (j : ℕ) (hj : 2*m ≤ j) (μ : ℕ → ℝ≥0∞) (hC : 0 ≤ C)
    (hμ : ∀ k,Valid .odd (point m k) → μ k ≤
      ENNReal.ofReal (C*MarginalGrowth.factor L κ w S*width m*W (point m k)*weight .odd (point m k))) :
    (∑ k ∈ weakIndices m j .odd,ENNReal.ofReal (entry L κ w S m .odd j k)*μ k) ≤
      ENNReal.ofReal ((24*C)*(MarginalGrowth.factor L κ w S)^2*width m*weight .even (point m j)) := by
  classical
  have hjV : Valid Side.even (point m j) := index_valid hm .even hj
  have hI : ∀ k ∈ weakIndices m j .odd,Valid .odd (point m k) := by
    intro k hk
    exact (Finset.mem_filter.mp hk).2
  have hF : ∀ k ∈ weakIndices m j .odd,0 ≤ W (point m k) :=
    fun k hk => (WeightFutureIntegrals.W_pos (valid_pos (hI k hk))).le
  have ht := transport_sum L κ w S C m 1 j .odd (weakIndices m j .odd) W μ hC hjV hI hF
    (fun k hk => by simpa only [pow_one,mul_assoc,mul_comm,mul_left_comm] using hμ k (hI k hk))
  rw [pow_one] at ht
  have hfirst := first_row_sum hm hj (weakIndices m j .odd)
    (fun k hk => (Finset.mem_filter.mp hk).1)
    (fun k hk => by have h := hI k hk; change 95/100 ≤ point m k at h; linarith)
  have hg := (MarginalGrowth.factor_pos L κ w S).le
  have hr := (rowFactor_pos L κ w S).le
  have hw := width_nonneg m
  have hp := (weight_pos hjV).le
  have hscale : 0 ≤ C*MarginalGrowth.factor L κ w S*rowFactor L κ w S*width m*weight .even (point m j) := by positivity
  refine ht.trans (ENNReal.ofReal_le_ofReal ?_)
  calc
    _ ≤ (C*MarginalGrowth.factor L κ w S*rowFactor L κ w S*width m*weight .even (point m j))*24 :=
      mul_le_mul_of_nonneg_left hfirst hscale
    _ = (24*C*MarginalGrowth.factor L κ w S*width m*weight .even (point m j))*rowFactor L κ w S := by ring
    _ ≤ (24*C*MarginalGrowth.factor L κ w S*width m*weight .even (point m j))*MarginalGrowth.factor L κ w S :=
      mul_le_mul_of_nonneg_left (row_le_factor L κ w S) (by positivity)
    _ = _ := by ring

end NumberTheoryLean.MarginalTransport

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_SourceParentBin
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.OAI.Erdos970.NumberTheoryLean.ReferenceBenchmarkDecay.benchmark_even_below_two
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SourceParentBin

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeSideSupport PrimeGridGeometry PrimeGridKernel
open PrimeMarginalRecursion DerivativeWeights

theorem initialConstant_pos : 0 < initialConstant := by
  apply one_div_pos.mpr
  exact phiEven_pos (by norm_num)

theorem source_cell {m : ℕ} (hm : 1 ≤ m) (start : Node) (hs : 0 ≤ start.ratio) :
    start.ratio ∈ Ico (point m (index m start)) (point m (index m start+1)) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hlo := Nat.floor_le (mul_nonneg hs hm0.le)
  have hhi := Nat.lt_floor_add_one (start.ratio*(m:ℝ))
  constructor
  · exact (div_le_iff₀ hm0).mpr hlo
  · apply (lt_div_iff₀ hm0).mpr
    simpa only [Nat.cast_add,Nat.cast_one,index] using hhi

theorem source_left_valid {m : ℕ} (hm : 1 ≤ m) (hsmall : width m ≤ 1/100)
    (start : Node) (hs : (199/100:ℝ) ≤ start.ratio) :
    Valid .even (point m (index m start)) := by
  have hcell := source_cell hm start (by linarith)
  rw [point_succ] at hcell
  change 198/100 ≤ point m (index m start)
  linarith [hcell.2]

theorem source_inverse_weight {m : ℕ} (hm : 1 ≤ m) (hsmall : width m ≤ 1/100)
    (start : Node) (hlo : (199/100:ℝ) ≤ start.ratio) (hhi : start.ratio ≤ 23/10) :
    1/weight .even (point m (index m start)) ≤ initialConstant := by
  have hu := source_left_valid hm hsmall start hlo
  have hEnd : Valid .even (23/10:ℝ) := by norm_num [Valid]
  have hcell := (source_cell hm start (by linarith)).1
  have hphi := TwoStepDensityBounds.weight_antitone hu hEnd (hcell.trans hhi)
  exact one_div_le_one_div_of_le (weight_pos hEnd) hphi

variable {w ell S : ℝ} {start : Node}

theorem source_coverage {m : ℕ} (hm : 1 ≤ m) (hsmall : width m ≤ 1/100)
    (hi : start.side = .even) (hs : (199/100:ℝ) ≤ start.ratio) (j : ℕ) :
    ∀ᵐ p ∂pathLaw w ell S start 0, coveredParents m j .even {index m start} p := by
  change ∀ᵐ p ∂Measure.dirac (some (History.empty : History w ell S start)), coveredParents m j .even {index m start} p
  apply (ae_dirac_iff (show MeasurableSet {p | coveredParents m j .even {index m start} p} from trivial)).mpr
  refine ⟨hi,?_⟩
  intro _
  exact ⟨index m start,Finset.mem_singleton_self _,source_cell hm start (by linarith),source_left_valid hm hsmall start hs⟩

theorem source_grid_mass {m : ℕ} (hm : 1 ≤ m) (hs : 0 ≤ start.ratio) :
    mass w ell S start m 0 (index m start) = 1 := by
  have hcell : some (History.empty : History w ell S start) ∈ bin m (index m start) := source_cell hm start hs
  change Measure.dirac (some (History.empty : History w ell S start)) (bin m (index m start)) = 1
  rw [Measure.dirac_apply' _ (bin_measurable _ _),indicator_of_mem hcell,Pi.one_apply]

theorem bin_empty_above (hsS : start.ratio ≤ S) {m j : ℕ} (hhigh : S < point m j) :
    (bin (w:=w) (ell:=ell) (S:=S) (start:=start) m j) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  cases p with
  | none => exact False.elim hp
  | some g =>
    have hcap : g.node.ratio ≤ S := terminal_ratio_le hsS g.admissible
    exact ((mem_bin g m j).mp hp).1.not_gt (hcap.trans_lt hhigh)

theorem mass_zero_above (hsS : start.ratio ≤ S) {m j : ℕ} (hhigh : S < point m j) (n : ℕ) :
    mass w ell S start m n j = 0 := by
  rw [mass,bin_empty_above hsS hhigh,measure_empty]

end NumberTheoryLean.SourceParentBin

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeMarginalInduction
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section


namespace NumberTheoryLean.PrimeMarginalInduction

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeSideSupport PrimeGridGeometry PrimeGridKernel
open PrimeMarginalRecursion MarginalProfiles MarginalTransport SourceParentBin ExponentialMesh DerivativeWeights

theorem finite_marginal_profiles : ∃ κ₀ L : ℝ, 0 < κ₀ ∧ 0 < L ∧
    ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∃ w₀ : ℝ, 1 < w₀ ∧ ∀ w : ℝ, w₀ ≤ w →
    ∀ ell S : ℝ, 3 ≤ S → S ≤ (Real.log w)^3 → ∀ start : Node,
      1 ≤ ell → 0 < start.gap → start.side = .even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
      ∀ m : ℕ, 1 ≤ m → width m = mesh κ w → width m ≤ 1/100 →
      (∀ n,IsProbabilityMeasure (pathLaw w ell S start n)) ∧
      (∀ j,Valid .odd (point m j) → mass w ell S start m 1 j ≤
        ENNReal.ofReal (initialConstant*MarginalGrowth.factor L κ w S*width m*W (point m j)*weight .odd (point m j))) ∧
      (∀ n,2 ≤ n → ∀ j,lowerIndex m (sideAfter .even n) ≤ j → mass w ell S start m n j ≤
        ENNReal.ofReal ((24*initialConstant)*(MarginalGrowth.factor L κ w S)^n*width m*
          weight (sideAfter .even n) (point m j)*profile m (sideAfter .even n) (point m j))) := by
  obtain ⟨κ₀,L,hκ₀,hL,hcovered⟩ := covered_recursion
  refine ⟨κ₀,L,hκ₀,hL,?_⟩
  intro κ hκ hκle
  obtain ⟨wR,hwR,hrec⟩ := hcovered κ hκ hκle
  refine ⟨max wR normalizationThreshold,hwR.trans_le (le_max_left _ _),?_⟩
  intro w hw ell S hS3 hS start hell hr hi h199 h23 m hm hmesh hsmall
  have hwR' := (le_max_left _ _).trans hw
  have hnorm := (le_max_right _ _).trans hw
  have hs : Valid start.side start.ratio := by rw [hi,Valid]; linarith
  have hsS : start.ratio ≤ S := by linarith
  have hC0 := initialConstant_pos.le
  have hg := (MarginalGrowth.factor_pos L κ w S).le
  have hwidth := width_nonneg m
  refine ⟨fun n => pathLaw_isProbability hnorm hell (by linarith) hS hr hs hsS n,?_⟩
  have hfirst : ∀ j,Valid .odd (point m j) → mass w ell S start m 1 j ≤
      ENNReal.ofReal (initialConstant*MarginalGrowth.factor L κ w S*width m*W (point m j)*weight .odd (point m j)) := by
    intro j hjV
    by_cases hjS : point m j ≤ S
    · have hbase := hrec w hwR' ell S hS3 hS start hell hr hs hsS m 0 j hm hmesh .even {index m start}
        hjV hjS (source_coverage hm hsmall hi h199 j)
      rw [Finset.sum_singleton,source_grid_mass hm (by linarith : 0 ≤ start.ratio),mul_one] at hbase
      have hInv := source_inverse_weight hm hsmall start h199 h23
      have hkV := source_left_valid hm hsmall start h199
      have hWt := (WeightFutureIntegrals.W_pos (valid_pos hjV)).le
      have hφ := (weight_pos hjV).le
      have hFactor : 0 ≤ width m*W (point m j)*weight .odd (point m j) := by positivity
      refine hbase.trans (ENNReal.ofReal_le_ofReal ?_)
      calc
        _ = (rowFactor L κ w S*(width m*W (point m j)*weight .odd (point m j)))*
            (1/weight .even (point m (index m start))) := by unfold entry rowFactor; simp only [Side.flip] <;> ring
        _ ≤ (MarginalGrowth.factor L κ w S*(width m*W (point m j)*weight .odd (point m j)))*initialConstant :=
          mul_le_mul (mul_le_mul_of_nonneg_right (row_le_factor L κ w S) hFactor) hInv
            (one_div_nonneg.mpr (weight_pos hkV).le) (by positivity)
        _ = _ := by ring
    · rw [mass_zero_above hsS (lt_of_not_ge hjS) 1]
      exact zero_le
  have hsecond : ∀ j,2*m ≤ j → mass w ell S start m 2 j ≤
      ENNReal.ofReal ((24*initialConstant)*(MarginalGrowth.factor L κ w S)^2*width m*weight .even (point m j)) := by
    intro j hj
    by_cases hjS : point m j ≤ S
    · have hjV : Valid .even (point m j) := index_valid hm .even hj
      have hcover := weak_coverage (w:=w) (ell:=ell) (S:=S) hs hi hm hsmall 1 (by omega) j
      have hbase := hrec w hwR' ell S hS3 hS start hell hr hs hsS m 1 j hm hmesh .odd (weakIndices m j .odd)
        hjV hjS (by simpa only [sideAfter,Side.flip] using hcover)
      exact hbase.trans (first_to_second L κ w S initialConstant hm j hj (fun k => mass w ell S start m 1 k) hC0 hfirst)
    · rw [mass_zero_above hsS (lt_of_not_ge hjS) 2]
      exact zero_le
  refine ⟨hfirst,?_⟩
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    intro j hj
    have hj' : 2*m ≤ j := hj
    simpa only [sideAfter,Side.flip,profile,mul_one] using hsecond j hj'
  | succ n hn ih =>
    intro j hj
    by_cases hjS : point m j ≤ S
    · let i := sideAfter .even n
      have hj' : lowerIndex m i.flip ≤ j := hj
      have hjV := index_valid hm i.flip hj'
      have hbase := hrec w hwR' ell S hS3 hS start hell hr hs hsS m n j hm hmesh i
        (Finset.Icc (lowerIndex m i) (j+m+1)) hjV hjS (regular_coverage hs hi hm n hn j)
      have hnext := profile_step L κ w S (24*initialConstant) hm hmesh n j i
        (fun k => mass w ell S start m n k) (by positivity) hj' (fun k hk => ih k hk)
      exact hbase.trans hnext
    · rw [mass_zero_above hsS (lt_of_not_ge hjS) (n+1)]
      exact zero_le

end NumberTheoryLean.PrimeMarginalInduction

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourceMarginalRate
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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
open UniformFailureBudget ExponentialMesh BudgetPolynomialBound HorizonMeshSmallness PrimeKilledChain

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

section

namespace NumberTheoryLean.SourceMarginalRate

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeSideSupport PrimeGridGeometry PrimeGridKernel
open PrimeMarginalInduction MarginalProfiles SourceParentBin ExponentialMesh UniformBudgetRate
open DerivativeWeights LowStateHorizon

theorem mesh_eventually_small {κ ε : ℝ} (hκ : 0 < κ) (hε : 0 < ε) :
    ∀ᶠ w : ℝ in atTop, mesh κ w ≤ ε := by
  have ht := log_power_exp_tendsto 1 0 hκ
  filter_upwards [ht.eventually (eventually_lt_nhds hε)] with w hw
  have he : Real.exp (-κ*Real.sqrt (Real.log w)) < ε := by simpa only [pow_zero,one_mul] using hw
  exact (mesh_upper κ w).trans he.le

theorem source_discrete_marginals : ∃ κ₀ C : ℝ, 0 < κ₀ ∧ 0 < C ∧
    ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∀ d : ℝ, 0 < d → ∃ w₀ : ℝ, 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ ell B : ℝ, ∀ start : Node,
      1 ≤ ell → 0 < B → 2 ≤ Real.log B → Real.log B ≤ d*Real.log w →
      0 < start.gap → start.side = .even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
      let S := (Real.log B)^2
      let N := sourceHorizon S B
      let m := ⌈Real.exp (κ*Real.sqrt (Real.log w))⌉₊
      (∀ n,IsProbabilityMeasure (pathLaw w ell S start n)) ∧
      (∀ j,Valid .odd (point m j) → mass w ell S start m 1 j ≤
        ENNReal.ofReal (C*width m*W (point m j)*weight .odd (point m j))) ∧
      (∀ n,2 ≤ n → n ≤ N → ∀ j,lowerIndex m (sideAfter .even n) ≤ j → mass w ell S start m n j ≤
        ENNReal.ofReal (C*width m*weight (sideAfter .even n) (point m j)*profile m (sideAfter .even n) (point m j))) := by
  obtain ⟨κ₀,L,hκ₀,hL,hprofiles⟩ := finite_marginal_profiles
  have hCpos := initialConstant_pos
  refine ⟨κ₀,48*initialConstant,hκ₀,by positivity,?_⟩
  intro κ hκ hκle d hd
  obtain ⟨wP,hwP,hprofiles⟩ := hprofiles κ hκ hκle
  let A := 5*d^3
  have hA : 0 ≤ A := by dsimp [A] <;> positivity
  have hevent := (MarginalGrowth.factor_power_bounded hA hL.le hκ).and
    ((mesh_eventually_small hκ (by norm_num : (0:ℝ) < 1/100)).and
      (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (d^2))))
  obtain ⟨W₀,hW₀⟩ := eventually_atTop.mp hevent
  refine ⟨max wP W₀,hwP.trans_le (le_max_left _ _),?_⟩
  intro w hw ell B start hell _hB hlogB hcomp hr hi h199 h23
  dsimp only
  let S := (Real.log B)^2
  let N := sourceHorizon S B
  let m := ⌈Real.exp (κ*Real.sqrt (Real.log w))⌉₊
  have hwe := hW₀ w ((le_max_right _ _).trans hw)
  have hscale := source_scale_bound hwe.2.2 hlogB hcomp
  have hS0 : 0 ≤ S := sq_nonneg _
  have hS3 : 3 ≤ S := by dsimp [S] <;> nlinarith
  have hS : S ≤ (Real.log w)^3 := hscale.1
  have hN : (N:ℝ) ≤ A*(Real.log w)^3 := hscale.2
  have hm : 1 ≤ m := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hmesh : width m = mesh κ w := rfl
  have hsmall : width m ≤ 1/100 := by rw [hmesh]; exact hwe.2.1
  have hp := hprofiles w ((le_max_left _ _).trans hw) ell S hS3 hS start hell hr hi h199 h23 m hm hmesh hsmall
  have hC0 := initialConstant_pos.le
  have hwidth := width_nonneg m
  have hNpos : 1 ≤ N := by dsimp [N,sourceHorizon]; omega
  have hOne : (1:ℝ) ≤ A*(Real.log w)^3 := by
    have h : ((1:ℕ):ℝ) ≤ (N:ℝ) := by exact_mod_cast hNpos
    simpa only [Nat.cast_one] using h.trans hN
  have hG : MarginalGrowth.factor L κ w S ≤ 2 := by
    simpa only [pow_one] using hwe.1 S hS0 hS 1 (by simpa only [Nat.cast_one] using hOne)
  refine ⟨hp.1,?_,?_⟩
  · intro j hjV
    have hb := hp.2.1 j hjV
    have hWt := (WeightFutureIntegrals.W_pos (valid_pos hjV)).le
    have hφ := (weight_pos hjV).le
    have hC : initialConstant*MarginalGrowth.factor L κ w S ≤ 48*initialConstant := by nlinarith
    exact hb.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hwidth) hWt) hφ))
  · intro n hn2 hnN j hj
    have hb := hp.2.2 n hn2 j hj
    have hn : (n:ℝ) ≤ A*(Real.log w)^3 := (show (n:ℝ) ≤ (N:ℝ) by exact_mod_cast hnN).trans hN
    have hGn := hwe.1 S hS0 hS n hn
    have hφ := (weight_pos (index_valid hm (sideAfter .even n) hj)).le
    have hProf := profile_nonneg m (index_regular hm (sideAfter .even n) hj)
    have hC : (24*initialConstant)*(MarginalGrowth.factor L κ w S)^n ≤ 48*initialConstant := by nlinarith
    exact hb.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hwidth) hφ) hProf))

end NumberTheoryLean.SourceMarginalRate

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeInverseBins
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.PrimeInverseBins

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeSideSupport
open PrimeGridGeometry PrimeGridKernel GridWeightComparison DerivativeWeights MarginalProfiles

variable {w ell S : ℝ} {start : Node}

theorem actual_inverse_bin_local : ∃ L : ℝ,0 < L ∧
    ∀ w ell S : ℝ,3 ≤ S → ∀ start : Node,
      Valid start.side start.ratio → start.side = .even → start.ratio ≤ S →
      ∀ m n j : ℕ,Valid (sideAfter .even n) (point m j) →
        inverseBin w ell S start m n j ≤
          ENNReal.ofReal (Real.exp (L*(1+S)^3*width m)/weight (sideAfter .even n) (point m j))*
            mass w ell S start m n j := by
  obtain ⟨L,hL,hlocal⟩ := weight_local_ratio
  refine ⟨L,hL,?_⟩
  intro w ell S hS start hs hi hsS m n j hj
  let c := Real.exp (L*(1+S)^3*width m)/weight (sideAfter .even n) (point m j)
  have hpoint : ∀ᵐ z ∂(pathLaw w ell S start n).restrict (bin m j),inverseWeight z ≤ ENNReal.ofReal c := by
    filter_upwards [ae_restrict_of_ae (pathLaw_side hi n),ae_restrict_mem (bin_measurable m j)] with z hz hbin
    cases z with
    | none => exact False.elim hbin
    | some h =>
      have hcell := (mem_bin h m j).mp hbin
      have hgv : Valid h.node.side h.node.ratio := terminal_valid hs h.admissible
      have hgS : h.node.ratio ≤ S := terminal_ratio_le hsS h.admissible
      have hj' : Valid h.node.side (point m j) := by rwa [hz]
      have hlast : h.node.ratio ≤ point m j+width m := by
        rw [point_succ] at hcell
        exact hcell.2.le
      have hr := hlocal S hS h.node.side (point m j) h.node.ratio (width m) hj' hgv hgS hcell.1 hlast
      have hratio : 1/weight h.node.side h.node.ratio ≤
          Real.exp (L*(1+S)^3*width m)/weight h.node.side (point m j) := by
        have heq : 1/weight h.node.side h.node.ratio =
            (weight h.node.side (point m j)/weight h.node.side h.node.ratio)/weight h.node.side (point m j) := by
          field_simp [(weight_pos hj').ne']
        rw [heq]
        exact div_le_div_of_nonneg_right hr (weight_pos hj').le
      change ENNReal.ofReal (1/weight h.node.side h.node.ratio) ≤ _
      apply ENNReal.ofReal_le_ofReal
      simpa only [c,hz] using hratio
  calc
    _ ≤ ∫⁻ _z in bin m j,ENNReal.ofReal c ∂pathLaw w ell S start n := lintegral_mono_ae hpoint
    _ = _ := by rw [setLIntegral_const]; rfl

theorem cancel_inverse_bin {C E F : ℝ} {m n j : ℕ}
    (hE : 0 ≤ E)
    (hj : Valid (sideAfter .even n) (point m j))
    (hlocal : inverseBin w ell S start m n j ≤
      ENNReal.ofReal (E/weight (sideAfter .even n) (point m j))*mass w ell S start m n j)
    (hmass : mass w ell S start m n j ≤
      ENNReal.ofReal (C*width m*weight (sideAfter .even n) (point m j)*F)) :
    inverseBin w ell S start m n j ≤ ENNReal.ofReal (E*C*width m*F) := by
  have hφ := weight_pos hj
  have hw := width_nonneg m
  refine hlocal.trans ((mul_le_mul_of_nonneg_left hmass zero_le).trans ?_)
  rw [← ENNReal.ofReal_mul (div_nonneg hE hφ.le)]
  apply le_of_eq
  congr 1
  field_simp

theorem profile_le_nineteen {m : ℕ} {i : Side} {t : ℝ}
    (hm : width m ≤ 1) (ht : regularLower i ≤ t) : profile m i t ≤ 19 := by
  cases i with
  | even => norm_num [profile]
  | odd =>
    have ht1 : 1 ≤ t := ht
    have hW := W_le_six (by linarith : (1:ℝ)/2 ≤ t)
    have hW0 := (WeightFutureIntegrals.W_pos (by linarith : 0 < t)).le
    have hw := width_nonneg m
    have hh : width m*W t ≤ 6 :=
      (mul_le_mul hm hW hW0 zero_le_one).trans_eq (one_mul 6)
    have hinv : 0 ≤ 1/t^2 := by positivity
    change 1-1/t^2+3*width m*W t ≤ 19
    nlinarith

end NumberTheoryLean.PrimeInverseBins

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_SourceAllInverseBins
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SourceInverseBinRate

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeSideSupport
open PrimeGridGeometry PrimeGridKernel PrimeInverseBins DerivativeWeights MarginalProfiles
open SourceMarginalRate ExponentialMesh UniformBudgetRate HorizonMeshSmallness LowStateHorizon

theorem source_inverse_bins : ∃ κ₀ C : ℝ,0 < κ₀ ∧ 0 < C ∧
    ∀ κ : ℝ,0 < κ → κ ≤ κ₀ → ∀ d : ℝ,0 < d → ∃ w₀ : ℝ,1 < w₀ ∧
      ∀ w : ℝ,w₀ ≤ w → ∀ ell B : ℝ,∀ start : Node,
        1 ≤ ell → 0 < B → 2 ≤ Real.log B → Real.log B ≤ d*Real.log w →
        0 < start.gap → start.side = .even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        let S := (Real.log B)^2
        let N := sourceHorizon S B
        let m := ⌈Real.exp (κ*Real.sqrt (Real.log w))⌉₊
        (∀ j,Valid .odd (point m j) → inverseBin w ell S start m 1 j ≤ ENNReal.ofReal (C*width m)) ∧
        (∀ n,2 ≤ n → n ≤ N → ∀ j,lowerIndex m (sideAfter .even n) ≤ j →
          inverseBin w ell S start m n j ≤ ENNReal.ofReal (C*width m)) := by
  obtain ⟨κ₀,C,hκ₀,hC,hsource⟩ := source_discrete_marginals
  obtain ⟨L,hL,hlocal⟩ := actual_inverse_bin_local
  refine ⟨κ₀,57*C,hκ₀,by positivity,?_⟩
  intro κ hκ hκle d hd
  obtain ⟨wP,hwP,hsource⟩ := hsource κ hκ hκle d hd
  have hevent := (horizon_mesh_smallness (A:=0) (D:=L) (by norm_num) hL.le hκ).and
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (d^2)))
  obtain ⟨wAux,hwAux⟩ := eventually_atTop.mp hevent
  refine ⟨max wP wAux,hwP.trans_le (le_max_left _ _),?_⟩
  intro w hw ell B start hell hB hlogB hcomp hr hi h199 h23
  dsimp only
  let S := (Real.log B)^2
  let N := sourceHorizon S B
  let m := ⌈Real.exp (κ*Real.sqrt (Real.log w))⌉₊
  have hs : Valid start.side start.ratio := by rw [hi]; change 198/100 ≤ start.ratio; linarith
  have hwe := hwAux w ((le_max_right _ _).trans hw)
  have hscale := source_scale_bound hwe.2 hlogB hcomp
  have hS0 : 0 ≤ S := sq_nonneg _
  have hS3 : 3 ≤ S := by dsimp [S] <;> nlinarith
  have hsS : start.ratio ≤ S := by linarith
  have hm : 1 ≤ m := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hmesh : width m = mesh κ w := rfl
  have hsmall := hwe.1 S hS0 hscale.1 0 (by simp)
  have hh : width m ≤ 1 := by rw [hmesh]; linarith [hsmall.1]
  have hE : Real.exp (L*(1+S)^3*width m) ≤ 3 := by
    rw [hmesh]
    exact (Real.exp_le_exp.mpr hsmall.2.2.1).trans Real.exp_one_lt_three.le
  have hprofiles := hsource w ((le_max_left _ _).trans hw) ell B start hell hB hlogB hcomp hr hi h199 h23
  have hwidth := width_nonneg m
  have hE0 := (Real.exp_pos (L*(1+S)^3*width m)).le
  constructor
  · intro j hj
    have hj' : Valid (sideAfter .even 1) (point m j) := hj
    have hmass : mass w ell S start m 1 j ≤
        ENNReal.ofReal (C*width m*weight (sideAfter .even 1) (point m j)*W (point m j)) := by
      simpa only [sideAfter,Side.flip,mul_assoc,mul_comm,mul_left_comm] using hprofiles.2.1 j hj
    have hb := cancel_inverse_bin hE0 hj' (hlocal w ell S hS3 start hs hi hsS m 1 j hj') hmass
    have ht : (1:ℝ)/2 ≤ point m j := by change 95/100 ≤ point m j at hj; linarith
    have hW := W_le_six ht
    have hW0 := (WeightFutureIntegrals.W_pos (by linarith : 0 < point m j)).le
    refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
    calc
      _ ≤ 3*C*width m*6 := mul_le_mul
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hE hC.le) hwidth) hW hW0 (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg hC.le hwidth]
  · intro n hn hnN j hj
    have hjV := index_valid hm (sideAfter .even n) hj
    have hb := cancel_inverse_bin hE0 hjV (hlocal w ell S hS3 start hs hi hsS m n j hjV)
      (hprofiles.2.2 n hn hnN j hj)
    have hprof := profile_le_nineteen hh (index_regular hm (sideAfter .even n) hj)
    have hp0 := profile_nonneg m (index_regular hm (sideAfter .even n) hj)
    refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
    calc
      _ ≤ 3*C*width m*19 := mul_le_mul
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hE hC.le) hwidth) hprof hp0 (by positivity)
      _ = _ := by ring

end NumberTheoryLean.SourceInverseBinRate

end

section

namespace NumberTheoryLean.SourceAllInverseBins

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeSideSupport
open PrimeGridGeometry PrimeGridKernel PrimeInverseBins SourceInverseBinRate
open SourceMarginalRate ExponentialMesh LowStateHorizon

variable {w ell S : ℝ} {start : Node}

theorem inverse_bin_zero_first {m j : ℕ} (hm : 1 ≤ m) (hsmall : width m ≤ 1/100)
    (hs : Valid start.side start.ratio) (hi : start.side = .even)
    (hj : ¬Valid .odd (point m j)) : inverseBin w ell S start m 1 j = 0 := by
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_of_ae (pathLaw_side (w:=w) (ell:=ell) (S:=S) hi 1),
    ae_restrict_of_ae (pathLaw_weak hs 1 le_rfl),ae_restrict_mem (bin_measurable m j)] with z hz hweak hbin
  cases z with
  | none => exact False.elim hbin
  | some h =>
    have hv := weak_bin_domain hm hsmall hweak ((mem_bin h m j).mp hbin)
    have he : h.node.side = .odd := hz
    rw [he] at hv
    exact False.elim (hj hv)

theorem inverse_bin_zero_lower {m n j : ℕ} (hm : 1 ≤ m) (hn : 2 ≤ n)
    (hi : start.side = .even) (hj : j < lowerIndex m (sideAfter .even n)) :
    inverseBin w ell S start m n j = 0 := by
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_of_ae (pathLaw_side (w:=w) (ell:=ell) (S:=S) hi n),
    ae_restrict_of_ae (pathLaw_regular (w:=w) (ell:=ell) (S:=S) (start:=start) n hn),
    ae_restrict_mem (bin_measurable m j)] with z hz hreg hbin
  cases z with
  | none => exact False.elim hbin
  | some h =>
    have hv := (regular_bin_domain hm hreg ((mem_bin h m j).mp hbin)).1
    rw [hz] at hv
    omega

theorem source_all_inverse_bins : ∃ κ₀ C : ℝ,0 < κ₀ ∧ 0 < C ∧
    ∀ κ : ℝ,0 < κ → κ ≤ κ₀ → ∀ d : ℝ,0 < d → ∃ w₀ : ℝ,1 < w₀ ∧
      ∀ w : ℝ,w₀ ≤ w → ∀ ell B : ℝ,∀ start : Node,
        1 ≤ ell → 0 < B → 2 ≤ Real.log B → Real.log B ≤ d*Real.log w →
        0 < start.gap → start.side = .even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        let S := (Real.log B)^2
        let N := sourceHorizon S B
        let m := ⌈Real.exp (κ*Real.sqrt (Real.log w))⌉₊
        ∀ n,1 ≤ n → n ≤ N → ∀ j,inverseBin w ell S start m n j ≤ ENNReal.ofReal (C*width m) := by
  obtain ⟨κ₀,C,hκ₀,hC,hsource⟩ := source_inverse_bins
  refine ⟨κ₀,C,hκ₀,hC,?_⟩
  intro κ hκ hκle d hd
  obtain ⟨wP,hwP,hsource⟩ := hsource κ hκ hκle d hd
  obtain ⟨wAux,hwAux⟩ := eventually_atTop.mp (mesh_eventually_small hκ (by norm_num : (0:ℝ) < 1/100))
  refine ⟨max wP wAux,hwP.trans_le (le_max_left _ _),?_⟩
  intro w hw ell B start hell hB hlogB hcomp hr hi h199 h23
  dsimp only
  let m := ⌈Real.exp (κ*Real.sqrt (Real.log w))⌉₊
  have hm : 1 ≤ m := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hh : width m ≤ 1/100 := hwAux w ((le_max_right _ _).trans hw)
  have hs : Valid start.side start.ratio := by rw [hi]; change 198/100 ≤ start.ratio; linarith
  have hb := hsource w ((le_max_left _ _).trans hw) ell B start hell hB hlogB hcomp hr hi h199 h23
  intro n hn hnN j
  by_cases he : n=1
  · subst n
    by_cases hj : Valid .odd (point m j)
    · exact hb.1 j hj
    · rw [inverse_bin_zero_first hm hh hs hi hj]
      exact zero_le
  · have hn2 : 2 ≤ n := by omega
    by_cases hj : lowerIndex m (sideAfter .even n) ≤ j
    · exact hb.2 n hn2 hnN j hj
    · rw [inverse_bin_zero_lower hm hn2 hi (by omega : j < lowerIndex m (sideAfter .even n))]
      exact zero_le

end NumberTheoryLean.SourceAllInverseBins

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_PrimeExponentialTail
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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

theorem reward_le_envelope {c r K t : ℝ} (hc : 0 < c) (hr : 0 ≤ r)
    (hK : K ≤ r) (ht : t ≤ r) : r^2*Real.exp (-c*r) ≤ envelope c K t := by
  refine (quadratic_exp_majorant hc hr).trans ?_
  unfold envelope
  rw [mul_assoc,← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  nlinarith

theorem exponential_mesh_sum {a h : ℝ} (ha : 0 < a) (hh : 0 < h) (N : ℕ) :
    (∑ j ∈ range N,h*Real.exp (-a*((j:ℝ)*h))) ≤ h+1/a := by
  let e := Real.exp (-a*h)
  have he0 : 0 < e := Real.exp_pos _
  have he1 : e < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hg : (∑ j ∈ range N,e^j) ≤ 1/(1-e) := by
    simpa only [Nat.Ico_zero_eq_range,pow_zero] using
      (geom_sum_Ico_le_of_lt_one (m:=0) (n:=N) he0.le he1)
  have heq : (∑ j ∈ range N,h*Real.exp (-a*((j:ℝ)*h))) = h*(∑ j ∈ range N,e^j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    dsimp [e]
    rw [← Real.exp_nat_mul]
    congr 2
    ring
  have hbasic : (1+a*h)*e ≤ 1 := by
    calc
      _ ≤ Real.exp (a*h)*e := mul_le_mul_of_nonneg_right (by simpa only [add_comm] using Real.add_one_le_exp (a*h)) he0.le
      _ = _ := by dsimp [e]; rw [← Real.exp_add]; simp
  have hInv : a*(1/a) = 1 := by field_simp
  have hden : 0 < 1-e := by linarith
  have hlast : h/(1-e) ≤ h+1/a := by
    apply (div_le_iff₀ hden).mpr
    have hinv0 : 0 < 1/a := one_div_pos.mpr ha
    have hm := mul_le_mul_of_nonneg_left hbasic hinv0.le
    nlinarith
  rw [heq]
  exact (mul_le_mul_of_nonneg_left hg hh.le).trans (by simpa only [mul_one_div] using hlast)

theorem envelope_mesh_sum {c h : ℝ} (hc : 0 < c) (hh : 0 < h) (hh1 : h ≤ 1) (K : ℝ) (N : ℕ) :
    (∑ j ∈ range N,h*envelope c K ((j:ℝ)*h)) ≤
      (8/c^2)*(1+4/c)*Real.exp (-c*K/4) := by
  have hb := exponential_mesh_sum (a:=c/4) (by positivity) hh N
  have heq : (∑ j ∈ range N,h*envelope c K ((j:ℝ)*h)) =
      ((8/c^2)*Real.exp (-c*K/4))*(∑ j ∈ range N,h*Real.exp (-(c/4)*((j:ℝ)*h))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    unfold envelope
    rw [show -(c/4)*((j:ℝ)*h) = -c*((j:ℝ)*h)/4 by ring]
    ring
  rw [heq]
  have hconst : 0 ≤ (8/c^2)*Real.exp (-c*K/4) := by positivity
  calc
    _ ≤ ((8/c^2)*Real.exp (-c*K/4))*(h+1/(c/4)) := mul_le_mul_of_nonneg_left hb hconst
    _ ≤ ((8/c^2)*Real.exp (-c*K/4))*(1+4/c) := by
      apply mul_le_mul_of_nonneg_left _ hconst
      have he : 1/(c/4) = 4/c := by ring
      rw [he]
      linarith
    _ = _ := by ring

end NumberTheoryLean.ExponentialMeshTail

end

section

namespace NumberTheoryLean.PrimeExponentialTail

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeBinMembership
open PrimeGridGeometry PrimeGridKernel PrimeInverseBins PrimeCompactWeights ExponentialMeshTail DerivativeWeights

variable {w ell S : ℝ} {start : Node}

theorem grid_above {m : ℕ} (hm : 1 ≤ m) (S : ℝ) :
    S < point m (⌈S*(m:ℝ)⌉₊+1) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hceil := Nat.le_ceil (S*(m:ℝ))
  unfold point
  apply (lt_div_iff₀ hm0).mpr
  push_cast
  linarith

theorem actual_tail_bin_envelope {c K : ℝ} (hc : 0 < c) {m : ℕ} (hm : 1 ≤ m)
    (hell : 1 ≤ ell) (hr : 0 < start.gap) (hs : Valid start.side start.ratio)
    (hcons : Consistent start) (hcut : ell ≤ start.cutoff) (hsS : start.ratio ≤ S)
    (z : ChainState w ell S start) :
    tailReward c K z ≤ ∑ j ∈ range (⌈S*(m:ℝ)⌉₊+1),
      ENNReal.ofReal (envelope c K (point m j))*(bin m j).indicator inverseWeight z := by
  classical
  cases z with
  | none => exact zero_le
  | some h =>
    by_cases hh : K < h.node.gap
    · have hg : 0 < h.node.gap := terminal_gap_positive (by linarith) hr hs h.admissible
      have hv : Valid h.node.side h.node.ratio := terminal_valid hs h.admissible
      have hs0 := (valid_pos hv).le
      have hS : h.node.ratio ≤ S := terminal_ratio_le hsS h.admissible
      obtain ⟨j,hj,hcell⟩ := finite_grid_cover hm hs0 (hS.trans_lt (grid_above hm S))
      have hmem : some h ∈ bin m j := (mem_bin h m j).mpr hcell
      have hratio : point m j ≤ h.node.gap := hcell.1.trans (history_ratio_le_gap hell hr hs hcons hcut h)
      have hreward := reward_le_envelope hc hg.le hh.le hratio
      have hφ := weight_pos hv
      have hterm : tailReward c K (some h) ≤
          ENNReal.ofReal (envelope c K (point m j))*(bin m j).indicator inverseWeight (some h) := by
        rw [indicator_of_mem hmem]
        change (if K < h.node.gap then _ else _) ≤ ENNReal.ofReal _*ENNReal.ofReal _
        rw [ite_eq_left hh,← ENNReal.ofReal_mul (by unfold envelope; positivity)]
        apply ENNReal.ofReal_le_ofReal
        simpa only [mul_one_div] using div_le_div_of_nonneg_right hreward hφ.le
      exact hterm.trans (Finset.single_le_sum (s:=range (⌈S*(m:ℝ)⌉₊+1)) (a:=j)
        (f:=fun k => ENNReal.ofReal (envelope c K (point m k))*(bin m k).indicator inverseWeight (some h))
        (fun _ _ => zero_le) (by simpa only [Finset.mem_range] using Nat.lt_succ_of_le hj))
    · simp only [tailReward,ite_eq_right hh]
      exact zero_le

theorem actual_tail_integral_bins {c K : ℝ} (hc : 0 < c) {m : ℕ} (hm : 1 ≤ m)
    (hell : 1 ≤ ell) (hr : 0 < start.gap) (hs : Valid start.side start.ratio)
    (hcons : Consistent start) (hcut : ell ≤ start.cutoff) (hsS : start.ratio ≤ S) (n : ℕ) :
    (∫⁻ z,tailReward c K z ∂pathLaw w ell S start n) ≤
      ∑ j ∈ range (⌈S*(m:ℝ)⌉₊+1),ENNReal.ofReal (envelope c K (point m j))*inverseBin w ell S start m n j := by
  calc
    _ ≤ ∫⁻ z,∑ j ∈ range (⌈S*(m:ℝ)⌉₊+1),
        ENNReal.ofReal (envelope c K (point m j))*(bin m j).indicator inverseWeight z ∂pathLaw w ell S start n :=
      lintegral_mono (actual_tail_bin_envelope hc hm hell hr hs hcons hcut hsS)
    _ = _ := by
      rw [lintegral_finsetSum]
      · apply Finset.sum_congr rfl
        intro j _hj
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_indicator (bin_measurable m j)]
        rfl
      · intro j _hj
        exact measurable_const.mul ((measurable_of_countable inverseWeight).indicator (bin_measurable m j))

theorem actual_tail_from_inverse_bins {c K C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    {m : ℕ} (hm : 1 ≤ m) (hm1 : width m ≤ 1)
    (hell : 1 ≤ ell) (hr : 0 < start.gap) (hs : Valid start.side start.ratio)
    (hcons : Consistent start) (hcut : ell ≤ start.cutoff) (hsS : start.ratio ≤ S) (n : ℕ)
    (hbins : ∀ j,inverseBin w ell S start m n j ≤ ENNReal.ofReal (C*width m)) :
    (∫⁻ z,tailReward c K z ∂pathLaw w ell S start n) ≤
      ENNReal.ofReal (C*(8/c^2)*(1+4/c)*Real.exp (-c*K/4)) := by
  have hh := width_pos hm
  refine (actual_tail_integral_bins hc hm hell hr hs hcons hcut hsS n).trans ?_
  calc
    _ ≤ ∑ j ∈ range (⌈S*(m:ℝ)⌉₊+1),ENNReal.ofReal (envelope c K (point m j))*ENNReal.ofReal (C*width m) :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hbins j) zero_le)
    _ = ENNReal.ofReal (C*(∑ j ∈ range (⌈S*(m:ℝ)⌉₊+1),width m*envelope c K (point m j))) := by
      rw [Finset.mul_sum,ENNReal.ofReal_sum_of_nonneg]
      · apply Finset.sum_congr rfl
        intro j _hj
        rw [← ENNReal.ofReal_mul (by unfold envelope; positivity)]
        congr 1
        ring
      · intro j _hj
        unfold envelope
        positivity
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have he : ∀ j : ℕ,point m j = (j:ℝ)*width m := by intro j; unfold point width; ring
      simp only [he]
      have h := envelope_mesh_sum hc hh hm1 K (⌈S*(m:ℝ)⌉₊+1)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h hC

end NumberTheoryLean.PrimeExponentialTail

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_GrowingFarTail
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SourceFarGapTail

open _root_.Set _root_.Filter _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeBinMembership
open PrimeGridGeometry PrimeGridKernel PrimeInverseBins PrimeExponentialTail
open SourceAllInverseBins ExponentialMesh LowStateHorizon

theorem source_far_gap_tail : ∃ κ₀ C : ℝ,0 < κ₀ ∧ 0 < C ∧
    ∀ κ : ℝ,0 < κ → κ ≤ κ₀ → ∀ d : ℝ,0 < d → ∃ w₀ : ℝ,1 < w₀ ∧
      ∀ w : ℝ,w₀ ≤ w → ∀ ell B : ℝ,∀ start : Node,
        1 ≤ ell → ell ≤ B → 0 < B → 2 ≤ Real.log B → Real.log B ≤ d*Real.log w →
        0 < start.gap → start.side = .even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff = B →
        let S := (Real.log B)^2
        let N := sourceHorizon S B
        ∀ c : ℝ,0 < c → ∀ K : ℝ,
        (∀ n,1 ≤ n → n ≤ N → (∫⁻ z,tailReward c K z ∂pathLaw w ell S start n) ≤
          ENNReal.ofReal (C*(8/c^2)*(1+4/c)*Real.exp (-c*K/4))) ∧
        ((∑ n ∈ range N,∫⁻ z,tailReward c K z ∂pathLaw w ell S start (n+1)) ≤
          (N:ℝ≥0∞)*ENNReal.ofReal (C*(8/c^2)*(1+4/c)*Real.exp (-c*K/4))) := by
  obtain ⟨κ₀,C,hκ₀,hC,hsource⟩ := source_all_inverse_bins
  refine ⟨κ₀,C,hκ₀,hC,?_⟩
  intro κ hκ hκle d hd
  obtain ⟨w₀,hw₀,hsource⟩ := hsource κ hκ hκle d hd
  refine ⟨w₀,hw₀,?_⟩
  intro w hw ell B start hell hellB hB hlogB hcomp hr hi h199 h23 hcons hcut
  dsimp only
  intro c hc K
  let S := (Real.log B)^2
  let N := sourceHorizon S B
  let m := ⌈Real.exp (κ*Real.sqrt (Real.log w))⌉₊
  have hm : 1 ≤ m := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hh : width m ≤ 1 := mesh_le_one hκ.le w
  have hs : Valid start.side start.ratio := by rw [hi]; change 198/100 ≤ start.ratio; linarith
  have hS3 : 3 ≤ S := by dsimp [S] <;> nlinarith
  have hsS : start.ratio ≤ S := by linarith
  have hb := hsource w hw ell B start hell hB hlogB hcomp hr hi h199 h23
  have hper : ∀ n,1 ≤ n → n ≤ N → (∫⁻ z,tailReward c K z ∂pathLaw w ell S start n) ≤
      ENNReal.ofReal (C*(8/c^2)*(1+4/c)*Real.exp (-c*K/4)) := by
    intro n hn hnN
    exact actual_tail_from_inverse_bins hc hC.le hm hh hell hr hs hcons (by rwa [hcut]) hsS n (hb n hn hnN)
  refine ⟨hper,?_⟩
  change (∑ n ∈ range N,∫⁻ z,tailReward c K z ∂pathLaw w ell S start (n+1)) ≤
    (N:ℝ≥0∞)*ENNReal.ofReal (C*(8/c^2)*(1+4/c)*Real.exp (-c*K/4))
  calc
    _ ≤ ∑ _n ∈ range N,ENNReal.ofReal (C*(8/c^2)*(1+4/c)*Real.exp (-c*K/4)) := by
      apply Finset.sum_le_sum
      intro n hn
      exact hper (n+1) (by omega) (by have hh := Finset.mem_range.mp hn; omega)
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]

end NumberTheoryLean.SourceFarGapTail

end

section

namespace NumberTheoryLean.GrowingFarTail

open _root_.Set _root_.Filter _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeBinMembership
open PrimeExponentialTail SourceFarGapTail SourceModerateFailure LowStateHorizon

theorem source_horizon_comparison {B d w : ℝ} (hlogB : 2 ≤ Real.log B)
    (hcomp : Real.log B ≤ d*Real.log w) :
    (sourceHorizon ((Real.log B)^2) B:ℝ) ≤ 5*d^3*(Real.log w)^3 := by
  have hN := source_horizon_log_cube hlogB
  have hp := pow_le_pow_left₀ (by linarith : 0 ≤ Real.log B) hcomp 3
  nlinarith

theorem source_growing_far_tail_jb247_oai : ∃ κ₀ C : ℝ,0 < κ₀ ∧ 0 < C ∧
    ∀ κ : ℝ,0 < κ → κ ≤ κ₀ → ∀ d : ℝ,0 < d → ∃ w₀ : ℝ,1 < w₀ ∧
      ∀ w : ℝ,w₀ ≤ w → ∀ ell B : ℝ,∀ start : Node,
        1 ≤ ell → ell ≤ B → 0 < B → 2 ≤ Real.log B → Real.log B ≤ d*Real.log w →
        0 < start.gap → start.side = .even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff = B →
        let S := (Real.log B)^2
        let N := sourceHorizon S B
        ∀ c : ℝ,0 < c →
          (∑ n ∈ range N,∫⁻ z,tailReward c (growingCutoff w) z ∂pathLaw w ell S start (n+1)) ≤
            ENNReal.ofReal (farBudget C c d w) := by
  obtain ⟨κ₀,C,hκ₀,hC,hsource⟩ := source_far_gap_tail
  refine ⟨κ₀,C,hκ₀,hC,?_⟩
  intro κ hκ hκle d hd
  obtain ⟨w₀,hw₀,hsource⟩ := hsource κ hκ hκle d hd
  refine ⟨w₀,hw₀,?_⟩
  intro w hw ell B start hell hellB hB hlogB hcomp hr hi h199 h23 hcons hcut
  dsimp only
  intro c hc
  have hb := (hsource w hw ell B start hell hellB hB hlogB hcomp hr hi h199 h23 hcons hcut c hc (growingCutoff w)).2
  have hN := source_horizon_comparison hlogB hcomp
  refine hb.trans ?_
  rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hcst : 0 ≤ C*(8/c^2)*(1+4/c)*Real.exp (-c*growingCutoff w/4) := by positivity
  have h := mul_le_mul_of_nonneg_right hN hcst
  unfold farBudget
  rw [show -(c/4)*growingCutoff w = -c*growingCutoff w/4 by ring]
  simpa only [mul_assoc,mul_left_comm,mul_comm] using h

end NumberTheoryLean.GrowingFarTail

end

end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.NumberTheoryLean.GrowingFarTail.source_growing_far_tail_jb247_oai := @OAI.Erdos970.NumberTheoryLean.GrowingFarTail.source_growing_far_tail_jb247_oai
