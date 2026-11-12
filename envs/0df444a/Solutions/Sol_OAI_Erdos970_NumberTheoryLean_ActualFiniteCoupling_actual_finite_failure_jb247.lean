-- Prove2me | solution 1 for OAI.Erdos970.NumberTheoryLean.ActualFiniteCoupling.actual_finite_failure_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:02:40.569414+00:00
-- url     : https://prove2.me/submissions/baf2f33a-90ec-43c6-9285-b2736bce130a

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

theorem nextGap_eq_cost {r t : ℝ} (ht : 0 < t) : nextGap r t = r * Real.exp (-cost t) := by
  have hx : 0 < 1 + 1 / t := by positivity
  unfold cost nextGap
  rw [Real.exp_neg, Real.exp_log hx]
  field_simp

end NumberTheoryLean.FinitePathGeometry



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
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_UniformCycleMoments
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.InitialRegeneration.hitOrReturn_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.OccupationBoundaries

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures KernelDensityBridge
open PairedCostProcess CostReturnLaw CycleOccupation

 theorem stateRatio_pos (s : State) : 0 < stateRatio s := by
  cases s with
  | inl s => change 0 < s.1; linarith [s.2]
  | inr s => change 0 < s.1; linarith [s.2]

theorem cost_add_log {t : ℝ} (ht : 0 < t) : cost t + Real.log t = Real.log (t + 1) := by
  rw [cost, ← Real.log_mul (by positivity : (1 + 1 / t : ℝ) ≠ 0) ht.ne']
  congr 1
  field_simp

end NumberTheoryLean.OccupationBoundaries



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_CostPrefixTransport
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.CostPrefixTransport

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostGrouping
open OccupationBoundaries OccupationDecomposition OccupationRegeneration
open InitialOccupation FullOccupationCovariance KernelPotential

theorem stateRatio_ge_half (s : State) : (1 / 2 : ℝ) ≤ stateRatio s := by
  cases s with
  | inl s => change (1 / 2 : ℝ) ≤ s.1; linarith [s.2]
  | inr s => change (1 / 2 : ℝ) ≤ s.1; linarith [s.2]

end NumberTheoryLean.CostPrefixTransport

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_ArrivalKernelGeometry
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.ArrivalKernelGeometry

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostGrouping
open OccupationBoundaries RegeneratingInverseBands KernelDensityBridge
open HarmonicWeightKernel KernelWeightTransform

theorem gapValue_update (v : ℝ) (z : CostState) (s : State) :
    gapValue v (s, z.2 + cost (stateRatio s)) = nextGap (gapValue v z) (stateRatio s) := by
  rw [nextGap_eq_cost (stateRatio_pos s)]
  change Real.exp (v - (z.2 + cost (stateRatio s))) = Real.exp (v - z.2) * Real.exp (-cost (stateRatio s))
  rw [show v - (z.2 + cost (stateRatio s)) = (v - z.2) + (-cost (stateRatio s)) by ring, Real.exp_add]

theorem currentExponent_update (v : ℝ) (z : CostState) (s : State) :
    currentExponent v (s, z.2 + cost (stateRatio s)) = nextExponent (gapValue v z) (stateRatio s) := by
  change gapValue v (s, z.2 + cost (stateRatio s)) / stateRatio s = _
  rw [gapValue_update, nextGap_div_ratio (stateRatio_pos s)]

theorem stateKernel_ae_minRatio (s : State) :
    ∀ᵐ t ∂stateKernel s, minRatio (stateSide s) (stateRatio s) ≤ stateRatio t := by
  cases s with
  | inl s =>
    change ∀ᵐ t ∂stateKernel (.inl s), s.1 - 1 ≤ stateRatio t
    have h : ∀ᵐ u ∂(stateKernel (.inl s)).map stateRatio, s.1 - 1 ≤ u := by
      rw [stateKernel_even_ratio]
      exact evenKernel_ae_support s
    exact (ae_map_iff stateRatio_measurable.aemeasurable measurableSet_Ici).mp h
  | inr s =>
    change ∀ᵐ t ∂stateKernel (.inr s), max 2 (s.1 - 1) ≤ stateRatio t
    have h : ∀ᵐ u ∂(stateKernel (.inr s)).map stateRatio, max 2 (s.1 - 1) ≤ u := by
      rw [stateKernel_odd_ratio]
      exact oddKernel_ae_support s
    exact (ae_map_iff stateRatio_measurable.aemeasurable measurableSet_Ici).mp h

end NumberTheoryLean.ArrivalKernelGeometry

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_LowStateHorizon
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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
open OccupationBoundaries ArrivalKernelGeometry RegeneratingInverseBands HarmonicWeightKernel

theorem costKernel_time_update (z : CostState) :
    ∀ᵐ y ∂costKernel z, y.2 = z.2 + cost (stateRatio y.1) := by
  have hm : Measurable (fun s : State => (s, z.2 + cost (stateRatio s))) :=
    measurable_id.prodMk (measurable_const.add (cost_measurable.comp stateRatio_measurable))
  have hp : MeasurableSet {y : CostState | y.2 = z.2 + cost (stateRatio y.1)} :=
    measurableSet_eq_fun measurable_snd
      (measurable_const.add (cost_measurable.comp (stateRatio_measurable.comp measurable_fst)))
  rw [costKernel_eq_map]
  apply (ae_map_iff hm.aemeasurable hp).mpr
  exact Eventually.of_forall fun _ => rfl

end NumberTheoryLean.LowStateHorizon

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeRatioBins
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSingletonClassChainState _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.OAI.Erdos970.NumberTheoryLean.ReferenceBenchmarkDecay.benchmark_even_below_two
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.PrimeTiltBounds

open _root_.Erdos970.Set
open FinitePathGeometry PrimeTiltGeometry WeightGlobalBounds DerivativeWeights

theorem log_lipschitz_half {u v : ℝ} (hu : (1/2 : ℝ) ≤ u) (hv : (1/2 : ℝ) ≤ v) :
    |Real.log u - Real.log v| ≤ 2 * |u-v| := by
  have ordered : ∀ a b : ℝ, (1/2 : ℝ) ≤ a → a ≤ b →
      |Real.log b - Real.log a| ≤ 2*(b-a) := by
    intro a b ha hab
    apply interval_abs_bound hab
    · exact Real.continuousOn_log.mono (by intro t ht; exact ne_of_gt (by linarith [ht.1] : 0 < t))
    · intro t ht
      exact Real.hasDerivAt_log (by linarith [ht.1] : t ≠ 0)
    · intro t ht
      have ht0 : 0 < t := by linarith [ht.1]
      rw [abs_of_nonneg (inv_nonneg.mpr ht0.le)]
      exact (inv_le_comm₀ ht0 (by norm_num : (0 : ℝ) < 2)).mpr (by linarith [ht.1])
  rcases le_total u v with huv | hvu
  · rw [abs_sub_comm (Real.log u), abs_sub_comm u, abs_of_nonneg (sub_nonneg.mpr huv)]
    exact ordered u v hu huv
  · rw [abs_of_nonneg (sub_nonneg.mpr hvu)]
    exact ordered v u hv hvu

theorem log_multiplier {i : Side} {s t : ℝ} (hs : Valid i s) (ht : Valid i.flip t) :
    Real.log (multiplier i s t) = 2*(Real.log (t+1)-Real.log t) + Real.log (weight i.flip t) - Real.log (weight i s) := by
  have ht0 := valid_pos ht
  have hq : (t+1)/t ≠ 0 := (div_pos (by linarith) ht0).ne'
  unfold multiplier
  rw [Real.log_div (mul_ne_zero (pow_ne_zero _ hq) (weight_pos ht).ne') (weight_pos hs).ne',
    Real.log_mul (pow_ne_zero _ hq) (weight_pos ht).ne', Real.log_pow,
    Real.log_div (by linarith : t+1 ≠ 0) ht0.ne']
  norm_num

theorem multiplier_log_lipschitz : ∃ C : ℝ, 0 < C ∧ ∀ S : ℝ, 3 ≤ S →
    ∀ i : Side, ∀ s u v : ℝ, Valid i s → Valid i.flip u → Valid i.flip v → u ≤ S → v ≤ S →
      |Real.log (multiplier i s u) - Real.log (multiplier i s v)| ≤ C * (1+S)^3 * |u-v| := by
  obtain ⟨C,hC,hbound⟩ := weights_log_lipschitz
  refine ⟨C+8, by linarith, ?_⟩
  intro S hS i s u v hs hu hv huS hvS
  have hw : |Real.log (weight i.flip u) - Real.log (weight i.flip v)| ≤ C*(1+S)^3*|u-v| := by
    cases i with
    | even => exact (hbound S hS).2 u v hu hv huS hvS
    | odd => exact (hbound S hS).1 u v hu hv huS hvS
  have hbase := log_lipschitz_half (valid_ge_half hu) (valid_ge_half hv)
  have hshift : |Real.log (u+1)-Real.log (v+1)| ≤ 2*|u-v| := by
    have h := log_lipschitz_half (u := u+1) (v := v+1)
      (by linarith [valid_ge_half hu]) (by linarith [valid_ge_half hv])
    simpa only [add_sub_add_right_eq_sub] using h
  have hp : (1 : ℝ) ≤ (1+S)^3 := one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1+S)
  rw [log_multiplier hs hu, log_multiplier hs hv]
  calc
    _ = |2*(Real.log (u+1)-Real.log (v+1)) - 2*(Real.log u-Real.log v) +
        (Real.log (weight i.flip u)-Real.log (weight i.flip v))| := by congr 1; ring
    _ ≤ 2*|Real.log (u+1)-Real.log (v+1)| + 2*|Real.log u-Real.log v| +
        |Real.log (weight i.flip u)-Real.log (weight i.flip v)| := by
      rw [abs_le]
      constructor <;> nlinarith [
        le_abs_self (Real.log (u+1)-Real.log (v+1)), neg_abs_le (Real.log (u+1)-Real.log (v+1)),
        le_abs_self (Real.log u-Real.log v), neg_abs_le (Real.log u-Real.log v),
        le_abs_self (Real.log (weight i.flip u)-Real.log (weight i.flip v)),
        neg_abs_le (Real.log (weight i.flip u)-Real.log (weight i.flip v))]
    _ ≤ (C+8)*(1+S)^3*|u-v| := by
      have hmul := mul_le_mul_of_nonneg_right hp (show 0 ≤ 8*|u-v| by positivity)
      nlinarith

end NumberTheoryLean.PrimeTiltBounds

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

section

namespace NumberTheoryLean.PrimeRatioBins

open _root_.Erdos970.Set
open FinitePathGeometry PrimeTiltGeometry PrimeTiltBounds
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimeEndpoints

theorem ratio_interval_iff {r a b x : ℝ} (ha : 0 < a) (hab : a ≤ b) (hx : 0 < x) :
    (a ≤ r/x-1 ∧ r/x-1 < b) ↔ r/(b+1) < x ∧ x ≤ r/(a+1) := by
  have ha1 : 0 < a+1 := by linarith
  have hb1 : 0 < b+1 := by linarith
  constructor
  · rintro ⟨hlo,hhi⟩
    constructor
    · apply (div_lt_iff₀ hb1).mpr
      have h := (div_lt_iff₀ hx).mp (show r/x < b+1 by linarith)
      nlinarith
    · apply (le_div_iff₀ ha1).mpr
      have h := (le_div_iff₀ hx).mp (show a+1 ≤ r/x by linarith)
      nlinarith
  · rintro ⟨hlo,hhi⟩
    constructor
    · have h := (le_div_iff₀ ha1).mp hhi
      have hh : a+1 ≤ r/x := (le_div_iff₀ hx).mpr (by nlinarith)
      linarith
    · have h := (div_lt_iff₀ hb1).mp hlo
      have hh : r/x < b+1 := (div_lt_iff₀ hx).mpr (by nlinarith)
      linarith

theorem ratioBinMass_eq_harmonic {w r a b : ℝ} (hw : 1 < w) (ha : 0 < a) (hab : a ≤ b) :
    ratioBinMass w r a b = harmonicMass w false true (r/(b+1)) (r/(a+1)) := by
  classical
  unfold ratioBinMass ratioBin harmonicMass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  have heq := ratio_interval_iff (r := r) ha hab (primeExponent_pos hw (Nat.mem_primesLE.mp hp).2)
  simp only [childRatio, intervalGuard, Bool.false_eq_true, ite_false, if_false, ite_true, if_true, heq]

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

theorem prime_ratio_bin_error : ∃ c C w₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ r a b : ℝ, 0 < r → 0 < a → a ≤ b → 1/2 ≤ r/(b+1) →
      |ratioBinMass w r a b - (Real.log (b+1)-Real.log (a+1))| ≤
        C * Real.exp (-c * Real.sqrt ((1/2 : ℝ) * Real.log w)) := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,hbound⟩ := harmonic_prime_measure
  refine ⟨c,C,w₀,hc,hC,hw₀,?_⟩
  intro w hw r a b hr ha hab hlow
  have hw1 := hw₀.trans_le hw
  have hend : r/(b+1) ≤ r/(a+1) := div_le_div_of_nonneg_left hr.le (by linarith : 0 < a+1) (by linarith)
  have h := hbound w hw (r/(b+1)) (r/(a+1)) hlow hend false true
  rw [← ratioBinMass_eq_harmonic hw1 ha hab, bin_log_width hr ha hab] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hlow (Real.log_pos hw1).le)) (by linarith)

end NumberTheoryLean.PrimeRatioBins

end

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

namespace NumberTheoryLean.ContinuousRatioBins

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry TransitionKernels PrimeTiltBounds PrimeTiltMonotone
open PrimeRatioMeasure HarmonicExponentMeasure

theorem weightedRatioLaw_probability {i : Side} {s : ℝ} (hs : Valid i s) :
    IsProbabilityMeasure (weightedRatioLaw i s) := by
  constructor
  rw [weightedRatioLaw, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ, multiplier_ratio_integral hs]

theorem ratio_restrict_bin {m a b : ℝ} (hma : m ≤ a) :
    (ratioMeasure m).restrict (Ico a b) = (ratioMeasure a).restrict (Ico a b) := by
  simp only [ratioMeasure, restrict_withDensity measurableSet_Ico, Measure.restrict_restrict measurableSet_Ico]
  rw [Set.inter_eq_left.mpr (show Ico a b ⊆ Ici m from fun _ ht => hma.trans ht.1),
    Set.inter_eq_left.mpr Ico_subset_Ici_self]

theorem ratio_bin_mass {m a b : ℝ} (ha : 0 < a) (hma : m ≤ a) (hab : a ≤ b) :
    ratioMeasure m (Ico a b) = ENNReal.ofReal (Real.log (b+1)-Real.log (a+1)) := by
  have h := congrArg (fun μ : Measure ℝ => μ univ) (ratio_restrict_bin (b := b) hma)
  simp only [Measure.restrict_apply_univ] at h
  rw [h]
  have h' := congrArg (fun μ : Measure ℝ => μ univ)
    (restrict_Ico_eq_restrict_Icc (μ := ratioMeasure a) (a := a) (b := b))
  simp only [Measure.restrict_apply_univ] at h'
  rw [h', ratioMeasure_Icc ha hab]

theorem continuousBin_sandwich {i : Side} {s a b : ℝ} (hs : Valid i s)
    (hma : minRatio i s ≤ a) (hab : a ≤ b) :
    multiplier i s b * (Real.log (b+1)-Real.log (a+1)) ≤ continuousBin i s a b ∧
      continuousBin i s a b ≤ multiplier i s a * (Real.log (b+1)-Real.log (a+1)) := by
  let := weightedRatioLaw_probability hs
  have ha := (minRatio_pos hs).trans_le hma
  have hb := ha.trans_le hab
  have hma0 := (multiplier_pos hs (valid_next hs hma)).le
  have hmb0 := (multiplier_pos hs (valid_next hs (hma.trans hab))).le
  have hH : 0 ≤ Real.log (b+1)-Real.log (a+1) :=
    sub_nonneg.mpr (Real.log_le_log (by linarith) (by linarith))
  have hfinite : weightedRatioLaw i s (Ico a b) ≠ ∞ := measure_ne_top _ _
  have hu : weightedRatioLaw i s (Ico a b) ≤
      ENNReal.ofReal (multiplier i s a * (Real.log (b+1)-Real.log (a+1))) := by
    rw [weightedRatioLaw, withDensity_apply _ measurableSet_Ico]
    calc
      _ ≤ ∫⁻ _t in Ico a b, ENNReal.ofReal (multiplier i s a) ∂ratioMeasure (minRatio i s) := by
        apply lintegral_mono_ae
        apply ae_restrict_of_forall_mem measurableSet_Ico
        intro t ht
        exact ENNReal.ofReal_le_ofReal (multiplier_antitone hs (Set.mem_Ici.mpr hma)
          (Set.mem_Ici.mpr (hma.trans ht.1)) ht.1)
      _ = _ := by
        rw [lintegral_const, Measure.restrict_apply_univ, ratio_bin_mass ha hma hab,
          ← ENNReal.ofReal_mul hma0]
  have hl : ENNReal.ofReal (multiplier i s b * (Real.log (b+1)-Real.log (a+1))) ≤
      weightedRatioLaw i s (Ico a b) := by
    rw [weightedRatioLaw, withDensity_apply _ measurableSet_Ico]
    calc
      _ = ∫⁻ _t in Ico a b, ENNReal.ofReal (multiplier i s b) ∂ratioMeasure (minRatio i s) := by
        rw [lintegral_const, Measure.restrict_apply_univ, ratio_bin_mass ha hma hab,
          ← ENNReal.ofReal_mul hmb0]
      _ ≤ _ := by
        apply lintegral_mono_ae
        apply ae_restrict_of_forall_mem measurableSet_Ico
        intro t ht
        exact ENNReal.ofReal_le_ofReal (multiplier_antitone hs
          (Set.mem_Ici.mpr (hma.trans ht.1)) (Set.mem_Ici.mpr (hma.trans hab)) ht.2.le)
  constructor
  · have h := ENNReal.toReal_mono hfinite hl
    simpa only [continuousBin, ENNReal.toReal_ofReal (mul_nonneg hmb0 hH)] using h
  · have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hu
    simpa only [continuousBin, ENNReal.toReal_ofReal (mul_nonneg hma0 hH)] using h

end NumberTheoryLean.ContinuousRatioBins

end

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

theorem ratioBinSet_measurable (a b : ℝ) : MeasurableSet (ratioBinSet a b) :=
  (measurableSet_le measurable_const (stateRatio_measurable.comp measurable_fst)).inter
    (measurableSet_lt (stateRatio_measurable.comp measurable_fst) measurable_const)

theorem costKernel_bin (z : CostState) (a b : ℝ) :
    costKernel z (ratioBinSet a b) = weightedRatioLaw (stateSide z.1) (stateRatio z.1) (Ico a b) := by
  have h := congrArg (fun μ : Measure ℝ => μ (Ico a b)) (costKernel_ratioLaw z)
  rw [Measure.map_apply (f := fun y : CostState => stateRatio y.1) (stateRatio_measurable.comp measurable_fst) measurableSet_Ico] at h
  exact h

theorem lowKernel_full_bin (v : ℝ) {ell S a b : ℝ} (hell : 0 < ell) (z : CostState)
    (hbS : b ≤ S) (harr : b ≤ gapValue v z/ell-1) :
    lowKernel costKernel v ell S z (ratioBinSet a b) = costKernel z (ratioBinSet a b) := by
  rw [lowKernel, Kernel.restrict_apply, Measure.restrict_apply (ratioBinSet_measurable a b)]
  apply measure_congr
  filter_upwards [costKernel_time_update z] with y hy
  apply propext
  constructor
  · exact And.left
  · intro hbin
    refine ⟨hbin,?_,?_⟩
    · have ht := OccupationBoundaries.stateRatio_pos y.1
      have hpair : y = (y.1,z.2+cost (stateRatio y.1)) := Prod.ext rfl hy
      have hcur : currentExponent v y = nextExponent (gapValue v z) (stateRatio y.1) := by
        calc
          _ = currentExponent v (y.1,z.2+cost (stateRatio y.1)) := congrArg (currentExponent v) hpair
          _ = _ := currentExponent_update v z y.1
      change ell < currentExponent v y
      rw [hcur]
      change ell < gapValue v z/(stateRatio y.1+1)
      apply (lt_div_iff₀ (by linarith : 0 < stateRatio y.1+1)).mpr
      have hratio : stateRatio y.1+1 < gapValue v z/ell := by
        change a ≤ stateRatio y.1 ∧ stateRatio y.1 < b at hbin
        linarith [hbin.2]
      have hm := (lt_div_iff₀ hell).mp hratio
      nlinarith
    · exact hbin.2.le.trans hbS

theorem continuousChain_full_bin (v : ℝ) {ell S a b : ℝ} (hell : 0 < ell) (z : CostState)
    (hbS : b ≤ S) (harr : b ≤ gapValue v z/ell-1) :
    continuousChain v ell S (.inl z) (Sum.inl '' ratioBinSet a b) =
      weightedRatioLaw (stateSide z.1) (stateRatio z.1) (Ico a b) := by
  rw [continuousChain, CemeteryKernel.complete_live_mass _ _ (ratioBinSet_measurable a b),
    lowKernel_full_bin v hell z hbS harr, costKernel_bin]

theorem continuousChain_full_bin_real (v : ℝ) {ell S a b : ℝ} (hell : 0 < ell) (z : CostState)
    (hbS : b ≤ S) (harr : b ≤ gapValue v z/ell-1) :
    (continuousChain v ell S (.inl z) (Sum.inl '' ratioBinSet a b)).toReal =
      continuousBin (stateSide z.1) (stateRatio z.1) a b := by
  rw [continuousChain_full_bin v hell z hbS harr]
  rfl

end NumberTheoryLean.ContinuousKilledBins

end

section

namespace NumberTheoryLean.ContinuousIntervalUpper

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeTiltBounds PrimeTiltMonotone
open ContinuousRatioBins ContinuousKilledBins LowStateHorizon

theorem completed_interval_upper : ∃ C : ℝ, 0 < C ∧ ∀ v ell S a b : ℝ, ∀ z : CostState,
    stateRatio z.1 ≤ S →
      continuousChain v ell S (.inl z) (Sum.inl '' closedCostBin a b) ≤
        ENNReal.ofReal (C*(1+S)^2) * ENNReal.ofReal (b-a) := by
  obtain ⟨C,hC,hbound⟩ := weighted_interval_upper
  refine ⟨C,hC,?_⟩
  intro v ell S a b z hsS
  rw [continuousChain,CemeteryKernel.complete_live_mass _ _ (closedCostBin_measurable a b),
    lowKernel,Kernel.restrict_apply,Measure.restrict_apply (closedCostBin_measurable a b)]
  calc
    _ ≤ costKernel z (closedCostBin a b) := measure_mono inter_subset_left
    _ = weightedRatioLaw (stateSide z.1) (stateRatio z.1) (Icc a b) := costKernel_closedBin z a b
    _ ≤ _ := hbound S (stateSide z.1) (stateRatio z.1) a b (stateRatio_valid z.1) hsS

end NumberTheoryLean.ContinuousIntervalUpper

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeCompactWeights
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

namespace NumberTheoryLean.WeightedPrimeBins

open _root_.Set _root_.Finset
open FinitePathGeometry PrimeTiltGeometry PrimeTiltBounds PrimeTiltMonotone
open PrimeRatioBins ContinuousRatioBins

theorem weightedPrimeBin_sandwich {w r s a b : ℝ} {i : Side} (hs : Valid i s)
    (hma : minRatio i s ≤ a) (hab : a ≤ b) :
    multiplier i s b * ratioBinMass w r a b ≤ weightedPrimeBin w r i s a b ∧
      weightedPrimeBin w r i s a b ≤ multiplier i s a * ratioBinMass w r a b := by
  classical
  have hlo : ∀ p ∈ ratioBin w r a b, multiplier i s b ≤ multiplier i s (childRatio w r p) := by
    intro p hp
    have ht := (Finset.mem_filter.mp hp).2
    exact multiplier_antitone hs (Set.mem_Ici.mpr (hma.trans ht.1))
      (Set.mem_Ici.mpr (hma.trans hab)) ht.2.le
  have hup : ∀ p ∈ ratioBin w r a b, multiplier i s (childRatio w r p) ≤ multiplier i s a := by
    intro p hp
    have ht := (Finset.mem_filter.mp hp).2
    exact multiplier_antitone hs (Set.mem_Ici.mpr hma) (Set.mem_Ici.mpr (hma.trans ht.1)) ht.1
  constructor
  · rw [ratioBinMass, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    rw [primeTilt_eq_multiplier, mul_comm (multiplier i s b)]
    exact mul_le_mul_of_nonneg_left (hlo p hp) (inv_nonneg.mpr (Nat.cast_nonneg p))
  · rw [ratioBinMass, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    rw [primeTilt_eq_multiplier, mul_comm (multiplier i s a)]
    exact mul_le_mul_of_nonneg_left (hup p hp) (inv_nonneg.mpr (Nat.cast_nonneg p))

theorem sandwich_difference {ma mb R H D C E : ℝ} (hma : 0 ≤ ma) (hmb : 0 ≤ mb)
    (hm : mb ≤ ma) (hE : 0 ≤ E) (hraw : |R-H| ≤ E)
    (hD : mb*R ≤ D ∧ D ≤ ma*R) (hC : mb*H ≤ C ∧ C ≤ ma*H) :
    |D-C| ≤ ma*E + (ma-mb)*H := by
  rw [abs_le]
  constructor
  · have h := mul_le_mul_of_nonneg_left (show H-R ≤ E by linarith [(abs_le.mp hraw).1]) hmb
    have h' := mul_le_mul_of_nonneg_right hm hE
    nlinarith [hD.1,hC.2]
  · have h := mul_le_mul_of_nonneg_left (abs_le.mp hraw).2 hma
    nlinarith [hD.2,hC.1]

theorem sub_le_mul_log_sub {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a-b ≤ a*(Real.log a-Real.log b) := by
  have h := Real.log_le_sub_one_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne'] at h
  have hm := mul_le_mul_of_nonneg_left h ha.le
  have he : a*(b/a-1) = b-a := by field_simp
  rw [he] at hm
  nlinarith

theorem multiplier_drop : ∃ C : ℝ, 0 < C ∧ ∀ S : ℝ, 3 ≤ S →
    ∀ i : Side, ∀ s a b : ℝ, Valid i s → minRatio i s ≤ a → a ≤ b → b ≤ S →
      multiplier i s a-multiplier i s b ≤ multiplier i s a*(C*(1+S)^3*(b-a)) := by
  obtain ⟨C,hC,hbound⟩ := multiplier_log_lipschitz
  refine ⟨C,hC,?_⟩
  intro S hS i s a b hs hma hab hbS
  have ha := valid_next hs hma
  have hb := valid_next hs (hma.trans hab)
  have h := hbound S hS i s a b hs ha hb (hab.trans hbS) hbS
  rw [abs_sub_comm a b, abs_of_nonneg (sub_nonneg.mpr hab)] at h
  exact (sub_le_mul_log_sub (multiplier_pos hs ha) (multiplier_pos hs hb)).trans
    (mul_le_mul_of_nonneg_left ((le_abs_self _).trans h) (multiplier_pos hs ha).le)

theorem weighted_bin_error : ∃ c C w₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ r : ℝ, 0 < r → ∀ i : Side, ∀ s a b : ℝ,
      Valid i s → minRatio i s ≤ a → a ≤ b → 1/2 ≤ r/(b+1) →
      |weightedPrimeBin w r i s a b-continuousBin i s a b| ≤
        multiplier i s a * (C*Real.exp (-c*Real.sqrt ((1/2 : ℝ)*Real.log w))) +
          (multiplier i s a-multiplier i s b)*(Real.log (b+1)-Real.log (a+1)) := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,hraw⟩ := prime_ratio_bin_error
  refine ⟨c,C,w₀,hc,hC,hw₀,?_⟩
  intro w hw r hr i s a b hs hma hab hlow
  have ha := (minRatio_pos hs).trans_le hma
  apply sandwich_difference (multiplier_pos hs (valid_next hs hma)).le
    (multiplier_pos hs (valid_next hs (hma.trans hab))).le
    (multiplier_antitone hs (Set.mem_Ici.mpr hma) (Set.mem_Ici.mpr (hma.trans hab)) hab)
    (by positivity) (hraw w hw r a b hr ha hab hlow)
    (weightedPrimeBin_sandwich hs hma hab) (continuousBin_sandwich hs hma hab)

theorem weighted_bin_polynomial_error : ∃ c C w₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ r S : ℝ, 0 < r → 3 ≤ S → ∀ i : Side, ∀ s a b : ℝ,
      Valid i s → s ≤ S → minRatio i s ≤ a → a ≤ b → b ≤ S → 1/2 ≤ r/(b+1) →
      |weightedPrimeBin w r i s a b-continuousBin i s a b| ≤
        C*(1+S)^5*((b-a)^2+Real.exp (-c*Real.sqrt ((1/2 : ℝ)*Real.log w))) := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,herr⟩ := weighted_bin_error
  obtain ⟨D,hD,henv⟩ := multiplier_envelope
  obtain ⟨L,hL,hdrop⟩ := multiplier_drop
  let M := D*C+D*L
  have hM : 0 < M := by dsimp [M] <;> positivity
  refine ⟨c,M,w₀,hc,hM,hw₀,?_⟩
  intro w hw r S hr hS i s a b hs hsS hma hab hbS hlow
  let P := 1+S
  let e := Real.exp (-c*Real.sqrt ((1/2 : ℝ)*Real.log w))
  let H := Real.log (b+1)-Real.log (a+1)
  let delta := multiplier i s a-multiplier i s b
  have hP : 1 ≤ P := by dsimp [P] <;> linarith
  have hP0 : 0 ≤ P := by linarith
  have he : 0 ≤ e := (Real.exp_pos _).le
  have hh : 0 ≤ b-a := sub_nonneg.mpr hab
  have ha := (minRatio_pos hs).trans_le hma
  have hH0 : 0 ≤ H := sub_nonneg.mpr (Real.log_le_log (by linarith) (by linarith))
  have hH : H ≤ b-a := ((bin_log_width_bounds ha hab).2).trans (div_le_self hh (by linarith))
  have hd0 : 0 ≤ delta := sub_nonneg.mpr
    (multiplier_antitone hs (Set.mem_Ici.mpr hma) (Set.mem_Ici.mpr (hma.trans hab)) hab)
  have hm := henv S i s a hs hsS hma
  have hd : delta ≤ D*L*P^5*(b-a) := by
    calc
      _ ≤ multiplier i s a*(L*P^3*(b-a)) := hdrop S hS i s a b hs hma hab hbS
      _ ≤ (D*P^2)*(L*P^3*(b-a)) := mul_le_mul_of_nonneg_right hm (by positivity)
      _ = _ := by ring
  have hp25 : P^2 ≤ P^5 := by
    have h := mul_le_mul_of_nonneg_left (one_le_pow₀ hP : (1 : ℝ) ≤ P^3) (sq_nonneg P)
    nlinarith
  have hfirst : multiplier i s a*(C*e) ≤ D*C*P^5*e := by
    calc
      _ ≤ (D*P^2)*(C*e) := mul_le_mul_of_nonneg_right hm (mul_nonneg hC.le he)
      _ = (D*C*e)*P^2 := by ring
      _ ≤ (D*C*e)*P^5 := mul_le_mul_of_nonneg_left hp25 (by positivity)
      _ = _ := by ring
  have hsecond : delta*H ≤ D*L*P^5*(b-a)^2 := by
    calc
      _ ≤ (D*L*P^5*(b-a))*H := mul_le_mul_of_nonneg_right hd hH0
      _ ≤ (D*L*P^5*(b-a))*(b-a) := mul_le_mul_of_nonneg_left hH (by positivity)
      _ = _ := by ring
  have hDC : D*C ≤ M := le_add_of_nonneg_right (mul_nonneg hD.le hL.le)
  have hDL : D*L ≤ M := le_add_of_nonneg_left (mul_nonneg hD.le hC.le)
  calc
    _ ≤ multiplier i s a*(C*e)+delta*H := herr w hw r hr i s a b hs hma hab hlow
    _ ≤ D*C*P^5*e + D*L*P^5*(b-a)^2 := add_le_add hfirst hsecond
    _ ≤ M*P^5*e + M*P^5*(b-a)^2 := add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDC (pow_nonneg hP0 _)) he)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDL (pow_nonneg hP0 _)) (sq_nonneg _))
    _ = _ := by dsimp [P,e] <;> ring

end NumberTheoryLean.WeightedPrimeBins

end

section

namespace NumberTheoryLean.NormalizedPrimeBins

open _root_.Set _root_.Finset
open FinitePathGeometry PrimeTiltGeometry PrimeRatioBins PrimeTiltBounds
open WeightedPrimeBins ContinuousRatioBins PrimeKilledChain

theorem division_error {D C e : ℝ} (hC : 0 ≤ C) (he : 0 ≤ e) :
    |D/(1+e)-C| ≤ |D-C|+e*C := by
  let A := |D-C|
  have hA : 0 ≤ A := abs_nonneg _
  have hlo : C-A ≤ D := by dsimp [A] <;> linarith [neg_abs_le (D-C)]
  have hup : D ≤ C+A := by dsimp [A] <;> linarith [le_abs_self (D-C)]
  have hZ : 0 < 1+e := by linarith
  have hu : D/(1+e) ≤ C+A := (div_le_iff₀ hZ).mpr (by
    nlinarith [mul_nonneg (add_nonneg hC hA) he])
  have hl : C-A-e*C ≤ D/(1+e) := (le_div_iff₀ hZ).mpr (by
    nlinarith [mul_nonneg hA he, mul_nonneg hC (sq_nonneg e)])
  rw [abs_le]
  constructor <;> dsimp [A] at hu hl <;> nlinarith [mul_nonneg he hC]

theorem normalizedPrimeBin_eq (w r : ℝ) (i : Side) (s a b : ℝ) :
    normalizedPrimeBin w r i s a b = weightedPrimeBin w r i s a b/(1+epsilon w) := by
  exact (Finset.sum_div _ _ _).symm

theorem normalized_bin_error : ∃ c C w₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ r S : ℝ, 0 < r → 3 ≤ S → ∀ i : Side, ∀ s a b : ℝ,
      Valid i s → s ≤ S → minRatio i s ≤ a → a ≤ b → b ≤ S → 1/2 ≤ r/(b+1) →
      |normalizedPrimeBin w r i s a b-continuousBin i s a b| ≤
        C*(1+S)^5*((b-a)^2+Real.exp (-c*Real.sqrt ((1/2 : ℝ)*Real.log w))) +
          epsilon w*continuousBin i s a b := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,hbound⟩ := weighted_bin_polynomial_error
  refine ⟨c,C,w₀,hc,hC,hw₀,?_⟩
  intro w hw r S hr hS i s a b hs hsS hma hab hbS hlow
  rw [normalizedPrimeBin_eq]
  exact (division_error (show 0 ≤ continuousBin i s a b from ENNReal.toReal_nonneg) (epsilon_pos w).le).trans
    (add_le_add (hbound w hw r S hr hS i s a b hs hsS hma hab hbS hlow) le_rfl)

end NumberTheoryLean.NormalizedPrimeBins

end

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

theorem children_full_bin {w ell S s r cap a b : ℝ} {i : Side} (hw : 1 < w)
    (hell : 0 < ell) (_hr : 0 < r) (hs : Valid i s) (hcap : cap = r/s)
    (hma : minRatio i s < a) (hab : a ≤ b) (hbS : b ≤ S) (harr : b ≤ r/ell-1) (closed : Bool) :
    (children w ell S i s r cap closed).filter (fun p => a ≤ childRatio w r p ∧ childRatio w r p < b) =
      ratioBin w r a b := by
  classical
  have ha : 0 < a := (PrimeTiltMonotone.minRatio_pos hs).trans hma
  have hb : 0 < b := ha.trans_le hab
  have hs0 := valid_pos hs
  ext p
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hchild,hbin⟩
    have hprime := ((mem_children_iff hw i closed p).mp hchild).1
    have hxp := PrimeRatioBins.primeExponent_pos hw hprime
    have hinterval := (ratio_interval_iff (r := r) ha hab hxp).mp hbin
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hreal : (p : ℝ) ≤ w^(r/(a+1)) := (exponent_le_iff hw hp0).mp hinterval.2
    apply Finset.mem_filter.mpr
    exact ⟨Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff (Real.rpow_pos_of_pos (by linarith : 0 < w) _).le).mpr hreal,hprime⟩,hbin⟩
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hpprime,hbin⟩
    have hprime := (Nat.mem_primesLE.mp hpprime).2
    have hxp := PrimeRatioBins.primeExponent_pos hw hprime
    have hinterval := (ratio_interval_iff (r := r) ha hab hxp).mp hbin
    have hlow : ell ≤ r/(b+1) := by
      apply (le_div_iff₀ (by linarith : 0 < b+1)).mpr
      have h := (le_div_iff₀ hell).mp (show b+1 ≤ r/ell by linarith)
      nlinarith
    have hbelow : primeExponent w p < cap := by
      rw [hcap]
      apply (lt_div_iff₀ hs0).mpr
      have hrat : s < r/primeExponent w p := by
        have hmin := minRatio_ge_sub_one i s
        have hlo : a ≤ r/primeExponent w p-1 := hbin.1
        linarith
      have h := (lt_div_iff₀ hxp).mp hrat
      nlinarith
    have hguard : capGuard closed cap (primeExponent w p) := by
      cases closed with
      | false => exact hbelow
      | true => exact hbelow.le
    apply Finset.mem_filter.mpr
    refine ⟨(mem_children_iff hw i closed p).mpr ⟨hprime,hlow.trans_lt hinterval.1,hguard,?_,?_⟩,hbin⟩
    · exact hma.le.trans hbin.1
    · exact hbin.2.le.trans hbS

theorem normalized_children_full_bin {w ell S s r cap a b : ℝ} {i : Side} (hw : 1 < w)
    (hell : 0 < ell) (hr : 0 < r) (hs : Valid i s) (hcap : cap = r/s)
    (hma : minRatio i s < a) (hab : a ≤ b) (hbS : b ≤ S) (harr : b ≤ r/ell-1) (closed : Bool) :
    (∑ p ∈ children w ell S i s r cap closed,
      if a ≤ childRatio w r p ∧ childRatio w r p < b then primeTilt w r i s p/(1+epsilon w) else 0) =
      normalizedPrimeBin w r i s a b := by
  classical
  rw [← Finset.sum_filter, children_full_bin hw hell hr hs hcap hma hab hbS harr closed]
  rfl

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

theorem chain_full_bin (h : History w ell S start) {a b : ℝ} (hw : 1 < w)
    (hell : 0 < ell) (hr : 0 < h.node.gap) (hs : Valid h.node.side h.node.ratio) (hc : Consistent h.node)
    (hma : minRatio h.node.side h.node.ratio < a) (hab : a ≤ b) (hbS : b ≤ S)
    (harr : b ≤ h.node.gap/ell-1) :
    chain w ell S start (some h) (liveBin a b) =
      ENNReal.ofReal (normalizedPrimeBin w h.node.gap h.node.side h.node.ratio a b) := by
  classical
  rw [chain_live_bin_formula]
  have hnonneg : ∀ p ∈ nodeChildren w ell S h.node,
      0 ≤ if a ≤ childRatio w h.node.gap p ∧ childRatio w h.node.gap p < b
        then primeTilt w h.node.gap h.node.side h.node.ratio p/(1+epsilon w) else 0 := by
    intro p hp
    split_ifs
    · exact div_nonneg (primeTilt_nonneg (w := w) (r := h.node.gap) (i := h.node.side) (s := h.node.ratio) hs hp) (normalizer_pos w).le
    · exact le_rfl
  calc
    _ = ENNReal.ofReal (∑ p ∈ nodeChildren w ell S h.node,
        if a ≤ childRatio w h.node.gap p ∧ childRatio w h.node.gap p < b
          then primeTilt w h.node.gap h.node.side h.node.ratio p/(1+epsilon w) else 0) := by
      rw [ENNReal.ofReal_sum_of_nonneg hnonneg]
      apply Finset.sum_congr rfl
      intro p hp
      split_ifs <;> simp only [childProbability, ENNReal.ofReal_zero]
    _ = _ := congrArg ENNReal.ofReal (normalized_children_full_bin hw hell hr hs hc hma hab hbS harr h.node.closed)

theorem chain_full_bin_real (h : History w ell S start) {a b : ℝ} (hw : 1 < w)
    (hell : 0 < ell) (hr : 0 < h.node.gap) (hs : Valid h.node.side h.node.ratio) (hc : Consistent h.node)
    (hma : minRatio h.node.side h.node.ratio < a) (hab : a ≤ b) (hbS : b ≤ S)
    (harr : b ≤ h.node.gap/ell-1) :
    (chain w ell S start (some h) (liveBin a b)).toReal =
      normalizedPrimeBin w h.node.gap h.node.side h.node.ratio a b := by
  rw [chain_full_bin h hw hell hr hs hc hma hab hbS harr]
  apply ENNReal.toReal_ofReal
  unfold normalizedPrimeBin
  apply Finset.sum_nonneg
  intro p hp
  have ht := (Finset.mem_filter.mp hp).2
  rw [primeTilt_eq_multiplier]
  exact div_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p))
    (multiplier_pos hs (valid_next hs (hma.le.trans ht.1))).le) (normalizer_pos w).le

end NumberTheoryLean.ActualPrimeBins

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_CrossingBandGeometry
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace NumberTheoryLean.NearbyParentGeometry

open FinitePathGeometry OccupationBoundaries

theorem minRatio_stability (i : Side) (s t : ℝ) :
    |minRatio i s-minRatio i t| ≤ |s-t| := by
  cases i with
  | even => simp [minRatio]
  | odd =>
    simpa only [minRatio, sub_sub_sub_cancel_right, sub_self, abs_zero,
      max_eq_right (abs_nonneg (s-t))] using abs_max_sub_max_le_max (2:ℝ) (s-1) 2 (t-1)

theorem log_stability {m x y : ℝ} (hm : 0 < m) (hx : m ≤ x) (hy : m ≤ y) :
    |Real.log x-Real.log y| ≤ |x-y|/m := by
  wlog hxy : y ≤ x generalizing x y
  · simpa only [abs_sub_comm] using this hy hx (le_of_not_ge hxy)
  have hx0 := hm.trans_le hx
  have hy0 := hm.trans_le hy
  rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hy0 hxy)), abs_of_nonneg (sub_nonneg.mpr hxy)]
  have h := Real.log_le_sub_one_of_pos (div_pos hx0 hy0)
  rw [Real.log_div hx0.ne' hy0.ne'] at h
  calc
    Real.log x-Real.log y ≤ (x-y)/y := by
      convert h using 1
      all_goals try with_reducible_and_instances rfl
      field_simp
    _ ≤ (x-y)/m := div_le_div_of_nonneg_left (sub_nonneg.mpr hxy) hm hy

theorem cost_stability {s t : ℝ} (hs : (1/2:ℝ) ≤ s) (ht : (1/2:ℝ) ≤ t) :
    |cost s-cost t| ≤ 4*|s-t| := by
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have h1 := log_stability (m:=1/2) (by norm_num) hs ht
  have h2 := log_stability (m:=1/2) (x:=s+1) (y:=t+1) (by norm_num) (by linarith) (by linarith)
  have heq : cost s-cost t = (Real.log (s+1)-Real.log (t+1))-(Real.log s-Real.log t) := by
    linarith [cost_add_log hs0, cost_add_log ht0]
  rw [heq]
  calc
    _ ≤ |Real.log (s+1)-Real.log (t+1)|+|Real.log s-Real.log t| := abs_sub _ _
    _ ≤ 4*|s-t| := by
      simp only [add_sub_add_right_eq_sub] at h2
      linarith

theorem clipped_relative_stability {A x y c : ℝ} (hA : 0 ≤ A) (hc : 1 ≤ c)
    (hxy : x ≤ c*y) (hyx : y ≤ c*x) :
    |min A x-min A y| ≤ A*(c-1) := by
  have hnonneg : 0 ≤ A*(c-1) := mul_nonneg hA (by linarith)
  simp only [min_def]
  split_ifs <;> apply abs_le.mpr <;> constructor <;> nlinarith

theorem log_gap_relative {r q d : ℝ} (hr : 0 < r) (hq : 0 < q)
    (hd : |Real.log r-Real.log q| ≤ d) : r ≤ Real.exp d*q ∧ q ≤ Real.exp d*r := by
  have h1 := Real.exp_le_exp.mpr (abs_le.mp hd).2
  have h2 := Real.exp_le_exp.mpr (show Real.log q-Real.log r ≤ d by linarith [(abs_le.mp hd).1])
  rw [Real.exp_sub,Real.exp_log hr,Real.exp_log hq] at h1
  rw [Real.exp_sub,Real.exp_log hq,Real.exp_log hr] at h2
  exact ⟨(div_le_iff₀ hq).mp h1,(div_le_iff₀ hr).mp h2⟩

theorem arrival_endpoint_stability {r q ell S d : ℝ} (hr : 0 < r) (hq : 0 < q)
    (hell : 0 < ell) (hS : 0 ≤ S+1) (hd : |Real.log r-Real.log q| ≤ d) :
    |min S (r/ell-1)-min S (q/ell-1)| ≤ (S+1)*(Real.exp d-1) := by
  have hrel := log_gap_relative hr hq hd
  have hd0 : 0 ≤ d := (abs_nonneg _).trans hd
  have he : 1 ≤ Real.exp d := Real.one_le_exp_iff.mpr hd0
  have h1 : r/ell ≤ Real.exp d*(q/ell) := by
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hrel.1 hell.le
  have h2 : q/ell ≤ Real.exp d*(r/ell) := by
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hrel.2 hell.le
  have h := clipped_relative_stability hS he h1 h2
  have hu (x:ℝ) : min S (x-1) = min (S+1) x-1 := by
    rw [← min_sub_sub_right]
    simp
  simpa only [hu,sub_sub_sub_cancel_right] using h

theorem log_gap_step {r q s t d e : ℝ} (hr : 0 < r) (hq : 0 < q)
    (hs : (1/2:ℝ) ≤ s) (ht : (1/2:ℝ) ≤ t)
    (hd : |Real.log r-Real.log q| ≤ d) (he : |s-t| ≤ e) :
    |Real.log (nextGap r s)-Real.log (nextGap q t)| ≤ d+4*e := by
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  rw [nextGap_eq_cost hs0,nextGap_eq_cost ht0,Real.log_mul hr.ne' (Real.exp_pos _).ne',
    Real.log_mul hq.ne' (Real.exp_pos _).ne',Real.log_exp,Real.log_exp]
  have ha := abs_sub (Real.log r-Real.log q) (cost s-cost t)
  have hc := cost_stability hs ht
  have heq : Real.log r + -cost s-(Real.log q + -cost t) =
      (Real.log r-Real.log q)-(cost s-cost t) := by ring
  rw [heq]
  linarith

end NumberTheoryLean.NearbyParentGeometry



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_MeshBoundaryGeometry
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.MeshRatioLabels

open Set MeasureTheory

theorem ratioLabel_val {S h t : ℝ} (hh : 0 < h) (ht : t ≤ S) :
    (ratioLabel S h t).val = ⌊t/h⌋₊ := by
  rw [ratioLabel,ite_eq_left ht,Fin.val_ofNat]
  apply Nat.mod_eq_of_lt
  have hb : ⌊t/h⌋₊ ≤ binCount S h := Nat.floor_mono (div_le_div_of_nonneg_right ht hh.le)
  omega

theorem ratioLabel_ne_cemetery {S h t : ℝ} (hh : 0 < h) (ht : t ≤ S) :
    ratioLabel S h t ≠ cemeteryLabel S h := by
  intro heq
  have he := congrArg Fin.val heq
  rw [ratioLabel_val hh ht] at he
  change ⌊t/h⌋₊ = binCount S h+1 at he
  have hb : ⌊t/h⌋₊ ≤ binCount S h := Nat.floor_mono (div_le_div_of_nonneg_right ht hh.le)
  omega

theorem ratioLabel_eq_iff {S h t : ℝ} (hh : 0 < h) (ht0 : 0 ≤ t) (htS : t ≤ S) (j : Label S h) :
    ratioLabel S h t = j ↔ (j.val : ℝ)*h ≤ t ∧ t < ((j.val : ℝ)+1)*h := by
  rw [Fin.ext_iff,ratioLabel_val hh htS,Nat.floor_eq_iff (div_nonneg ht0 hh.le),le_div_iff₀ hh,div_lt_iff₀ hh]

theorem matching_ratios_close {S h u v : ℝ} (hh : 0 < h) (hu0 : 0 ≤ u) (hv0 : 0 ≤ v)
    (huS : u ≤ S) (hvS : v ≤ S) (heq : ratioLabel S h u = ratioLabel S h v) : |u-v| < h := by
  have hu := (ratioLabel_eq_iff hh hu0 huS (ratioLabel S h v)).mp heq
  have hv := (ratioLabel_eq_iff hh hv0 hvS (ratioLabel S h v)).mp rfl
  rw [abs_lt]
  constructor <;> nlinarith [hu.1,hu.2,hv.1,hv.2]

theorem label_card_le {S h : ℝ} (hS : 0 ≤ S) (hh : 0 < h) :
    (Fintype.card (Label S h) : ℝ) ≤ S/h+2 := by
  have hc : Fintype.card (Label S h) = binCount S h+2 :=
    (Nat.card_eq_fintype_card (α := Label S h)).symm.trans (Nat.card_fin _)
  rw [hc]
  simp only [Nat.cast_add,Nat.cast_ofNat,binCount]
  linarith [Nat.floor_le (div_nonneg hS hh.le)]

end NumberTheoryLean.MeshRatioLabels

end

section

namespace NumberTheoryLean.MeshBoundaryGeometry

open Set MeshRatioLabels

theorem noninterior_in_packets {S mesh t Ld Lc Ud Uc : ℝ} (hm : 0 < mesh)
    (ht0 : 0 ≤ t) (htS : t ≤ S)
    (hvalid : (Ld ≤ t ∧ t ≤ Ud) ∨ (Lc ≤ t ∧ t ≤ Uc))
    (hbad : ¬fullCell Ld Lc Ud Uc (ratioLabel S mesh t)) :
    t ∈ lowerPacket mesh Ld Lc ∪ upperPacket mesh Ud Uc := by
  have hj := (ratioLabel_eq_iff hm ht0 htS (ratioLabel S mesh t)).mp rfl
  have hlo : min Ld Lc ≤ t := hvalid.elim (fun h => (min_le_left _ _).trans h.1)
    (fun h => (min_le_right _ _).trans h.1)
  have hup : t ≤ max Ud Uc := hvalid.elim (fun h => h.2.trans (le_max_left _ _))
    (fun h => h.2.trans (le_max_right _ _))
  have hwidth : upperEdge (ratioLabel S mesh t) = lowerEdge (ratioLabel S mesh t)+mesh := by
    unfold upperEdge lowerEdge
    ring
  change lowerEdge (ratioLabel S mesh t) ≤ t ∧ t < upperEdge (ratioLabel S mesh t) at hj
  by_cases hl : max Ld Lc < lowerEdge (ratioLabel S mesh t)
  · have hu : min Ud Uc < upperEdge (ratioLabel S mesh t) := by
      exact lt_of_not_ge (fun h => hbad ⟨hl,h⟩)
    exact Or.inr ⟨by linarith,hup⟩
  · exact Or.inl ⟨hlo,by linarith⟩

theorem lowerPacket_width (mesh Ld Lc : ℝ) :
    (max Ld Lc+mesh)-min Ld Lc = |Ld-Lc|+mesh := by
  rw [show max Ld Lc+mesh-min Ld Lc = max Ld Lc-min Ld Lc+mesh by ring,
    max_sub_min_eq_abs,abs_sub_comm]

theorem upperPacket_width (mesh Ud Uc : ℝ) :
    max Ud Uc-(min Ud Uc-mesh) = |Ud-Uc|+mesh := by
  rw [show max Ud Uc-(min Ud Uc-mesh) = max Ud Uc-min Ud Uc+mesh by ring,
    max_sub_min_eq_abs,abs_sub_comm]

theorem clipPacket {a b t : ℝ} (hab : a ≤ b) (ht : (1/2:ℝ) ≤ t) (hm : t ∈ Icc a b) :
    t ∈ Icc (max (1/2) a) (max (1/2) b) ∧
      max (1/2) b-max (1/2) a ≤ b-a := by
  refine ⟨⟨max_le ht hm.1,hm.2.trans (le_max_right _ _)⟩,?_⟩
  have h := abs_max_sub_max_le_abs b a (1/2:ℝ)
  rw [max_comm b (1/2),max_comm a (1/2),abs_of_nonneg (sub_nonneg.mpr hab),
    abs_of_nonneg (sub_nonneg.mpr (max_le_max_left _ hab))] at h
  exact h

theorem clipped_packet_width {a b mesh d : ℝ} (hab : a ≤ b) (hwidth : b-a ≤ d+mesh) :
    0 < max (1/2:ℝ) a ∧ max (1/2:ℝ) a ≤ max (1/2:ℝ) b ∧
      max (1/2:ℝ) b-max (1/2:ℝ) a ≤ d+mesh := by
  refine ⟨lt_of_lt_of_le (by norm_num) (le_max_left _ _),max_le_max_left _ hab,?_⟩
  have h := abs_max_sub_max_le_abs b a (1/2:ℝ)
  rw [max_comm b (1/2),max_comm a (1/2),abs_of_nonneg (sub_nonneg.mpr hab),
    abs_of_nonneg (sub_nonneg.mpr (max_le_max_left _ hab))] at h
  exact h.trans hwidth

end NumberTheoryLean.MeshBoundaryGeometry

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
theorem rightRemainder_zero {a b : ι → ℝ} (hb : ∑ i, b i = 1) (hr : residual a b = 0) (i : ι) :
    rightRemainder a b i = 0 := by
  have h := single_le_sum (fun j _ => rightRemainder_nonneg a b j) (mem_univ i)
  rw [sum_rightRemainder hb, hr] at h
  exact le_antisymm h (rightRemainder_nonneg a b i)

omit [Fintype ι] in

theorem remainder_product_self (a b : ι → ℝ) (i : ι) :
    leftRemainder a b i * rightRemainder a b i = 0 := by
  rcases le_total (a i) (b i) with h | h
  · simp [leftRemainder, rightRemainder, common, min_eq_left h]
  · simp [leftRemainder, rightRemainder, common, min_eq_right h]

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

theorem column_sum {a b : ι → ℝ} (ha : ∑ i, a i = 1) (hb : ∑ i, b i = 1) (j : ι) :
    ∑ i, matrix a b i j = b j := by
  classical
  by_cases hr : residual a b = 0
  · have hz := rightRemainder_zero hb hr j
    simp only [matrix, ite_eq_left hr, add_zero]
    simp only [sum_ite_eq', mem_univ, ite_true, if_true]
    unfold rightRemainder at hz
    linarith
  · simp only [matrix, ite_eq_right hr, sum_add_distrib]
    rw [sum_ite_eq']
    simp only [mem_univ, ite_true, if_true]
    rw [← sum_div, ← sum_mul, sum_leftRemainder ha]
    rw [mul_div_cancel_left₀ _ hr]
    unfold rightRemainder
    ring

theorem matrix_diagonal (a b : ι → ℝ) (i : ι) : matrix a b i i = common a b i := by
  simp [matrix, remainder_product_self]

theorem mismatch_mass {a b : ι → ℝ} (ha : ∑ i, a i = 1) (hb : ∑ i, b i = 1) :
    (∑ i, ∑ j, if i ≠ j then matrix a b i j else 0) = residual a b := by
  classical
  have hi (i : ι) : (∑ j, if i ≠ j then matrix a b i j else 0) + matrix a b i i = a i := by
    have h := sum_filter_add_sum_filter_not (univ : Finset ι) (fun j => i ≠ j) (fun j => matrix a b i j)
    simp only [sum_filter, not_not, sum_ite_eq, mem_univ, ite_true, if_true, row_sum ha hb] at h
    exact h
  have hsum := congrArg (fun f : ι → ℝ => ∑ i, f i) (funext hi)
  simp only [sum_add_distrib, matrix_diagonal, ha] at hsum
  unfold residual
  linarith

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

theorem conditional_map_label (K : Kernel α β) [IsMarkovKernel K] {label : β → ι}
    (hl : Measurable label) (default : β) (x : α) (i : ι) (hi : K x (label ⁻¹' {i}) ≠ 0) :
    (conditional K (hl (measurableSet_singleton i)) default x).map label = Measure.dirac i := by
  have hAE : ∀ᵐ y ∂conditional K (hl (measurableSet_singleton i)) default x, label y = i := by
    rw [conditional_apply, ite_eq_right hi]
    apply Measure.ae_smul_measure
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using
      ae_restrict_mem (hl (measurableSet_singleton i)) (μ := K x)
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hl, lintegral_dirac' _ hf]
  calc
    _ = ∫⁻ _y, f i ∂conditional K (hl (measurableSet_singleton i)) default x :=
      lintegral_congr_ae (hAE.mono (fun y hy => congrArg f hy))
    _ = _ := by rw [lintegral_const, measure_univ, mul_one]

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

theorem weight_column (x : α) (j : ι) : ∑ i, weight K L f g x i j = labelMass L g x j :=
  column_sum (labelMass_sum K hf x) (labelMass_sum L hg x) j

theorem weight_row_ofReal (x : α) (i : ι) :
    ∑ j, ENNReal.ofReal (weight K L f g x i j) = K x (f ⁻¹' {i}) := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => weight_nonnegative K L (g := g) hf x i j), weight_row K L hf hg]
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

theorem weight_column_ofReal (x : α) (j : ι) :
    ∑ i, ENNReal.ofReal (weight K L f g x i j) = L x (g ⁻¹' {j}) := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => weight_nonnegative K L (g := g) hf x i j), weight_column K L hf hg]
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

theorem weight_total_ofReal (x : α) : ∑ i, ∑ j, ENNReal.ofReal (weight K L f g x i j) = 1 := by
  simp_rw [weight_row_ofReal K L hf hg]
  have h := sum_measure_preimage_singleton (μ := K x) (Finset.univ : Finset ι)
    (fun i _ => hf (measurableSet_singleton i))
  simpa only [Finset.coe_univ, Set.preimage_univ, measure_univ] using h

theorem weight_le_left (x : α) (i j : ι) : weight K L f g x i j ≤ labelMass K f x i := by
  have h := single_le_sum (fun j _ => weight_nonnegative K L (g := g) hf x i j) (Finset.mem_univ j)
  rwa [weight_row K L hf hg] at h

theorem weight_le_right (x : α) (i j : ι) : weight K L f g x i j ≤ labelMass L g x j := by
  have h := single_le_sum (fun i _ => weight_nonnegative K L (g := g) hf x i j) (Finset.mem_univ i)
  rwa [weight_column K L hf hg] at h

theorem weight_zero_left (x : α) (i j : ι) (hi : K x (f ⁻¹' {i}) = 0) : weight K L f g x i j = 0 := by
  apply le_antisymm _ (weight_nonnegative K L (g := g) hf x i j)
  have h := weight_le_left K L hf hg x i j
  simpa only [labelMass, hi, ENNReal.toReal_zero] using h

theorem weight_zero_right (x : α) (i j : ι) (hj : L x (g ⁻¹' {j}) = 0) : weight K L f g x i j = 0 := by
  apply le_antisymm _ (weight_nonnegative K L (g := g) hf x i j)
  have h := weight_le_right K L hf hg x i j
  simpa only [labelMass, hj, ENNReal.toReal_zero] using h

theorem weight_mismatch (x : α) :
    (∑ i, ∑ j, if i ≠ j then weight K L f g x i j else 0) = errorMass K L f g x := by
  exact mismatch_mass (labelMass_sum K hf x) (labelMass_sum L hg x)

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

theorem coupled_map_snd (x : α) :
    (coupled K L hf hg dβ dγ x).map Prod.snd = L x := by
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply measurable_snd hB, coupled_apply_set K L hf hg dβ dγ x (measurable_snd hB)]
  have hpre : (Prod.snd ⁻¹' B : Set (β × γ)) = univ ×ˢ B := by ext p; simp
  rw [hpre]
  simp only [Measure.prod_prod, measure_univ, one_mul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, weight_column_ofReal K L hf hg]
  have h := congrArg (fun μ : Measure γ => μ B) (conditional_mixture L hg dγ x)
  simpa only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul] using h

end NumberTheoryLean.KernelCouplingLift

end

section

namespace NumberTheoryLean.KernelCouplingLabels

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open KernelBinConditioning KernelCouplingWeights KernelCouplingLift
open Erdos970Dependency.MaximalCoupling

variable {α β γ ι : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
variable (K : Kernel α β) (L : Kernel α γ) [IsMarkovKernel K] [IsMarkovKernel L]
variable {f : β → ι} {g : γ → ι} (hf : Measurable f) (hg : Measurable g) (dβ : β) (dγ : γ)
include hf hg

theorem component_labels (i j : ι) (x : α) :
    (component K L hf hg dβ dγ i j x).map (Prod.map f g) =
      ENNReal.ofReal (weight K L f g x i j) • Measure.dirac (i,j) := by
  by_cases hi : K x (f ⁻¹' {i}) = 0
  · simp only [component_apply, weight_zero_left K L hf hg x i j hi, ENNReal.ofReal_zero, zero_smul, Measure.map_zero]
  · by_cases hj : L x (g ⁻¹' {j}) = 0
    · simp only [component_apply, weight_zero_right K L hf hg x i j hj, ENNReal.ofReal_zero, zero_smul, Measure.map_zero]
    · rw [component_apply, Measure.map_smul, ← Measure.map_prod_map _ _ hf hg,
        conditional_map_label K hf dβ x i hi, conditional_map_label L hg dγ x j hj,
        Measure.dirac_prod_dirac]

theorem coupled_labels (x : α) :
    (coupled K L hf hg dβ dγ x).map (Prod.map f g) =
      Measure.sum (fun p : ι × ι => ENNReal.ofReal (weight K L f g x p.1 p.2) • Measure.dirac p) := by
  rw [coupled, Kernel.sum_apply, Measure.map_sum (hf.prodMap hg).aemeasurable]
  apply congrArg Measure.sum
  funext p
  exact component_labels K L hf hg dβ dγ p.1 p.2 x

theorem coupled_mismatch (x : α) :
    coupled K L hf hg dβ dγ x {p : β × γ | f p.1 ≠ g p.2} =
      ENNReal.ofReal (errorMass K L f g x) := by
  classical
  let D : Set (ι × ι) := {p | p.1 ≠ p.2}
  have hD : MeasurableSet D := (Set.to_countable D).measurableSet
  change coupled K L hf hg dβ dγ x ((Prod.map f g) ⁻¹' D) = _
  rw [← Measure.map_apply (hf.prodMap hg) hD, coupled_labels, Measure.sum_apply _ hD,
    tsum_fintype, Fintype.sum_prod_type]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hD, Set.indicator,
    D, Set.mem_ofPred_eq, Pi.one_apply, mul_ite, mul_one, mul_zero]
  have hn (i j : ι) : 0 ≤ if i ≠ j then weight K L f g x i j else 0 := by
    split_ifs
    · exact weight_nonnegative K L (g := g) hf x i j
    · exact le_rfl
  have he : (∑ i, ∑ j, if i ≠ j then ENNReal.ofReal (weight K L f g x i j) else 0) =
      ENNReal.ofReal (∑ i, ∑ j, if i ≠ j then weight K L f g x i j else 0) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hn i j))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => hn i j)]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> simp only [ENNReal.ofReal_zero]
  rw [he, weight_mismatch K L hf hg]

omit hg [IsMarkovKernel L] in
theorem errorMass_le_l1 (x : α) : errorMass K L f g x ≤
    ∑ i, |labelMass K f x i-labelMass L g x i| := by
  rw [errorMass, ← sum_leftRemainder (labelMass_sum K hf x)]
  apply Finset.sum_le_sum
  intro i hi
  unfold leftRemainder common
  rcases le_total (labelMass K f x i) (labelMass L g x i) with hab | hba
  · rw [min_eq_left hab, sub_self]
    exact abs_nonneg _
  · rw [min_eq_right hba]
    exact le_abs_self _

theorem coupled_mismatch_le_l1 (x : α) :
    coupled K L hf hg dβ dγ x {p : β × γ | f p.1 ≠ g p.2} ≤
      ENNReal.ofReal (∑ i, |labelMass K f x i-labelMass L g x i|) := by
  rw [coupled_mismatch]
  exact ENNReal.ofReal_le_ofReal (errorMass_le_l1 K L (g := g) hf x)

end NumberTheoryLean.KernelCouplingLabels

end

section

namespace NumberTheoryLean.ActualProcessCoupling

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ContinuousKilledBins MeshRatioLabels KernelCouplingLift KernelCouplingLabels KernelBinConditioning

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

theorem jointKernel_right (v mesh : ℝ) (p : ChainState w ell S start) (z : CemeteryKernel.Space CostState) :
    (jointKernel hw hell hS0 hS hr hs hsS v mesh (p,z)).map Prod.snd = continuousChain v ell S z := by
  let := chain_isMarkov hw hell hS0 hS hr hs hsS
  exact coupled_map_snd (primeParent w ell S start) (continuousParent w ell S start v)
    (primeLabel_measurable w ell S mesh start) (continuousLabel_measurable S mesh)
    none CemeteryKernel.dead (p,z)

theorem jointKernel_mismatch_bound (v mesh : ℝ) (p : ChainState w ell S start) (z : CemeteryKernel.Space CostState) :
    jointKernel hw hell hS0 hS hr hs hsS v mesh (p,z)
      {q | primeLabel w ell S mesh start q.1 ≠ continuousLabel S mesh q.2} ≤
      ENNReal.ofReal (∑ i : Label S mesh,
        |(chain w ell S start p ((primeLabel w ell S mesh start) ⁻¹' {i})).toReal -
          (continuousChain v ell S z ((continuousLabel S mesh) ⁻¹' {i})).toReal|) := by
  let := chain_isMarkov hw hell hS0 hS hr hs hsS
  exact coupled_mismatch_le_l1 (primeParent w ell S start) (continuousParent w ell S start v)
    (primeLabel_measurable w ell S mesh start) (continuousLabel_measurable S mesh)
    none CemeteryKernel.dead (p,z)

end NumberTheoryLean.ActualProcessCoupling

end

section

namespace NumberTheoryLean.ActualCouplingSupport

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ContinuousKilledBins MeshRatioLabels ActualProcessCoupling LowStateHorizon

variable {w ell S : ℝ} {start : Node}

theorem badRatio_measurable (S : ℝ) : MeasurableSet (badRatio S) :=
  (measurableSet_le (stateRatio_measurable.comp measurable_fst) measurable_const).compl

theorem unsupported_eq (S : ℝ) :
    {q : CemeteryKernel.Space CostState | ¬continuousSupported S q} = Sum.inl '' badRatio S := by
  ext q
  cases q <;> simp [continuousSupported,badRatio]

theorem continuousSupported_measurable (S : ℝ) : MeasurableSet {q | continuousSupported S q} := by
  have h : MeasurableSet {q : CemeteryKernel.Space CostState | ¬continuousSupported S q} := by
    rw [unsupported_eq]
    exact (badRatio_measurable S).inl_image
  simpa only [Set.compl_ofPred, not_not] using h.compl

theorem continuous_supported (v ell S : ℝ) (q : CemeteryKernel.Space CostState) :
    ∀ᵐ y ∂continuousChain v ell S q, continuousSupported S y := by
  apply ae_iff.mpr
  rw [unsupported_eq]
  cases q with
  | inl z =>
    rw [continuousChain, CemeteryKernel.complete_live_mass _ _ (badRatio_measurable S),
      lowKernel, Kernel.restrict_apply, Measure.restrict_apply (badRatio_measurable S)]
    have he : badRatio S ∩ lowDomain v ell S = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact hy.1 hy.2.2
    rw [he,measure_empty]
  | inr u =>
    cases u
    change Measure.dirac (CemeteryKernel.dead : CemeteryKernel.Space CostState) (Sum.inl '' badRatio S) = 0
    rw [Measure.dirac_apply' _ (badRatio_measurable S).inl_image, indicator_of_notMem (by simp [CemeteryKernel.dead])]

theorem labels_match_outcomes {mesh : ℝ} (hm : 0 < mesh)
    (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)
    (p : ChainState w ell S start) (z : CemeteryKernel.Space CostState)
    (hSup : continuousSupported S z) (hlabel : primeLabel w ell S mesh start p = continuousLabel S mesh z) :
    matchedOutcome mesh (p,z) := by
  cases p with
  | none =>
    cases z with
    | inl z =>
      change cemeteryLabel S mesh = ratioLabel S mesh (stateRatio z.1) at hlabel
      exact False.elim (ratioLabel_ne_cemetery hm hSup hlabel.symm)
    | inr u => trivial
  | some h =>
    have hpos := valid_pos (terminal_valid hs h.admissible)
    have hbound := terminal_ratio_le hsS h.admissible
    cases z with
    | inl z =>
      change ratioLabel S mesh h.node.ratio = ratioLabel S mesh (stateRatio z.1) at hlabel
      exact matching_ratios_close hm hpos.le (OccupationBoundaries.stateRatio_pos z.1).le hbound hSup hlabel
    | inr u =>
      change ratioLabel S mesh h.node.ratio = cemeteryLabel S mesh at hlabel
      exact False.elim (ratioLabel_ne_cemetery hm hbound hlabel)

variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
variable (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem joint_continuous_supported (v mesh : ℝ) (p : ChainState w ell S start) (z : CemeteryKernel.Space CostState) :
    ∀ᵐ q ∂jointKernel hw hell hS0 hS hr hs hsS v mesh (p,z), continuousSupported S q.2 := by
  have h : ∀ᵐ q ∂(jointKernel hw hell hS0 hS hr hs hsS v mesh (p,z)).map Prod.snd, continuousSupported S q := by
    rw [jointKernel_right hw hell hS0 hS hr hs hsS]
    exact continuous_supported v ell S z
  exact (ae_map_iff measurable_snd.aemeasurable (continuousSupported_measurable S)).mp h

theorem joint_matching_control (v : ℝ) {mesh : ℝ} (hm : 0 < mesh)
    (p : ChainState w ell S start) (z : CemeteryKernel.Space CostState) :
    ∀ᵐ q ∂jointKernel hw hell hS0 hS hr hs hsS v mesh (p,z),
      primeLabel w ell S mesh start q.1 = continuousLabel S mesh q.2 → matchedOutcome mesh q := by
  filter_upwards [joint_continuous_supported hw hell hS0 hS hr hs hsS v mesh p z] with q hq
  intro heq
  exact labels_match_outcomes hm hs hsS q.1 q.2 hq heq

end NumberTheoryLean.ActualCouplingSupport

end

section

namespace NumberTheoryLean.ActualCouplingFinite

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ContinuousKilledBins PrimeChainHorizon LowStateHorizon

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

instance jointPathLaw_probability (v mesh : ℝ) (z : CostState) (n : ℕ) :
    IsProbabilityMeasure (jointPathLaw hw hell hS0 hS hr hs hsS v mesh z n) := by
  unfold jointPathLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end NumberTheoryLean.ActualCouplingFinite

end

section

namespace NumberTheoryLean.ActualCouplingUpdates

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ActualCouplingSupport ContinuousKilledBins
open LowStateHorizon NearbyParentGeometry ArrivalKernelGeometry RegeneratingInverseBands
open PrimeTiltGeometry KernelDensityBridge PairedCostGrouping

variable {w ell S : ℝ} {start : Node}

theorem liftPredicate_measurable {α : Type*} [MeasurableSpace α] {P : α → Prop}
    (hP : MeasurableSet {x | P x}) : MeasurableSet {x | liftPredicate P x} := by
  exact measurableSet_sum_iff.mpr ⟨hP,MeasurableSet.univ⟩

theorem complete_ae {α : Type*} [MeasurableSpace α] (K : Kernel α α) (x : α)
    {P : α → Prop} (hP : MeasurableSet {y | P y}) (h : ∀ᵐ y ∂K x, P y) :
    ∀ᵐ y ∂CemeteryKernel.complete K (.inl x), liftPredicate P y := by
  rw [CemeteryKernel.complete_live,CemeteryKernel.liveRow_apply,ae_add_measure_iff]
  constructor
  · exact (ae_map_iff measurable_inl.aemeasurable (liftPredicate_measurable hP)).mpr h
  · apply Measure.ae_smul_measure _ _
    exact (ae_dirac_iff (liftPredicate_measurable hP)).mpr trivial

theorem prime_follows (h : History w ell S start) :
    ∀ᵐ k ∂chain w ell S start (some h), primeFollows h k := by
  classical
  apply ae_iff.mpr
  simp [chain_some,completedLaw,liveLaw,primeFollows]
  intro p hp
  exact Or.inr ⟨p,hp,rfl⟩

theorem side_set_measurable (i : Side) : MeasurableSet {s : State | stateSide s = i} := by
  cases i <;> apply measurableSet_sum_iff.mpr <;> simp [stateSide]

theorem stateKernel_side (s : State) :
    ∀ᵐ t ∂stateKernel s, stateSide t = (stateSide s).flip := by
  cases s with
  | inl s =>
    change ∀ᵐ t ∂evenBranch s, stateSide t = Side.odd
    rw [evenBranch,Kernel.map_apply _ measurable_inr]
    exact (ae_map_iff measurable_inr.aemeasurable (side_set_measurable .odd)).mpr
      (Filter.Eventually.of_forall (fun _ => rfl))
  | inr s =>
    change ∀ᵐ t ∂oddBranch s, stateSide t = Side.even
    rw [oddBranch,Kernel.map_apply _ measurable_inl]
    exact (ae_map_iff measurable_inl.aemeasurable (side_set_measurable .even)).mpr
      (Filter.Eventually.of_forall (fun _ => rfl))

theorem continuousFollows_measurable (z : CostState) : MeasurableSet {y | continuousFollows z y} :=
  (measurableSet_eq_fun measurable_snd
    (measurable_const.add (cost_measurable.comp (stateRatio_measurable.comp measurable_fst)))).inter
    (measurable_fst (side_set_measurable (stateSide z.1).flip))

theorem costKernel_follows (z : CostState) : ∀ᵐ y ∂costKernel z, continuousFollows z y := by
  have hm : Measurable (fun s : State => (s,z.2+cost (stateRatio s))) :=
    measurable_id.prodMk (measurable_const.add (cost_measurable.comp stateRatio_measurable))
  rw [costKernel_eq_map]
  apply (ae_map_iff hm.aemeasurable (continuousFollows_measurable z)).mpr
  filter_upwards [stateKernel_side z.1] with y hy
  exact ⟨rfl,hy⟩

theorem continuous_follows (v ell S : ℝ) (z : CostState) :
    ∀ᵐ y ∂continuousChain v ell S (.inl z), liftPredicate (continuousFollows z) y := by
  apply complete_ae _ _ (continuousFollows_measurable z)
  exact ae_restrict_of_ae (costKernel_follows z)

variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
variable (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem joint_follows (v mesh : ℝ) (h : History w ell S start) (z : CostState) :
    ∀ᵐ q ∂jointKernel hw hell hS0 hS hr hs hsS v mesh (some h,.inl z),
      primeFollows h q.1 ∧ liftPredicate (continuousFollows z) q.2 := by
  have hL : ∀ᵐ p ∂(jointKernel hw hell hS0 hS hr hs hsS v mesh (some h,.inl z)).map Prod.fst,
      primeFollows h p := by
    rw [jointKernel_left hw hell hS0 hS hr hs hsS]
    exact prime_follows h
  have hR : ∀ᵐ y ∂(jointKernel hw hell hS0 hS hr hs hsS v mesh (some h,.inl z)).map Prod.snd,
      liftPredicate (continuousFollows z) y := by
    rw [jointKernel_right hw hell hS0 hS hr hs hsS]
    exact continuous_follows v ell S z
  exact ((ae_map_iff measurable_fst.aemeasurable (show MeasurableSet {p | primeFollows h p} from trivial)).mp hL).and
    ((ae_map_iff measurable_snd.aemeasurable (liftPredicate_measurable (continuousFollows_measurable z))).mp hR)

include hell hr hs

theorem prime_step_gap (h : History w ell S start) (p : ℕ) (hp : p ∈ nodeChildren w ell S h.node) :
    (h.append p hp).node.gap = nextGap h.node.gap (h.append p hp).node.ratio := by
  have hrg := terminal_gap_positive (show 0 ≤ ell by linarith) hr hs h.admissible
  have hvalid := terminal_valid hs h.admissible
  rw [History.append_node]
  exact (nextGap_childRatio hrg (child_exponent_positive (show 0 ≤ ell by linarith) hp)
    (valid_pos (child_valid hvalid hp))).symm

theorem matched_live_update {v mesh d : ℝ} (h k : History w ell S start) (z y : CostState)
    (hfollow : primeFollows h (some k)) (hcont : continuousFollows z y)
    (hside : h.node.side = stateSide z.1)
    (hgap : |Real.log h.node.gap-Real.log (gapValue v z)| ≤ d)
    (hmatch : |k.node.ratio-stateRatio y.1| ≤ mesh) :
    k.node.side = stateSide y.1 ∧
      |Real.log k.node.gap-Real.log (gapValue v y)| ≤ d+4*mesh := by
  obtain ⟨p,hp,rfl⟩ := hfollow
  have hrg := terminal_gap_positive (show 0 ≤ ell by linarith) hr hs h.admissible
  have hnext := terminal_valid hs (h.append p hp).admissible
  constructor
  · rw [History.append_node]
    change h.node.side.flip = stateSide y.1
    rw [hcont.2,hside]
  · have hy : y = (y.1,z.2+cost (stateRatio y.1)) := Prod.ext rfl hcont.1
    have hygap : gapValue v y = nextGap (gapValue v z) (stateRatio y.1) := by
      calc
        _ = gapValue v (y.1,z.2+cost (stateRatio y.1)) := congrArg (gapValue v) hy
        _ = _ := gapValue_update v z y.1
    rw [prime_step_gap hell hr hs, hygap]
    exact log_gap_step hrg (Real.exp_pos _) (PrimeTiltBounds.valid_ge_half hnext)
      (CostPrefixTransport.stateRatio_ge_half y.1) hgap hmatch

end NumberTheoryLean.ActualCouplingUpdates

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_CommonCellSum
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ContinuousParentBins

open _root_.Set _root_.MeasureTheory
open scoped ENNReal
open FinitePathGeometry PrimeTiltBounds PrimeTiltMonotone ContinuousRatioBins
open HarmonicExponentMeasure WeightGlobalBounds

theorem multiplier_source_ratio {i : Side} {s t : ℝ} (hs : Valid i s) (ht : Valid i t) (u : ℝ) :
    multiplier i s u = (weight i t/weight i s)*multiplier i t u := by
  by_cases hu : u = 0
  · simp [multiplier,hu]
  · unfold multiplier
    field_simp [hu,(weight_pos hs).ne',(weight_pos ht).ne']

theorem continuous_bin_mass_ratio {i : Side} {s t a b : ℝ} (hs : Valid i s) (ht : Valid i t)
    (hsa : minRatio i s ≤ a) (hta : minRatio i t ≤ a) :
    weightedRatioLaw i s (Ico a b) = ENNReal.ofReal (weight i t/weight i s) * weightedRatioLaw i t (Ico a b) := by
  have hq : 0 ≤ weight i t/weight i s := (div_pos (weight_pos ht) (weight_pos hs)).le
  simp only [weightedRatioLaw, withDensity_apply _ measurableSet_Ico]
  rw [ratio_restrict_bin hsa, ratio_restrict_bin hta, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro u
  rw [multiplier_source_ratio hs ht u, ENNReal.ofReal_mul hq]

theorem continuousBin_parent_ratio {i : Side} {s t a b : ℝ} (hs : Valid i s) (ht : Valid i t)
    (hsa : minRatio i s ≤ a) (hta : minRatio i t ≤ a) :
    continuousBin i s a b = (weight i t/weight i s)*continuousBin i t a b := by
  unfold continuousBin
  rw [continuous_bin_mass_ratio hs ht hsa hta, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (div_pos (weight_pos ht) (weight_pos hs)).le]

theorem positive_ratio_error {a b d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hlog : |Real.log a-Real.log b| ≤ d) : |a/b-1| ≤ Real.exp d-1 := by
  have hq := div_pos ha hb
  rw [← Real.log_div ha.ne' hb.ne'] at hlog
  have hlo := Real.exp_le_exp.mpr (abs_le.mp hlog).1
  have hup := Real.exp_le_exp.mpr (abs_le.mp hlog).2
  rw [Real.exp_log hq] at hlo hup
  have hsum : 2 ≤ Real.exp d+Real.exp (-d) := by
    linarith [Real.add_one_le_exp d, Real.add_one_le_exp (-d)]
  rw [abs_le]
  constructor <;> linarith

theorem continuous_parent_bin_error : ∃ C : ℝ, 0 < C ∧ ∀ S : ℝ, 3 ≤ S →
    ∀ i : Side, ∀ s t a b : ℝ, Valid i s → Valid i t → s ≤ S → t ≤ S →
      minRatio i s ≤ a → minRatio i t ≤ a →
      |continuousBin i s a b-continuousBin i t a b| ≤
        (Real.exp (C*(1+S)^3*|s-t|)-1)*continuousBin i t a b := by
  obtain ⟨C,hC,hbound⟩ := weights_log_lipschitz
  refine ⟨C,hC,?_⟩
  intro S hS i s t a b hs ht hsS htS hsa hta
  have hlogs : |Real.log (weight i s)-Real.log (weight i t)| ≤ C*(1+S)^3*|s-t| := by
    cases i with
    | even => exact (hbound S hS).1 s t hs ht hsS htS
    | odd => exact (hbound S hS).2 s t hs ht hsS htS
  have hr := positive_ratio_error (weight_pos ht) (weight_pos hs)
    ((abs_sub_comm _ _).trans_le hlogs)
  have hmass : 0 ≤ continuousBin i t a b := ENNReal.toReal_nonneg
  rw [continuousBin_parent_ratio hs ht hsa hta]
  rw [show (weight i t/weight i s)*continuousBin i t a b-continuousBin i t a b =
    (weight i t/weight i s-1)*continuousBin i t a b by ring, abs_mul, abs_of_nonneg hmass]
  exact mul_le_mul_of_nonneg_right hr hmass

end NumberTheoryLean.ContinuousParentBins

end

section

namespace NumberTheoryLean.NearbyParentFullBins

open _root_.Set _root_.MeasureTheory
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open PrimeBinMembership ActualPrimeBins ContinuousKilledBins
open NormalizedPrimeBins ContinuousRatioBins ContinuousParentBins RegeneratingInverseBands

 theorem nearby_parent_full_bin_error : ∃ c C D w₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < D ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ ell S : ℝ, ∀ start : Node, ∀ h : History w ell S start,
    ∀ v : ℝ, ∀ z : CostState, ∀ a b : ℝ,
      1 ≤ ell → 3 ≤ S → 0 < start.gap → Valid start.side start.ratio → start.ratio ≤ S → Consistent start →
      stateRatio z.1 ≤ S → h.node.side = stateSide z.1 →
      minRatio h.node.side h.node.ratio < a → minRatio (stateSide z.1) (stateRatio z.1) < a →
      a ≤ b → b ≤ S → b ≤ h.node.gap/ell-1 → b ≤ gapValue v z/ell-1 →
      |(chain w ell S start (some h) (liveBin a b)).toReal -
        (continuousChain v ell S (.inl z) (Sum.inl '' ratioBinSet a b)).toReal| ≤
      C*(1+S)^5*((b-a)^2+Real.exp (-c*Real.sqrt ((1/2 : ℝ)*Real.log w))) +
        epsilon w*continuousBin h.node.side h.node.ratio a b +
        (Real.exp (D*(1+S)^3*|h.node.ratio-stateRatio z.1|)-1)*
          continuousBin (stateSide z.1) (stateRatio z.1) a b := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,hprime⟩ := normalized_bin_error
  obtain ⟨D,hD,hparent⟩ := continuous_parent_bin_error
  refine ⟨c,C,D,w₀,hc,hC,hD,hw₀,?_⟩
  intro w hw ell S start h v z a b hell hS hr hs hsS hcons htS hside hma hta hab hbS harrP harrC
  have hw1 := hw₀.trans_le hw
  have hell0 : 0 < ell := by linarith
  have hnvalid := terminal_valid hs h.admissible
  have hngap := terminal_gap_positive hell0.le hr hs h.admissible
  have hnS := terminal_ratio_le hsS h.admissible
  have hncons := history_consistent hell0.le hr hs hcons h
  have htvalid : Valid h.node.side (stateRatio z.1) := by rw [hside]; exact stateRatio_valid z.1
  have hta' : minRatio h.node.side (stateRatio z.1) < a := by rwa [hside]
  have ha : 0 < a := (PrimeTiltMonotone.minRatio_pos hnvalid).trans hma
  have hlow : (1/2 : ℝ) ≤ h.node.gap/(b+1) := by
    have h : ell ≤ h.node.gap/(b+1) := by
      apply (le_div_iff₀ (by linarith : 0 < b+1)).mpr
      have hm := (le_div_iff₀ hell0).mp (show b+1 ≤ h.node.gap/ell by linarith)
      nlinarith
    linarith
  rw [chain_full_bin_real h hw1 hell0 hngap hnvalid hncons hma hab hbS harrP,
    continuousChain_full_bin_real v hell0 z hbS harrC, ← hside]
  exact (abs_sub_le _ (continuousBin h.node.side h.node.ratio a b) _).trans (add_le_add
    (hprime w hw h.node.gap S hngap hS h.node.side h.node.ratio a b hnvalid hnS hma.le hab hbS hlow)
    (hparent S hS h.node.side h.node.ratio (stateRatio z.1) a b hnvalid htvalid hnS htS hma.le hta'.le))

end NumberTheoryLean.NearbyParentFullBins

end

section

namespace NumberTheoryLean.ActualSupportIntervals

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open PrimeTiltGeometry ActualCouplingUpdates ContinuousKilledBins LowStateHorizon
open ArrivalKernelGeometry RegeneratingInverseBands PairedCostGrouping

theorem prime_child_interval {w ell S : ℝ} {start : Node} (h : History w ell S start)
    (hell : 0 < ell) (hr : 0 < h.node.gap) (hs : Valid h.node.side h.node.ratio)
    (p : ℕ) (hp : p ∈ nodeChildren w ell S h.node) :
    (h.append p hp).node.ratio ∈ Icc (minRatio h.node.side h.node.ratio) (upperSupport S ell h.node.gap) := by
  classical
  have hp' := (Finset.mem_filter.mp hp).2
  have ht0 := valid_pos (child_valid hs hp)
  have hx := hp'.1
  have heq := nextExponent_childRatio hr (child_exponent_positive hell.le hp)
  have hu : childRatio w h.node.gap p < h.node.gap/ell-1 := by
    rw [← heq] at hx
    have hmul := (lt_div_iff₀ (by linarith : 0 < childRatio w h.node.gap p+1)).mp hx
    have hdiv : childRatio w h.node.gap p+1 < h.node.gap/ell := (lt_div_iff₀ hell).mpr (by nlinarith)
    linarith
  rw [History.append_node]
  exact ⟨hp'.2.2.1,le_min hp'.2.2.2 hu.le⟩

theorem prime_row_interval {w ell S : ℝ} {start : Node} (h : History w ell S start)
    (hell : 0 < ell) (hr : 0 < h.node.gap) (hs : Valid h.node.side h.node.ratio) :
    ∀ᵐ k ∂chain w ell S start (some h),
      match k with
      | none => True
      | some k => k.node.ratio ∈ Icc (minRatio h.node.side h.node.ratio) (upperSupport S ell h.node.gap) := by
  filter_upwards [prime_follows h] with k hk
  cases k with
  | none => trivial
  | some k =>
    obtain ⟨p,hp,rfl⟩ := hk
    exact prime_child_interval h hell hr hs p hp

theorem costKernel_lower_support (z : CostState) :
    ∀ᵐ y ∂costKernel z, minRatio (stateSide z.1) (stateRatio z.1) ≤ stateRatio y.1 := by
  have hm : Measurable (fun s : State => (s,z.2+cost (stateRatio s))) :=
    measurable_id.prodMk (measurable_const.add (cost_measurable.comp stateRatio_measurable))
  have hP : MeasurableSet {y : CostState | minRatio (stateSide z.1) (stateRatio z.1) ≤ stateRatio y.1} :=
    measurableSet_le measurable_const (stateRatio_measurable.comp measurable_fst)
  rw [costKernel_eq_map]
  exact (ae_map_iff hm.aemeasurable hP).mpr (stateKernel_ae_minRatio z.1)

theorem continuous_interval_measurable (v ell S : ℝ) (z : CostState) :
    MeasurableSet {y : CostState | stateRatio y.1 ∈
      Icc (minRatio (stateSide z.1) (stateRatio z.1)) (upperSupport S ell (gapValue v z))} :=
  (stateRatio_measurable.comp measurable_fst) measurableSet_Icc

theorem continuous_low_interval (v S : ℝ) {ell : ℝ} (hell : 0 < ell) (z : CostState) :
    ∀ᵐ y ∂lowKernel costKernel v ell S z, stateRatio y.1 ∈
      Icc (minRatio (stateSide z.1) (stateRatio z.1)) (upperSupport S ell (gapValue v z)) := by
  rw [lowKernel,Kernel.restrict_apply]
  filter_upwards [ae_restrict_of_ae (costKernel_time_update z),ae_restrict_of_ae (costKernel_lower_support z),
    ae_restrict_mem (lowDomain_measurable v ell S)] with y htime hlo hD
  have hy : y = (y.1,z.2+cost (stateRatio y.1)) := Prod.ext rfl htime
  have hcur : currentExponent v y = nextExponent (gapValue v z) (stateRatio y.1) := by
    calc
      _ = currentExponent v (y.1,z.2+cost (stateRatio y.1)) := congrArg (currentExponent v) hy
      _ = _ := currentExponent_update v z y.1
  have hupper : stateRatio y.1 < gapValue v z/ell-1 := by
    have hx : ell < nextExponent (gapValue v z) (stateRatio y.1) := by
      rw [← hcur]
      exact hD.1
    have ht0 := OccupationBoundaries.stateRatio_pos y.1
    have hmul := (lt_div_iff₀ (by linarith : 0 < stateRatio y.1+1)).mp hx
    have hdiv : stateRatio y.1+1 < gapValue v z/ell := (lt_div_iff₀ hell).mpr (by nlinarith)
    linarith
  exact ⟨hlo,le_min hD.2 hupper.le⟩

theorem continuous_row_interval (v S : ℝ) {ell : ℝ} (hell : 0 < ell) (z : CostState) :
    ∀ᵐ y ∂continuousChain v ell S (.inl z), liftPredicate (fun y : CostState => stateRatio y.1 ∈
      Icc (minRatio (stateSide z.1) (stateRatio z.1)) (upperSupport S ell (gapValue v z))) y :=
  complete_ae _ z (continuous_interval_measurable v ell S z) (continuous_low_interval v S hell z)

end NumberTheoryLean.ActualSupportIntervals

end

section

namespace NumberTheoryLean.ActualMeshBins

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ActualCouplingSupport ActualPrimeBins ContinuousKilledBins
open MeshRatioLabels MeshBoundaryGeometry ActualSupportIntervals PrimeBinMembership
open NearbyParentFullBins ContinuousRatioBins RegeneratingInverseBands

variable {w ell S : ℝ} {start : Node}

theorem prime_label_eq_bin {mesh : ℝ} (hm : 0 < mesh) (hs : Valid start.side start.ratio)
    (hsS : start.ratio ≤ S) (j : Label S mesh) (hj : j ≠ cemeteryLabel S mesh) :
    (primeLabel w ell S mesh start) ⁻¹' {j} = liveBin (lowerEdge j) (upperEdge j) := by
  ext p
  cases p with
  | none =>
    change cemeteryLabel S mesh = j ↔ False
    simp [Ne.symm hj]
  | some h =>
    have ht := valid_pos (terminal_valid hs h.admissible)
    have hS := terminal_ratio_le hsS h.admissible
    exact ratioLabel_eq_iff hm ht.le hS j

theorem continuous_label_mass_eq_bin (v ell S : ℝ) {mesh : ℝ} (hm : 0 < mesh)
    (z : CostState) (j : Label S mesh) (hj : j ≠ cemeteryLabel S mesh) :
    continuousChain v ell S (.inl z) ((continuousLabel S mesh) ⁻¹' {j}) =
      continuousChain v ell S (.inl z) (Sum.inl '' ratioBinSet (lowerEdge j) (upperEdge j)) := by
  apply measure_congr
  filter_upwards [continuous_supported v ell S (.inl z)] with y hy
  apply propext
  cases y with
  | inr u =>
    change (cemeteryLabel S mesh = j) ↔ ∃ x ∈ ratioBinSet (lowerEdge j) (upperEdge j), (Sum.inl x : CemeteryKernel.Space CostState) = Sum.inr u
    simp [Ne.symm hj]
  | inl y =>
    have heq := ratioLabel_eq_iff hm (OccupationBoundaries.stateRatio_pos y.1).le hy j
    change (ratioLabel S mesh (stateRatio y.1) = j) ↔ ∃ x ∈ ratioBinSet (lowerEdge j) (upperEdge j), (Sum.inl x : CemeteryKernel.Space CostState) = Sum.inl y
    simpa only [Set.mem_image,Sum.inl.injEq,exists_eq_right,ratioBinSet,mem_ofPred_eq,lowerEdge,upperEdge] using heq

theorem cell_below_S_not_cemetery {S mesh : ℝ} (hm : 0 < mesh) (j : Label S mesh)
    (hj : upperEdge j ≤ S) : j ≠ cemeteryLabel S mesh := by
  intro heq
  subst j
  have hf := Nat.lt_floor_add_one (S/mesh)
  have hmul : S < ((⌊S/mesh⌋₊:ℝ)+1)*mesh := (div_lt_iff₀ hm).mp hf
  change (((binCount S mesh+1:ℕ):ℝ)+1)*mesh ≤ S at hj
  simp only [Nat.cast_add,Nat.cast_one,binCount] at hj
  nlinarith

theorem mesh_cells_disjoint {S mesh : ℝ} (hm : 0 < mesh) :
    Pairwise (fun j k : Label S mesh => Disjoint (Ico (lowerEdge j) (upperEdge j)) (Ico (lowerEdge k) (upperEdge k))) := by
  intro j k hjk
  apply Set.disjoint_left.mpr
  intro t htj htk
  have hne : j.val ≠ k.val := fun h => hjk (Fin.ext h)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hle : (j.val:ℝ)+1 ≤ (k.val:ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
    have he : upperEdge j ≤ lowerEdge k := mul_le_mul_of_nonneg_right hle hm.le
    exact (htj.2.trans_le (he.trans htk.1)).false
  · have hle : (k.val:ℝ)+1 ≤ (j.val:ℝ) := by exact_mod_cast Nat.succ_le_of_lt hgt
    have he : upperEdge k ≤ lowerEdge j := mul_le_mul_of_nonneg_right hle hm.le
    exact (htk.2.trans_le (he.trans htj.1)).false

theorem continuous_mesh_sum_le_one {S mesh s : ℝ} {i : Side} (hm : 0 < mesh) (hs : Valid i s)
    (I : Finset (Label S mesh)) :
    (∑ j ∈ I,continuousBin i s (lowerEdge j) (upperEdge j)) ≤ 1 := by
  let := weightedRatioLaw_probability hs
  have hUnion := measure_biUnion_finset (μ:=weightedRatioLaw i s)
    (s:=I) (f:=fun j => Ico (lowerEdge j) (upperEdge j))
    (fun _ _ _ _ hne => mesh_cells_disjoint hm hne) (fun _ _ => measurableSet_Ico)
  have hmass : (∑ j ∈ I,weightedRatioLaw i s (Ico (lowerEdge j) (upperEdge j))) ≤ 1 := by
    rw [← hUnion]
    exact (measure_mono (subset_univ _)).trans_eq measure_univ
  unfold continuousBin
  rw [← ENNReal.toReal_sum (fun j _ => measure_ne_top (weightedRatioLaw i s) (Ico (lowerEdge j) (upperEdge j)))]
  simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top hmass

theorem common_cell_error : ∃ c C D w₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < D ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ ell S : ℝ, ∀ start : Node, ∀ h : History w ell S start,
    ∀ v : ℝ, ∀ z : CostState, ∀ mesh : ℝ, ∀ j : Label S mesh,
      1 ≤ ell → 3 ≤ S → 0 < start.gap → Valid start.side start.ratio → start.ratio ≤ S → Consistent start →
      stateRatio z.1 ≤ S → h.node.side = stateSide z.1 → 0 < mesh →
      fullCell (minRatio h.node.side h.node.ratio) (minRatio (stateSide z.1) (stateRatio z.1))
        (upperSupport S ell h.node.gap) (upperSupport S ell (gapValue v z)) j →
      |(chain w ell S start (some h) ((primeLabel w ell S mesh start) ⁻¹' {j})).toReal-
        (continuousChain v ell S (.inl z) ((continuousLabel S mesh) ⁻¹' {j})).toReal| ≤
        C*(1+S)^5*(mesh^2+Real.exp (-c*Real.sqrt ((1/2:ℝ)*Real.log w)))+
        epsilon w*continuousBin h.node.side h.node.ratio (lowerEdge j) (upperEdge j)+
        (Real.exp (D*(1+S)^3*|h.node.ratio-stateRatio z.1|)-1)*
          continuousBin (stateSide z.1) (stateRatio z.1) (lowerEdge j) (upperEdge j) := by
  obtain ⟨c,C,D,w₀,hc,hC,hD,hw₀,hbound⟩ := nearby_parent_full_bin_error
  refine ⟨c,C,D,w₀,hc,hC,hD,hw₀,?_⟩
  intro w hw ell S start h v z mesh j hell hS hr hs hsS hcons hzS hside hm hcell
  have hLd := (le_max_left _ _).trans_lt hcell.1
  have hLc := (le_max_right _ _).trans_lt hcell.1
  have hUd := hcell.2.trans (min_le_left _ _)
  have hUc := hcell.2.trans (min_le_right _ _)
  have hbS := hUd.trans (min_le_left _ _)
  have hbp := hUd.trans (min_le_right _ _)
  have hbc := hUc.trans (min_le_right _ _)
  have hj := cell_below_S_not_cemetery hm j hbS
  rw [prime_label_eq_bin hm hs hsS j hj,continuous_label_mass_eq_bin v ell S hm z j hj]
  have hab : lowerEdge j ≤ upperEdge j := by unfold lowerEdge upperEdge; nlinarith
  have he := hbound w hw ell S start h v z (lowerEdge j) (upperEdge j) hell hS hr hs hsS hcons hzS hside hLd hLc hab hbS hbp hbc
  have hwidth : upperEdge j-lowerEdge j = mesh := by unfold upperEdge lowerEdge; ring
  rwa [hwidth] at he

end NumberTheoryLean.ActualMeshBins

end

section

namespace NumberTheoryLean.CommonCellSum

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open MeshRatioLabels MeshBoundaryGeometry ActualSupportIntervals ActualMeshBins
open ActualProcessCoupling ContinuousKilledBins PrimeBinMembership
open ContinuousRatioBins RegeneratingInverseBands KernelBinConditioning

theorem common_cell_sum_error : ∃ c C D w₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < D ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ ell S : ℝ, ∀ start : Node, ∀ h : History w ell S start,
    ∀ v : ℝ, ∀ z : CostState, ∀ mesh : ℝ, ∀ I : Finset (Label S mesh),
      1 ≤ ell → 3 ≤ S → 0 < start.gap → Valid start.side start.ratio → start.ratio ≤ S → Consistent start →
      stateRatio z.1 ≤ S → h.node.side = stateSide z.1 → 0 < mesh →
      (∀ j ∈ I, fullCell (minRatio h.node.side h.node.ratio) (minRatio (stateSide z.1) (stateRatio z.1))
        (upperSupport S ell h.node.gap) (upperSupport S ell (gapValue v z)) j) →
      (∑ j ∈ I, |labelMass (chain w ell S start) (primeLabel w ell S mesh start) (some h) j-
        labelMass (continuousChain v ell S) (continuousLabel S mesh) (.inl z) j|) ≤
        (S/mesh+2)*(C*(1+S)^5*(mesh^2+Real.exp (-c*Real.sqrt ((1/2:ℝ)*Real.log w))))+
        epsilon w+(Real.exp (D*(1+S)^3*|h.node.ratio-stateRatio z.1|)-1) := by
  obtain ⟨c,C,D,w₀,hc,hC,hD,hw₀,hbound⟩ := common_cell_error
  refine ⟨c,C,D,w₀,hc,hC,hD,hw₀,?_⟩
  intro w hw ell S start h v z mesh I hell hS hr hs hsS hcons hzS hside hm hcells
  let A := C*(1+S)^5*(mesh^2+Real.exp (-c*Real.sqrt ((1/2:ℝ)*Real.log w)))
  let Q := Real.exp (D*(1+S)^3*|h.node.ratio-stateRatio z.1|)-1
  let P : Label S mesh → ℝ := fun j => continuousBin h.node.side h.node.ratio (lowerEdge j) (upperEdge j)
  let R : Label S mesh → ℝ := fun j => continuousBin (stateSide z.1) (stateRatio z.1) (lowerEdge j) (upperEdge j)
  have hS1 : 0 ≤ 1+S := by linarith
  have hA : 0 ≤ A := by dsimp [A] <;> positivity
  have hQ : 0 ≤ Q := by
    apply sub_nonneg.mpr
    apply Real.one_le_exp_iff.mpr
    positivity
  have hPsum : (∑ j ∈ I,P j) ≤ 1 := continuous_mesh_sum_le_one hm (terminal_valid hs h.admissible) I
  have hRsum : (∑ j ∈ I,R j) ≤ 1 := continuous_mesh_sum_le_one hm (stateRatio_valid z.1) I
  have hcard : (I.card:ℝ) ≤ S/mesh+2 := by
    have h : (I.card:ℝ) ≤ (Fintype.card (Label S mesh):ℝ) := by exact_mod_cast Finset.card_le_univ I
    exact h.trans (label_card_le (by linarith) hm)
  calc
    _ ≤ ∑ j ∈ I,(A+epsilon w*P j+Q*R j) := by
      apply Finset.sum_le_sum
      intro j hj
      exact hbound w hw ell S start h v z mesh j hell hS hr hs hsS hcons hzS hside hm (hcells j hj)
    _ = (I.card:ℝ)*A+epsilon w*(∑ j ∈ I,P j)+Q*(∑ j ∈ I,R j) := by
      simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,← Finset.mul_sum]
    _ ≤ _ := by
      have h1 := mul_le_mul_of_nonneg_right hcard hA
      have h2 := mul_le_mul_of_nonneg_left hPsum (epsilon_pos w).le
      have h3 := mul_le_mul_of_nonneg_left hRsum hQ
      dsimp only [A,Q] at h1 h3 ⊢
      linarith

end NumberTheoryLean.CommonCellSum

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_FiniteLabelBudget
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.FiniteLabelBudget

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open KernelBinConditioning

section Vectors
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem total_l1_le_twice_live (a b : ι → ℝ) (c : ι)
    (ha : ∑ i,a i = 1) (hb : ∑ i,b i = 1) :
    ∑ i,|a i-b i| ≤ 2*(∑ i ∈ Finset.univ.erase c,|a i-b i|) := by
  have hsa := Finset.sum_erase_add (s:=Finset.univ) a (Finset.mem_univ c)
  have hsb := Finset.sum_erase_add (s:=Finset.univ) b (Finset.mem_univ c)
  have hsd := Finset.sum_sub_distrib (s:=Finset.univ.erase c) (f:=a) (g:=b)
  have heq : a c-b c = -(∑ i ∈ Finset.univ.erase c,(a i-b i)) := by rw [hsd]; linarith
  have hc : |a c-b c| ≤ ∑ i ∈ Finset.univ.erase c,|a i-b i| := by
    rw [heq,abs_neg]
    exact Finset.abs_sum_le_sum_abs _ _
  have hse := Finset.sum_erase_add (s:=Finset.univ) (fun i => |a i-b i|) (Finset.mem_univ c)
  linarith

theorem interior_boundary_budget (a b : ι → ℝ) (c : ι) (good : ι → Prop) [DecidablePred good]
    (ha0 : ∀ i,0 ≤ a i) (hb0 : ∀ i,0 ≤ b i) (ha : ∑ i,a i = 1) (hb : ∑ i,b i = 1) :
    ∑ i,|a i-b i| ≤ 2*((∑ i ∈ (Finset.univ.erase c).filter good,|a i-b i|)+
      (∑ i ∈ (Finset.univ.erase c).filter (fun i => ¬good i),(a i+b i))) := by
  classical
  apply (total_l1_le_twice_live a b c ha hb).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hsplit := Finset.sum_filter_add_sum_filter_not (s:=Finset.univ.erase c)
    (p:=good) (f:=fun i => |a i-b i|)
  rw [← hsplit]
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro i _
  rw [abs_le]
  constructor <;> linarith [ha0 i,hb0 i]
end Vectors

theorem selected_label_mass {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [Fintype ι]
    (K : Kernel α β) [IsMarkovKernel K] {f : β → ι} (hf : Measurable f)
    (x : α) (I : Finset ι) :
    (∑ i ∈ I,labelMass K f x i) = (K x (f ⁻¹' (I:Set ι))).toReal := by
  exact sum_measureReal_preimage_singleton I (fun i _ => hf (measurableSet_singleton i))

end NumberTheoryLean.FiniteLabelBudget


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_RetainedIntervalUpper
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualCouplingFinite.jointKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.ActualCouplingFinite.jointPathLaw_probability _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.jointKernel_isMarkov _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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

theorem retained_short_interval_upper : ∃ c C w₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ ell S : ℝ, ∀ i : Side, ∀ s r cap a b : ℝ, ∀ closed : Bool,
      1 ≤ ell → 0 < r → Valid i s → s ≤ S → 0 < a → a ≤ b → b-a ≤ 1 →
      retainedIntervalTilt w ell S i s r cap closed a b ≤
        C*(1+S)^2*((b-a)+Real.exp (-c*Real.sqrt ((1/2:ℝ)*Real.log w))) := by
  classical
  obtain ⟨c,C,w₀,hc,hC,hw₀,herr⟩ := closed_prime_error
  obtain ⟨D,hD,henv⟩ := multiplier_envelope
  refine ⟨c,D*(1+C),w₀,hc,by positivity,hw₀,?_⟩
  intro w hw ell S i s r cap a b closed hell hr hs hsS ha hab hwidth
  let A := retainedInterval w ell S i s r cap closed a b
  let e := Real.exp (-c*Real.sqrt ((1/2:ℝ)*Real.log w))
  by_cases hne : A.Nonempty
  · have hlow := short_interval_lower_exponent hell hs ha hab hwidth hne
    have herror := herr w hw r a b hr ha hab hlow
    have hlog : Real.log (b+1)-Real.log (a+1) ≤ b-a :=
      ((bin_log_width_bounds ha hab).2).trans (div_le_self (sub_nonneg.mpr hab) (by linarith))
    have hraw : closedMass w r a b ≤ (b-a)+C*e := by linarith [(abs_le.mp herror).2]
    have hsub : (∑ p ∈ A,(p:ℝ)⁻¹) ≤ closedMass w r a b :=
      Finset.sum_le_sum_of_subset_of_nonneg (retained_subset_closed (hw₀.trans_le hw) ha hab)
        (fun p _ _ => inv_nonneg.mpr (Nat.cast_nonneg p))
    have htilt : retainedIntervalTilt w ell S i s r cap closed a b ≤ D*(1+S)^2*(∑ p ∈ A,(p:ℝ)⁻¹) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro p hp
      have hchild := (Finset.mem_filter.mp hp).1
      have hm := henv S i s (childRatio w r p) hs hsS (Finset.mem_filter.mp hchild).2.2.2.1
      rw [primeTilt_eq_multiplier,mul_comm (D*(1+S)^2)]
      exact mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr (Nat.cast_nonneg p))
    calc
      _ ≤ D*(1+S)^2*closedMass w r a b := htilt.trans (mul_le_mul_of_nonneg_left hsub (by positivity))
      _ ≤ D*(1+S)^2*((b-a)+C*e) := mul_le_mul_of_nonneg_left hraw (by positivity)
      _ ≤ (D*(1+C))*(1+S)^2*((b-a)+e) := by
        have hh : 0 ≤ b-a := sub_nonneg.mpr hab
        have he : 0 ≤ e := (Real.exp_pos _).le
        have hm := mul_nonneg (show 0 ≤ D*(1+S)^2 by positivity)
          (show 0 ≤ C*(b-a)+e by positivity)
        nlinarith
  · have he : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    change ∑ p ∈ A, _ ≤ _
    rw [he,Finset.sum_empty]
    have hh : 0 ≤ b-a := sub_nonneg.mpr hab
    positivity

end NumberTheoryLean.RetainedIntervalUpper


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_ConditionalPrimeBins
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.ActualCouplingFinite.jointKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.ActualCouplingFinite.jointPathLaw_probability _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.continuousParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.jointKernel_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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

theorem prime_completed_interval_upper : ∃ c C w₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ ell S : ℝ, ∀ start : Node,
      1 ≤ ell → 0 < start.gap → Valid start.side start.ratio → start.ratio ≤ S →
      ∀ h : History w ell S start, ∀ a b : ℝ, 0 < a → a ≤ b → b-a ≤ 1 →
        chain w ell S start (some h) (closedLiveBin a b) ≤
          ENNReal.ofReal (C*(1+S)^2*((b-a)+Real.exp (-c*Real.sqrt ((1/2:ℝ)*Real.log w)))) := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,hbound⟩ := retained_short_interval_upper
  refine ⟨c,C,w₀,hc,hC,hw₀,?_⟩
  intro w hw ell S start hell hr hs hsS h a b ha hab hwidth
  have hv := terminal_valid hs h.admissible
  have hg := terminal_gap_positive (show 0 ≤ ell by linarith) hr hs h.admissible
  have hS := terminal_ratio_le hsS h.admissible
  exact (chain_interval_le_tilt h hv a b).trans (ENNReal.ofReal_le_ofReal
    (hbound w hw ell S h.node.side h.node.ratio h.node.gap h.node.cutoff a b h.node.closed
      hell hg hv hS ha hab hwidth))

end NumberTheoryLean.PrimeCompletedIntervalUpper



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_CouplingLabelEvents
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.CoupledBoundaryEvents

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualSupportIntervals MeshBoundaryGeometry MeshRatioLabels
open PrimeCompletedIntervalUpper ContinuousIntervalUpper ActualCouplingSupport
open RegeneratingInverseBands ContinuousKilledBins

variable {w ell S : ℝ} {start : Node}

theorem packet_widths {mesh : ℝ} (hm : 0 ≤ mesh) (Ld Lc Ud Uc : ℝ) :
    (0 < lowerA Ld Lc ∧ lowerA Ld Lc ≤ lowerB mesh Ld Lc ∧
      lowerB mesh Ld Lc-lowerA Ld Lc ≤ |Ld-Lc|+mesh) ∧
    (0 < upperA mesh Ud Uc ∧ upperA mesh Ud Uc ≤ upperB Ud Uc ∧
      upperB Ud Uc-upperA mesh Ud Uc ≤ |Ud-Uc|+mesh) := by
  have hl : min Ld Lc ≤ max Ld Lc+mesh := by linarith [min_le_max (a:=Ld) (b:=Lc)]
  have hu : min Ud Uc-mesh ≤ max Ud Uc := by linarith [min_le_max (a:=Ud) (b:=Uc)]
  exact ⟨clipped_packet_width hl (le_of_eq (lowerPacket_width mesh Ld Lc)),
    clipped_packet_width hu (le_of_eq (upperPacket_width mesh Ud Uc))⟩

theorem point_in_clipped_packets {mesh t Ld Lc Ud Uc : ℝ} (hm : 0 ≤ mesh) (ht : (1/2:ℝ) ≤ t)
    (h : t ∈ lowerPacket mesh Ld Lc ∪ upperPacket mesh Ud Uc) :
    t ∈ Icc (lowerA Ld Lc) (lowerB mesh Ld Lc) ∪ Icc (upperA mesh Ud Uc) (upperB Ud Uc) := by
  rcases h with h | h
  · exact Or.inl (clipPacket (show min Ld Lc ≤ max Ld Lc+mesh by linarith [min_le_max (a:=Ld) (b:=Lc)]) ht h).1
  · exact Or.inr (clipPacket (show min Ud Uc-mesh ≤ max Ud Uc by linarith [min_le_max (a:=Ud) (b:=Uc)]) ht h).1

theorem prime_bad_cell_packets (h : History w ell S start) (hell : 0 < ell)
    (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)
    {mesh : ℝ} (hm : 0 < mesh) (Lc Uc : ℝ) :
    let Ld := minRatio h.node.side h.node.ratio
    let Ud := upperSupport S ell h.node.gap
    chain w ell S start (some h) (primeBadCells mesh Ld Lc Ud Uc) ≤
      chain w ell S start (some h) (closedLiveBin (lowerA Ld Lc) (lowerB mesh Ld Lc))+
      chain w ell S start (some h) (closedLiveBin (upperA mesh Ud Uc) (upperB Ud Uc)) := by
  dsimp only
  have hvalid := terminal_valid hs h.admissible
  have hgap := terminal_gap_positive hell.le hr hs h.admissible
  apply le_trans (measure_mono_ae ?_) (measure_union_le _ _)
  filter_upwards [prime_row_interval h hell hgap hvalid] with k hk
  intro hbad
  cases k with
  | none => exact False.elim hbad
  | some k =>
    have hhalf : (1/2:ℝ) ≤ k.node.ratio := PrimeTiltBounds.valid_ge_half (terminal_valid hs k.admissible)
    have hS := terminal_ratio_le hsS k.admissible
    have hp := noninterior_in_packets hm (by linarith : 0 ≤ k.node.ratio) hS (Or.inl hk) hbad
    exact point_in_clipped_packets hm.le hhalf hp

theorem continuous_bad_cell_packets (v : ℝ) (z : CostState) (hell : 0 < ell)
    {mesh : ℝ} (hm : 0 < mesh) (Ld Ud : ℝ) :
    let Lc := minRatio (stateSide z.1) (stateRatio z.1)
    let Uc := upperSupport S ell (gapValue v z)
    continuousChain v ell S (.inl z) (continuousBadCells S mesh Ld Lc Ud Uc) ≤
      continuousChain v ell S (.inl z) (Sum.inl '' closedCostBin (lowerA Ld Lc) (lowerB mesh Ld Lc))+
      continuousChain v ell S (.inl z) (Sum.inl '' closedCostBin (upperA mesh Ud Uc) (upperB Ud Uc)) := by
  dsimp only
  apply le_trans (measure_mono_ae ?_) (measure_union_le _ _)
  filter_upwards [continuous_row_interval v S hell z,continuous_supported v ell S (.inl z)] with y hy hS
  intro hbad
  cases y with
  | inr u => exact False.elim hbad
  | inl y =>
    have hhalf := CostPrefixTransport.stateRatio_ge_half y.1
    have hp := noninterior_in_packets hm (by linarith : 0 ≤ stateRatio y.1) hS (Or.inr hy) hbad
    rcases point_in_clipped_packets hm.le hhalf hp with hp | hp
    · exact Or.inl (Set.mem_image_of_mem Sum.inl hp)
    · exact Or.inr (Set.mem_image_of_mem Sum.inl hp)

end NumberTheoryLean.CoupledBoundaryEvents

end

section


namespace NumberTheoryLean.CouplingLabelEvents

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open MeshRatioLabels MeshBoundaryGeometry ActualProcessCoupling ActualCouplingSupport
open CoupledBoundaryEvents KernelBinConditioning FiniteLabelBudget ContinuousKilledBins

variable {w ell S : ℝ} {start : Node}

theorem prime_boundary_event {mesh : ℝ} (hm : 0 < mesh)
    (hsS : start.ratio ≤ S) (Ld Lc Ud Uc : ℝ) :
    (primeLabel w ell S mesh start) ⁻¹' (boundaryLabels S mesh Ld Lc Ud Uc : Set (Label S mesh)) =
      primeBadCells mesh Ld Lc Ud Uc := by
  classical
  ext p
  cases p with
  | none =>
    change cemeteryLabel S mesh ∈ boundaryLabels S mesh Ld Lc Ud Uc ↔ False
    simp [boundaryLabels]
  | some h =>
    have hne : ratioLabel S mesh h.node.ratio ≠ cemeteryLabel S mesh := ratioLabel_ne_cemetery hm (terminal_ratio_le hsS h.admissible)
    change ratioLabel S mesh h.node.ratio ∈ boundaryLabels S mesh Ld Lc Ud Uc ↔ ¬fullCell Ld Lc Ud Uc (ratioLabel S mesh h.node.ratio)
    simp [boundaryLabels,hne]

theorem continuous_boundary_event_mass (v ell S : ℝ) {mesh : ℝ} (hm : 0 < mesh)
    (z : CostState) (Ld Lc Ud Uc : ℝ) :
    continuousChain v ell S (.inl z)
      ((continuousLabel S mesh) ⁻¹' (boundaryLabels S mesh Ld Lc Ud Uc : Set (Label S mesh))) =
      continuousChain v ell S (.inl z) (continuousBadCells S mesh Ld Lc Ud Uc) := by
  classical
  apply measure_congr
  filter_upwards [continuous_supported v ell S (.inl z)] with y hy
  apply propext
  cases y with
  | inr u =>
    change cemeteryLabel S mesh ∈ boundaryLabels S mesh Ld Lc Ud Uc ↔ False
    simp [boundaryLabels]
  | inl y =>
    have hne := ratioLabel_ne_cemetery hm hy
    change ratioLabel S mesh (stateRatio y.1) ∈ boundaryLabels S mesh Ld Lc Ud Uc ↔ ¬fullCell Ld Lc Ud Uc (ratioLabel S mesh (stateRatio y.1))
    simp [boundaryLabels,hne]

theorem prime_boundary_mass [IsMarkovKernel (chain w ell S start)] {mesh : ℝ} (hm : 0 < mesh)
    (hsS : start.ratio ≤ S)
    (h : History w ell S start) (Ld Lc Ud Uc : ℝ) :
    (∑ j ∈ boundaryLabels S mesh Ld Lc Ud Uc,labelMass (chain w ell S start) (primeLabel w ell S mesh start) (some h) j) =
      (chain w ell S start (some h) (primeBadCells mesh Ld Lc Ud Uc)).toReal := by
  rw [selected_label_mass _ (primeLabel_measurable w ell S mesh start),prime_boundary_event hm hsS]

theorem continuous_boundary_mass (v ell S : ℝ) {mesh : ℝ} (hm : 0 < mesh)
    (z : CostState) (Ld Lc Ud Uc : ℝ) :
    (∑ j ∈ boundaryLabels S mesh Ld Lc Ud Uc,labelMass (continuousChain v ell S) (continuousLabel S mesh) (.inl z) j) =
      (continuousChain v ell S (.inl z) (continuousBadCells S mesh Ld Lc Ud Uc)).toReal := by
  rw [selected_label_mass _ (continuousLabel_measurable S mesh),continuous_boundary_event_mass v ell S hm z]

theorem actual_label_budget (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell)
    (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
    (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)
    (h : History w ell S start) (v : ℝ) (z : CostState) {mesh : ℝ} (hm : 0 < mesh)
    (Ld Lc Ud Uc : ℝ) :
    (∑ j : Label S mesh, |labelMass (chain w ell S start) (primeLabel w ell S mesh start) (some h) j-
      labelMass (continuousChain v ell S) (continuousLabel S mesh) (.inl z) j|) ≤
      2*((∑ j ∈ interiorLabels S mesh Ld Lc Ud Uc,
        |labelMass (chain w ell S start) (primeLabel w ell S mesh start) (some h) j-
          labelMass (continuousChain v ell S) (continuousLabel S mesh) (.inl z) j|)+
        (chain w ell S start (some h) (primeBadCells mesh Ld Lc Ud Uc)).toReal+
        (continuousChain v ell S (.inl z) (continuousBadCells S mesh Ld Lc Ud Uc)).toReal) := by
  classical
  let := chain_isMarkov hw hell hS0 hS hr hs hsS
  let a := labelMass (chain w ell S start) (primeLabel w ell S mesh start) (some h)
  let b := labelMass (continuousChain v ell S) (continuousLabel S mesh) (.inl z)
  let good := fullCell (S:=S) (mesh:=mesh) Ld Lc Ud Uc
  have hbudget := interior_boundary_budget a b (cemeteryLabel S mesh) good
    (labelMass_nonneg (chain w ell S start) (primeLabel w ell S mesh start) (some h))
    (labelMass_nonneg (continuousChain v ell S) (continuousLabel S mesh) (.inl z))
    (labelMass_sum (chain w ell S start) (primeLabel_measurable w ell S mesh start) (some h))
    (labelMass_sum (continuousChain v ell S) (continuousLabel_measurable S mesh) (.inl z))
  have hsub : (Finset.univ.erase (cemeteryLabel S mesh)).filter good ⊆ interiorLabels S mesh Ld Lc Ud Uc := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hj).2⟩
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => abs_nonneg (a j-b j))
  change (∑ j,|a j-b j|) ≤ _
  have hbad : (∑ j ∈ (Finset.univ.erase (cemeteryLabel S mesh)).filter (fun j => ¬good j),(a j+b j)) =
      (chain w ell S start (some h) (primeBadCells mesh Ld Lc Ud Uc)).toReal+
      (continuousChain v ell S (.inl z) (continuousBadCells S mesh Ld Lc Ud Uc)).toReal := by
    rw [Finset.sum_add_distrib]
    exact congrArg₂ (·+·) (prime_boundary_mass hm hsS h Ld Lc Ud Uc)
      (continuous_boundary_mass v ell S hm z Ld Lc Ud Uc)
  rw [hbad] at hbudget
  linarith

end NumberTheoryLean.CouplingLabelEvents

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_CoupledBoundaryBounds
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.CoupledBoundaryBounds

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualSupportIntervals CoupledBoundaryEvents PrimeCompletedIntervalUpper
open ContinuousIntervalUpper RegeneratingInverseBands ContinuousKilledBins

theorem prime_bad_cells_upper : ∃ c C w₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ ell S : ℝ, ∀ start : Node,
      1 ≤ ell → 0 < start.gap → Valid start.side start.ratio → start.ratio ≤ S →
      ∀ h : History w ell S start, ∀ mesh Lc Uc : ℝ, 0 < mesh →
      let Ld := minRatio h.node.side h.node.ratio
      let Ud := upperSupport S ell h.node.gap
      |Ld-Lc|+mesh ≤ 1 → |Ud-Uc|+mesh ≤ 1 →
      chain w ell S start (some h) (primeBadCells mesh Ld Lc Ud Uc) ≤
        ENNReal.ofReal (C*(1+S)^2*(|Ld-Lc|+|Ud-Uc|+2*mesh+
          2*Real.exp (-c*Real.sqrt ((1/2:ℝ)*Real.log w)))) := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,hbound⟩ := prime_completed_interval_upper
  refine ⟨c,C,w₀,hc,hC,hw₀,?_⟩
  intro w hw ell S start hell hr hs hsS h mesh Lc Uc hm
  dsimp only
  intro hL hU
  let Ld := minRatio h.node.side h.node.ratio
  let Ud := upperSupport S ell h.node.gap
  let e := Real.exp (-c*Real.sqrt ((1/2:ℝ)*Real.log w))
  have hwid := packet_widths hm.le Ld Lc Ud Uc
  have hleft := hbound w hw ell S start hell hr hs hsS h (lowerA Ld Lc) (lowerB mesh Ld Lc)
    hwid.1.1 hwid.1.2.1 (hwid.1.2.2.trans hL)
  have hright := hbound w hw ell S start hell hr hs hsS h (upperA mesh Ud Uc) (upperB Ud Uc)
    hwid.2.1 hwid.2.2.1 (hwid.2.2.2.trans hU)
  have hM : 0 ≤ C*(1+S)^2 := by positivity
  have he : 0 ≤ e := (Real.exp_pos _).le
  calc
    _ ≤ chain w ell S start (some h) (closedLiveBin (lowerA Ld Lc) (lowerB mesh Ld Lc))+
        chain w ell S start (some h) (closedLiveBin (upperA mesh Ud Uc) (upperB Ud Uc)) :=
      prime_bad_cell_packets h (by linarith) hr hs hsS hm Lc Uc
    _ ≤ ENNReal.ofReal (C*(1+S)^2*(lowerB mesh Ld Lc-lowerA Ld Lc+e))+
        ENNReal.ofReal (C*(1+S)^2*(upperB Ud Uc-upperA mesh Ud Uc+e)) := add_le_add hleft hright
    _ = ENNReal.ofReal (C*(1+S)^2*((lowerB mesh Ld Lc-lowerA Ld Lc)+
        (upperB Ud Uc-upperA mesh Ud Uc)+2*e)) := by
      rw [← ENNReal.ofReal_add (mul_nonneg hM (by linarith [hwid.1.2.1]))
        (mul_nonneg hM (by linarith [hwid.2.2.1]))]
      congr 1
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (by linarith [hwid.1.2.2,hwid.2.2.2]) hM)

theorem continuous_bad_cells_upper : ∃ C : ℝ, 0 < C ∧ ∀ v ell S : ℝ, ∀ z : CostState,
    0 < ell → stateRatio z.1 ≤ S → ∀ mesh Ld Ud : ℝ, 0 < mesh →
      let Lc := minRatio (stateSide z.1) (stateRatio z.1)
      let Uc := upperSupport S ell (gapValue v z)
      continuousChain v ell S (.inl z) (continuousBadCells S mesh Ld Lc Ud Uc) ≤
        ENNReal.ofReal (C*(1+S)^2*(|Ld-Lc|+|Ud-Uc|+2*mesh)) := by
  obtain ⟨C,hC,hbound⟩ := completed_interval_upper
  refine ⟨C,hC,?_⟩
  intro v ell S z hell hsS mesh Ld Ud hm
  dsimp only
  let Lc := minRatio (stateSide z.1) (stateRatio z.1)
  let Uc := upperSupport S ell (gapValue v z)
  have hwid := packet_widths hm.le Ld Lc Ud Uc
  have hleft := hbound v ell S (lowerA Ld Lc) (lowerB mesh Ld Lc) z hsS
  have hright := hbound v ell S (upperA mesh Ud Uc) (upperB Ud Uc) z hsS
  have hM : 0 ≤ C*(1+S)^2 := by positivity
  rw [← ENNReal.ofReal_mul hM] at hleft hright
  calc
    _ ≤ continuousChain v ell S (.inl z) (Sum.inl '' closedCostBin (lowerA Ld Lc) (lowerB mesh Ld Lc))+
        continuousChain v ell S (.inl z) (Sum.inl '' closedCostBin (upperA mesh Ud Uc) (upperB Ud Uc)) :=
      continuous_bad_cell_packets v z hell hm Ld Ud
    _ ≤ ENNReal.ofReal (C*(1+S)^2*(lowerB mesh Ld Lc-lowerA Ld Lc))+
        ENNReal.ofReal (C*(1+S)^2*(upperB Ud Uc-upperA mesh Ud Uc)) := add_le_add hleft hright
    _ = ENNReal.ofReal (C*(1+S)^2*((lowerB mesh Ld Lc-lowerA Ld Lc)+
        (upperB Ud Uc-upperA mesh Ud Uc))) := by
      rw [← ENNReal.ofReal_add (mul_nonneg hM (sub_nonneg.mpr hwid.1.2.1))
        (mul_nonneg hM (sub_nonneg.mpr hwid.2.2.1))]
      congr 1
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (by linarith [hwid.1.2.2,hwid.2.2.2]) hM)

end NumberTheoryLean.CoupledBoundaryBounds


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_AllLabelDiscrepancy
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.AllLabelDiscrepancy

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open MeshRatioLabels MeshBoundaryGeometry ActualSupportIntervals ActualProcessCoupling
open ContinuousKilledBins PrimeBinMembership RegeneratingInverseBands KernelBinConditioning
open CommonCellSum CouplingLabelEvents CoupledBoundaryEvents CoupledBoundaryBounds

theorem all_label_discrepancy : ∃ c₁ c₂ C₁ C₂ C₃ D w₀ : ℝ,
    0 < c₁ ∧ 0 < c₂ ∧ 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧ 0 < D ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ ell S : ℝ, ∀ start : Node, ∀ h : History w ell S start,
    ∀ v : ℝ, ∀ z : CostState, ∀ mesh : ℝ,
      normalizationThreshold ≤ w → 1 ≤ ell → 3 ≤ S → S ≤ (Real.log w)^3 →
      0 < start.gap → Valid start.side start.ratio → start.ratio ≤ S → Consistent start →
      stateRatio z.1 ≤ S → h.node.side = stateSide z.1 → 0 < mesh →
      let Ld := minRatio h.node.side h.node.ratio
      let Lc := minRatio (stateSide z.1) (stateRatio z.1)
      let Ud := upperSupport S ell h.node.gap
      let Uc := upperSupport S ell (gapValue v z)
      |Ld-Lc|+mesh ≤ 1 → |Ud-Uc|+mesh ≤ 1 →
      (∑ j : Label S mesh, |labelMass (chain w ell S start) (primeLabel w ell S mesh start) (some h) j-
        labelMass (continuousChain v ell S) (continuousLabel S mesh) (.inl z) j|) ≤
      2*((S/mesh+2)*(C₁*(1+S)^5*(mesh^2+Real.exp (-c₁*Real.sqrt ((1/2:ℝ)*Real.log w))))+
        epsilon w+(Real.exp (D*(1+S)^3*|h.node.ratio-stateRatio z.1|)-1)+
        C₂*(1+S)^2*(|Ld-Lc|+|Ud-Uc|+2*mesh+2*Real.exp (-c₂*Real.sqrt ((1/2:ℝ)*Real.log w)))+
        C₃*(1+S)^2*(|Ld-Lc|+|Ud-Uc|+2*mesh)) := by
  classical
  obtain ⟨c₁,C₁,D,w₁,hc₁,hC₁,hD,hw₁,hcommon⟩ := common_cell_sum_error
  obtain ⟨c₂,C₂,w₂,hc₂,hC₂,hw₂,hprime⟩ := prime_bad_cells_upper
  obtain ⟨C₃,hC₃,hcontinuous⟩ := continuous_bad_cells_upper
  refine ⟨c₁,c₂,C₁,C₂,C₃,D,max w₁ w₂,hc₁,hc₂,hC₁,hC₂,hC₃,hD,
    hw₁.trans_le (le_max_left _ _),?_⟩
  intro w hw ell S start h v z mesh hnorm hell hS3 hS hr hs hsS hcons hzS hside hm
  dsimp only
  intro hL hU
  let Ld := minRatio h.node.side h.node.ratio
  let Lc := minRatio (stateSide z.1) (stateRatio z.1)
  let Ud := upperSupport S ell h.node.gap
  let Uc := upperSupport S ell (gapValue v z)
  let I := interiorLabels S mesh Ld Lc Ud Uc
  let δ := |Ld-Lc|+|Ud-Uc|+2*mesh
  let Bp := C₂*(1+S)^2*(δ+2*Real.exp (-c₂*Real.sqrt ((1/2:ℝ)*Real.log w)))
  let Bc := C₃*(1+S)^2*δ
  have hδ : 0 ≤ δ := by dsimp [δ] <;> positivity
  have hBp : 0 ≤ Bp := by dsimp [Bp] <;> positivity
  have hBc : 0 ≤ Bc := by dsimp [Bc] <;> positivity
  have hi := hcommon w ((le_max_left _ _).trans hw) ell S start h v z mesh I
    hell hS3 hr hs hsS hcons hzS hside hm (fun j hj => (Finset.mem_filter.mp hj).2)
  have hp := hprime w ((le_max_right _ _).trans hw) ell S start hell hr hs hsS h mesh Lc Uc hm hL hU
  have hc := hcontinuous v ell S z (by linarith) hzS mesh Ld Ud hm
  have hpR : (chain w ell S start (some h) (primeBadCells mesh Ld Lc Ud Uc)).toReal ≤ Bp := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hp
    rwa [ENNReal.toReal_ofReal hBp] at h
  have hcR : (continuousChain v ell S (.inl z) (continuousBadCells S mesh Ld Lc Ud Uc)).toReal ≤ Bc := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hc
    rwa [ENNReal.toReal_ofReal hBc] at h
  have hb := actual_label_budget hnorm hell (by linarith) hS hr hs hsS h v z hm Ld Lc Ud Uc
  change (∑ j,_) ≤ _ at hb
  dsimp only [I,Bp,Bc,δ,Ld,Lc,Ud,Uc] at hi hpR hcR hb
  linarith

end NumberTheoryLean.AllLabelDiscrepancy


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_ActualCouplingError
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.ActualCouplingError

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open MeshRatioLabels ActualSupportIntervals ActualProcessCoupling
open PrimeBinMembership RegeneratingInverseBands AllLabelDiscrepancy

theorem actual_one_step_failure : ∃ c₁ c₂ C₁ C₂ C₃ D w₀ : ℝ,
    0 < c₁ ∧ 0 < c₂ ∧ 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧ 0 < D ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ ell S : ℝ, ∀ start : Node, ∀ h : History w ell S start,
    ∀ v : ℝ, ∀ z : CostState, ∀ mesh : ℝ,
      ∀ (hnorm : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS3 : 3 ≤ S) (hS : S ≤ (Real.log w)^3)
        (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S), Consistent start →
      stateRatio z.1 ≤ S → h.node.side = stateSide z.1 → 0 < mesh →
      let Ld := minRatio h.node.side h.node.ratio
      let Lc := minRatio (stateSide z.1) (stateRatio z.1)
      let Ud := upperSupport S ell h.node.gap
      let Uc := upperSupport S ell (gapValue v z)
      |Ld-Lc|+mesh ≤ 1 → |Ud-Uc|+mesh ≤ 1 →
      jointKernel hnorm hell (show 0 ≤ S from (by linarith)) hS hr hs hsS v mesh (some h,.inl z)
        {q | primeLabel w ell S mesh start q.1 ≠ continuousLabel S mesh q.2} ≤
      ENNReal.ofReal (2*((S/mesh+2)*(C₁*(1+S)^5*(mesh^2+Real.exp (-c₁*Real.sqrt ((1/2:ℝ)*Real.log w))))+
        epsilon w+(Real.exp (D*(1+S)^3*|h.node.ratio-stateRatio z.1|)-1)+
        C₂*(1+S)^2*(|Ld-Lc|+|Ud-Uc|+2*mesh+2*Real.exp (-c₂*Real.sqrt ((1/2:ℝ)*Real.log w)))+
        C₃*(1+S)^2*(|Ld-Lc|+|Ud-Uc|+2*mesh))) := by
  obtain ⟨c₁,c₂,C₁,C₂,C₃,D,w₀,hc₁,hc₂,hC₁,hC₂,hC₃,hD,hw₀,hbound⟩ := all_label_discrepancy
  refine ⟨c₁,c₂,C₁,C₂,C₃,D,w₀,hc₁,hc₂,hC₁,hC₂,hC₃,hD,hw₀,?_⟩
  intro w hw ell S start h v z mesh hnorm hell hS3 hS hr hs hsS hcons hzS hside hm
  dsimp only
  intro hL hU
  exact (jointKernel_mismatch_bound hnorm hell (by linarith) hS hr hs hsS v mesh (some h) (.inl z)).trans
    (ENNReal.ofReal_le_ofReal (hbound w hw ell S start h v z mesh hnorm hell hS3 hS hr hs hsS hcons hzS hside hm hL hU))

end NumberTheoryLean.ActualCouplingError


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

theorem failed_measurable : MeasurableSet (failed (α:=α)) :=
  measurable_snd (measurableSet_singleton true)

theorem marked_failed_true (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (x : α) : marked K hBad (x,true) failed = 1 := by
  rw [marked_apply K hBad (x,true) failed_measurable]
  simp [failed]

theorem marked_failed_false (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (x : α) : marked K hBad (x,false) failed = K x {y | Bad y} := by
  classical
  rw [marked_apply K hBad (x,false) failed_measurable]
  congr 1
  ext y
  simp [failed,badBit]

instance marked_pow_markov (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (n : ℕ) : IsMarkovKernel ((marked K hBad)^n) := by
  induction n with
  | zero => change IsMarkovKernel (Kernel.id : Kernel (FlagState α) (FlagState α)); infer_instance
  | succ n ih =>
    let := ih
    have hp : (marked K hBad)^(n+1) = (marked K hBad) ∘ₖ ((marked K hBad)^n) := pow_succ' _ _
    rw [hp]
    first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply update_measurable <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance law_probability (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (x : α) (n : ℕ) : IsProbabilityMeasure (law K hBad x n) := by
  unfold law
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end NumberTheoryLean.PersistentFailureFlag



namespace NumberTheoryLean.FailureFlagBounds

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open PersistentFailureFlag

variable {α : Type*} [MeasurableSpace α]

theorem surviving_measurable {Good : α → Prop} (hGood : MeasurableSet {x | Good x}) :
    MeasurableSet {z | surviving Good z} :=
  (measurable_snd (measurableSet_singleton false)).imp (measurable_fst hGood)

theorem surviving_step (K : Kernel α α) [IsMarkovKernel K] {Bad P Q : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (hQ : MeasurableSet {x | Q x})
    (hstep : ∀ x,P x → ∀ᵐ y ∂K x, ¬Bad y → Q y) (z : FlagState α) (hz : surviving P z) :
    ∀ᵐ y ∂marked K hBad z, surviving Q y := by
  classical
  rw [marked_eq_map K hBad z]
  apply (ae_map_iff (row_update_measurable hBad z.2).aemeasurable (surviving_measurable hQ)).mpr
  rcases z with ⟨x,b⟩
  cases b with
  | false =>
    filter_upwards [hstep x (hz rfl)] with y hy
    intro hf
    apply hy
    simpa [badBit] using hf
  | true =>
    exact Eventually.of_forall (fun y => by
      intro hf
      have hf' : (true || badBit Bad y) = false := hf
      simp at hf')

theorem law_survives (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (Good : ℕ → α → Prop)
    (hGood : ∀ n,MeasurableSet {x | Good n x})
    (hstep : ∀ n x,Good n x → ∀ᵐ y ∂K x, ¬Bad y → Good (n+1) y)
    (x : α) (hx : Good 0 x) (n : ℕ) :
    ∀ᵐ z ∂law K hBad x n, surviving (Good n) z := by
  induction n with
  | zero =>
    change ∀ᵐ z ∂Measure.dirac (x,false), surviving (Good 0) z
    exact (ae_dirac_iff (surviving_measurable (hGood 0))).mpr (fun _ => hx)
  | succ n ih =>
    have hp : (marked K hBad)^(n+1) = (marked K hBad) ∘ₖ ((marked K hBad)^n) := pow_succ' _ _
    change ∀ᵐ z ∂((marked K hBad)^(n+1)) (x,false), surviving (Good (n+1)) z
    rw [hp]
    apply Kernel.ae_comp_of_ae_ae (surviving_measurable (hGood (n+1)))
    filter_upwards [ih] with z hz
    exact surviving_step K hBad (hGood (n+1)) (hstep n) z hz

theorem marked_failure_row_bound (K : Kernel α α) [IsMarkovKernel K] {Bad Good : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (η : ℝ≥0∞)
    (hrow : ∀ x,Good x → K x {y | Bad y} ≤ η) (z : FlagState α) (hz : surviving Good z) :
    marked K hBad z failed ≤ failed.indicator (fun _ => (1:ℝ≥0∞)) z+η := by
  classical
  rcases z with ⟨x,b⟩
  cases b with
  | false =>
    rw [marked_failed_false,indicator_of_notMem (show (x,false) ∉ (failed:Set (FlagState α)) by change ¬(false=true); decide),zero_add]
    exact hrow x (hz rfl)
  | true =>
    rw [marked_failed_true,indicator_of_mem (show (x,true) ∈ (failed:Set (FlagState α)) from rfl)]
    exact le_add_of_nonneg_right zero_le

theorem law_failure_step (K : Kernel α α) [IsMarkovKernel K] {Bad Good : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (x : α) (n : ℕ) (η : ℝ≥0∞)
    (hgood : ∀ᵐ z ∂law K hBad x n, surviving Good z)
    (hrow : ∀ y,Good y → K y {z | Bad z} ≤ η) :
    law K hBad x (n+1) failed ≤ law K hBad x n failed+η := by
  have hp : (marked K hBad)^(n+1) = (marked K hBad) ∘ₖ ((marked K hBad)^n) := pow_succ' _ _
  calc
    _ = ∫⁻ z,marked K hBad z failed ∂law K hBad x n := by
      change ((marked K hBad)^(n+1)) (x,false) failed = _
      rw [hp,Kernel.comp_apply' _ _ _ failed_measurable]
      rfl
    _ ≤ ∫⁻ z,(failed.indicator (fun _ => (1:ℝ≥0∞)) z+η) ∂law K hBad x n := by
      apply lintegral_mono_ae
      filter_upwards [hgood] with z hz
      exact marked_failure_row_bound K hBad η hrow z hz
    _ = _ := by
      rw [lintegral_add_left (measurable_const.indicator failed_measurable),
        lintegral_indicator failed_measurable,setLIntegral_const,one_mul,lintegral_const,measure_univ,mul_one]

theorem failure_probability_le (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (Good : ℕ → α → Prop)
    (hGood : ∀ n,MeasurableSet {x | Good n x})
    (hstep : ∀ n x,Good n x → ∀ᵐ y ∂K x, ¬Bad y → Good (n+1) y)
    (x : α) (hx : Good 0 x) (η : ℝ≥0∞) (N : ℕ)
    (hrow : ∀ n < N, ∀ y,Good n y → K y {z | Bad z} ≤ η)
    (n : ℕ) (hn : n ≤ N) : law K hBad x n failed ≤ (n:ℝ≥0∞)*η := by
  classical
  induction n with
  | zero =>
    rw [Nat.cast_zero,zero_mul]
    change Measure.dirac (x,false) failed ≤ 0
    rw [Measure.dirac_apply' _ failed_measurable]
    change (if (x,false) ∈ (failed:Set (FlagState α)) then 1 else 0) ≤ 0
    simp [failed]
  | succ n ih =>
    calc
      _ ≤ law K hBad x n failed+η := law_failure_step K hBad x n η
        (law_survives K hBad Good hGood hstep x hx n) (hrow n (by omega))
      _ ≤ (n:ℝ≥0∞)*η+η := add_le_add (ih (by omega)) le_rfl
      _ = _ := by rw [Nat.cast_add,Nat.cast_one,add_mul,one_mul]

end NumberTheoryLean.FailureFlagBounds



namespace NumberTheoryLean.ActualFlagInvariant

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ActualCouplingSupport ActualCouplingUpdates ActualCouplingFinite
open PersistentFailureFlag FailureFlagBounds RegeneratingInverseBands ArrivalKernelGeometry

variable {w ell S : ℝ} {start : Node}

theorem liveGood_measurable (v mesh : ℝ) (n : ℕ) (h : History w ell S start) :
    MeasurableSet {z | liveGood v mesh n h z} := by
  have hside : MeasurableSet {z : CostState | h.node.side = stateSide z.1} := by
    have heq : {z : CostState | h.node.side = stateSide z.1} = {z : CostState | stateSide z.1 = h.node.side} := by
      ext z
      exact eq_comm
    rw [heq]
    exact measurable_fst (side_set_measurable h.node.side)
  exact (measurableSet_le (stateRatio_measurable.comp measurable_fst) measurable_const).inter
    (hside.inter ((measurableSet_le
      (measurable_const.sub (stateRatio_measurable.comp measurable_fst)).abs measurable_const).inter
      (measurableSet_le (measurable_const.sub (Real.measurable_log.comp (gapValue_measurable v))).abs measurable_const)))

theorem GoodAt_measurable (v mesh : ℝ) (n : ℕ) :
    MeasurableSet {q : JointState w ell S start | GoodAt v mesh n q} := by
  apply Measurable.setOf
  apply measurable_from_prod_countable_right
  intro p
  cases p with
  | none => exact measurable_const.sumElim measurable_const
  | some h => exact (measurableSet_setOfPred.mp (liveGood_measurable v mesh n h)).sumElim measurable_const

variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
variable (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem joint_dead_ae (v mesh : ℝ) :
    ∀ᵐ q ∂jointKernel hw hell hS0 hS hr hs hsS v mesh (none,CemeteryKernel.dead),
      q = (none,CemeteryKernel.dead) := by
  have hL : ∀ᵐ p ∂(jointKernel hw hell hS0 hS hr hs hsS v mesh (none,CemeteryKernel.dead)).map Prod.fst, p = none := by
    rw [jointKernel_left hw hell hS0 hS hr hs hsS,chain_none]
    exact (ae_dirac_iff (measurableSet_singleton _)).mpr rfl
  have hdead : MeasurableSet {y : CemeteryKernel.Space CostState | y = CemeteryKernel.dead} := by
    apply measurableSet_sum_iff.mpr
    constructor
    · have hp : (Sum.inl : CostState → CemeteryKernel.Space CostState) ⁻¹' {y | y = CemeteryKernel.dead} = ∅ := by
        ext x
        change ((Sum.inl x : CemeteryKernel.Space CostState) = Sum.inr ()) ↔ False
        simp
      rw [hp]
      exact MeasurableSet.empty
    · simp [CemeteryKernel.dead]
  have hR : ∀ᵐ y ∂(jointKernel hw hell hS0 hS hr hs hsS v mesh (none,CemeteryKernel.dead)).map Prod.snd,
      y = CemeteryKernel.dead := by
    rw [jointKernel_right hw hell hS0 hS hr hs hsS]
    change ∀ᵐ y ∂Measure.dirac (CemeteryKernel.dead : CemeteryKernel.Space CostState), y = CemeteryKernel.dead
    exact (ae_dirac_iff hdead).mpr rfl
  have hl := (ae_map_iff measurable_fst.aemeasurable (measurableSet_singleton _)).mp hL
  have hr' := (ae_map_iff measurable_snd.aemeasurable hdead).mp hR
  filter_upwards [hl,hr'] with q hq hq'
  exact Prod.ext hq hq'

theorem actual_good_step (v : ℝ) {mesh : ℝ} (hm : 0 < mesh) (n : ℕ)
    (q : JointState w ell S start) (hq : GoodAt v mesh n q) :
    ∀ᵐ y ∂jointKernel hw hell hS0 hS hr hs hsS v mesh q,
      ¬mismatch mesh y → GoodAt v mesh (n+1) y := by
  rcases q with ⟨p,z⟩
  cases p with
  | none =>
    cases z with
    | inl z => exact False.elim hq
    | inr u =>
      cases u
      filter_upwards [joint_dead_ae hw hell hS0 hS hr hs hsS v mesh] with y hy
      intro _
      rw [hy]
      trivial
  | some h =>
    cases z with
    | inr u => exact False.elim hq
    | inl z =>
      filter_upwards [joint_follows hw hell hS0 hS hr hs hsS v mesh h z,
        joint_matching_control hw hell hS0 hS hr hs hsS v hm (some h) (.inl z),
        joint_continuous_supported hw hell hS0 hS hr hs hsS v mesh (some h) (.inl z)] with y hy hmatch hSup
      intro hnot
      have heq : primeLabel w ell S mesh start y.1 = continuousLabel S mesh y.2 := not_ne_iff.mp hnot
      have hmout := hmatch heq
      rcases y with ⟨p,y⟩
      cases p with
      | none =>
        cases y with
        | inl y => exact False.elim hmout
        | inr u => trivial
      | some k =>
        cases y with
        | inr u => exact False.elim hmout
        | inl y =>
          have hup := matched_live_update hell hr hs h k z y hy.1 hy.2 hq.2.1 hq.2.2.2
            (show |k.node.ratio-stateRatio y.1| ≤ mesh from hmout.le)
          refine ⟨hSup,hup.1,hmout.le,?_⟩
          have he : 4*(n:ℝ)*mesh+4*mesh = 4*((n+1:ℕ):ℝ)*mesh := by push_cast <;> ring
          exact hup.2.trans_eq he

end NumberTheoryLean.ActualFlagInvariant



namespace NumberTheoryLean.FlaggedSourceStart

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ActualCouplingFinite ActualFlagInvariant PersistentFailureFlag
open RegeneratingInverseBands ContinuousKilledBins

theorem typedState_side (i : Side) (s : ℝ) (hs : Valid i s) : stateSide (typedState i s hs) = i := by
  cases i <;> rfl

theorem typedState_ratio (i : Side) (s : ℝ) (hs : Valid i s) : stateRatio (typedState i s hs) = s := by
  cases i <;> rfl

variable {w ell S : ℝ} {start : Node}

theorem source_good {mesh : ℝ} (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S) (hm : 0 ≤ mesh) :
    GoodAt (Real.log start.gap) mesh 0 (sourceJoint w ell S start hs) := by
  change liveGood (Real.log start.gap) mesh 0 History.empty (sourceCostState hs)
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [sourceCostState,typedState_ratio] using hsS
  · change start.side = stateSide (typedState start.side start.ratio hs)
    exact (typedState_side _ _ _).symm
  · change |start.ratio-stateRatio (typedState start.side start.ratio hs)| ≤ mesh
    rw [typedState_ratio,sub_self,abs_zero]
    exact hm
  · rw [Nat.cast_zero,mul_zero,zero_mul]
    change |Real.log start.gap-Real.log (gapValue (Real.log start.gap) (sourceCostState hs))| ≤ 0
    simp [gapValue,sourceCostState]

variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
variable (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

instance sourceLaw_probability (mesh : ℝ) (n : ℕ) :
    IsProbabilityMeasure (sourceLaw hw hell hS0 hS hr hs hsS mesh n) := by
  unfold sourceLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end NumberTheoryLean.FlaggedSourceStart


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_UniformFailureBudget
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.UniformFailureBudget

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ActualFlagInvariant ActualCouplingUpdates ActualCouplingError
open NearbyParentGeometry ActualSupportIntervals PrimeBinMembership RegeneratingInverseBands

theorem uniform_actual_bad_row : ∃ c₁ c₂ C₁ C₂ C₃ D w₀ : ℝ,
    0 < c₁ ∧ 0 < c₂ ∧ 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧ 0 < D ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ ell S : ℝ, ∀ start : Node, ∀ v mesh : ℝ, ∀ N : ℕ,
      ∀ (hnorm : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS3 : 3 ≤ S) (hS : S ≤ (Real.log w)^3)
        (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S),
      Consistent start → 0 < mesh → 2*mesh ≤ 1 → upperDisplacement S mesh N+mesh ≤ 1 →
      ∀ n ≤ N, ∀ q : JointState w ell S start, GoodAt v mesh n q →
        jointKernel hnorm hell (show 0 ≤ S from by linarith) hS hr hs hsS v mesh q {y | mismatch mesh y} ≤
          ENNReal.ofReal (stepBudget c₁ c₂ C₁ C₂ C₃ D w S mesh N) := by
  obtain ⟨c₁,c₂,C₁,C₂,C₃,D,w₀,hc₁,hc₂,hC₁,hC₂,hC₃,hD,hw₀,hbound⟩ := actual_one_step_failure
  refine ⟨c₁,c₂,C₁,C₂,C₃,D,w₀,hc₁,hc₂,hC₁,hC₂,hC₃,hD,hw₀,?_⟩
  intro w hw ell S start v mesh N hnorm hell hS3 hS hr hs hsS hcons hm hmesh hupper n hn q hq
  have hS1 : 0 ≤ S+1 := by linarith
  rcases q with ⟨p,z⟩
  cases p with
  | none =>
    cases z with
    | inl z => exact False.elim hq
    | inr u =>
      cases u
      have hnot : ∀ᵐ y ∂jointKernel hnorm hell (by linarith) hS hr hs hsS v mesh (none,CemeteryKernel.dead),
          ¬mismatch mesh y := by
        filter_upwards [joint_dead_ae hnorm hell (by linarith) hS hr hs hsS v mesh] with y hy
        rw [hy]
        change ¬(MeshRatioLabels.cemeteryLabel S mesh ≠ MeshRatioLabels.cemeteryLabel S mesh)
        exact not_not.mpr rfl
      have hzero : jointKernel hnorm hell (by linarith) hS hr hs hsS v mesh (none,CemeteryKernel.dead)
          {y | mismatch mesh y} = 0 := by
        simpa only [not_not] using ae_iff.mp hnot
      exact hzero.le.trans zero_le
  | some h =>
    cases z with
    | inr u => exact False.elim hq
    | inl z =>
      have hgap := terminal_gap_positive (show 0 ≤ ell by linarith) hr hs h.admissible
      have hnR : (n:ℝ) ≤ (N:ℝ) := by exact_mod_cast hn
      have hgapN : |Real.log h.node.gap-Real.log (gapValue v z)| ≤ 4*(N:ℝ)*mesh :=
        hq.2.2.2.trans (mul_le_mul_of_nonneg_right (by linarith) hm.le)
      have hdl : |minRatio h.node.side h.node.ratio-minRatio (stateSide z.1) (stateRatio z.1)| ≤ mesh := by
        rw [← hq.2.1]
        exact (minRatio_stability _ _ _).trans hq.2.2.1
      have hdu : |upperSupport S ell h.node.gap-upperSupport S ell (gapValue v z)| ≤ upperDisplacement S mesh N :=
        arrival_endpoint_stability hgap (Real.exp_pos _) (by linarith) hS1 hgapN
      have hp := hbound w hw ell S start h v z mesh hnorm hell hS3 hS hr hs hsS hcons hq.1 hq.2.1 hm
        (by linarith) (by linarith)
      refine hp.trans (ENNReal.ofReal_le_ofReal ?_)
      have hD0 : 0 ≤ D*(1+S)^3 := by positivity
      have hpar := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hq.2.2.1 hD0)
      have hdelta : |minRatio h.node.side h.node.ratio-minRatio (stateSide z.1) (stateRatio z.1)|+
          |upperSupport S ell h.node.gap-upperSupport S ell (gapValue v z)|+2*mesh ≤
          upperDisplacement S mesh N+3*mesh := by linarith
      have h2 := mul_le_mul_of_nonneg_left
        (add_le_add_right hdelta (2*Real.exp (-c₂*Real.sqrt ((1/2:ℝ)*Real.log w))))
        (show 0 ≤ C₂*(1+S)^2 by positivity)
      have h3 := mul_le_mul_of_nonneg_left hdelta (show 0 ≤ C₃*(1+S)^2 by positivity)
      unfold stepBudget
      linarith

end NumberTheoryLean.UniformFailureBudget

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

namespace NumberTheoryLean.ActualFiniteCoupling

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ActualFlagInvariant PersistentFailureFlag FailureFlagBounds
open FlaggedSourceStart UniformFailureBudget PrimeBinMembership LowStateHorizon PrimeChainHorizon

theorem actual_finite_failure_jb247_oai : ∃ c₁ c₂ C₁ C₂ C₃ D w₀ : ℝ,
    0 < c₁ ∧ 0 < c₂ ∧ 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧ 0 < D ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ ell S : ℝ, ∀ start : Node, ∀ mesh : ℝ, ∀ N : ℕ,
      ∀ (hnorm : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS3 : 3 ≤ S) (hS : S ≤ (Real.log w)^3)
        (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S),
      Consistent start → 0 < mesh → 2*mesh ≤ 1 → upperDisplacement S mesh N+mesh ≤ 1 →
      ∀ n ≤ N,
        sourceLaw hnorm hell (show 0 ≤ S from by linarith) hS hr hs hsS mesh n failed ≤
          (n:ℝ≥0∞)*ENNReal.ofReal (stepBudget c₁ c₂ C₁ C₂ C₃ D w S mesh N) := by
  obtain ⟨c₁,c₂,C₁,C₂,C₃,D,w₀,hc₁,hc₂,hC₁,hC₂,hC₃,hD,hw₀,hrow⟩ := uniform_actual_bad_row
  refine ⟨c₁,c₂,C₁,C₂,C₃,D,w₀,hc₁,hc₂,hC₁,hC₂,hC₃,hD,hw₀,?_⟩
  intro w hw ell S start mesh N hnorm hell hS3 hS hr hs hsS hcons hm hmesh hupper n hn
  exact failure_probability_le
    (jointKernel hnorm hell (by linarith) hS hr hs hsS (Real.log start.gap) mesh)
    (mismatch_measurable mesh) (GoodAt (Real.log start.gap) mesh)
    (GoodAt_measurable (Real.log start.gap) mesh)
    (actual_good_step hnorm hell (by linarith) hS hr hs hsS (Real.log start.gap) hm)
    (sourceJoint w ell S start hs) (source_good hs hsS hm.le)
    (ENNReal.ofReal (stepBudget c₁ c₂ C₁ C₂ C₃ D w S mesh N)) N
    (fun m hm' q hq => hrow w hw ell S start (Real.log start.gap) mesh N hnorm hell hS3 hS hr hs hsS
      hcons hm hmesh hupper m hm'.le q hq) n hn

end NumberTheoryLean.ActualFiniteCoupling

end

end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.NumberTheoryLean.ActualFiniteCoupling.actual_finite_failure_jb247_oai := @OAI.Erdos970.NumberTheoryLean.ActualFiniteCoupling.actual_finite_failure_jb247_oai
