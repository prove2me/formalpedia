-- Prove2me | solution 1 for OAI.Erdos970.NumberTheoryLean.ContinuousLowOccupationLimit.source_continuous_low_limit_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:03:08.147003+00:00
-- url     : https://prove2.me/submissions/8cde7062-4073-4009-bb70-cf66ab86f371

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
import Mathlib.Analysis.Normed.Group.Bounded
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
import Mathlib.Data.List.OfFn
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
import Mathlib.Probability.Distributions.Bernoulli
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
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_OAIQ247J010
import Theorems.Thm_OAI_Erdos970_NumberTheoryLean_ContinuousOccupationIdentification_full_admitted_eq_response_jb247
import Theorems.Thm_OAI_Erdos970_NumberTheoryLean_EvenStartOccupation_source_start_occupation_limit_jb247

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_WeightFutureIntegrals
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.DeficitFutureIntegrals

open Filter Set MeasureTheory
open scoped Topology
open LinearSieveFunctions BuchstabBridge NormalizedDeficits

theorem future_integral_of_mass {a b : ℝ → ℝ} {base : ℝ} (hbase : 1 ≤ base)
    (ha : ContinuousOn a (Ioi 0))
    (hb : ∀ t, base - 1 < t → 0 ≤ b t)
    (hd : ∀ t, base < t → HasDerivAt (fun u => u * a u) (-b (t - 1)) t)
    (hl : Tendsto (fun t => t * a t) atTop (𝓝 0))
    {s : ℝ} (hs : base ≤ s) :
    IntegrableOn b (Ioi (s - 1)) ∧ s * a s = ∫ t in Ioi (s - 1), b t := by
  let H : ℝ → ℝ := fun t => (t + 1) * a (t + 1)
  have hs0 : 0 < s := lt_of_lt_of_le (by linarith : 0 < base) hs
  have hc : ContinuousWithinAt H (Ici (s - 1)) (s - 1) := by
    have hm : ContinuousAt (fun t => t * a t) s :=
      continuousAt_id.mul (ha.continuousAt (Ioi_mem_nhds hs0))
    have hm' : ContinuousAt (fun t => t * a t) ((s - 1) + 1) := by simpa only [sub_add_cancel] using hm
    have hc' := hm'.comp (f := fun t : ℝ => t + 1) (x := s - 1)
      ((continuous_id.add continuous_const : Continuous (fun t : ℝ => t + 1)).continuousAt)
    convert! hc'.continuousWithinAt using 1
    all_goals try with_reducible_and_instances rfl
  have hder : ∀ t ∈ Ioi (s - 1), HasDerivAt H (-b t) t := by
    intro t ht
    have hdt := (hd (t + 1) (by change s - 1 < t at ht; linarith)).comp t
      ((hasDerivAt_id t).add_const 1)
    convert! hdt using 1
    all_goals try with_reducible_and_instances rfl
    simp
  have hnonpos : ∀ t ∈ Ioi (s - 1), -b t ≤ 0 := by
    intro t ht
    exact neg_nonpos.mpr (hb t (by change s - 1 < t at ht; linarith))
  have hshift : Tendsto (fun t : ℝ => t + 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro v
    exact eventually_atTop.mpr ⟨v - 1, fun t ht => by linarith⟩
  have hlim : Tendsto H atTop (𝓝 0) := hl.comp hshift
  have hint := integrableOn_Ioi_deriv_of_nonpos hc hder hnonpos hlim
  have heq := integral_Ioi_of_hasDerivAt_of_nonpos hc hder hnonpos hlim
  constructor
  · exact integrable_neg_iff.mp hint
  · simp only [integral_neg, H, sub_add_cancel, zero_sub] at heq
    linarith

theorem lowerDeficit_nonneg (s : ℝ) : 0 ≤ lowerDeficit s := by
  by_cases hs : 1 ≤ s
  · exact (deficits_pos hs).1.le
  · simp only [lowerDeficit, f_initial sieveA (by linarith : s ≤ 2), sub_zero, zero_le_one]

theorem lower_future_integral {s : ℝ} (hs : 2 ≤ s) :
    IntegrableOn upperDeficit (Ioi (s - 1)) ∧
      s * lowerDeficit s = ∫ t in Ioi (s - 1), upperDeficit t := by
  exact future_integral_of_mass (a := lowerDeficit) (b := upperDeficit) (base := 2) (by norm_num)
    lowerDeficit_continuous.continuousOn (fun t ht => (deficits_pos (s := t) (by linarith)).2.le)
    (fun _ ht => lowerDeficit_mass_deriv ht) lowerDeficit_mass_tendsto_zero hs

theorem upper_future_integral {s : ℝ} (hs : 1 ≤ s) :
    IntegrableOn lowerDeficit (Ioi (s - 1)) ∧
      s * upperDeficit s = ∫ t in Ioi (s - 1), lowerDeficit t := by
  exact future_integral_of_mass (a := upperDeficit) (b := lowerDeficit) (base := 1) le_rfl
    ((F_continuousOn sieveA).sub continuousOn_const) (fun t _ => lowerDeficit_nonneg t)
    (fun _ ht => upperDeficit_mass_deriv_of_one_lt ht) upperDeficit_mass_tendsto_zero hs

end NumberTheoryLean.DeficitFutureIntegrals

end

end Erdos970

end OAI
end

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

theorem minRatio_ge_sub_one (i : Side) (s : ℝ) : s - 1 ≤ minRatio i s := by
  cases i with
  | even => exact le_rfl
  | odd => exact le_max_right _ _

theorem nextExponent_pos {r t : ℝ} (hr : 0 < r) (ht : 0 < t) : 0 < nextExponent r t := by
  unfold nextExponent
  positivity

theorem nextGap_div_ratio {r t : ℝ} (ht : 0 < t) : nextGap r t / t = nextExponent r t := by
  unfold nextGap nextExponent
  field_simp

theorem exponent_le_cutoff {i : Side} {s t r : ℝ}
    (hs : Valid i s) (ht : minRatio i s ≤ t) (hr : 0 < r) : nextExponent r t ≤ r / s := by
  have hs0 := valid_pos hs
  have ht0 := valid_pos (valid_next hs ht)
  have hst : s ≤ t + 1 := by linarith [minRatio_ge_sub_one i s]
  exact div_le_div_of_nonneg_left hr.le hs0 hst

theorem step_weight_identity {i : Side} {s t r : ℝ}
    (hs : Valid i s) (ht : minRatio i s ≤ t) (hr : 0 < r) :
    1 / (t + 1) = transitionDensity i s t * (nextGap r t / r) ^ 2 *
      (weight i s / weight i.flip t) := by
  have hv := valid_next hs ht
  have ht0 := valid_pos hv
  have hw := weight_pos hs
  have hw' := weight_pos hv
  unfold transitionDensity tailDensity
  rw [indicator_of_mem (show t ∈ Ici (minRatio i s) from ht)]
  unfold W nextGap
  field_simp

theorem cost_pos {t : ℝ} (ht : 0 < t) : 0 < cost t := by
  unfold cost
  exact Real.log_pos (by have h : 0 < 1 / t := one_div_pos.mpr ht; linarith)

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_RegenerationDrift
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedPairKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.RegenerativeOddOccupation.ratioVisits_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.CostReturnLaw.costCaptured_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostReturnLaw.costKilled_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostReturnLaw.costKilled_pow_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostReturnLaw.firstReturn_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostReturnLaw.returnLaw_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.CycleConvolutionLaw.returnLaw_pow_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.CycleOccupation.pairSampling_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.CycleRegeneration.cycleJointLaw_isProbabilityMeasure _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.InitialRegeneration.hitOrReturn_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.KernelDensityBridge.oddTwoStep_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PairedCostProcess.pairedCostKernel_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.PairedCostProcess.pairedDraws_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.PairedHitting.pairedKilled_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PairedHitting.pairedKilled_pow_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PairedHitting.pairedOdd_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.Erdos970.NumberTheoryLean.FirstHitKernels.regeneration_even _root_.OAI.Erdos970.NumberTheoryLean.FirstHitKernels.regeneration_odd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.RegenerationTails

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
open BuchstabBridge DerivativeWeights WeightFutureIntegrals WeightTailBounds
open TransitionKernels FinitePathMeasures

theorem oddKernel_regeneration (s : OddState) (hs : s.1 ≤ 3) :
    oddKernel s = oddKernel regenerationState := by
  ext B hB
  rw [oddKernel_apply, oddKernel_apply]
  congr 1
  ext t
  congr 1
  unfold oddDensity
  rw [max_eq_left (show s.1 - 1 ≤ 2 by linarith), phiOdd_initial hs]
  norm_num [regenerationState, phiOdd, tailDensity]

end NumberTheoryLean.RegenerationTails

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_InvariantFiniteness
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal
namespace Erdos970Dependency.InvariantDensities
open NumberTheoryLean NumberTheoryLean.BuchstabBridge NumberTheoryLean.DerivativeWeights
open NumberTheoryLean.TransitionKernels NumberTheoryLean.FinitePathGeometry

theorem oddFactor_bounds {s : ℝ} (hs : 1 ≤ s) : 0 ≤ oddFactor s ∧ oddFactor s ≤ 1 := by
  have hs0 : 0 < s := by linarith
  have hsq : 1 ≤ s ^ 2 := by nlinarith
  have hinv : 1 / s ^ 2 ≤ 1 := (div_le_one (sq_pos_of_pos hs0)).mpr hsq
  have hnonneg : 0 ≤ 1 / s ^ 2 := by positivity
  unfold oddFactor
  constructor <;> linarith

theorem oddFactor_measurable : Measurable oddFactor := by
  unfold oddFactor
  fun_prop

theorem evenDensity_measurable : Measurable evenDensity :=
  phiEven_measurable.indicator measurableSet_Ici

theorem oddDensity_measurable : Measurable oddDensity :=
  (oddFactor_measurable.mul phiOdd_continuous.measurable).indicator measurableSet_Ici

theorem evenDensity_nonneg (s : ℝ) : 0 ≤ evenDensity s := by
  by_cases hs : 2 ≤ s
  · rw [evenDensity, indicator_of_mem (show s ∈ Ici (2 : ℝ) from hs)]
    exact (phiEven_pos (by linarith)).le
  · rw [evenDensity, indicator_of_notMem (show s ∉ Ici (2 : ℝ) from hs)]

theorem oddDensity_nonneg (s : ℝ) : 0 ≤ oddDensity s := by
  by_cases hs : 1 ≤ s
  · rw [oddDensity, indicator_of_mem (show s ∈ Ici (1 : ℝ) from hs)]
    exact mul_nonneg (oddFactor_bounds hs).1 (phiOdd_pos s).le
  · rw [oddDensity, indicator_of_notMem (show s ∉ Ici (1 : ℝ) from hs)]

theorem oddFactor_hasDerivAt {s : ℝ} (hs : s ≠ 0) :
    HasDerivAt (fun t : ℝ ↦ t + 1 / t) (oddFactor s) s := by
  have h := (hasDerivAt_id s).add ((hasDerivAt_const s (1 : ℝ)).div (hasDerivAt_id s) hs)
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [oddFactor, id_eq, zero_mul, zero_sub, mul_one]
  ring

theorem integral_oddFactor {b : ℝ} (hb : 1 ≤ b) :
    (∫ s in (1 : ℝ)..b, oddFactor s) = b + 1 / b - 2 := by
  have hd : ∀ s ∈ uIcc (1 : ℝ) b,
      HasDerivAt (fun t : ℝ ↦ t + 1 / t) (oddFactor s) s := by
    intro s hs
    rw [uIcc_of_le hb] at hs
    exact oddFactor_hasDerivAt (by linarith [hs.1])
  have hi : IntervalIntegrable oddFactor volume 1 b := by
    apply ContinuousOn.intervalIntegrable
    intro s hs
    rw [uIcc_of_le hb] at hs
    apply ContinuousAt.continuousWithinAt
    unfold oddFactor
    exact continuousAt_const.sub (continuousAt_const.div (continuousAt_id.pow 2) (by nlinarith [hs.1]))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  norm_num at h
  simpa only [one_div] using h

theorem beta_eq : beta = 4 * sieveA / 3 := by
  unfold beta
  calc
    (∫ s in (1 : ℝ)..3, oddDensity s) = ∫ s in (1 : ℝ)..3, sieveA * oddFactor s := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)] at hs
      rw [oddDensity, indicator_of_mem (show s ∈ Ici (1 : ℝ) from hs.1), phiOdd_initial hs.2, mul_comm]
    _ = sieveA * (3 + 1 / 3 - 2) := by
      rw [intervalIntegral.integral_const_mul, integral_oddFactor (by norm_num)]
    _ = _ := by ring

theorem beta_pos : 0 < beta := by
  rw [beta_eq]
  exact div_pos (mul_pos (by norm_num) sieveA_pos) (by norm_num)

end Erdos970Dependency.InvariantDensities

end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Erdos970Dependency.InvariantFiniteness
open NumberTheoryLean NumberTheoryLean.DerivativeWeights NumberTheoryLean.TransitionKernels
open Erdos970Dependency.InvariantDensities

theorem integrableOn_Ici_of_exp_tail {f : ℝ → ℝ} {a : ℝ}
    (hm : Measurable f) (hc : ContinuousOn f (Ici a)) (hn : ∀ s, a ≤ s → 0 ≤ f s)
    {C T : ℝ} (hT : a ≤ T) (hb : ∀ s, T ≤ s → f s ≤ C * Real.exp (-s)) :
    IntegrableOn f (Ici a) := by
  have hcompact : IntegrableOn f (Icc a T) :=
    (hc.mono Icc_subset_Ici_self).integrableOn_Icc
  have htail : IntegrableOn f (Ioi T) := by
    apply ((integrableOn_exp_neg_Ioi T).const_mul C).mono_nonneg hm.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact hn s (hT.trans hs.le)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact hb s hs.le
  rw [← Icc_union_Ioi_eq_Ici hT]
  exact hcompact.union htail

theorem weights_exp_majorant : ∃ D U : ℝ, 0 < D ∧ 2 ≤ U ∧ ∀ s : ℝ, U ≤ s →
    phiEven s ≤ D * Real.exp (-s) ∧ phiOdd s ≤ D * Real.exp (-s) := by
  obtain ⟨c, C, hc, hC, hphi⟩ := WeightDickmanComparison.weights_dickman_bounds
  obtain ⟨R, hR, T, hT, hrho⟩ := DickmanDecay.rho_exponential_majorant 1
  refine ⟨C * R * Real.exp 2, T + 2, by positivity, by linarith, ?_⟩
  intro s hs
  have hs2 : 2 ≤ s := by linarith
  have hr := hrho (s - 2) (by linarith)
  have heq : Real.exp (-(s - 2)) = Real.exp 2 * Real.exp (-s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [neg_one_mul, heq] at hr
  have hbound : C * Dickman.rho (s - 2) ≤ (C * R * Real.exp 2) * Real.exp (-s) := by
    have h := mul_le_mul_of_nonneg_left hr hC.le
    convert! h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  exact ⟨(hphi s hs2).1.2.trans hbound, (hphi s hs2).2.2.trans hbound⟩

theorem phiEven_integrableOn : IntegrableOn phiEven (Ici (2 : ℝ)) := by
  obtain ⟨D, U, _, hU, hb⟩ := weights_exp_majorant
  apply integrableOn_Ici_of_exp_tail phiEven_measurable ?_
    (fun s hs ↦ (phiEven_pos (by linarith)).le) hU (fun s hs ↦ (hb s hs).1)
  intro s hs
  exact (phiEven_continuousAt (by change (2 : ℝ) ≤ s at hs; linarith)).continuousWithinAt

theorem phiOdd_integrableOn : IntegrableOn phiOdd (Ici (1 : ℝ)) := by
  obtain ⟨D, U, _, hU, hb⟩ := weights_exp_majorant
  exact integrableOn_Ici_of_exp_tail phiOdd_continuous.measurable phiOdd_continuous.continuousOn
    (fun s _ ↦ (phiOdd_pos s).le) (show (1 : ℝ) ≤ U by linarith) (fun s hs ↦ (hb s hs).2)

theorem evenDensity_integrable : Integrable InvariantDensities.evenDensity :=
  (integrable_indicator_iff measurableSet_Ici).mpr phiEven_integrableOn

theorem oddDensity_integrable : Integrable InvariantDensities.oddDensity := by
  apply (integrable_indicator_iff measurableSet_Ici).mpr
  apply phiOdd_integrableOn.mono_nonneg
    (oddFactor_measurable.mul phiOdd_continuous.measurable).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
    exact mul_nonneg (oddFactor_bounds hs).1 (phiOdd_pos s).le
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
    have h := mul_le_mul_of_nonneg_right (oddFactor_bounds hs).2 (phiOdd_pos s).le
    convert! h using 1
    all_goals try with_reducible_and_instances rfl
    simp only [one_mul]

instance evenMeasure_isFiniteMeasure : IsFiniteMeasure evenMeasure := by
  constructor
  rw [evenMeasure, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal evenDensity_integrable
      (Filter.Eventually.of_forall InvariantDensities.evenDensity_nonneg)]
  exact ENNReal.ofReal_lt_top

instance oddMeasure_isFiniteMeasure : IsFiniteMeasure oddMeasure := by
  constructor
  rw [oddMeasure, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal oddDensity_integrable
      (Filter.Eventually.of_forall InvariantDensities.oddDensity_nonneg)]
  exact ENNReal.ofReal_lt_top

end Erdos970Dependency.InvariantFiniteness

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_DensityConservation
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.Erdos970.NumberTheoryLean.ReferenceBenchmarkDecay.benchmark_even_below_two
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set MeasureTheory
namespace Erdos970Dependency.IncomingDensityIdentities
open NumberTheoryLean.DerivativeWeights NumberTheoryLean.FinitePathGeometry
open Erdos970Dependency.InvariantDensities

theorem incomingOdd_formula {t : ℝ} (ht : 2 ≤ t) (s : ℝ) :
    incomingOdd t s = (Icc (1 : ℝ) (t + 1)).indicator
      (fun s ↦ (W t * phiEven t) * oddFactor s) s := by
  classical
  by_cases hs1 : 1 ≤ s
  · rw [incomingOdd, oddDensity, indicator_of_mem (show s ∈ Ici (1 : ℝ) from hs1)]
    by_cases hst : s ≤ t + 1
    · have hmax : max 2 (s - 1) ≤ t := max_le ht (by linarith)
      rw [transitionDensity, minRatio, weight, Side.flip, weight,
        NumberTheoryLean.TransitionKernels.tailDensity,
        indicator_of_mem (show t ∈ Ici (max 2 (s - 1)) from hmax),
        indicator_of_mem (show s ∈ Icc (1 : ℝ) (t + 1) from ⟨hs1, hst⟩)]
      field_simp [(phiOdd_pos s).ne']
    · have hmax : ¬max 2 (s - 1) ≤ t := by
        intro h
        have := le_trans (le_max_right (2 : ℝ) (s - 1)) h
        linarith
      rw [transitionDensity, minRatio, weight, Side.flip, weight,
        NumberTheoryLean.TransitionKernels.tailDensity,
        indicator_of_notMem (show t ∉ Ici (max 2 (s - 1)) from hmax),
        indicator_of_notMem (show s ∉ Icc (1 : ℝ) (t + 1) from fun h ↦ hst h.2), mul_zero]
  · rw [incomingOdd, oddDensity,
      indicator_of_notMem (show s ∉ Ici (1 : ℝ) from hs1), zero_mul,
      indicator_of_notMem (show s ∉ Icc (1 : ℝ) (t + 1) from fun h ↦ hs1 h.1)]

theorem incomingEven_formula (t s : ℝ) :
    incomingEven t s = (Icc (2 : ℝ) (t + 1)).indicator (fun _ ↦ W t * phiOdd t) s := by
  classical
  by_cases hs2 : 2 ≤ s
  · rw [incomingEven, evenDensity, indicator_of_mem (show s ∈ Ici (2 : ℝ) from hs2)]
    by_cases hst : s ≤ t + 1
    · rw [transitionDensity, minRatio, weight, Side.flip, weight,
        NumberTheoryLean.TransitionKernels.tailDensity,
        indicator_of_mem (show t ∈ Ici (s - 1) by change s - 1 ≤ t; linarith),
        indicator_of_mem (show s ∈ Icc (2 : ℝ) (t + 1) from ⟨hs2, hst⟩)]
      field_simp [(phiEven_pos (by linarith : 1 < s)).ne']
    · rw [transitionDensity, minRatio, weight, Side.flip, weight,
        NumberTheoryLean.TransitionKernels.tailDensity,
        indicator_of_notMem (show t ∉ Ici (s - 1) by change ¬s - 1 ≤ t; linarith),
        indicator_of_notMem (show s ∉ Icc (2 : ℝ) (t + 1) from fun h ↦ hst h.2), mul_zero]
  · rw [incomingEven, evenDensity,
      indicator_of_notMem (show s ∉ Ici (2 : ℝ) from hs2), zero_mul,
      indicator_of_notMem (show s ∉ Icc (2 : ℝ) (t + 1) from fun h ↦ hs2 h.1)]

theorem incomingOdd_zero {t : ℝ} (ht : t < 2) (s : ℝ) : incomingOdd t s = 0 := by
  unfold incomingOdd transitionDensity
  simp only [minRatio, weight, Side.flip, NumberTheoryLean.TransitionKernels.tailDensity]
  rw [indicator_of_notMem (show t ∉ Ici (max 2 (s - 1)) from fun h ↦
    (not_le_of_gt ht) (le_trans (le_max_left _ _) h)), mul_zero]

theorem incomingEven_zero {t : ℝ} (ht : t < 1) (s : ℝ) : incomingEven t s = 0 := by
  by_cases hs : 2 ≤ s
  · unfold incomingEven transitionDensity
    simp only [minRatio, weight, Side.flip, NumberTheoryLean.TransitionKernels.tailDensity]
    rw [indicator_of_notMem (show t ∉ Ici (s - 1) by change ¬s - 1 ≤ t; linarith), mul_zero]
  · rw [incomingEven, evenDensity, indicator_of_notMem (show s ∉ Ici (2 : ℝ) from hs), zero_mul]

theorem incomingOdd_integral (t : ℝ) : (∫ s, incomingOdd t s) = evenDensity t := by
  by_cases ht : 2 ≤ t
  · simp_rw [incomingOdd_formula ht]
    rw [integral_indicator measurableSet_Icc, integral_const_mul,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (show (1 : ℝ) ≤ t + 1 by linarith),
      integral_oddFactor (by linarith : (1 : ℝ) ≤ t + 1),
      evenDensity, indicator_of_mem (show t ∈ Ici (2 : ℝ) from ht)]
    unfold W
    field_simp
    ring
  · simp only [incomingOdd_zero (lt_of_not_ge ht), integral_zero]
    rw [evenDensity, indicator_of_notMem (show t ∉ Ici (2 : ℝ) from ht)]

theorem incomingEven_integral (t : ℝ) : (∫ s, incomingEven t s) = oddDensity t := by
  by_cases ht : 1 ≤ t
  · simp_rw [incomingEven_formula]
    rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (show (2 : ℝ) ≤ t + 1 by linarith),
      intervalIntegral.integral_const, oddDensity, indicator_of_mem (show t ∈ Ici (1 : ℝ) from ht)]
    simp only [smul_eq_mul]
    unfold W oddFactor
    field_simp
    ring
  · simp only [incomingEven_zero (lt_of_not_ge ht), integral_zero]
    rw [oddDensity, indicator_of_notMem (show t ∉ Ici (1 : ℝ) from ht)]

theorem incomingOdd_integrable (t : ℝ) : Integrable (incomingOdd t) := by
  by_cases ht : 2 ≤ t
  · rw [show incomingOdd t = (Icc (1 : ℝ) (t + 1)).indicator
      (fun s ↦ (W t * phiEven t) * oddFactor s) from funext (incomingOdd_formula ht)]
    apply (integrable_indicator_iff measurableSet_Icc).mpr
    apply ContinuousOn.integrableOn_Icc
    intro s hs
    apply ContinuousAt.continuousWithinAt
    unfold oddFactor
    exact continuousAt_const.mul (continuousAt_const.sub
      (continuousAt_const.div (continuousAt_id.pow 2) (by nlinarith [hs.1])))
  · rw [show incomingOdd t = 0 from funext (incomingOdd_zero (lt_of_not_ge ht))]
    exact integrable_zero _ _ _

theorem incomingEven_integrable (t : ℝ) : Integrable (incomingEven t) := by
  rw [show incomingEven t = (Icc (2 : ℝ) (t + 1)).indicator (fun _ ↦ W t * phiOdd t)
    from funext (incomingEven_formula t)]
  exact (integrable_indicator_iff measurableSet_Icc).mpr continuous_const.integrableOn_Icc

end Erdos970Dependency.IncomingDensityIdentities

end

section

open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory
namespace Erdos970Dependency.DensityConservation

theorem kernel_density_conservation (K : Kernel ℝ ℝ) (d e : ℝ → ℝ) (k : ℝ → ℝ → ℝ)
    (hd : Measurable d) (hd0 : ∀ s, 0 ≤ d s)
    (hprod : Measurable (fun z : ℝ × ℝ ↦ d z.1 * k z.1 z.2))
    (hkernel : ∀ s (B : Set ℝ), MeasurableSet B → K s B = ∫⁻ t in B, ENNReal.ofReal (k s t))
    (hint : ∀ t, Integrable (fun s ↦ d s * k s t))
    (hpos : ∀ s t, 0 ≤ d s * k s t)
    (hconserve : ∀ t, (∫ s, d s * k s t) = e t) :
    K ∘ₘ (volume.withDensity (fun s ↦ ENNReal.ofReal (d s))) =
      volume.withDensity (fun t ↦ ENNReal.ofReal (e t)) := by
  apply Measure.ext
  intro B hB
  rw [Measure.bind_apply hB K.aemeasurable]
  have hdensity := lintegral_withDensity_eq_lintegral_mul volume (ENNReal.measurable_ofReal.comp hd)
    (K.measurable_coe hB)
  simp only [Function.comp_def, Pi.mul_apply] at hdensity
  rw [hdensity]
  simp_rw [hkernel _ _ hB]
  have hrewrite (s : ℝ) : ENNReal.ofReal (d s) * (∫⁻ t in B, ENNReal.ofReal (k s t)) =
      ∫⁻ t in B, ENNReal.ofReal (d s * k s t) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro t
    exact (ENNReal.ofReal_mul (hd0 s)).symm
  simp_rw [hrewrite]
  have hm : Measurable (Function.uncurry (fun s t : ℝ ↦ ENNReal.ofReal (d s * k s t))) := by
    change Measurable (fun z : ℝ × ℝ ↦ ENNReal.ofReal (d z.1 * k z.1 z.2))
    simpa only [Function.comp_def] using ENNReal.measurable_ofReal.comp hprod
  rw [lintegral_lintegral_swap (μ := volume) (ν := volume.restrict B) hm.aemeasurable]
  simp_rw [← ofReal_integral_eq_lintegral_ofReal (hint _) (Eventually.of_forall (fun s ↦ hpos s _)),
    hconserve]
  exact (withDensity_apply _ hB).symm

end Erdos970Dependency.DensityConservation

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_StateKernelInvariance
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedPairKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.RegenerativeOddOccupation.ratioVisits_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.CostReturnLaw.costCaptured_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostReturnLaw.costKilled_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostReturnLaw.costKilled_pow_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostReturnLaw.firstReturn_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostReturnLaw.returnLaw_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.CycleConvolutionLaw.returnLaw_pow_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.CycleOccupation.pairSampling_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.CycleRegeneration.cycleJointLaw_isProbabilityMeasure _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.InitialRegeneration.hitOrReturn_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PairedCostProcess.pairedCostKernel_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.PairedCostProcess.pairedDraws_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.PairedHitting.pairedKilled_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PairedHitting.pairedKilled_pow_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PairedHitting.pairedOdd_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory
namespace Erdos970Dependency.OrdinaryKernelInvariance
open NumberTheoryLean NumberTheoryLean.DerivativeWeights NumberTheoryLean.FinitePathGeometry
open NumberTheoryLean.TransitionKernels NumberTheoryLean.KernelDensityBridge
open Erdos970Dependency.InvariantDensities Erdos970Dependency.InvariantFiniteness
open Erdos970Dependency.IncomingDensityIdentities Erdos970Dependency.DensityConservation

theorem even_lifted_product (s t : ℝ) :
    InvariantDensities.evenDensity s * transitionDensity .even (evenLift s).1 t = incomingEven t s := by
  by_cases hs : 2 ≤ s
  · have heq : (evenLift s).1 = s := max_eq_right (by linarith)
    rw [heq]
    rfl
  · rw [incomingEven, InvariantDensities.evenDensity,
      indicator_of_notMem (show s ∉ Ici (2 : ℝ) from hs), zero_mul, zero_mul]

theorem odd_lifted_product (s t : ℝ) :
    InvariantDensities.oddDensity s * transitionDensity .odd (oddLift s).1 t = incomingOdd t s := by
  by_cases hs : 1 ≤ s
  · have heq : (oddLift s).1 = s := max_eq_right (by linarith)
    rw [heq]
    rfl
  · rw [incomingOdd, InvariantDensities.oddDensity,
      indicator_of_notMem (show s ∉ Ici (1 : ℝ) from hs), zero_mul, zero_mul]

theorem even_ratio_invariance : evenRealKernel ∘ₘ evenMeasure = oddMeasure := by
  apply kernel_density_conservation evenRealKernel InvariantDensities.evenDensity
    InvariantDensities.oddDensity (fun s t ↦ transitionDensity .even (evenLift s).1 t)
    InvariantDensities.evenDensity_measurable InvariantDensities.evenDensity_nonneg
  · exact (InvariantDensities.evenDensity_measurable.comp measurable_fst).mul
      ((transitionDensity_joint_measurable .even).comp
        (((measurable_subtype_coe.comp evenLift_measurable).comp measurable_fst).prodMk measurable_snd))
  · intro s B _
    exact evenKernel_apply (evenLift s) B
  · intro t
    rw [show (fun s ↦ InvariantDensities.evenDensity s * transitionDensity .even (evenLift s).1 t) =
      incomingEven t from funext (fun s ↦ even_lifted_product s t)]
    exact incomingEven_integrable t
  · intro s t
    exact mul_nonneg (InvariantDensities.evenDensity_nonneg s)
      (TransitionKernels.evenDensity_nonneg (evenLift s) t)
  · intro t
    simp_rw [even_lifted_product]
    exact incomingEven_integral t

theorem odd_ratio_invariance : oddRealKernel ∘ₘ oddMeasure = evenMeasure := by
  apply kernel_density_conservation oddRealKernel InvariantDensities.oddDensity
    InvariantDensities.evenDensity (fun s t ↦ transitionDensity .odd (oddLift s).1 t)
    InvariantDensities.oddDensity_measurable InvariantDensities.oddDensity_nonneg
  · exact (InvariantDensities.oddDensity_measurable.comp measurable_fst).mul
      ((transitionDensity_joint_measurable .odd).comp
        (((measurable_subtype_coe.comp oddLift_measurable).comp measurable_fst).prodMk measurable_snd))
  · intro s B _
    exact oddKernel_apply (oddLift s) B
  · intro t
    rw [show (fun s ↦ InvariantDensities.oddDensity s * transitionDensity .odd (oddLift s).1 t) =
      incomingOdd t from funext (fun s ↦ odd_lifted_product s t)]
    exact incomingOdd_integrable t
  · intro s t
    exact mul_nonneg (InvariantDensities.oddDensity_nonneg s)
      (TransitionKernels.oddDensity_nonneg (oddLift s) t)
  · intro t
    simp_rw [odd_lifted_product]
    exact incomingOdd_integral t

end Erdos970Dependency.OrdinaryKernelInvariance

end

section

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
namespace Erdos970Dependency.StateKernelInvariance
open NumberTheoryLean.TransitionKernels NumberTheoryLean.FinitePathMeasures NumberTheoryLean.KernelDensityBridge
open Erdos970Dependency.InvariantFiniteness Erdos970Dependency.OrdinaryKernelInvariance

theorem comp_map_input {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (K : Kernel β γ) (mu : Measure α) (f : α → β) (hf : Measurable f) :
    K ∘ₘ mu.map f = K.comap f hf ∘ₘ mu := by
  ext B hB
  rw [Measure.bind_apply hB K.aemeasurable, lintegral_map (K.measurable_coe hB) hf,
    Measure.bind_apply hB (K.comap f hf).aemeasurable]
  rfl

theorem oddLift_ratio (s : OddState) : oddLift s.1 = s := by
  apply Subtype.ext
  exact max_eq_right s.2

theorem evenLift_ratio (s : EvenState) : evenLift s.1 = s := by
  apply Subtype.ext
  exact max_eq_right s.2

theorem evenKernel_map_lift (s : EvenState) : (evenKernel s).map oddLift = evenToOdd s := by
  rw [← evenToOdd_map_ratio s, Measure.map_map oddLift_measurable measurable_subtype_coe]
  rw [show oddLift ∘ (Subtype.val : OddState → ℝ) = id from funext oddLift_ratio, Measure.map_id]

theorem oddKernel_map_lift (s : OddState) : (oddKernel s).map evenLift = oddToEven s := by
  rw [← oddToEven_map_ratio s, Measure.map_map evenLift_measurable measurable_subtype_coe]
  rw [show evenLift ∘ (Subtype.val : EvenState → ℝ) = id from funext evenLift_ratio, Measure.map_id]

instance evenStateMeasure_isFiniteMeasure : IsFiniteMeasure evenStateMeasure := by unfold evenStateMeasure; infer_instance
instance oddStateMeasure_isFiniteMeasure : IsFiniteMeasure oddStateMeasure := by unfold oddStateMeasure; infer_instance

theorem even_state_invariance : evenToOdd ∘ₘ evenStateMeasure = oddStateMeasure := by
  have h := congrArg (fun mu : Measure ℝ ↦ mu.map oddLift) even_ratio_invariance
  rw [Measure.map_comp _ _ oddLift_measurable] at h
  have hK : evenRealKernel.map oddLift = evenToOdd.comap evenLift evenLift_measurable := by
    ext s B hB
    rw [Kernel.map_apply _ oddLift_measurable]
    change (evenKernel (evenLift s)).map oddLift B = evenToOdd (evenLift s) B
    rw [evenKernel_map_lift]
  rw [hK, ← comp_map_input] at h
  exact h

theorem odd_state_invariance : oddToEven ∘ₘ oddStateMeasure = evenStateMeasure := by
  have h := congrArg (fun mu : Measure ℝ ↦ mu.map evenLift) odd_ratio_invariance
  rw [Measure.map_comp _ _ evenLift_measurable] at h
  have hK : oddRealKernel.map evenLift = oddToEven.comap oddLift oddLift_measurable := by
    ext s B hB
    rw [Kernel.map_apply _ evenLift_measurable]
    change (oddKernel (oddLift s)).map evenLift B = oddToEven (oddLift s) B
    rw [oddKernel_map_lift]
  rw [hK, ← comp_map_input] at h
  exact h

instance stateMeasure_isFiniteMeasure : IsFiniteMeasure stateMeasure := by unfold stateMeasure; infer_instance

end Erdos970Dependency.StateKernelInvariance

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_MinorizingCostRegularity
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.MinorizingCostRegularity

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures JointMinorization

theorem cost_strictAntiOn : StrictAntiOn cost (Ioi 0) := by
  intro t ht u hu htu
  change 0 < t at ht
  change 0 < u at hu
  unfold cost
  have hi := one_div_lt_one_div_of_lt ht htu
  exact Real.log_lt_log (by positivity) (by linarith)

end NumberTheoryLean.MinorizingCostRegularity

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_PairedCostGrouping
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.RegenerativeOddOccupation.ratioVisits_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.StateKernelInvariance.evenStateMeasure_isFiniteMeasure _root_.OAI.Erdos970.Erdos970Dependency.StateKernelInvariance.oddStateMeasure_isFiniteMeasure _root_.OAI.Erdos970.Erdos970Dependency.StateKernelInvariance.stateMeasure_isFiniteMeasure _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.CycleConvolutionLaw.returnLaw_pow_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.CycleOccupation.pairSampling_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.CycleRegeneration.cycleJointLaw_isProbabilityMeasure _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.InitialRegeneration.hitOrReturn_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.PairedCostGrouping

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostProcess

theorem costKernel_odd_lintegral (s : OddState) (T : ℝ) {H : CostState → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ z, H z ∂costKernel (.inr s, T)) =
      ∫⁻ t : EvenState, H (.inl t, T + cost t.1) ∂oddToEven s := by
  have hm : Measurable (fun u : State => (u, T + cost (stateRatio u))) :=
    measurable_id.prodMk (measurable_const.add (cost_measurable.comp stateRatio_measurable))
  rw [costKernel_eq_map, lintegral_map hH hm]
  change (∫⁻ u, H (u, T + cost (stateRatio u)) ∂oddBranch s) = _
  rw [oddBranch, Kernel.map_apply _ measurable_inl,
    lintegral_map (f := fun u : State => H (u, T + cost (stateRatio u))) (hH.comp hm) measurable_inl]
  rfl

theorem costKernel_even_lintegral (s : EvenState) (T : ℝ) {H : CostState → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ z, H z ∂costKernel (.inl s, T)) =
      ∫⁻ t : OddState, H (.inr t, T + cost t.1) ∂evenToOdd s := by
  have hm : Measurable (fun u : State => (u, T + cost (stateRatio u))) :=
    measurable_id.prodMk (measurable_const.add (cost_measurable.comp stateRatio_measurable))
  rw [costKernel_eq_map, lintegral_map hH hm]
  change (∫⁻ u, H (u, T + cost (stateRatio u)) ∂evenBranch s) = _
  rw [evenBranch, Kernel.map_apply _ measurable_inr,
    lintegral_map (f := fun u : State => H (u, T + cost (stateRatio u))) (hH.comp hm) measurable_inr]
  rfl

end NumberTheoryLean.PairedCostGrouping

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_FiniteKernelResolvent
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory Topology BigOperators
namespace Erdos970Dependency.FiniteKernelResolvent
variable {X : Type*} [MeasurableSpace X]

theorem fixed_point_finite (Q : Kernel X X) (mu alpha : Measure X)
    (hfix : mu = alpha + Q ∘ₘ mu) (N : ℕ) :
    mu = (∑ j ∈ Finset.range N, (Q ^ j) ∘ₘ alpha) + (Q ^ N) ∘ₘ mu := by
  induction N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, pow_zero, zero_add]
    change mu = Kernel.id ∘ₘ mu
    exact Measure.id_comp.symm
  | succ N ih =>
    have hlast : (Q ^ N) ∘ₘ mu = (Q ^ N) ∘ₘ alpha + (Q ^ (N + 1)) ∘ₘ mu := by
      calc
        (Q ^ N) ∘ₘ mu = (Q ^ N) ∘ₘ (alpha + Q ∘ₘ mu) := congrArg (fun nu ↦ (Q ^ N) ∘ₘ nu) hfix
        _ = (Q ^ N) ∘ₘ alpha + ((Q ^ N) ∘ₖ Q) ∘ₘ mu := by rw [Measure.comp_add, Measure.comp_assoc]
        _ = _ := by rw [pow_succ]; rfl
    rw [Finset.sum_range_succ, add_assoc, ← hlast]
    exact ih

theorem residual_mass_tendsto_zero (Q : Kernel X X) (mu : Measure X) [IsFiniteMeasure mu]
    (hsub : ∀ n s, (Q ^ n) s univ ≤ 1)
    (htail : ∀ s, Tendsto (fun n : ℕ ↦ (Q ^ n) s univ) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ ((Q ^ n) ∘ₘ mu) univ) atTop (𝓝 0) := by
  have h := tendsto_lintegral_of_dominated_convergence (μ := mu)
    (F := fun n s ↦ (Q ^ n) s univ) (f := fun _ ↦ 0) (fun _ ↦ 1)
    (fun n ↦ (Q ^ n).measurable_coe MeasurableSet.univ)
    (fun n ↦ Eventually.of_forall (hsub n))
    (by simp) (Eventually.of_forall htail)
  have heq (n : ℕ) : ((Q ^ n) ∘ₘ mu) univ = ∫⁻ s, (Q ^ n) s univ ∂mu :=
    Measure.bind_apply MeasurableSet.univ (Q ^ n).aemeasurable
  simp_rw [heq]
  simpa only [lintegral_zero] using h

theorem residual_set_tendsto_zero (Q : Kernel X X) (mu : Measure X) [IsFiniteMeasure mu]
    (hsub : ∀ n s, (Q ^ n) s univ ≤ 1)
    (htail : ∀ s, Tendsto (fun n : ℕ ↦ (Q ^ n) s univ) atTop (𝓝 0)) (B : Set X) :
    Tendsto (fun n : ℕ ↦ ((Q ^ n) ∘ₘ mu) B) atTop (𝓝 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (residual_mass_tendsto_zero Q mu hsub htail) (Eventually.of_forall (fun _ ↦ zero_le))
    (Eventually.of_forall (fun _ ↦ measure_mono (subset_univ B)))

theorem fixed_point_resolvent (Q : Kernel X X) (mu alpha : Measure X) [IsFiniteMeasure mu]
    (hfix : mu = alpha + Q ∘ₘ mu) (hsub : ∀ n s, (Q ^ n) s univ ≤ 1)
    (htail : ∀ s, Tendsto (fun n : ℕ ↦ (Q ^ n) s univ) atTop (𝓝 0)) :
    mu = Measure.sum (fun n : ℕ ↦ (Q ^ n) ∘ₘ alpha) := by
  ext B hB
  rw [Measure.sum_apply _ hB]
  have hfinite (N : ℕ) : mu B =
      (∑ j ∈ Finset.range N, ((Q ^ j) ∘ₘ alpha) B) + ((Q ^ N) ∘ₘ mu) B := by
    have h := congrArg (fun nu : Measure X ↦ nu B) (fixed_point_finite Q mu alpha hfix N)
    simpa only [Measure.add_apply, Measure.finsetSum_apply] using h
  have hlim := (ENNReal.tendsto_nat_tsum (fun n : ℕ ↦ ((Q ^ n) ∘ₘ alpha) B)).add
    (residual_set_tendsto_zero Q mu hsub htail B)
  simp only [add_zero] at hlim
  have hlim' : Tendsto (fun _ : ℕ ↦ mu B) atTop
      (𝓝 (∑' n : ℕ, ((Q ^ n) ∘ₘ alpha) B)) :=
    hlim.congr' (Eventually.of_forall (fun N ↦ (hfinite N).symm))
  exact tendsto_nhds_unique tendsto_const_nhds hlim'

end Erdos970Dependency.FiniteKernelResolvent

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_RegenerativeResolvent
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory Topology
namespace Erdos970Dependency.RegenerativeResolvent
open NumberTheoryLean.KernelPotential FiniteKernelResolvent
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem restrict_kernel_comp (P : Kernel X X) (mu : Measure X) {R : Set X} (hR : MeasurableSet R) :
    P.restrict hR ∘ₘ mu = (P ∘ₘ mu).restrict R := by
  ext B hB
  rw [Measure.bind_apply hB (P.restrict hR).aemeasurable, Measure.restrict_apply hB,
    Measure.bind_apply (hB.inter hR) P.aemeasurable]
  apply lintegral_congr
  intro s
  rw [Kernel.restrict_apply, Measure.restrict_apply hB]

theorem compose_sum_measure (B : Kernel X Y) (mu : ℕ → Measure X) :
    B ∘ₘ Measure.sum mu = Measure.sum (fun n ↦ B ∘ₘ mu n) := by
  ext S hS
  rw [Measure.bind_apply hS B.aemeasurable, lintegral_sum_measure, Measure.sum_apply _ hS]
  congr 1
  funext n
  exact (Measure.bind_apply hS B.aemeasurable).symm

theorem common_on_restriction (B : Kernel X Y) (mu : Measure X) {R : Set X}
    (hR : MeasurableSet R) (r : X) (hB : ∀ s ∈ R, B s = B r) :
    B ∘ₘ mu.restrict R = mu R • B r := by
  ext S hS
  rw [Measure.bind_apply hS B.aemeasurable, Measure.smul_apply, smul_eq_mul]
  calc
    (∫⁻ s, B s S ∂mu.restrict R) = ∫⁻ _s, B r S ∂mu.restrict R := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hR] with s hs
      rw [hB s hs]
    _ = _ := by simp [mul_comm]

theorem post_power_common (B : Kernel X Y) (Q : Kernel X X) (R : Set X) (r : X)
    (hB : ∀ s ∈ R, B s = B r) (hQ : ∀ s ∈ R, Q s = Q r) (n : ℕ) :
    ∀ s ∈ R, (B ∘ₖ (Q ^ n)) s = (B ∘ₖ (Q ^ n)) r := by
  intro s hs
  cases n with
  | zero =>
    change (B ∘ₖ Kernel.id) s = (B ∘ₖ Kernel.id) r
    rw [Kernel.comp_id]
    exact hB s hs
  | succ n =>
    rw [pow_succ]
    change (B ∘ₖ ((Q ^ n) ∘ₖ Q)) s = (B ∘ₖ ((Q ^ n) ∘ₖ Q)) r
    rw [← Kernel.comp_assoc]
    rw [Kernel.comp_apply, Kernel.comp_apply, hQ s hs]

theorem post_resolvent (B : Kernel X Y) (Q : Kernel X X) (mu : Measure X) [IsFiniteMeasure mu]
    (R : Set X) (hR : MeasurableSet R) (r : X)
    (hfix : mu = mu.restrict R + Q ∘ₘ mu)
    (hsub : ∀ n s, (Q ^ n) s univ ≤ 1)
    (htail : ∀ s, Tendsto (fun n : ℕ ↦ (Q ^ n) s univ) atTop (𝓝 0))
    (hB : ∀ s ∈ R, B s = B r) (hQ : ∀ s ∈ R, Q s = Q r) :
    B ∘ₘ mu = mu R • (potential B Q) r := by
  have hresolve := fixed_point_resolvent Q mu (mu.restrict R) hfix hsub htail
  calc
    B ∘ₘ mu = B ∘ₘ Measure.sum (fun n : ℕ ↦ (Q ^ n) ∘ₘ mu.restrict R) :=
      congrArg (fun nu ↦ B ∘ₘ nu) hresolve
    _ = Measure.sum (fun n : ℕ ↦ (B ∘ₖ (Q ^ n)) ∘ₘ mu.restrict R) := by
      rw [compose_sum_measure]
      congr 1
      funext n
      exact Measure.comp_assoc
    _ = Measure.sum (fun n : ℕ ↦ mu R • (B ∘ₖ (Q ^ n)) r) := by
      congr 1
      funext n
      exact common_on_restriction _ mu hR r (post_power_common B Q R r hB hQ n)
    _ = mu R • (potential B Q) r := by
      ext S hS
      rw [Measure.sum_apply _ hS, Measure.smul_apply, smul_eq_mul, potential, Kernel.sum_apply' _ _ hS]
      simp only [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.tsum_mul_left

end Erdos970Dependency.RegenerativeResolvent

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_RegenerativeOddOccupation
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedPairKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.CostReturnLaw.costCaptured_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostReturnLaw.costKilled_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostReturnLaw.costKilled_pow_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostReturnLaw.firstReturn_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostReturnLaw.returnLaw_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.CycleConvolutionLaw.returnLaw_pow_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.CycleOccupation.pairSampling_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.CycleRegeneration.cycleJointLaw_isProbabilityMeasure _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.InitialRegeneration.hitOrReturn_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PairedCostProcess.pairedCostKernel_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.PairedCostProcess.pairedDraws_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
namespace Erdos970Dependency.RegenerationMass
open NumberTheoryLean.TransitionKernels NumberTheoryLean.PairedHitting
open Erdos970Dependency.InvariantDensities Erdos970Dependency.InvariantFiniteness
open Erdos970Dependency.OrdinaryKernelInvariance Erdos970Dependency.StateKernelInvariance

theorem oddMeasure_below_one : oddMeasure (Iio (1 : ℝ)) = 0 := by
  rw [oddMeasure, withDensity_apply _ measurableSet_Iio]
  apply setLIntegral_eq_zero measurableSet_Iio
  intro s hs
  change ENNReal.ofReal (InvariantDensities.oddDensity s) = 0
  unfold InvariantDensities.oddDensity
  rw [indicator_of_notMem (show s ∉ Ici (1 : ℝ) by change s < 1 at hs; change ¬1 ≤ s; linarith), ENNReal.ofReal_zero]

theorem oddMeasure_regeneration_interval : oddMeasure (Icc (1 : ℝ) 3) = ENNReal.ofReal beta := by
  rw [oddMeasure, withDensity_apply _ measurableSet_Icc,
    ← ofReal_integral_eq_lintegral_ofReal InvariantFiniteness.oddDensity_integrable.integrableOn
      (Filter.Eventually.of_forall InvariantDensities.oddDensity_nonneg)]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 3)]
  rfl

theorem oddMeasure_Iic_three : oddMeasure (Iic (3 : ℝ)) = ENNReal.ofReal beta := by
  rw [← Iio_union_Icc_eq_Iic (by norm_num : (1 : ℝ) ≤ 3)]
  rw [measure_union (by
    apply Set.disjoint_left.mpr
    intro s hs hcc
    exact (not_le_of_gt hs) hcc.1) measurableSet_Icc,
    oddMeasure_below_one, oddMeasure_regeneration_interval, zero_add]

theorem oddStateMeasure_regeneration : oddStateMeasure pairedRegeneration = ENNReal.ofReal beta := by
  rw [oddStateMeasure, Measure.map_apply oddLift_measurable pairedRegeneration_measurable]
  have hpre : oddLift ⁻¹' pairedRegeneration = Iic (3 : ℝ) := by
    ext s
    change max (95 / 100 : ℝ) s ≤ 3 ↔ s ≤ 3
    rw [max_le_iff]
    norm_num
  rw [hpre, oddMeasure_Iic_three]

end Erdos970Dependency.RegenerationMass

end

section

open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory Topology
namespace Erdos970Dependency.RegenerativeOddOccupation
open NumberTheoryLean.TransitionKernels NumberTheoryLean.FinitePathMeasures
open NumberTheoryLean.PairedHitting NumberTheoryLean.PairedBlockContraction
open NumberTheoryLean.RegenerationTails NumberTheoryLean.KernelPotential
open Erdos970Dependency.InvariantDensities Erdos970Dependency.StateKernelInvariance
open Erdos970Dependency.RegenerationMass Erdos970Dependency.RegenerativeResolvent

theorem paired_invariance : pairedOdd ∘ₘ oddStateMeasure = oddStateMeasure := by
  rw [pairedOdd, ← Measure.comp_assoc, odd_state_invariance, even_state_invariance]

theorem odd_draw_common {s : OddState} (hs : s ∈ pairedRegeneration) :
    oddToEven s = oddToEven regenerationState := by
  rw [oddToEven, Kernel.comapRight_apply, Kernel.comapRight_apply,
    oddKernel_regeneration s hs]

theorem paired_common {s : OddState} (hs : s ∈ pairedRegeneration) :
    pairedOdd s = pairedOdd regenerationState := by
  rw [pairedOdd, Kernel.comp_apply, Kernel.comp_apply, odd_draw_common hs]

theorem killed_common {s : OddState} (hs : s ∈ pairedRegeneration) :
    pairedKilled s = pairedKilled regenerationState := by
  rw [pairedKilled, Kernel.restrict_apply, Kernel.restrict_apply, paired_common hs]

theorem odd_source_equation : oddStateMeasure = oddStateMeasure.restrict pairedRegeneration +
    pairedKilled ∘ₘ oddStateMeasure := by
  rw [pairedKilled, restrict_kernel_comp, paired_invariance]
  exact (Measure.restrict_add_restrict_compl pairedRegeneration_measurable).symm

theorem ratioVisits_common {s : OddState} (hs : s ∈ pairedRegeneration) :
    ratioVisits s = ratioVisits regenerationState := by
  simp only [ratioVisits, add_apply, Kernel.map_apply _ measurable_inl, Kernel.map_apply _ measurable_inr]
  rw [odd_draw_common hs, paired_common hs]

theorem ratioVisits_invariant_mass : ratioVisits ∘ₘ oddStateMeasure = stateMeasure := by
  rw [ratioVisits, Measure.add_comp, ← Measure.map_comp _ _ measurable_inl,
    ← Measure.map_comp _ _ measurable_inr, odd_state_invariance, paired_invariance]
  rfl

theorem stateMeasure_eq_occupation : stateMeasure = ENNReal.ofReal beta • ratioOccupation := by
  have h := post_resolvent ratioVisits pairedKilled oddStateMeasure pairedRegeneration
    pairedRegeneration_measurable regenerationState odd_source_equation
    paired_survival_le_one paired_survival_tendsto_zero
    (fun _ hs ↦ ratioVisits_common hs) (fun _ hs ↦ killed_common hs)
  rw [ratioVisits_invariant_mass, oddStateMeasure_regeneration] at h
  exact h

theorem ratioOccupation_eq : ratioOccupation = (ENNReal.ofReal beta)⁻¹ • stateMeasure := by
  have h := congrArg (fun mu : Measure State ↦ (ENNReal.ofReal beta)⁻¹ • mu) stateMeasure_eq_occupation
  rw [smul_smul, ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr beta_pos))
    ENNReal.ofReal_ne_top, one_smul] at h
  exact h.symm

end Erdos970Dependency.RegenerativeOddOccupation

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_OccupationAge
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.CycleConvolutionLaw.returnLaw_pow_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.InitialRegeneration.hitOrReturn_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.CycleCostLower

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostProcess CostReturnLaw
open MinorizingCostRegularity

theorem pairedCost_cost_monotone (z : OddCost) : ∀ᵐ y ∂pairedCostKernel z, z.2 ≤ y.2 := by
  apply ae_iff.mpr
  simp only [not_le]
  change pairedCostKernel z {y : OddCost | y.2 < z.2} = 0
  rw [pairedCostKernel_apply z (measurableSet_lt measurable_snd measurable_const)]
  have he : {x : EvenState × OddState | (x.2, z.2 + cost x.1.1 + cost x.2.1) ∈ {y : OddCost | y.2 < z.2}} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have h1 : 0 < cost x.1.1 := cost_pos (by linarith [x.1.2])
    have h2 : 0 < cost x.2.1 := cost_pos (by linarith [x.2.2])
    change z.2 + cost x.1.1 + cost x.2.1 < z.2 at hx
    linarith
  rw [he, measure_empty]

theorem costKilled_cost_monotone (z : OddCost) : ∀ᵐ y ∂costKilled z, z.2 ≤ y.2 :=
  ae_restrict_of_ae (pairedCost_cost_monotone z)

theorem costKilled_pow_cost_monotone (n : ℕ) (z : OddCost) :
    ∀ᵐ y ∂(costKilled ^ n) z, z.2 ≤ y.2 := by
  induction n generalizing z with
  | zero =>
    change ∀ᵐ y ∂Measure.dirac z, z.2 ≤ y.2
    exact (ae_dirac_iff (measurableSet_le measurable_const measurable_snd)).mpr le_rfl
  | succ n ih =>
    have hp : costKilled ^ (n + 1) = costKilled ∘ₖ (costKilled ^ n) := pow_succ' costKilled n
    rw [hp]
    apply Kernel.ae_comp_of_ae_ae (measurableSet_le measurable_const measurable_snd)
    filter_upwards [ih z] with y hy
    filter_upwards [costKilled_cost_monotone y] with w hw
    exact le_trans hy hw

theorem captured_cost_lower (z : OddCost) :
    ∀ᵐ y ∂costCaptured z, z.2 + cost 3 ≤ y.2 := by
  apply ae_iff.mpr
  simp only [not_le]
  change costCaptured z {y : OddCost | y.2 < z.2 + cost 3} = 0
  have hB : MeasurableSet {y : OddCost | y.2 < z.2 + cost 3} :=
    measurableSet_lt measurable_snd measurable_const
  rw [costCaptured, Kernel.restrict_apply' _ _ _ hB,
    pairedCostKernel_apply z (hB.inter returnSet_measurable)]
  have he : {x : EvenState × OddState | (x.2, z.2 + cost x.1.1 + cost x.2.1) ∈
      ({y : OddCost | y.2 < z.2 + cost 3} ∩ returnSet)} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hu : x.2.1 ≤ 3 := hx.2
    have hcost : cost 3 ≤ cost x.2.1 := cost_strictAntiOn.antitoneOn
      (by change 0 < x.2.1; linarith [x.2.2]) (by norm_num) hu
    have hfirst : 0 < cost x.1.1 := cost_pos (by linarith [x.1.2])
    have hbad : z.2 + cost x.1.1 + cost x.2.1 < z.2 + cost 3 := hx.1
    linarith
  rw [he, measure_empty]

theorem firstReturn_cost_lower (n : ℕ) (z : OddCost) :
    ∀ᵐ y ∂firstReturn n z, z.2 + cost 3 ≤ y.2 := by
  rw [firstReturn]
  apply Kernel.ae_comp_of_ae_ae (measurableSet_le measurable_const measurable_snd)
  filter_upwards [costKilled_pow_cost_monotone n z] with y hy
  filter_upwards [captured_cost_lower y] with w hw
  linarith

theorem returnLaw_cost_lower (z : OddCost) : ∀ᵐ y ∂returnLaw z, z.2 + cost 3 ≤ y.2 := by
  rw [returnLaw, Kernel.sum_apply, Measure.ae_sum_iff]
  exact fun n => firstReturn_cost_lower n z

theorem cost_three : cost 3 = Real.log (4 / 3) := by
  unfold cost
  congr 1
  norm_num

theorem cycleCostLaw_lower : ∀ᵐ G ∂cycleCostLaw, Real.log (4 / 3) ≤ G := by
  change ∀ᵐ G ∂(returnLaw (RegenerationTails.regenerationState, 0)).map Prod.snd, Real.log (4 / 3) ≤ G
  apply (ae_map_iff measurable_snd.aemeasurable measurableSet_Ici).mpr
  have h := returnLaw_cost_lower (RegenerationTails.regenerationState, 0)
  simpa only [zero_add, cost_three] using h

theorem cycleCostLaw_positive : ∀ᵐ G ∂cycleCostLaw, 0 < G := by
  filter_upwards [cycleCostLaw_lower] with G hG
  exact lt_of_lt_of_le (by rw [← cost_three]; exact cost_pos (by norm_num)) hG

end NumberTheoryLean.CycleCostLower

end

section

namespace NumberTheoryLean.CycleDurationMoments

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open TransitionKernels PairedHitting PairedDrift PairedBlockContraction PairedCostProcess
open CostReturnLaw MarkedCycleLaw

theorem weighted_geometric_bound {m : ℕ} (hm : 0 < m) {ρ θ : ℝ}
    (hρ : 0 < ρ) (hθ : 0 < θ) (hrel : 4 * (m : ℝ) * θ = -Real.log ρ) (n : ℕ) :
    Real.exp (θ * (2 * ((n : ℝ) + 1))) * ρ ^ (n / m) ≤
      Real.exp (-Real.log ρ + 2 * θ) * (Real.exp (-2 * θ)) ^ n := by
  have hlog : Real.log ρ = -4 * (m : ℝ) * θ := by linarith
  have hmod : ((n % m : ℕ) : ℝ) < (m : ℝ) := by exact_mod_cast Nat.mod_lt n hm
  have hdiv : (n : ℝ) = (m : ℝ) * ((n / m : ℕ) : ℝ) + ((n % m : ℕ) : ℝ) := by
    have h : ((n % m : ℕ) : ℝ) + (m : ℝ) * ((n / m : ℕ) : ℝ) = (n : ℝ) := by
      exact_mod_cast Nat.mod_add_div n m
    linarith
  have he : θ * (2 * ((n : ℝ) + 1)) + ((n / m : ℕ) : ℝ) * Real.log ρ ≤
      (-Real.log ρ + 2 * θ) + (n : ℝ) * (-2 * θ) := by
    rw [hlog, hdiv]
    nlinarith [mul_nonneg hθ.le (sub_nonneg.mpr hmod.le)]
  calc
    _ = Real.exp (θ * (2 * ((n : ℝ) + 1)) + ((n / m : ℕ) : ℝ) * Real.log ρ) := by
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hρ]
    _ ≤ Real.exp ((-Real.log ρ + 2 * θ) + (n : ℝ) * (-2 * θ)) := Real.exp_le_exp.mpr he
    _ = _ := by rw [Real.exp_add, Real.exp_nat_mul]

end NumberTheoryLean.CycleDurationMoments

end

section

namespace NumberTheoryLean.CycleCostMoments

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostProcess CostReturnLaw
open MarkedCycleLaw CycleDurationMoments

theorem draw_cost_le_log_three {s : ℝ} (hs : 1 / 2 ≤ s) : cost s ≤ Real.log 3 := by
  have hs0 : 0 < s := by linarith
  have hi : 1 / s ≤ 2 := (div_le_iff₀ hs0).mpr (by linarith)
  unfold cost
  exact Real.log_le_log (by positivity) (by linarith)

theorem pairedCost_cost_upper (z : OddCost) :
    ∀ᵐ y ∂pairedCostKernel z, y.2 ≤ z.2 + 2 * Real.log 3 := by
  apply ae_iff.mpr
  simp only [not_le]
  change pairedCostKernel z {y : OddCost | z.2 + 2 * Real.log 3 < y.2} = 0
  rw [pairedCostKernel_apply z (measurableSet_lt measurable_const measurable_snd)]
  have he : {x : EvenState × OddState | (x.2, z.2 + cost x.1.1 + cost x.2.1) ∈
      {y : OddCost | z.2 + 2 * Real.log 3 < y.2}} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have h1 := draw_cost_le_log_three (s := x.1.1) (by linarith [x.1.2])
    have h2 := draw_cost_le_log_three (s := x.2.1) (by linarith [x.2.2])
    change z.2 + 2 * Real.log 3 < z.2 + cost x.1.1 + cost x.2.1 at hx
    linarith
  rw [he, measure_empty]

theorem costKilled_cost_upper (z : OddCost) :
    ∀ᵐ y ∂costKilled z, y.2 ≤ z.2 + 2 * Real.log 3 := ae_restrict_of_ae (pairedCost_cost_upper z)

theorem costKilled_pow_cost_upper (n : ℕ) (z : OddCost) :
    ∀ᵐ y ∂(costKilled ^ n) z, y.2 ≤ z.2 + 2 * (n : ℝ) * Real.log 3 := by
  induction n generalizing z with
  | zero =>
    simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]
    change ∀ᵐ y ∂Measure.dirac z, y.2 ≤ z.2
    exact (ae_dirac_iff (measurableSet_le measurable_snd measurable_const)).mpr le_rfl
  | succ n ih =>
    have hp : costKilled ^ (n + 1) = costKilled ∘ₖ (costKilled ^ n) := pow_succ' costKilled n
    rw [hp]
    apply Kernel.ae_comp_of_ae_ae (measurableSet_le measurable_snd measurable_const)
    filter_upwards [ih z] with y hy
    filter_upwards [costKilled_cost_upper y] with w hw
    push_cast
    nlinarith

end NumberTheoryLean.CycleCostMoments

end

section

namespace NumberTheoryLean.CycleOccupation

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostProcess PairedCostGrouping
open CostReturnLaw CycleCostLower CycleCostMoments

theorem evenVisitMap_measurable : Measurable evenVisitMap :=
  (measurable_inl.comp (measurable_fst.comp measurable_snd)).prodMk
    ((measurable_snd.comp measurable_fst).add
      (cost_measurable.comp (measurable_subtype_coe.comp (measurable_fst.comp measurable_snd))))

theorem oddVisitMap_measurable : Measurable oddVisitMap :=
  (measurable_inr.comp (measurable_snd.comp measurable_snd)).prodMk
    (((measurable_snd.comp measurable_fst).add
      (cost_measurable.comp (measurable_subtype_coe.comp (measurable_fst.comp measurable_snd)))).add
      (cost_measurable.comp (measurable_subtype_coe.comp (measurable_snd.comp measurable_snd))))

instance evenVisit_isMarkovKernel : IsMarkovKernel evenVisit := Kernel.IsMarkovKernel.map _ evenVisitMap_measurable
instance oddVisit_isMarkovKernel : IsMarkovKernel oddVisit := Kernel.IsMarkovKernel.map _ oddVisitMap_measurable

theorem sampling_map_measure {α : Type*} [MeasurableSpace α]
    (f : OddCost × (EvenState × OddState) → α) (hf : Measurable f) (z : OddCost) :
    (pairSampling.map f) z = (pairedDraws z.1).map (fun x => f (z, x)) := by
  ext B hB
  rw [Kernel.map_apply' _ hf _ hB, pairSampling,
    Kernel.prod_apply' _ _ _ (hf hB), Kernel.id_apply, lintegral_dirac']
  · rw [Measure.map_apply (f := fun x : EvenState × OddState => f (z, x)) (hf.comp measurable_prodMk_left) hB]
    rfl
  · exact measurable_measure_prodMk_left (hf hB)

theorem evenVisit_eq_full_step (z : OddCost) : evenVisit z = costKernel (embedOdd z) := by
  apply Measure.ext_of_lintegral
  intro H hH
  rw [evenVisit, sampling_map_measure _ evenVisitMap_measurable,
    lintegral_map (g := fun x : EvenState × OddState => evenVisitMap (z, x)) hH
      (evenVisitMap_measurable.comp measurable_prodMk_left), pairedDraws,
    Kernel.lintegral_compProd _ _ _ (f := fun x : EvenState × OddState => H (evenVisitMap (z, x)))
      (hH.comp (evenVisitMap_measurable.comp measurable_prodMk_left))]
  change (∫⁻ t : EvenState, ∫⁻ _u : OddState, H (.inl t, z.2 + cost t.1) ∂evenToOdd t ∂oddToEven z.1) = _
  simp only [lintegral_const, measure_univ, mul_one]
  exact (costKernel_odd_lintegral z.1 z.2 hH).symm

theorem oddVisit_eq_paired (z : OddCost) : oddVisit z = (pairedCostKernel z).map embedOdd := by
  have h : oddVisit = pairedCostKernel.map embedOdd := by
    rw [oddVisit, pairedCostKernel, ← Kernel.map_comp_right _ pairUpdate_measurable embedOdd_measurable]
    rfl
  rw [h, Kernel.map_apply _ embedOdd_measurable]

instance pairVisits_isFiniteKernel : IsFiniteKernel pairVisits := by unfold pairVisits; infer_instance

theorem pairVisits_mass (z : OddCost) : pairVisits z univ = 2 := by
  rw [pairVisits, add_apply, Measure.add_apply]
  simp only [measure_univ]
  norm_num

theorem evenVisit_age_bounds (z : OddCost) :
    ∀ᵐ y ∂evenVisit z, z.2 ≤ y.2 ∧ y.2 ≤ z.2 + 2 * Real.log 3 := by
  rw [evenVisit, sampling_map_measure _ evenVisitMap_measurable]
  apply (ae_map_iff (evenVisitMap_measurable.comp measurable_prodMk_left).aemeasurable
    ((measurableSet_le measurable_const measurable_snd).inter (measurableSet_le measurable_snd measurable_const))).mpr
  apply Eventually.of_forall
  intro x
  have hp : 0 < cost x.1.1 := cost_pos (by linarith [x.1.2])
  have hu := draw_cost_le_log_three (s := x.1.1) (by linarith [x.1.2])
  have hL : 0 < Real.log 3 := Real.log_pos (by norm_num)
  change z.2 ≤ z.2 + cost x.1.1 ∧ z.2 + cost x.1.1 ≤ z.2 + 2 * Real.log 3
  constructor <;> linarith

theorem oddVisit_age_bounds (z : OddCost) :
    ∀ᵐ y ∂oddVisit z, z.2 ≤ y.2 ∧ y.2 ≤ z.2 + 2 * Real.log 3 := by
  rw [oddVisit, sampling_map_measure _ oddVisitMap_measurable]
  apply (ae_map_iff (oddVisitMap_measurable.comp measurable_prodMk_left).aemeasurable
    ((measurableSet_le measurable_const measurable_snd).inter (measurableSet_le measurable_snd measurable_const))).mpr
  apply Eventually.of_forall
  intro x
  have hp : 0 < cost x.1.1 := cost_pos (by linarith [x.1.2])
  have hq : 0 < cost x.2.1 := cost_pos (by linarith [x.2.2])
  have hu := draw_cost_le_log_three (s := x.1.1) (by linarith [x.1.2])
  have hv := draw_cost_le_log_three (s := x.2.1) (by linarith [x.2.2])
  change z.2 ≤ z.2 + cost x.1.1 + cost x.2.1 ∧
    z.2 + cost x.1.1 + cost x.2.1 ≤ z.2 + 2 * Real.log 3
  constructor <;> linarith

theorem pairVisits_age_bounds (z : OddCost) :
    ∀ᵐ y ∂pairVisits z, z.2 ≤ y.2 ∧ y.2 ≤ z.2 + 2 * Real.log 3 := by
  rw [pairVisits, add_apply, ae_add_measure_iff]
  exact ⟨evenVisit_age_bounds z, oddVisit_age_bounds z⟩

instance visitBlock_isFiniteKernel (n : ℕ) : IsFiniteKernel (visitBlock n) := by unfold visitBlock; infer_instance

theorem visitBlock_mass (n : ℕ) (z : OddCost) : visitBlock n z univ = 2 * (costKilled ^ n) z univ := by
  rw [visitBlock, Kernel.comp_apply' _ _ _ MeasurableSet.univ]
  simp only [pairVisits_mass, lintegral_const]

theorem visitBlock_age_bounds (n : ℕ) (z : OddCost) :
    ∀ᵐ y ∂visitBlock n z, z.2 ≤ y.2 ∧ y.2 ≤ z.2 + 2 * ((n + 1 : ℕ) : ℝ) * Real.log 3 := by
  rw [visitBlock]
  apply Kernel.ae_comp_of_ae_ae
    ((measurableSet_le measurable_const measurable_snd).inter (measurableSet_le measurable_snd measurable_const))
  filter_upwards [costKilled_pow_cost_monotone n z, costKilled_pow_cost_upper n z] with w hwL hwU
  filter_upwards [pairVisits_age_bounds w] with y hy
  constructor
  · exact le_trans hwL hy.1
  · calc
      y.2 ≤ w.2 + 2 * Real.log 3 := hy.2
      _ ≤ (z.2 + 2 * (n : ℝ) * Real.log 3) + 2 * Real.log 3 := add_le_add hwU le_rfl
      _ = _ := by push_cast <;> ring

instance occupationKernel_isSFiniteKernel : IsSFiniteKernel occupationKernel := by unfold occupationKernel; infer_instance

theorem occupation_age_nonneg : ∀ᵐ y ∂occupationMeasure, 0 ≤ y.2 := by
  rw [occupationMeasure, occupationKernel, Kernel.sum_apply, Measure.ae_sum_iff]
  intro n
  exact (visitBlock_age_bounds n (RegenerationTails.regenerationState, 0)).mono (fun _ h => h.1)

theorem occupationFrom_exponential_moment : ∃ η : ℝ, 0 < η ∧ ∀ z : OddCost,
    (∫⁻ y, ENNReal.ofReal (Real.exp (η * (y.2 - z.2))) ∂occupationKernel z) < ∞ := by
  obtain ⟨m, hm, ρ, D, hρ, hρ1, hD, hb⟩ := PairedBlockContraction.paired_survival_geometric
  let θ := -Real.log ρ / (4 * (m : ℝ))
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hθ : 0 < θ := div_pos (neg_pos.mpr (Real.log_neg hρ hρ1)) (by positivity)
  have hrel : 4 * (m : ℝ) * θ = -Real.log ρ := by dsimp [θ]; field_simp
  have hL : 0 < Real.log 3 := Real.log_pos (by norm_num)
  let η := θ / Real.log 3
  have hη : 0 < η := div_pos hθ hL
  refine ⟨η, hη, ?_⟩
  intro z
  let A := 2 * Real.exp (-Real.log ρ + 2 * θ) * (PairedDrift.V z.1 + D)
  let r := Real.exp (-2 * θ)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hsum : Summable (fun n : ℕ => A * r ^ n) := (summable_geometric_of_lt_one hr0 hr1).mul_left A
  rw [occupationKernel, Kernel.sum_apply, lintegral_sum_measure]
  apply lt_of_le_of_lt (ENNReal.tsum_le_tsum ?_) hsum.tsum_ofReal_lt_top
  intro n
  have hW : 0 < PairedDrift.V z.1 + D := add_pos (PairedDrift.V_pos z.1) hD
  have hn := CycleDurationMoments.weighted_geometric_bound hm hρ hθ hrel n
  have hsurv : (costKilled ^ n) z univ ≤ ENNReal.ofReal (ρ ^ (n / m) * (PairedDrift.V z.1 + D)) := by
    rw [costKilled_mass]
    exact le_trans (PairedHitting.paired_survival_antitone z.1 (Nat.mul_div_le n m)) (hb (n / m) z.1)
  calc
    _ ≤ ∫⁻ _y, ENNReal.ofReal (Real.exp (θ * (2 * ((n : ℝ) + 1)))) ∂visitBlock n z := by
      apply lintegral_mono_ae
      filter_upwards [visitBlock_age_bounds n z] with y hy
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      calc
        η * (y.2 - z.2) ≤ η * (2 * ((n + 1 : ℕ) : ℝ) * Real.log 3) :=
          mul_le_mul_of_nonneg_left (by linarith [hy.2]) hη.le
        _ = θ * (2 * ((n : ℝ) + 1)) := by dsimp [η]; push_cast; field_simp
    _ = ENNReal.ofReal (Real.exp (θ * (2 * ((n : ℝ) + 1)))) *
        (2 * (costKilled ^ n) z univ) := by rw [lintegral_const, visitBlock_mass]
    _ ≤ ENNReal.ofReal (Real.exp (θ * (2 * ((n : ℝ) + 1)))) *
        (2 * ENNReal.ofReal (ρ ^ (n / m) * (PairedDrift.V z.1 + D))) :=
      mul_le_mul le_rfl (mul_le_mul le_rfl hsurv zero_le zero_le) zero_le zero_le
    _ = ENNReal.ofReal (2 * (Real.exp (θ * (2 * ((n : ℝ) + 1)))) * ρ ^ (n / m) * (PairedDrift.V z.1 + D)) := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ← ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (A * r ^ n) := ENNReal.ofReal_le_ofReal (by
      dsimp [A, r]
      nlinarith [mul_le_mul_of_nonneg_right hn hW.le])

theorem occupation_exponential_moment : ∃ η : ℝ, 0 < η ∧
    (∫⁻ y, ENNReal.ofReal (Real.exp (η * y.2)) ∂occupationMeasure) < ∞ := by
  obtain ⟨η, hη, hb⟩ := occupationFrom_exponential_moment
  exact ⟨η, hη, by simpa only [occupationMeasure, sub_zero] using hb (RegenerationTails.regenerationState, 0)⟩

instance occupationMeasure_isFiniteMeasure : IsFiniteMeasure occupationMeasure := by
  obtain ⟨η, hη, hb⟩ := occupation_exponential_moment
  constructor
  apply lt_of_le_of_lt (show occupationMeasure univ ≤ ∫⁻ y, ENNReal.ofReal (Real.exp (η * y.2)) ∂occupationMeasure from ?_) hb
  calc
    _ = ∫⁻ _y, (1 : ℝ≥0∞) ∂occupationMeasure := by simp
    _ ≤ _ := by
      apply lintegral_mono_ae
      filter_upwards [occupation_age_nonneg] with y hy
      exact ENNReal.one_le_ofReal.mpr (Real.one_le_exp (mul_nonneg hη.le hy))

theorem occupation_exponential_integrable : ∃ η : ℝ, 0 < η ∧
    Integrable (fun y : CostState => Real.exp (η * y.2)) occupationMeasure := by
  obtain ⟨η, hη, hb⟩ := occupation_exponential_moment
  refine ⟨η, hη, (Real.measurable_exp.comp (measurable_const.mul measurable_snd)).aestronglyMeasurable, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall
    (fun y : CostState => (Real.exp_pos (η * y.2)).le))).mpr hb

end NumberTheoryLean.CycleOccupation

end

section

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
namespace Erdos970Dependency.ActualCycleOccupation
open NumberTheoryLean.TransitionKernels NumberTheoryLean.FinitePathGeometry NumberTheoryLean.FinitePathMeasures
open NumberTheoryLean.PairedHitting NumberTheoryLean.PairedCostProcess NumberTheoryLean.PairedCostGrouping
open NumberTheoryLean.CostReturnLaw NumberTheoryLean.CycleOccupation NumberTheoryLean.KernelPotential
open Erdos970Dependency.InvariantDensities Erdos970Dependency.StateKernelInvariance
open Erdos970Dependency.RegenerativeOddOccupation

theorem costKernel_map_state (z : CostState) : (costKernel z).map Prod.fst = stateKernel z.1 := by
  have hm : Measurable (fun s : State ↦ (s, z.2 + cost (stateRatio s))) :=
    measurable_id.prodMk (measurable_const.add (cost_measurable.comp stateRatio_measurable))
  rw [costKernel_eq_map, Measure.map_map measurable_fst hm]
  change (stateKernel z.1).map id = stateKernel z.1
  exact Measure.map_id

theorem evenVisit_map_state (z : OddCost) :
    (evenVisit z).map Prod.fst = (oddToEven z.1).map Sum.inl := by
  rw [evenVisit_eq_full_step, costKernel_map_state]
  change oddBranch z.1 = _
  exact Kernel.map_apply _ measurable_inl _

theorem oddVisit_map_state (z : OddCost) :
    (oddVisit z).map Prod.fst = (pairedOdd z.1).map Sum.inr := by
  rw [oddVisit_eq_paired, Measure.map_map measurable_fst embedOdd_measurable,
    ← pairedCost_map_state z, Measure.map_map measurable_inr measurable_fst]
  rfl

theorem pairVisits_map_state (z : OddCost) : (pairVisits z).map Prod.fst = ratioVisits z.1 := by
  rw [pairVisits, add_apply, Measure.map_add _ _ measurable_fst, evenVisit_map_state, oddVisit_map_state]
  simp only [ratioVisits, add_apply, Kernel.map_apply _ measurable_inl, Kernel.map_apply _ measurable_inr]

theorem visitBlock_map_state (n : ℕ) (z : OddCost) :
    (visitBlock n z).map Prod.fst = (ratioVisits ∘ₖ (pairedKilled ^ n)) z.1 := by
  apply Measure.ext_of_lintegral
  intro H hH
  rw [lintegral_map hH measurable_fst, visitBlock,
    Kernel.lintegral_comp _ _ _ (g := fun y : CostState ↦ H y.1) (hH.comp measurable_fst),
    Kernel.lintegral_comp _ _ _ hH]
  have hi (w : OddCost) : (∫⁻ y : CostState, H y.1 ∂pairVisits w) =
      ∫⁻ s : State, H s ∂ratioVisits w.1 := by
    rw [← pairVisits_map_state w, lintegral_map hH measurable_fst]
  simp_rw [hi]
  have hJ : Measurable (fun s : OddState ↦ ∫⁻ t : State, H t ∂ratioVisits s) := hH.lintegral_kernel
  rw [← costKilled_pow_map_state n z, lintegral_map hJ measurable_fst]

theorem occupation_map_ratioOccupation : occupationMeasure.map Prod.fst = ratioOccupation := by
  rw [occupationMeasure, occupationKernel, Kernel.sum_apply, Measure.map_sum measurable_fst.aemeasurable]
  simp_rw [visitBlock_map_state]
  rw [ratioOccupation, potential, Kernel.sum_apply]

theorem occupation_map_stateMeasure :
    occupationMeasure.map Prod.fst = (ENNReal.ofReal beta)⁻¹ • stateMeasure := by
  rw [occupation_map_ratioOccupation, ratioOccupation_eq]

theorem integrable_state_occupation_iff {Q : State → ℝ} (hQ : Measurable Q) :
    Integrable Q stateMeasure ↔ Integrable (fun y : CostState ↦ Q y.1) occupationMeasure := by
  have h := integrable_map_measure (μ := occupationMeasure) (f := Prod.fst) (g := Q)
    hQ.aestronglyMeasurable measurable_fst.aemeasurable
  rw [occupation_map_stateMeasure, integrable_inv_smul_measure
    (ne_of_gt (ENNReal.ofReal_pos.mpr beta_pos)) ENNReal.ofReal_ne_top] at h
  simpa only [Function.comp_def] using h

theorem integral_state_occupation {Q : State → ℝ} (hQ : Measurable Q)
    (hI : Integrable (fun y : CostState ↦ Q y.1) occupationMeasure) :
    Integrable Q stateMeasure ∧
      (∫ y : CostState, Q y.1 ∂occupationMeasure) = (1 / InvariantDensities.beta) * ∫ s : State, Q s ∂stateMeasure := by
  refine ⟨(integrable_state_occupation_iff hQ).mpr hI, ?_⟩
  rw [← integral_map measurable_fst.aemeasurable hQ.aestronglyMeasurable,
    occupation_map_stateMeasure, integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal beta_pos.le, smul_eq_mul, one_div]

end Erdos970Dependency.ActualCycleOccupation

end

section

open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory Topology
namespace Erdos970Dependency.OccupationAge
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess NumberTheoryLean.PairedCostGrouping
open NumberTheoryLean.CostReturnLaw NumberTheoryLean.CycleOccupation NumberTheoryLean.RegenerationTails

theorem oddAge_measurable : Measurable (fun y : OddCost ↦ ENNReal.ofReal y.2) :=
  ENNReal.measurable_ofReal.comp measurable_snd

theorem stateAge_measurable : Measurable (fun y : CostState ↦ ENNReal.ofReal y.2) :=
  ENNReal.measurable_ofReal.comp measurable_snd

theorem occupation_age_integrable : Integrable (fun y : CostState ↦ y.2) occupationMeasure := by
  obtain ⟨eta, heta, hI⟩ := occupation_exponential_integrable
  apply (hI.const_mul (1 / eta)).mono' measurable_snd.aestronglyMeasurable
  filter_upwards [occupation_age_nonneg] with y hy
  rw [Real.norm_of_nonneg hy]
  have h := Real.add_one_le_exp (eta * y.2)
  calc
    y.2 = (1 / eta) * (eta * y.2) := by field_simp
    _ ≤ (1 / eta) * Real.exp (eta * y.2) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem blockAge_sum_finite : (∑' n : ℕ, blockAge n) < ∞ := by
  have heq : (∑' n : ℕ, blockAge n) = ∫⁻ y : CostState, ENNReal.ofReal y.2 ∂occupationMeasure := by
    rw [occupationMeasure, occupationKernel, Kernel.sum_apply, lintegral_sum_measure]
    rfl
  rw [heq, ← ofReal_integral_eq_lintegral_ofReal occupation_age_integrable occupation_age_nonneg]
  exact ENNReal.ofReal_lt_top

theorem blockAge_tendsto_zero : Tendsto blockAge atTop (𝓝 0) :=
  ENNReal.tendsto_atTop_zero_of_tsum_ne_top (ne_of_lt blockAge_sum_finite)

theorem killed_age_le_pair (z : OddCost) :
    (∫⁻ y : OddCost, ENNReal.ofReal y.2 ∂costKilled z) ≤
      ∫⁻ y : CostState, ENNReal.ofReal y.2 ∂pairVisits z := by
  calc
    _ ≤ ∫⁻ y : OddCost, ENNReal.ofReal y.2 ∂pairedCostKernel z :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ = ∫⁻ y : CostState, ENNReal.ofReal y.2 ∂oddVisit z := by
      rw [oddVisit_eq_paired, lintegral_map stateAge_measurable embedOdd_measurable]
      rfl
    _ ≤ _ := lintegral_mono' (by
      rw [pairVisits, add_apply]
      apply Measure.le_iff.mpr
      intro B _
      rw [Measure.add_apply]
      exact le_add_left le_rfl) le_rfl

theorem residualAge_succ_le (n : ℕ) : residualAge (n + 1) ≤ blockAge n := by
  have hp : costKilled ^ (n + 1) = costKilled ∘ₖ (costKilled ^ n) := pow_succ' costKilled n
  rw [residualAge, hp,
    Kernel.lintegral_comp _ _ _ oddAge_measurable,
    blockAge, visitBlock,
    Kernel.lintegral_comp _ _ _ stateAge_measurable]
  exact lintegral_mono killed_age_le_pair

theorem residualAge_tendsto_zero : Tendsto residualAge atTop (𝓝 0) := by
  have hshift : Tendsto (fun n : ℕ ↦ residualAge (n + 1)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds blockAge_tendsto_zero
      (Eventually.of_forall (fun _ ↦ zero_le)) (Eventually.of_forall residualAge_succ_le)
  exact (tendsto_add_atTop_iff_nat 1).mp hshift

end Erdos970Dependency.OccupationAge

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_UniformCycleMoments
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.InitialRegeneration.hitOrReturn_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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
open PairedCostProcess CostReturnLaw CycleOccupation MinorizingCostRegularity

 theorem stateRatio_pos (s : State) : 0 < stateRatio s := by
  cases s with
  | inl s => change 0 < s.1; linarith [s.2]
  | inr s => change 0 < s.1; linarith [s.2]

end NumberTheoryLean.OccupationBoundaries



namespace NumberTheoryLean.AdmissibleCycleTests

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathMeasures CycleOccupation OccupationBoundaries CycleResponse

theorem HasCompactBound.mask {F : Test} (hF : HasCompactBound F) (B : Set (ℝ × State)) :
    HasCompactBound (mask B F) := by
  classical
  obtain ⟨C, M, hC, hM, hb, hs⟩ := hF
  refine ⟨C, M, hC, hM, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ B
    · simpa [AdmissibleCycleTests.mask, hx] using hb x
    · simpa [AdmissibleCycleTests.mask, hx] using hC
  · intro x hx
    by_cases h : x ∈ B <;> simp [AdmissibleCycleTests.mask, h, hs x hx]

theorem HasCompactBound.add {F G : Test} (hF : HasCompactBound F) (hG : HasCompactBound G) :
    HasCompactBound (fun x => F x + G x) := by
  obtain ⟨C, M, hC, hM, hb, hs⟩ := hF
  obtain ⟨D, N, hD, hN, hb', hs'⟩ := hG
  refine ⟨C + D, max M N, add_nonneg hC hD, le_trans hM (le_max_left _ _), ?_, ?_⟩
  · intro x
    exact le_trans (norm_add_le _ _) (add_le_add (hb x) (hb' x))
  · intro x hx
    change F x + G x = 0
    rw [hs x (lt_of_le_of_lt (le_max_left _ _) hx), hs' x (lt_of_le_of_lt (le_max_right _ _) hx), add_zero]

theorem HasCompactBound.scale {F : Test} (hF : HasCompactBound F) (c : ℝ) :
    HasCompactBound (fun x => c * F x) := by
  obtain ⟨C, M, hC, hM, hb, hs⟩ := hF
  refine ⟨‖c‖ * C, M, mul_nonneg (norm_nonneg _) hC, hM, ?_, ?_⟩
  · intro x
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _)
  · intro x hx
    change c * F x = 0
    rw [hs x hx, mul_zero]

theorem Admissible.measurable {F : Test} (hF : Admissible F) : Measurable F := by
  induction hF with
  | base hf _ _ => exact hf
  | upper _ a ih => exact ih.indicator (measurableSet_le measurable_fst measurable_const)
  | upperOpen _ a ih => exact ih.indicator (measurableSet_lt measurable_fst measurable_const)
  | state _ B hB ih => exact ih.indicator (measurable_snd hB)
  | arrival _ ell _ ih =>
    exact ih.indicator (measurableSet_lt (stateRatio_measurable.comp measurable_snd)
      ((Real.measurable_exp.comp measurable_fst).div_const ell))
  | add _ _ ihF ihG => exact ihF.add ihG
  | scale _ c ih => exact measurable_const.mul ih

theorem Admissible.compactBound {F : Test} (hF : Admissible F) : HasCompactBound F := by
  induction hF with
  | base _ _ hb => exact hb
  | upper _ _ ih => exact ih.mask _
  | upperOpen _ _ ih => exact ih.mask _
  | state _ _ _ ih => exact ih.mask _
  | arrival _ _ _ ih => exact ih.mask _
  | add _ _ ihF ihG => exact ihF.add ihG
  | scale _ c ih => exact ih.scale c

end NumberTheoryLean.AdmissibleCycleTests



namespace NumberTheoryLean.OccupationDecomposition

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathMeasures PairedCostProcess PairedCostGrouping
open CostReturnLaw CycleOccupation KernelPotential

instance pairedOccupation_isSFiniteKernel : IsSFiniteKernel pairedOccupation := by
  unfold pairedOccupation
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end NumberTheoryLean.OccupationDecomposition



namespace NumberTheoryLean.CycleResponseFubini

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathMeasures CycleOccupation CycleResponse AdmissibleCycleTests

theorem ageShear_measurePreserving : MeasurePreserving ageShear
    (occupationMeasure.prod volume) (occupationMeasure.prod volume) := by
  apply MeasurePreserving.skew_product (g := fun y : CostState => fun u : ℝ => u - y.2) (MeasurePreserving.id occupationMeasure)
    (measurable_snd.sub (measurable_snd.comp measurable_fst))
  apply Eventually.of_forall
  intro y
  simpa only [sub_eq_add_neg] using map_add_right_eq_self (volume : Measure ℝ) (-y.2)

theorem unshifted_test_product_integrable {F : Test} (hF : Measurable F)
    (hB : HasCompactBound F) :
    Integrable (fun x : CostState × ℝ => F (x.2, x.1.1)) (occupationMeasure.prod volume) := by
  classical
  obtain ⟨C, M, hC, hM, hb, hs⟩ := hB
  have hi : Integrable ((Icc (-M) M).indicator (fun _ : ℝ => (1 : ℝ))) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const isCompact_Icc.measure_ne_top)
  have hprod := (integrable_const C : Integrable (fun _ : CostState => C) occupationMeasure).mul_prod hi
  refine hprod.mono' (hF.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))).aestronglyMeasurable ?_
  apply Eventually.of_forall
  intro x
  by_cases hx : x.2 ∈ Icc (-M) M
  · simpa only [indicator_of_mem hx, mul_one] using hb (x.2, x.1.1)
  · have habs : M < |x.2| := by
      apply lt_of_not_ge
      intro hu
      exact hx (abs_le.mp hu)
    rw [hs (x.2, x.1.1) habs, norm_zero, indicator_of_notMem hx, mul_zero]

theorem shifted_test_product_integrable {F : Test} (hF : Measurable F)
    (hB : HasCompactBound F) :
    Integrable (fun x : CostState × ℝ => F (x.2 - x.1.2, x.1.1)) (occupationMeasure.prod volume) := by
  exact ageShear_measurePreserving.integrable_comp_of_integrable (unshifted_test_product_integrable hF hB)

theorem integrated_test_occupation_integrable {F : Test} (hF : Measurable F)
    (hB : HasCompactBound F) :
    Integrable (fun y : CostState => ∫ u : ℝ, F (u, y.1)) occupationMeasure :=
  (unshifted_test_product_integrable hF hB).integral_prod_left

theorem integral_response_eq_occupation {F : Test} (hF : Measurable F)
    (hB : HasCompactBound F) :
    (∫ v : ℝ, response F v) = ∫ y : CostState, (∫ u : ℝ, F (u, y.1)) ∂occupationMeasure := by
  calc
    _ = ∫ y : CostState, (∫ u : ℝ, F (u - y.2, y.1)) ∂occupationMeasure :=
      (integral_integral_swap (shifted_test_product_integrable hF hB)).symm
    _ = _ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro y
      exact integral_sub_right_eq_self (fun u : ℝ => F (u, y.1)) y.2

end NumberTheoryLean.CycleResponseFubini



namespace NumberTheoryLean.OccupationConstant

open Set MeasureTheory
open FinitePathMeasures CycleResponse CycleResponseFubini AdmissibleCycleTests
open Erdos970Dependency.InvariantDensities Erdos970Dependency.StateKernelInvariance
open Erdos970Dependency.ActualCycleOccupation

theorem integratedStateTest_measurable {F : Test} (hF : Measurable F) :
    Measurable (integratedStateTest F) := hF.stronglyMeasurable.integral_prod_left'.measurable

theorem response_integral_eq_invariant {F : Test} (hF : Measurable F) (hB : HasCompactBound F) :
    Integrable (integratedStateTest F) stateMeasure ∧
      (∫ v : ℝ, response F v) = (1 / Erdos970Dependency.InvariantDensities.beta) * ∫ s : State, integratedStateTest F s ∂stateMeasure := by
  obtain ⟨hI, hEq⟩ := integral_state_occupation (integratedStateTest_measurable hF)
    (integrated_test_occupation_integrable hF hB)
  refine ⟨hI, ?_⟩
  rw [integral_response_eq_occupation hF hB]
  exact hEq

end NumberTheoryLean.OccupationConstant



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_DeficitIntegralValues
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set MeasureTheory
namespace Erdos970Dependency.DeficitIntegralValues
open NumberTheoryLean.LinearSieveFunctions NumberTheoryLean.BuchstabBridge
open NumberTheoryLean.NormalizedDeficits NumberTheoryLean.DeficitFutureIntegrals

theorem shift_indicator (f : ℝ → ℝ) (a d : ℝ) :
    (fun s ↦ (Ioi a).indicator f (s - d)) = (Ioi (a + d)).indicator (fun s ↦ f (s - d)) := by
  funext s
  by_cases hs : a + d < s
  · rw [indicator_of_mem (show s ∈ Ioi (a + d) from hs),
      indicator_of_mem (show s - d ∈ Ioi a by change a < s - d; linarith)]
  · rw [indicator_of_notMem (show s ∉ Ioi (a + d) from hs),
      indicator_of_notMem (show s - d ∉ Ioi a by change ¬a < s - d; linarith)]

theorem integrableOn_shift_Ioi {f : ℝ → ℝ} {a : ℝ} (hf : IntegrableOn f (Ioi a)) (d : ℝ) :
    IntegrableOn (fun s ↦ f (s - d)) (Ioi (a + d)) := by
  have h := ((integrable_indicator_iff measurableSet_Ioi).mpr hf).comp_sub_right d
  rw [shift_indicator] at h
  exact (integrable_indicator_iff measurableSet_Ioi).mp h

theorem integral_shift_Ioi (f : ℝ → ℝ) (a d : ℝ) :
    (∫ s in Ioi (a + d), f (s - d)) = ∫ s in Ioi a, f s := by
  have h := integral_sub_right_eq_self (μ := (volume : Measure ℝ)) ((Ioi a).indicator f) d
  rw [shift_indicator, integral_indicator measurableSet_Ioi, integral_indicator measurableSet_Ioi] at h
  exact h

theorem upper_integral_one : IntegrableOn upperDeficit (Ioi (1 : ℝ)) ∧
    (∫ s in Ioi (1 : ℝ), upperDeficit s) = 2 := by
  have h := lower_future_integral (s := 2) (by norm_num)
  norm_num only [show (2 : ℝ) - 1 = 1 by norm_num] at h
  refine ⟨h.1, ?_⟩
  rw [← h.2]
  norm_num [lowerDeficit, f_initial sieveA (s := 2) (by norm_num)]

theorem lower_integral_two : IntegrableOn lowerDeficit (Ioi (2 : ℝ)) ∧
    (∫ s in Ioi (2 : ℝ), lowerDeficit s) = sieveA - 3 := by
  have h := upper_future_integral (s := 3) (by norm_num)
  norm_num only [show (3 : ℝ) - 1 = 2 by norm_num] at h
  refine ⟨h.1, ?_⟩
  rw [← h.2]
  simp only [upperDeficit, F_initial sieveA (s := 3) (by norm_num) (by norm_num)]
  ring

theorem even_majorant_integral :
    IntegrableOn (fun s ↦ lowerDeficit s + upperDeficit (s - 1)) (Ici (2 : ℝ)) ∧
      (∫ s in Ici (2 : ℝ), lowerDeficit s + upperDeficit (s - 1)) = sieveA - 1 := by
  have ha := lower_integral_two.1
  have hc : IntegrableOn (fun s ↦ upperDeficit (s - 1)) (Ioi (2 : ℝ)) := by
    simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using integrableOn_shift_Ioi upper_integral_one.1 1
  refine ⟨Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi (ha.add hc), ?_⟩
  rw [integral_Ici_eq_integral_Ioi, integral_add ha hc, lower_integral_two.2]
  have h := integral_shift_Ioi upperDeficit 1 1
  norm_num only [show (1 : ℝ) + 1 = 2 by norm_num] at h
  rw [h, upper_integral_one.2]
  ring

end Erdos970Dependency.DeficitIntegralValues

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_OnePairCost
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.CycleConvolutionLaw.returnLaw_pow_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.InitialRegeneration.hitOrReturn_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OccupationDecomposition.pairedOccupation_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set MeasureTheory
namespace Erdos970Dependency.InvariantCostBound
open NumberTheoryLean NumberTheoryLean.BuchstabBridge NumberTheoryLean.DerivativeWeights
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.FinitePathMeasures
open NumberTheoryLean.NormalizedDeficits NumberTheoryLean.DeficitFutureIntegrals
open Erdos970Dependency.InvariantDensities Erdos970Dependency.DeficitIntegralValues

theorem cost_le_inv {s : ℝ} (hs : 0 < s) : cost s ≤ 1 / s := by
  have h := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / s by positivity)
  change Real.log (1 + 1 / s) ≤ 1 / s
  linarith

theorem evenCost_nonneg (s : ℝ) : 0 ≤ evenCost s := by
  by_cases hs : 2 ≤ s
  · rw [evenCost, evenDensity, indicator_of_mem (show s ∈ Ici (2 : ℝ) from hs)]
    exact mul_nonneg (phiEven_pos (by linarith)).le (cost_pos (by linarith)).le
  · rw [evenCost, evenDensity, indicator_of_notMem (show s ∉ Ici (2 : ℝ) from hs), zero_mul]

theorem oddCost_nonneg (s : ℝ) : 0 ≤ oddCost s := by
  by_cases hs : 1 ≤ s
  · rw [oddCost]
    exact mul_nonneg (oddDensity_nonneg s) (cost_pos (by linarith)).le
  · rw [oddCost, oddDensity, indicator_of_notMem (show s ∉ Ici (1 : ℝ) from hs), zero_mul]

theorem evenCost_le_major (s : ℝ) : evenCost s ≤ evenMajor s := by
  by_cases hs : 2 ≤ s
  · rw [evenCost, evenDensity, evenMajor,
      indicator_of_mem (show s ∈ Ici (2 : ℝ) from hs), indicator_of_mem (show s ∈ Ici (2 : ℝ) from hs)]
    calc
      phiEven s * cost s ≤ phiEven s * (1 / s) :=
        mul_le_mul_of_nonneg_left (cost_le_inv (by linarith)) (phiEven_pos (by linarith)).le
      _ = _ := by rw [phiEven_eq_deficits hs]; field_simp
  · rw [evenCost, evenDensity, evenMajor,
      indicator_of_notMem (show s ∉ Ici (2 : ℝ) from hs),
      indicator_of_notMem (show s ∉ Ici (2 : ℝ) from hs), zero_mul]

theorem evenMajor_integrable : Integrable evenMajor :=
  (integrable_indicator_iff measurableSet_Ici).mpr even_majorant_integral.1

theorem evenCost_integrable : Integrable evenCost := by
  apply evenMajor_integrable.mono' (evenDensity_measurable.mul cost_measurable).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun s ↦ by
    change ‖evenCost s‖ ≤ evenMajor s
    rw [Real.norm_of_nonneg (evenCost_nonneg s)]
    exact evenCost_le_major s)

theorem even_cost_pos : 0 < ∫ s, evenCost s := by
  apply (integral_pos_iff_support_of_nonneg evenCost_nonneg evenCost_integrable).mpr
  have hsub : Icc (2 : ℝ) 3 ⊆ Function.support evenCost := by
    intro s hs
    apply ne_of_gt
    rw [evenCost, evenDensity, indicator_of_mem (show s ∈ Ici (2 : ℝ) from hs.1)]
    exact mul_pos (phiEven_pos (by linarith [hs.1])) (cost_pos (by linarith [hs.1]))
  exact lt_of_lt_of_le (by norm_num [Real.volume_Icc] : 0 < volume (Icc (2 : ℝ) 3)) (measure_mono hsub)

theorem costMass_pos : 0 < costMass :=
  add_pos_of_pos_of_nonneg even_cost_pos (integral_nonneg oddCost_nonneg)

end Erdos970Dependency.InvariantCostBound

end

section

open Set MeasureTheory ProbabilityTheory
namespace Erdos970Dependency.RawStateCost
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.FinitePathMeasures NumberTheoryLean.CycleCostMoments
open NumberTheoryLean.CycleOccupation
open Erdos970Dependency.InvariantDensities Erdos970Dependency.InvariantFiniteness
open Erdos970Dependency.OrdinaryKernelInvariance Erdos970Dependency.StateKernelInvariance
open Erdos970Dependency.InvariantCostBound Erdos970Dependency.ActualCycleOccupation

theorem stateCost_measurable : Measurable stateCost := cost_measurable.comp stateRatio_measurable

theorem stateCost_bounds (s : State) : 0 < stateCost s ∧ stateCost s ≤ Real.log 3 := by
  have hs : 1 / 2 ≤ stateRatio s := by
    cases s with
    | inl s => change 1 / 2 ≤ s.1; linarith [s.2]
    | inr s => change 1 / 2 ≤ s.1; linarith [s.2]
  exact ⟨cost_pos (by linarith), draw_cost_le_log_three hs⟩

theorem stateCost_integrable (mu : Measure State) [IsFiniteMeasure mu] : Integrable stateCost mu := by
  apply (integrable_const (Real.log 3)).mono' stateCost_measurable.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun s ↦ by
    rw [Real.norm_of_nonneg (stateCost_bounds s).1.le]
    exact (stateCost_bounds s).2)

theorem integral_evenMeasure (g : ℝ → ℝ) : (∫ s, g s ∂evenMeasure) =
    ∫ s, InvariantDensities.evenDensity s * g s := by
  have h := integral_withDensity_eq_integral_toReal_smul (μ := (volume : Measure ℝ))
    (ENNReal.measurable_ofReal.comp InvariantDensities.evenDensity_measurable)
    (Filter.Eventually.of_forall (fun _ : ℝ ↦ ENNReal.ofReal_lt_top)) g
  simpa only [evenMeasure, Function.comp_def, ENNReal.toReal_ofReal (InvariantDensities.evenDensity_nonneg _),
    smul_eq_mul] using h

theorem integral_oddMeasure (g : ℝ → ℝ) : (∫ s, g s ∂oddMeasure) =
    ∫ s, InvariantDensities.oddDensity s * g s := by
  have h := integral_withDensity_eq_integral_toReal_smul (μ := (volume : Measure ℝ))
    (ENNReal.measurable_ofReal.comp InvariantDensities.oddDensity_measurable)
    (Filter.Eventually.of_forall (fun _ : ℝ ↦ ENNReal.ofReal_lt_top)) g
  simpa only [oddMeasure, Function.comp_def, ENNReal.toReal_ofReal (InvariantDensities.oddDensity_nonneg _),
    smul_eq_mul] using h

theorem even_lifted_cost (s : ℝ) : InvariantDensities.evenDensity s * cost (evenLift s).1 = evenCost s := by
  by_cases hs : 2 ≤ s
  · have heq : (evenLift s).1 = s := max_eq_right (by linarith)
    rw [heq]
    rfl
  · rw [evenCost, InvariantDensities.evenDensity,
      indicator_of_notMem (show s ∉ Ici (2 : ℝ) from hs), zero_mul, zero_mul]

theorem odd_lifted_cost (s : ℝ) : InvariantDensities.oddDensity s * cost (oddLift s).1 = oddCost s := by
  by_cases hs : 1 ≤ s
  · have heq : (oddLift s).1 = s := max_eq_right (by linarith)
    rw [heq]
    rfl
  · rw [oddCost, InvariantDensities.oddDensity,
      indicator_of_notMem (show s ∉ Ici (1 : ℝ) from hs), zero_mul, zero_mul]

theorem state_cost_integral : (∫ s, stateCost s ∂stateMeasure) = costMass := by
  rw [stateMeasure, integral_add_measure (stateCost_integrable _) (stateCost_integrable _),
    integral_map measurable_inl.aemeasurable stateCost_measurable.aestronglyMeasurable,
    integral_map measurable_inr.aemeasurable stateCost_measurable.aestronglyMeasurable]
  simp only [stateCost, stateRatio, Sum.elim_inl, Sum.elim_inr]
  have he := integral_map (μ := evenMeasure) evenLift_measurable.aemeasurable
    (cost_measurable.comp (measurable_subtype_coe : Measurable
      (Subtype.val : NumberTheoryLean.TransitionKernels.EvenState → ℝ))).aestronglyMeasurable
  have ho := integral_map (μ := oddMeasure) oddLift_measurable.aemeasurable
    (cost_measurable.comp (measurable_subtype_coe : Measurable
      (Subtype.val : NumberTheoryLean.TransitionKernels.OddState → ℝ))).aestronglyMeasurable
  simp only [Function.comp_def] at he ho
  rw [evenStateMeasure, he, oddStateMeasure, ho, integral_evenMeasure, integral_oddMeasure]
  simp_rw [even_lifted_cost, odd_lifted_cost]
  rfl

theorem occupation_increment_integrable :
    Integrable (fun y : CostState ↦ stateCost y.1) occupationMeasure :=
  (integrable_state_occupation_iff stateCost_measurable).mp (stateCost_integrable stateMeasure)

theorem occupation_increment_integral :
    (∫ y : CostState, stateCost y.1 ∂occupationMeasure) = costMass / InvariantDensities.beta := by
  have h := (integral_state_occupation stateCost_measurable occupation_increment_integrable).2
  rw [state_cost_integral] at h
  simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul] using h

end Erdos970Dependency.RawStateCost

end

section

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
namespace Erdos970Dependency.OnePairCost
open NumberTheoryLean.TransitionKernels NumberTheoryLean.FinitePathGeometry NumberTheoryLean.FinitePathMeasures
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.CostReturnLaw NumberTheoryLean.CycleOccupation
open Erdos970Dependency.RawStateCost

theorem increment_test_measurable : Measurable (fun y : CostState ↦ ENNReal.ofReal (stateCost y.1)) :=
  ENNReal.measurable_ofReal.comp (stateCost_measurable.comp measurable_fst)

theorem age_test_measurable : Measurable (fun y : OddCost ↦ ENNReal.ofReal y.2) :=
  ENNReal.measurable_ofReal.comp measurable_snd

theorem even_increment_measurable :
    Measurable (fun x : EvenState × OddState ↦ ENNReal.ofReal (cost x.1.1)) :=
  ENNReal.measurable_ofReal.comp (cost_measurable.comp (measurable_subtype_coe.comp measurable_fst))

theorem pairIncrement_formula (z : OddCost) : pairIncrement z =
    ∫⁻ x : EvenState × OddState,
      ENNReal.ofReal (cost x.1.1) + ENNReal.ofReal (cost x.2.1) ∂pairedDraws z.1 := by
  rw [pairIncrement, pairVisits, add_apply, lintegral_add_measure,
    evenVisit, sampling_map_measure _ evenVisitMap_measurable,
    oddVisit, sampling_map_measure _ oddVisitMap_measurable,
    lintegral_map (g := fun x : EvenState × OddState ↦ evenVisitMap (z, x))
      increment_test_measurable (evenVisitMap_measurable.comp measurable_prodMk_left),
    lintegral_map (g := fun x : EvenState × OddState ↦ oddVisitMap (z, x))
      increment_test_measurable (oddVisitMap_measurable.comp measurable_prodMk_left)]
  change (∫⁻ x : EvenState × OddState, ENNReal.ofReal (cost x.1.1) ∂pairedDraws z.1) +
    (∫⁻ x : EvenState × OddState, ENNReal.ofReal (cost x.2.1) ∂pairedDraws z.1) = _
  exact (lintegral_add_left even_increment_measurable _).symm

theorem paired_age_balance (z : OddCost) (hz : 0 ≤ z.2) :
    (∫⁻ y : OddCost, ENNReal.ofReal y.2 ∂pairedCostKernel z) = ENNReal.ofReal z.2 + pairIncrement z := by
  have hK : pairedCostKernel = pairSampling.map pairUpdate := rfl
  rw [hK, sampling_map_measure _ pairUpdate_measurable,
    lintegral_map (g := fun x : EvenState × OddState ↦ pairUpdate (z, x)) age_test_measurable
      (pairUpdate_measurable.comp measurable_prodMk_left)]
  change (∫⁻ x : EvenState × OddState, ENNReal.ofReal (z.2 + cost x.1.1 + cost x.2.1) ∂pairedDraws z.1) = _
  have hp (x : EvenState × OddState) :
      ENNReal.ofReal (z.2 + cost x.1.1 + cost x.2.1) =
        ENNReal.ofReal z.2 + (ENNReal.ofReal (cost x.1.1) + ENNReal.ofReal (cost x.2.1)) := by
    have he : 0 ≤ cost x.1.1 := (cost_pos (by linarith [x.1.2])).le
    have ho : 0 ≤ cost x.2.1 := (cost_pos (by linarith [x.2.2])).le
    rw [ENNReal.ofReal_add (add_nonneg hz he) ho, ENNReal.ofReal_add hz he, add_assoc]
  simp_rw [hp]
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one, pairIncrement_formula]

theorem captured_killed_age_balance (z : OddCost) (hz : 0 ≤ z.2) :
    (∫⁻ y : OddCost, ENNReal.ofReal y.2 ∂costCaptured z) +
      (∫⁻ y : OddCost, ENNReal.ofReal y.2 ∂costKilled z) = ENNReal.ofReal z.2 + pairIncrement z := by
  rw [← lintegral_add_measure]
  have h := congrArg (fun K : Kernel OddCost OddCost ↦ K z) costCaptured_add_costKilled
  rw [add_apply] at h
  rw [h]
  exact paired_age_balance z hz

end Erdos970Dependency.OnePairCost

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_RegenerationBandBounds
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory Topology BigOperators
namespace Erdos970Dependency.CycleMeanCost
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.CostReturnLaw NumberTheoryLean.CycleCostLower NumberTheoryLean.CycleOccupation
open NumberTheoryLean.RegenerationTails
open Erdos970Dependency.InvariantDensities Erdos970Dependency.InvariantCostBound
open Erdos970Dependency.RawStateCost Erdos970Dependency.OccupationAge Erdos970Dependency.OnePairCost

theorem residualAge_zero : residualAge 0 = 0 := by
  change (∫⁻ y : OddCost, ENNReal.ofReal y.2 ∂Measure.dirac (regenerationState, 0)) = 0
  rw [lintegral_dirac' _ oddAge_measurable]
  norm_num

theorem age_balance (n : ℕ) : capturedAge n + residualAge (n + 1) = residualAge n + blockIncrement n := by
  have hp : costKilled ^ (n + 1) = costKilled ∘ₖ (costKilled ^ n) := pow_succ' costKilled n
  simp only [capturedAge, residualAge, blockIncrement, firstReturn, visitBlock]
  rw [hp, Kernel.lintegral_comp _ _ _ oddAge_measurable,
    Kernel.lintegral_comp _ _ _ oddAge_measurable,
    Kernel.lintegral_comp _ _ _ increment_test_measurable]
  have hC : Measurable (fun z : OddCost ↦ ∫⁻ y : OddCost, ENNReal.ofReal y.2 ∂costCaptured z) :=
    oddAge_measurable.lintegral_kernel
  rw [← lintegral_add_left hC, ← lintegral_add_left oddAge_measurable]
  apply lintegral_congr_ae
  filter_upwards [costKilled_pow_cost_monotone n (regenerationState, 0)] with z hz
  exact captured_killed_age_balance z hz

theorem finite_cost_balance (N : ℕ) :
    (∑ n ∈ Finset.range N, capturedAge n) + residualAge N = ∑ n ∈ Finset.range N, blockIncrement n := by
  induction N with
  | zero => simp [residualAge_zero]
  | succ N ih =>
    calc
      _ = ((∑ n ∈ Finset.range N, capturedAge n) + capturedAge N) + residualAge (N + 1) := by
        rw [Finset.sum_range_succ]
      _ = ((∑ n ∈ Finset.range N, capturedAge n) + residualAge N) + blockIncrement N := by
        rw [add_assoc, age_balance, ← add_assoc]
      _ = (∑ n ∈ Finset.range N, blockIncrement n) + blockIncrement N := by rw [ih]
      _ = _ := (Finset.sum_range_succ _ _).symm

theorem capturedAge_sum : (∑' n : ℕ, capturedAge n) =
    ∫⁻ G : ℝ, ENNReal.ofReal G ∂cycleCostLaw := by
  rw [cycleCostLaw, lintegral_map ENNReal.measurable_ofReal measurable_snd,
    returnLaw, Kernel.sum_apply, lintegral_sum_measure]
  rfl

theorem blockIncrement_sum : (∑' n : ℕ, blockIncrement n) =
    ∫⁻ y : CostState, ENNReal.ofReal (stateCost y.1) ∂occupationMeasure := by
  rw [occupationMeasure, occupationKernel, Kernel.sum_apply, lintegral_sum_measure]
  rfl

theorem cycle_cost_lintegral_eq_increments :
    (∫⁻ G : ℝ, ENNReal.ofReal G ∂cycleCostLaw) =
      ∫⁻ y : CostState, ENNReal.ofReal (stateCost y.1) ∂occupationMeasure := by
  have hleft : Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.range N, capturedAge n) + residualAge N)
      atTop (𝓝 (∑' n : ℕ, capturedAge n)) := by
    simpa only [add_zero] using (ENNReal.tendsto_nat_tsum capturedAge).add residualAge_tendsto_zero
  have hleft' : Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N, blockIncrement n)
      atTop (𝓝 (∑' n : ℕ, capturedAge n)) :=
    hleft.congr' (Eventually.of_forall finite_cost_balance)
  have h := tendsto_nhds_unique hleft' (ENNReal.tendsto_nat_tsum blockIncrement)
  rw [capturedAge_sum, blockIncrement_sum] at h
  exact h

theorem cycle_cost_integrable : Integrable (fun G : ℝ ↦ G) cycleCostLaw := by
  have hc : ∀ᵐ G ∂cycleCostLaw, 0 ≤ G := cycleCostLaw_positive.mono (fun _ h ↦ h.le)
  have ho : ∀ᵐ y : CostState ∂occupationMeasure, 0 ≤ stateCost y.1 :=
    Eventually.of_forall (fun y ↦ (stateCost_bounds y.1).1.le)
  refine ⟨measurable_id.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hc).mpr ?_⟩
  rw [cycle_cost_lintegral_eq_increments,
    ← ofReal_integral_eq_lintegral_ofReal occupation_increment_integrable ho]
  exact ENNReal.ofReal_lt_top

theorem cycle_mean_eq : (∫ G : ℝ, G ∂cycleCostLaw) = costMass / InvariantDensities.beta := by
  have hc : ∀ᵐ G ∂cycleCostLaw, 0 ≤ G := cycleCostLaw_positive.mono (fun _ h ↦ h.le)
  have ho : ∀ᵐ y : CostState ∂occupationMeasure, 0 ≤ stateCost y.1 :=
    Eventually.of_forall (fun y ↦ (stateCost_bounds y.1).1.le)
  have h := cycle_cost_lintegral_eq_increments
  rw [← ofReal_integral_eq_lintegral_ofReal cycle_cost_integrable hc,
    ← ofReal_integral_eq_lintegral_ofReal occupation_increment_integrable ho] at h
  have hr := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_ofReal (integral_nonneg_of_ae hc),
    ENNReal.toReal_ofReal (integral_nonneg_of_ae ho)] at hr
  exact hr.trans occupation_increment_integral

end Erdos970Dependency.CycleMeanCost

end

section

namespace NumberTheoryLean.InitialOccupation

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathMeasures PairedCostProcess PairedCostGrouping
open CostReturnLaw CycleOccupation OccupationDecomposition KernelPotential
open InitialOddDraw InitialRegeneration

instance beforeRegeneration_isSFiniteKernel : IsSFiniteKernel beforeRegeneration := by
  unfold beforeRegeneration
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end NumberTheoryLean.InitialOccupation

end

section

namespace NumberTheoryLean.NormalizedOccupationLimit

open Filter Set MeasureTheory
open scoped Topology
open FinitePathMeasures CycleResponse AdmissibleCycleTests OccupationConstant
open EvenStartOccupation FullOccupationCovariance
open Erdos970Dependency.InvariantDensities Erdos970Dependency.InvariantCostBound
open Erdos970Dependency.StateKernelInvariance Erdos970Dependency.CycleMeanCost

theorem occupation_constant_eq {F : Test} (hF : Measurable F) (hB : HasCompactBound F) :
    ((∫ v : ℝ, response F v) / (∫ G : ℝ, G ∂CostReturnLaw.cycleCostLaw)) = invariantAverage F := by
  rw [(response_integral_eq_invariant hF hB).2, cycle_mean_eq, invariantAverage]
  field_simp [beta_pos.ne', costMass_pos.ne']

theorem source_compact_occupation_limit {F : Test} (hF : Admissible F) :
    ∀ ε : ℝ, 0 < ε → ∃ V : ℝ, ∀ v : ℝ, V ≤ v → ∀ s : TransitionKernels.EvenState,
      (199 / 100 : ℝ) ≤ s.1 → s.1 ≤ 23 / 10 →
      ‖evenResponse F s v - invariantAverage F‖ < ε := by
  have h := source_start_occupation_limit_jb247 hF
  rwa [occupation_constant_eq hF.measurable hF.compactBound] at h

end NumberTheoryLean.NormalizedOccupationLimit

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_ArrivalKernelGeometry
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.Erdos970.NumberTheoryLean.ReferenceBenchmarkDecay.benchmark_even_below_two
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.KernelWeightTransform

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

theorem ratio_measurable (w : PositiveWeight α) :
    Measurable (Function.uncurry (fun a b => w b / w a)) :=
  (w.measurable_value.comp measurable_snd).div (w.measurable_value.comp measurable_fst)

theorem ratio_ne_top (w : PositiveWeight α) (a b : α) : w b / w a ≠ ∞ :=
  ENNReal.div_ne_top (w.ne_top b) (w.ne_zero a)

theorem ratio_cocycle (w : PositiveWeight α) (a b c : α) :
    (w b / w a) * (w c / w b) = w c / w a := by
  simp only [div_eq_mul_inv]
  calc
    _ = (w b * (w b)⁻¹) * (w c * (w a)⁻¹) := by ring
    _ = _ := by rw [ENNReal.mul_inv_cancel (w.ne_zero b) (w.ne_top b), one_mul]

instance conjugate_isSFiniteKernel (K : Kernel α α) [IsSFiniteKernel K] (w : PositiveWeight α) :
    IsSFiniteKernel (conjugate K w) := Kernel.IsSFiniteKernel.withDensity K (ratio_ne_top w)

theorem conjugate_apply (K : Kernel α α) [IsSFiniteKernel K] (w : PositiveWeight α) (a : α) :
    conjugate K w a = (K a).withDensity (fun b => w b / w a) :=
  Kernel.withDensity_apply K (ratio_measurable w) a

theorem conjugate_lintegral (K : Kernel α α) [IsSFiniteKernel K] (w : PositiveWeight α) (a : α)
    {F : α → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ b, F b ∂conjugate K w a) = ∫⁻ b, (w b / w a) * F b ∂K a :=
  Kernel.lintegral_withDensity K (ratio_measurable w) a hF

theorem conjugate_id (w : PositiveWeight α) : conjugate (Kernel.id : Kernel α α) w = Kernel.id := by
  ext a : 1
  apply Measure.ext_of_lintegral
  intro F hF
  rw [conjugate_lintegral _ w a hF,
    Kernel.lintegral_id' (f := fun b => (w b / w a) * F b) ((w.measurable_value.div measurable_const).mul hF),
    ENNReal.div_self (w.ne_zero a) (w.ne_top a), one_mul, Kernel.lintegral_id' hF]

theorem conjugate_comp (L K : Kernel α α) [IsSFiniteKernel L] [IsSFiniteKernel K]
    (w : PositiveWeight α) :
    (conjugate L w) ∘ₖ (conjugate K w) = conjugate (L ∘ₖ K) w := by
  ext a : 1
  apply Measure.ext_of_lintegral
  intro F hF
  have hInner : Measurable (fun b => ∫⁻ c, F c ∂conjugate L w b) := hF.lintegral_kernel
  have hWeighted : Measurable (fun c => (w c / w a) * F c) :=
    (w.measurable_value.div measurable_const).mul hF
  rw [Kernel.lintegral_comp _ _ _ hF,
    conjugate_lintegral K w a (F := fun b => ∫⁻ c, F c ∂conjugate L w b) hInner,
    conjugate_lintegral (L ∘ₖ K) w a hF,
    Kernel.lintegral_comp L K a hWeighted]
  apply lintegral_congr
  intro b
  rw [conjugate_lintegral L w b hF,
    ← lintegral_const_mul' _ _ (ratio_ne_top w a b)]
  apply lintegral_congr
  intro c
  rw [← mul_assoc, ratio_cocycle]

theorem conjugate_congr (L K : Kernel α α) [IsSFiniteKernel L] [IsSFiniteKernel K]
    (h : L = K) (w : PositiveWeight α) : conjugate L w = conjugate K w := by
  subst K
  rfl

theorem conjugate_pow (K : Kernel α α) [IsSFiniteKernel K] (w : PositiveWeight α) (n : ℕ) :
    (conjugate K w) ^ n = conjugate (K ^ n) w := by
  induction n with
  | zero =>
    change (Kernel.id : Kernel α α) = conjugate Kernel.id w
    exact (conjugate_id w).symm
  | succ n ih =>
    have hp : (conjugate K w) ^ (n + 1) = (conjugate K w) ∘ₖ ((conjugate K w) ^ n) := pow_succ' _ _
    have hq : K ^ (n + 1) = K ∘ₖ (K ^ n) := pow_succ' _ _
    rw [hp, ih, conjugate_comp]
    exact conjugate_congr (K ∘ₖ (K ^ n)) (K ^ (n + 1)) hq.symm w

end NumberTheoryLean.KernelWeightTransform

end

section

namespace NumberTheoryLean.KernelExitBarrier

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open KernelWeightTransform

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

theorem conjugate_restrict (K : Kernel α α) [IsSFiniteKernel K] (w : PositiveWeight α)
    {A : Set α} (hA : MeasurableSet A) :
    (conjugate K w).restrict hA = conjugate (K.restrict hA) w := by
  ext a : 1
  rw [Kernel.restrict_apply, conjugate_apply K w a, conjugate_apply (K.restrict hA) w a,
    Kernel.restrict_apply, MeasureTheory.restrict_withDensity hA]

end NumberTheoryLean.KernelExitBarrier

end

section

namespace NumberTheoryLean.KernelMappedDomination

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open KernelWeightTransform

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

theorem mapped_pow_lintegral_le (K : Kernel α α) (L : Kernel β β)
    [IsSFiniteKernel K] [IsSFiniteKernel L] (P : α → β) (hP : Measurable P)
    (hrow : ∀ x, (K x).map P ≤ L (P x)) :
    ∀ n : ℕ, ∀ x : α, ∀ f : β → ℝ≥0∞, Measurable f →
      (∫⁻ y, f (P y) ∂(K^n) x) ≤ ∫⁻ y, f y ∂(L^n) (P x) := by
  intro n
  induction n with
  | zero =>
    intro x f hf
    change (∫⁻ y, f (P y) ∂Measure.dirac x) ≤ ∫⁻ y, f y ∂Measure.dirac (P x)
    rw [lintegral_dirac' _ (f := fun y => f (P y)) (hf.comp hP), lintegral_dirac' _ hf]
  | succ n ih =>
    intro x f hf
    have hp : K^(n+1) = (K^n) ∘ₖ K := pow_succ _ _
    have hq : L^(n+1) = (L^n) ∘ₖ L := pow_succ _ _
    rw [hp, hq,
      Kernel.lintegral_comp _ _ _ (g := fun y => f (P y)) (hf.comp hP),
      Kernel.lintegral_comp _ _ _ hf]
    have hF : Measurable (fun y => ∫⁻ t, f t ∂(L^n) y) := hf.lintegral_kernel
    calc
      _ ≤ ∫⁻ y, ∫⁻ t, f t ∂(L^n) (P y) ∂K x := lintegral_mono (fun y => ih y f hf)
      _ = ∫⁻ y, ∫⁻ t, f t ∂(L^n) y ∂(K x).map P :=
        (lintegral_map (f := fun y => ∫⁻ t, f t ∂(L^n) y) hF hP).symm
      _ ≤ _ := lintegral_mono' (hrow x) le_rfl

theorem mapped_pow_le (K : Kernel α α) (L : Kernel β β)
    [IsSFiniteKernel K] [IsSFiniteKernel L] (P : α → β) (hP : Measurable P)
    (hrow : ∀ x, (K x).map P ≤ L (P x)) (n : ℕ) (x : α) :
    ((K^n) x).map P ≤ (L^n) (P x) := by
  apply Measure.le_iff.mpr
  intro A hA
  have hf : Measurable (A.indicator (fun _ : β => (1 : ℝ≥0∞))) := measurable_const.indicator hA
  have h := mapped_pow_lintegral_le K L P hP hrow n x _ hf
  rw [← lintegral_map (f := A.indicator (fun _ : β => (1 : ℝ≥0∞))) hf hP] at h
  simpa only [lintegral_indicator hA, lintegral_const, one_mul, Measure.restrict_apply_univ] using h

end NumberTheoryLean.KernelMappedDomination

end

section

namespace NumberTheoryLean.HarmonicWeightKernel

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open DerivativeWeights WeightFutureIntegrals TransitionKernels FinitePathGeometry
open FinitePathMeasures OccupationBoundaries InvariantInverseWeights
open KernelWeightTransform CostPrefixTransport OccupationDecomposition

instance harmonicKernel_isSFiniteKernel : IsSFiniteKernel harmonicKernel := by unfold harmonicKernel; infer_instance

theorem exp_neg_two_cost {t : ℝ} (ht : 0 < t) :
    Real.exp (-2 * cost t) = (t / (t + 1)) ^ 2 := by
  have h : Real.exp (-cost t) = t / (t + 1) := by
    simpa only [nextGap, one_mul] using (nextGap_eq_cost (r := 1) ht).symm
  calc
    _ = Real.exp (-cost t + -cost t) := congrArg Real.exp (by ring)
    _ = Real.exp (-cost t) * Real.exp (-cost t) := Real.exp_add _ _
    _ = _ := by rw [h, pow_two]

theorem transition_weight_ratio (z : CostState) (s : State) :
    harmonicWeight (s, z.2 + cost (stateRatio s)) / harmonicWeight z =
      ENNReal.ofReal ((stateRatio s / (stateRatio s + 1)) ^ 2 *
        (stateWeight z.1 / stateWeight s)) := by
  have hz : 0 < Real.exp (-2 * z.2) / stateWeight z.1 := div_pos (Real.exp_pos _) (stateWeight_pos z.1)
  change ENNReal.ofReal (Real.exp (-2 * (z.2 + cost (stateRatio s))) / stateWeight s) /
    ENNReal.ofReal (Real.exp (-2 * z.2) / stateWeight z.1) = _
  rw [← ENNReal.ofReal_div_of_pos hz]
  congr 1
  rw [show -2 * (z.2 + cost (stateRatio s)) = (-2 * z.2) + (-2 * cost (stateRatio s)) by ring,
    Real.exp_add, exp_neg_two_cost (stateRatio_pos s)]
  field_simp [(stateWeight_pos z.1).ne', (stateWeight_pos s).ne', (Real.exp_pos (-2 * z.2)).ne']

theorem weight_measurable (i : Side) : Measurable (weight i) := by
  cases i
  · exact phiEven_measurable
  · exact phiOdd_continuous.measurable

theorem correction_measurable (i : Side) (s : ℝ) : Measurable (correction i s) :=
  ((measurable_id.div (measurable_id.add measurable_const)).pow_const 2).mul
    (measurable_const.div (weight_measurable i.flip))

theorem harmonicRatioDensity_measurable (i : Side) (s : ℝ) : Measurable (harmonicRatioDensity i s) :=
  (ENNReal.measurable_ofReal.comp (measurable_const.div (measurable_id.add measurable_const))).indicator measurableSet_Ici

theorem corrected_density_eq {i : Side} {s : ℝ} (hs : Valid i s) (t : ℝ) :
    ENNReal.ofReal (transitionDensity i s t) * ENNReal.ofReal (correction i s t) =
      harmonicRatioDensity i s t := by
  by_cases ht : minRatio i s ≤ t
  · have hv := valid_next hs ht
    have hp : 0 ≤ transitionDensity i s t := by
      unfold transitionDensity tailDensity
      rw [indicator_of_mem (show t ∈ Ici (minRatio i s) from ht)]
      exact div_nonneg (mul_nonneg (W_pos (valid_pos hv)).le (weight_pos hv).le) (weight_pos hs).le
    rw [← ENNReal.ofReal_mul hp, harmonicRatioDensity,
      indicator_of_mem (show t ∈ Ici (minRatio i s) from ht)]
    congr 1
    have he := step_weight_identity (r := 1) hs ht (by norm_num)
    simpa only [correction, nextGap, one_mul, div_one, mul_assoc] using he.symm
  · rw [transitionDensity, tailDensity, indicator_of_notMem (show t ∉ Ici (minRatio i s) from ht),
      ENNReal.ofReal_zero, zero_mul, harmonicRatioDensity,
      indicator_of_notMem (show t ∉ Ici (minRatio i s) from ht)]

theorem initial_weight_inv (s : State) : (harmonicWeight (s, 0))⁻¹ = ENNReal.ofReal (stateWeight s) := by
  change (ENNReal.ofReal (Real.exp (-2 * (0 : ℝ)) / stateWeight s))⁻¹ = _
  rw [mul_zero, Real.exp_zero, ENNReal.ofReal_div_of_pos (stateWeight_pos s), ENNReal.ofReal_one, one_div, inv_inv]

end NumberTheoryLean.HarmonicWeightKernel

end

section

namespace NumberTheoryLean.HarmonicKernelDensities

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostGrouping
open KernelDensityBridge InvariantInverseWeights KernelWeightTransform HarmonicWeightKernel
open Erdos970Dependency.OrdinaryKernelInvariance Erdos970Dependency.StateKernelInvariance

theorem harmonic_even_typed (s : EvenState) (T : ℝ) {H : CostState → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ y, H y ∂harmonicKernel (.inl s, T)) =
      ∫⁻ t : OddState, ENNReal.ofReal (correction .even s.1 t.1) * H (.inr t, T + cost t.1) ∂evenToOdd s := by
  have hm : Measurable (fun y : CostState => (harmonicWeight y / harmonicWeight (.inl s, T)) * H y) :=
    (harmonicWeight.measurable_value.div measurable_const).mul hH
  rw [harmonicKernel, conjugate_lintegral costKernel harmonicWeight (.inl s, T) hH,
    costKernel_even_lintegral s T (H := fun y : CostState => (harmonicWeight y / harmonicWeight (.inl s, T)) * H y) hm]
  apply lintegral_congr
  intro t
  have hr : harmonicWeight (.inr t, T + cost t.1) / harmonicWeight (.inl s, T) =
      ENNReal.ofReal (correction .even s.1 t.1) := by
    simpa only [stateRatio, stateWeight, weight, Side.flip, correction, Sum.elim_inl, Sum.elim_inr] using
      transition_weight_ratio (.inl s, T) (.inr t)
  exact congrArg (fun c : ℝ≥0∞ => c * H (.inr t, T + cost t.1)) hr

theorem harmonic_odd_typed (s : OddState) (T : ℝ) {H : CostState → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ y, H y ∂harmonicKernel (.inr s, T)) =
      ∫⁻ t : EvenState, ENNReal.ofReal (correction .odd s.1 t.1) * H (.inl t, T + cost t.1) ∂oddToEven s := by
  have hm : Measurable (fun y : CostState => (harmonicWeight y / harmonicWeight (.inr s, T)) * H y) :=
    (harmonicWeight.measurable_value.div measurable_const).mul hH
  rw [harmonicKernel, conjugate_lintegral costKernel harmonicWeight (.inr s, T) hH,
    costKernel_odd_lintegral s T (H := fun y : CostState => (harmonicWeight y / harmonicWeight (.inr s, T)) * H y) hm]
  apply lintegral_congr
  intro t
  have hr : harmonicWeight (.inl t, T + cost t.1) / harmonicWeight (.inr s, T) =
      ENNReal.ofReal (correction .odd s.1 t.1) := by
    simpa only [stateRatio, stateWeight, weight, Side.flip, correction, Sum.elim_inl, Sum.elim_inr] using
      transition_weight_ratio (.inr s, T) (.inl t)
  exact congrArg (fun c : ℝ≥0∞ => c * H (.inl t, T + cost t.1)) hr

theorem evenUpdateReal_measurable (T : ℝ) : Measurable (evenUpdateReal T) :=
  (measurable_inr.comp oddLift_measurable).prodMk (measurable_const.add cost_measurable)

theorem oddUpdateReal_measurable (T : ℝ) : Measurable (oddUpdateReal T) :=
  (measurable_inl.comp evenLift_measurable).prodMk (measurable_const.add cost_measurable)

theorem harmonic_even_joint_lintegral (s : EvenState) (T : ℝ) {H : CostState → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ y, H y ∂harmonicKernel (.inl s, T)) =
      ∫⁻ t : ℝ, harmonicRatioDensity .even s.1 t * H (evenUpdateReal T t) := by
  let G : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (correction .even s.1 t) * H (evenUpdateReal T t)
  have hG : Measurable G := (ENNReal.measurable_ofReal.comp (correction_measurable .even s.1)).mul
    (hH.comp (evenUpdateReal_measurable T))
  rw [harmonic_even_typed s T hH]
  calc
    _ = ∫⁻ t : OddState, G t.1 ∂evenToOdd s := by
      apply lintegral_congr
      intro t
      simp only [G, evenUpdateReal, oddLift_ratio]
    _ = ∫⁻ t : ℝ, G t ∂evenKernel s := evenToOdd_lintegral_ratio s hG
    _ = ∫⁻ t : ℝ, ENNReal.ofReal (transitionDensity .even s.1 t) * G t := evenKernel_lintegral_density s hG
    _ = _ := by
      apply lintegral_congr
      intro t
      dsimp [G]
      rw [← mul_assoc, corrected_density_eq (i := .even) (s := s.1) s.2 t]

theorem harmonic_odd_joint_lintegral (s : OddState) (T : ℝ) {H : CostState → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ y, H y ∂harmonicKernel (.inr s, T)) =
      ∫⁻ t : ℝ, harmonicRatioDensity .odd s.1 t * H (oddUpdateReal T t) := by
  let G : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (correction .odd s.1 t) * H (oddUpdateReal T t)
  have hG : Measurable G := (ENNReal.measurable_ofReal.comp (correction_measurable .odd s.1)).mul
    (hH.comp (oddUpdateReal_measurable T))
  rw [harmonic_odd_typed s T hH]
  calc
    _ = ∫⁻ t : EvenState, G t.1 ∂oddToEven s := by
      apply lintegral_congr
      intro t
      simp only [G, oddUpdateReal, evenLift_ratio]
    _ = ∫⁻ t : ℝ, G t ∂oddKernel s := oddToEven_lintegral_ratio s hG
    _ = ∫⁻ t : ℝ, ENNReal.ofReal (transitionDensity .odd s.1 t) * G t := oddKernel_lintegral_density s hG
    _ = _ := by
      apply lintegral_congr
      intro t
      dsimp [G]
      rw [← mul_assoc, corrected_density_eq (i := .odd) (s := s.1) s.2 t]

theorem harmonic_even_measure (s : EvenState) (T : ℝ) :
    harmonicKernel (.inl s, T) =
      (volume.withDensity (harmonicRatioDensity .even s.1)).map (evenUpdateReal T) := by
  apply Measure.ext_of_lintegral
  intro H hH
  rw [harmonic_even_joint_lintegral s T hH,
    lintegral_map hH (evenUpdateReal_measurable T),
    lintegral_withDensity_eq_lintegral_mul volume (f := harmonicRatioDensity .even s.1)
      (g := fun t => H (evenUpdateReal T t)) (harmonicRatioDensity_measurable .even s.1)
      (hH.comp (evenUpdateReal_measurable T))]
  rfl

theorem harmonic_odd_measure (s : OddState) (T : ℝ) :
    harmonicKernel (.inr s, T) =
      (volume.withDensity (harmonicRatioDensity .odd s.1)).map (oddUpdateReal T) := by
  apply Measure.ext_of_lintegral
  intro H hH
  rw [harmonic_odd_joint_lintegral s T hH,
    lintegral_map hH (oddUpdateReal_measurable T),
    lintegral_withDensity_eq_lintegral_mul volume (f := harmonicRatioDensity .odd s.1)
      (g := fun t => H (oddUpdateReal T t)) (harmonicRatioDensity_measurable .odd s.1)
      (hH.comp (oddUpdateReal_measurable T))]
  rfl

end NumberTheoryLean.HarmonicKernelDensities

end

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

theorem costKernel_gap_flow (v : ℝ) (z : CostState) :
    ∀ᵐ y ∂costKernel z, gapValue v z = gapValue v y + currentExponent v y := by
  have hm : Measurable (fun s : State => (s, z.2 + cost (stateRatio s))) :=
    measurable_id.prodMk (measurable_const.add (cost_measurable.comp stateRatio_measurable))
  have hp : MeasurableSet {y : CostState | gapValue v z = gapValue v y + currentExponent v y} :=
    measurableSet_eq_fun measurable_const ((gapValue_measurable v).add (currentExponent_measurable v))
  rw [costKernel_eq_map]
  apply (ae_map_iff hm.aemeasurable hp).mpr
  apply Eventually.of_forall
  intro s
  rw [gapValue_update, currentExponent_update]
  exact (gap_exponent_conservation (stateRatio_pos s)).symm

theorem harmonicKernel_absolutelyContinuous (z : CostState) : harmonicKernel z ≪ costKernel z :=
  Kernel.withDensity_absolutelyContinuous (fun a b => harmonicWeight b / harmonicWeight a) z

theorem harmonicKernel_gap_flow (v : ℝ) (z : CostState) :
    ∀ᵐ y ∂harmonicKernel z, gapValue v z = gapValue v y + currentExponent v y :=
  (harmonicKernel_absolutelyContinuous z).ae_le (costKernel_gap_flow v z)

end NumberTheoryLean.ArrivalKernelGeometry

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_AdmittedHarmonicPaths
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.AdmittedHarmonicPaths

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open FinitePathMeasures RegeneratingInverseBands ArrivalKernelGeometry
open HarmonicWeightKernel KernelWeightTransform KernelExitBarrier

instance admittedHarmonic_isSFiniteKernel (v ell : ℝ) : IsSFiniteKernel (admittedHarmonic v ell) := by
  unfold admittedHarmonic
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem admitted_weight_transform (v ell : ℝ) :
    admittedHarmonic v ell = conjugate (admittedTilted v ell) harmonicWeight :=
  conjugate_restrict costKernel harmonicWeight (arrivalSet_measurable v ell)

theorem admitted_step_gap_bound (K : Kernel CostState CostState) (v ell : ℝ)
    (hflow : ∀ z, ∀ᵐ y ∂K z, gapValue v z = gapValue v y + currentExponent v y) (z : CostState) :
    ∀ᵐ y ∂K.restrict (arrivalSet_measurable v ell) z, gapValue v y ≤ gapValue v z - ell := by
  rw [Kernel.restrict_apply]
  filter_upwards [ae_restrict_of_ae (hflow z), ae_restrict_mem (arrivalSet_measurable v ell)] with y hy ha
  change ell < currentExponent v y at ha
  linarith

theorem admitted_pow_gap_bound (K : Kernel CostState CostState) (v ell : ℝ)
    (hflow : ∀ z, ∀ᵐ y ∂K z, gapValue v z = gapValue v y + currentExponent v y)
    (n : ℕ) (z : CostState) :
    ∀ᵐ y ∂((K.restrict (arrivalSet_measurable v ell)) ^ n) z,
      gapValue v y ≤ gapValue v z - (n : ℝ) * ell := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero]
    change ∀ᵐ y ∂Measure.dirac z, gapValue v y ≤ gapValue v z - (0 : ℝ) * ell
    exact (ae_dirac_iff (p := fun y => gapValue v y ≤ gapValue v z - (0 : ℝ) * ell)
      (measurableSet_le (gapValue_measurable v) measurable_const)).mpr (by simp)
  | succ n ih =>
    have hp : (K.restrict (arrivalSet_measurable v ell)) ^ (n + 1) =
        (K.restrict (arrivalSet_measurable v ell)) ∘ₖ ((K.restrict (arrivalSet_measurable v ell)) ^ n) := pow_succ' _ _
    rw [hp]
    apply Kernel.ae_comp_of_ae_ae (measurableSet_le (gapValue_measurable v) measurable_const)
    filter_upwards [ih] with y hy
    filter_upwards [admitted_step_gap_bound K v ell hflow y] with t ht
    calc
      gapValue v t ≤ gapValue v y - ell := ht
      _ ≤ (gapValue v z - (n : ℝ) * ell) - ell := sub_le_sub_right hy ell
      _ = _ := by push_cast <;> ring

theorem admitted_pow_zero_of_height (K : Kernel CostState CostState) (v ell : ℝ)
    (hflow : ∀ z, ∀ᵐ y ∂K z, gapValue v z = gapValue v y + currentExponent v y)
    (n : ℕ) (z : CostState) (hn : gapValue v z ≤ (n : ℝ) * ell) :
    ((K.restrict (arrivalSet_measurable v ell)) ^ n) z = 0 := by
  have hf : ∀ᵐ y ∂((K.restrict (arrivalSet_measurable v ell)) ^ n) z, False := by
    filter_upwards [admitted_pow_gap_bound K v ell hflow n z] with y hy
    have hp : 0 < gapValue v y := Real.exp_pos _
    linarith
  apply Measure.measure_univ_eq_zero.mp
  simpa only [ae_iff, not_false_eq_true, Set.ofPred_true] using hf

theorem admitted_tilted_finite_height (v : ℝ) {ell : ℝ} (hell : 0 < ell) (z : CostState)
    (n : ℕ) (hn : ⌈gapValue v z / ell⌉₊ ≤ n) : ((admittedTilted v ell) ^ n) z = 0 := by
  apply admitted_pow_zero_of_height costKernel v ell (costKernel_gap_flow v) n z
  apply (div_le_iff₀ hell).mp
  exact le_trans (Nat.le_ceil _) (by exact_mod_cast hn)

end NumberTheoryLean.AdmittedHarmonicPaths

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_LowStateHorizon
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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
open OccupationBoundaries ArrivalKernelGeometry RegeneratingInverseBands HarmonicWeightKernel

 theorem cost_ge_inv_add_one {t : ℝ} (ht : 0 < t) : 1 / (t + 1) ≤ cost t := by
  have hx : 0 < 1 + 1 / t := by positivity
  have h := Real.one_sub_inv_le_log_of_pos hx
  have heq : 1 - (1 + 1 / t)⁻¹ = 1 / (t + 1) := by
    field_simp [ht.ne', hx.ne', show t + 1 ≠ 0 by linarith]
    ring
  rw [heq] at h
  exact h

theorem stateRatio_ge_nineteen_twentieths (s : State) : (19 / 20 : ℝ) ≤ stateRatio s := by
  cases s with
  | inl s => change (19 / 20 : ℝ) ≤ s.1; linarith [s.2]
  | inr s => change (19 / 20 : ℝ) ≤ s.1; linarith [s.2]

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

theorem low_step_clock (K : Kernel CostState CostState) (v ell S : ℝ)
    (hTime : ∀ z, ∀ᵐ y ∂K z, y.2 = z.2 + cost (stateRatio y.1)) (z : CostState) :
    ∀ᵐ y ∂lowKernel K v ell S z, z.2 + 1 / (S + 1) ≤ y.2 := by
  rw [lowKernel, Kernel.restrict_apply]
  filter_upwards [ae_restrict_of_ae (hTime z), ae_restrict_mem (lowDomain_measurable v ell S)] with y hy hD
  have hs : stateRatio y.1 ≤ S := hD.2
  have ht := stateRatio_pos y.1
  have hc : 1 / (S + 1) ≤ cost (stateRatio y.1) :=
    le_trans (one_div_le_one_div_of_le (by linarith : 0 < stateRatio y.1 + 1) (by linarith))
      (cost_ge_inv_add_one ht)
  linarith

theorem low_pow_clock (K : Kernel CostState CostState) (v ell S : ℝ)
    (hTime : ∀ z, ∀ᵐ y ∂K z, y.2 = z.2 + cost (stateRatio y.1)) (n : ℕ) (z : CostState) :
    ∀ᵐ y ∂((lowKernel K v ell S) ^ n) z, z.2 + (n : ℝ) / (S + 1) ≤ y.2 := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero]
    change ∀ᵐ y ∂Measure.dirac z, z.2 + (0 : ℝ) / (S + 1) ≤ y.2
    exact (ae_dirac_iff (p := fun y : CostState => z.2 + (0 : ℝ) / (S + 1) ≤ y.2)
      (measurableSet_le measurable_const measurable_snd)).mpr (by simp)
  | succ n ih =>
    have hp : (lowKernel K v ell S) ^ (n + 1) = (lowKernel K v ell S) ∘ₖ ((lowKernel K v ell S) ^ n) := pow_succ' _ _
    rw [hp]
    apply Kernel.ae_comp_of_ae_ae (measurableSet_le measurable_const measurable_snd)
    filter_upwards [ih] with y hy
    filter_upwards [low_step_clock K v ell S hTime y] with t ht
    calc
      z.2 + ((n + 1 : ℕ) : ℝ) / (S + 1) = (z.2 + (n : ℝ) / (S + 1)) + 1 / (S + 1) := by push_cast <;> ring
      _ ≤ y.2 + 1 / (S + 1) := add_le_add hy le_rfl
      _ ≤ t.2 := ht

theorem low_pow_terminal (K : Kernel CostState CostState) (v ell S : ℝ) (n : ℕ) (z : CostState) :
    ∀ᵐ y ∂((lowKernel K v ell S) ^ (n + 1)) z, y ∈ lowDomain v ell S := by
  have hp : (lowKernel K v ell S) ^ (n + 1) = (lowKernel K v ell S) ∘ₖ ((lowKernel K v ell S) ^ n) := pow_succ' _ _
  rw [hp]
  apply Kernel.ae_comp_of_ae_ae (lowDomain_measurable v ell S)
  apply Eventually.of_forall
  intro y
  rw [lowKernel, Kernel.restrict_apply]
  exact ae_restrict_mem (lowDomain_measurable v ell S)

theorem low_pow_zero_of_clock (K : Kernel CostState CostState) (v ell S : ℝ)
    (hTime : ∀ z, ∀ᵐ y ∂K z, y.2 = z.2 + cost (stateRatio y.1))
    (hell : 0 < ell) (n : ℕ) (hn : 0 < n) (z : CostState)
    (hclock : v - z.2 - Real.log ((19 / 20 : ℝ) * ell) ≤ (n : ℝ) / (S + 1)) :
    ((lowKernel K v ell S) ^ n) z = 0 := by
  have hD : ∀ᵐ y ∂((lowKernel K v ell S) ^ n) z, y ∈ lowDomain v ell S := by
    cases n with
    | zero => omega
    | succ n => exact low_pow_terminal K v ell S n z
  have hfalse : ∀ᵐ y ∂((lowKernel K v ell S) ^ n) z, False := by
    filter_upwards [low_pow_clock K v ell S hTime n z, hD] with y hy hdom
    have ha : ell < gapValue v y / stateRatio y.1 := hdom.1
    have hmul := (lt_div_iff₀ (stateRatio_pos y.1)).mp ha
    have hgap : (19 / 20 : ℝ) * ell < gapValue v y := by
      have hlow := mul_le_mul_of_nonneg_left (stateRatio_ge_nineteen_twentieths y.1) hell.le
      nlinarith
    have hlog := Real.log_lt_log (mul_pos (by norm_num : (0 : ℝ) < 19 / 20) hell) hgap
    rw [gapValue, Real.log_exp] at hlog
    linarith
  apply Measure.measure_univ_eq_zero.mp
  simpa only [ae_iff, not_false_eq_true, Set.ofPred_true] using hfalse

theorem source_low_horizon (K : Kernel CostState CostState) (v ell S B : ℝ)
    (hTime : ∀ z, ∀ᵐ y ∂K z, y.2 = z.2 + cost (stateRatio y.1))
    (hell : 1 ≤ ell) (hS : 0 < S) (hB : 0 < B) (z : CostState)
    (hgap : gapValue v z ≤ (23 / 10 : ℝ) * B) (n : ℕ) (hn : sourceHorizon S B ≤ n) :
    ((lowKernel K v ell S) ^ n) z = 0 := by
  have hell0 : 0 < ell := by linarith
  have hn0 : 0 < n := by unfold sourceHorizon at hn; omega
  apply low_pow_zero_of_clock K v ell S hTime hell0 n hn0 z
  have hlogR := Real.log_le_log (Real.exp_pos (v - z.2)) hgap
  rw [Real.log_exp, Real.log_mul (by norm_num : (23 / 10 : ℝ) ≠ 0) hB.ne'] at hlogR
  have hlog23 : Real.log (23 / 10 : ℝ) ≤ 13 / 10 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 23 / 10)
    norm_num at h
    exact h
  have hlog19 : (-1 / 19 : ℝ) ≤ Real.log (19 / 20 : ℝ) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 19 / 20)
    norm_num at h
    linarith
  have hlogell : Real.log (19 / 20 : ℝ) ≤ Real.log ((19 / 20 : ℝ) * ell) :=
    Real.log_le_log (by norm_num) (by nlinarith)
  have hspan : v - z.2 - Real.log ((19 / 20 : ℝ) * ell) ≤ Real.log B + 2 := by linarith
  have hceil := Nat.le_ceil ((S + 1) * (Real.log B + 2))
  have hN : ((⌈(S + 1) * (Real.log B + 2)⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by
    have hN' : ⌈(S + 1) * (Real.log B + 2)⌉₊ ≤ n := by unfold sourceHorizon at hn; omega
    exact_mod_cast hN'
  apply le_trans hspan
  apply (le_div_iff₀ (by linarith : 0 < S + 1)).mpr
  nlinarith

theorem tilted_source_horizon (v ell S B : ℝ) (hell : 1 ≤ ell) (hS : 0 < S) (hB : 0 < B)
    (z : CostState) (hgap : gapValue v z ≤ (23 / 10 : ℝ) * B) (n : ℕ) (hn : sourceHorizon S B ≤ n) :
    ((lowKernel costKernel v ell S) ^ n) z = 0 :=
  source_low_horizon costKernel v ell S B costKernel_time_update hell hS hB z hgap n hn

end NumberTheoryLean.LowStateHorizon

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_HarmonicChangeOfVariable
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.HarmonicChangeOfVariable

open Set MeasureTheory
open FinitePathGeometry

theorem exponent_hasDerivAt {r t : ℝ} (ht : 0 < t) :
    HasDerivAt (nextExponent r) (-r / (t + 1) ^ 2) t := by
  have h := (hasDerivAt_const t r).div ((hasDerivAt_id t).add_const 1) (by linarith : t + 1 ≠ 0)
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [id_eq, zero_mul, zero_sub, mul_one]

theorem inverse_exponent {r t : ℝ} (hr : 0 < r) (_ht : 0 < t) :
    r / nextExponent r t - 1 = t := by
  unfold nextExponent
  field_simp
  ring

theorem harmonic_jacobian {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    |deriv (nextExponent r) t| / nextExponent r t = 1 / (t + 1) := by
  rw [(exponent_hasDerivAt ht).deriv, abs_of_neg (div_neg_of_neg_of_pos (by linarith)
    (sq_pos_of_pos (by linarith)))]
  unfold nextExponent
  field_simp

end NumberTheoryLean.HarmonicChangeOfVariable

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_HarmonicPrefixKernel
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosPrimeInputs.WeightedKernelMass

open Set Finset MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

lemma mass_succ (K : Kernel α α) (n : ℕ) (x : α) :
    mass K (n+1) x = ∫⁻ y, mass K n y ∂K x := by
  unfold mass
  rw [pow_succ]
  exact Kernel.comp_apply' _ _ _ MeasurableSet.univ

lemma mass_measurable (K : Kernel α α) (n : ℕ) : Measurable (mass K n) :=
  (K^n).measurable_coe MeasurableSet.univ

theorem weighted_sum_succ (K : Kernel α α) (c : ℝ≥0∞) (N : ℕ) (x : α) :
    (∑ n ∈ range (N+1), c^n * mass K n x) =
      1 + c * ∫⁻ y, (∑ n ∈ range N, c^n * mass K n y) ∂K x := by
  rw [lintegral_finsetSum (range N) (f := fun n y => c^n * mass K n y) (fun n _ => measurable_const.mul (mass_measurable K n)),mul_sum]
  simp_rw [lintegral_const_mul _ (mass_measurable K _),← mass_succ]
  rw [Finset.sum_range_succ']
  simp only [pow_zero,mass_zero,one_mul]
  rw [add_comm]
  congr 1
  apply sum_congr rfl
  intro n hn
  rw [pow_succ]
  ring

theorem weighted_finite_bound (K : Kernel α α) (c : ℝ≥0∞) (V : α → ℝ≥0∞)
    (hV : ∀ x, 1 + c * (∫⁻ y, V y ∂K x) ≤ V x) :
    ∀ N : ℕ, ∀ x : α, (∑ n ∈ range N, c^n * mass K n x) ≤ V x := by
  intro N
  induction N with
  | zero => intro x; simp
  | succ N ih =>
    intro x
    rw [weighted_sum_succ]
    exact (add_le_add le_rfl (mul_le_mul le_rfl (lintegral_mono (fun y => ih y)) zero_le zero_le)).trans (hV x)

theorem weighted_total_bound (K : Kernel α α) (c : ℝ≥0∞) (V : α → ℝ≥0∞)
    (hV : ∀ x, 1 + c * (∫⁻ y, V y ∂K x) ≤ V x) (x : α) :
    (∑' n : ℕ, c^n * mass K n x) ≤ V x := by
  exact ENNReal.tsum_le_of_sum_range_le (fun N => weighted_finite_bound K c V hV N x)

end ErdosPrimeInputs.WeightedKernelMass

end

section

namespace ErdosPrimeInputs.HarmonicPrefixKernel

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open WeightedKernelMass

lemma density_measurable (ell : ℝ) : Measurable (Function.uncurry (density ell)) := by
  exact Measurable.ite
    ((measurableSet_lt measurable_const measurable_snd).inter (measurableSet_le measurable_snd measurable_fst))
    (ENNReal.measurable_ofReal.comp measurable_snd.inv) measurable_const

theorem kernel_lintegral (ell B : ℝ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ t, f t ∂kernel ell B) = ∫⁻ t in Ioc ell B, ENNReal.ofReal (t⁻¹)*f t := by
  rw [kernel,Kernel.lintegral_withDensity _ (density_measurable ell) B hf,Kernel.const_apply]
  have heq : (fun t => density ell B t * f t) = (Ioc ell B).indicator (fun t => ENNReal.ofReal (t⁻¹)*f t) := by
    funext t
    simp only [density,Set.indicator,mem_Ioc,ite_mul,zero_mul]
  rw [heq,lintegral_indicator measurableSet_Ioc]

theorem kernel_eq_restrict (ell B : ℝ) : kernel ell B =
    (volume.restrict (Ioc ell B)).withDensity (fun t : ℝ => ENNReal.ofReal (t⁻¹)) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [kernel_lintegral ell B hf]
  have hm : Measurable (fun t : ℝ => ENNReal.ofReal (t⁻¹)) := ENNReal.measurable_ofReal.comp measurable_inv
  exact (lintegral_withDensity_eq_lintegral_mul _ hm hf).symm

lemma kernel_eq_zero {ell B : ℝ} (hB : B≤ell) : kernel ell B = 0 := by
  rw [kernel_eq_restrict,Ioc_eq_empty_of_le hB]
  simp

lemma bound_on {ell B : ℝ} (hell : 0<ell) (hB : ell≤B) : bound ell B = B/ell := by
  exact max_eq_right ((le_div_iff₀ hell).mpr (by linarith))

lemma bound_below {ell B : ℝ} (hell : 0<ell) (hB : B≤ell) : bound ell B = 1 := by
  exact max_eq_left ((div_le_iff₀ hell).mpr (by linarith))

end ErdosPrimeInputs.HarmonicPrefixKernel

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_AdmittedExponentMarginal
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.ContinuousRatioBins.ratioMeasure_noAtoms _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.HarmonicExponentMeasure

open Set MeasureTheory
open scoped ENNReal
open FinitePathGeometry HarmonicChangeOfVariable

theorem exponent_image_Ici {r a : ℝ} (hr : 0 < r) (ha : 0 < a) :
    nextExponent r '' Ici a = Ioc 0 (nextExponent r a) := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    change a ≤ t at ht
    refine ⟨nextExponent_pos hr (ha.trans_le ht), ?_⟩
    exact div_le_div_of_nonneg_left hr.le (by linarith : 0 < a + 1) (by linarith)
  · intro hx
    refine ⟨r / x - 1, ?_, ?_⟩
    · change a ≤ r / x - 1
      have hm := (le_div_iff₀ (by linarith : 0 < a + 1)).mp hx.2
      have hd : a + 1 ≤ r / x := (le_div_iff₀ hx.1).mpr (by nlinarith)
      linarith
    · unfold nextExponent
      simp only [sub_add_cancel]
      field_simp [hr.ne', hx.1.ne']

theorem nextExponent_injOn {r a : ℝ} (hr : 0 < r) (ha : 0 < a) :
    InjOn (nextExponent r) (Ici a) := by
  intro t ht u hu heq
  have h := congrArg (fun x : ℝ => r / x - 1) heq
  simpa only [inverse_exponent hr (ha.trans_le ht), inverse_exponent hr (ha.trans_le hu)] using h

theorem harmonic_lintegral_substitution {r a : ℝ} (hr : 0 < r) (ha : 0 < a)
    (H : ℝ → ℝ≥0∞) :
    (∫⁻ t in Ici a, ENNReal.ofReal (1 / (t + 1)) * H (nextExponent r t)) =
      ∫⁻ x in Ioc 0 (nextExponent r a), ENNReal.ofReal x⁻¹ * H x := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (f := nextExponent r)
    (f' := fun t => -r / (t + 1)^2) measurableSet_Ici
    (fun t ht => (exponent_hasDerivAt (r := r) (ha.trans_le ht)).hasDerivWithinAt)
    (nextExponent_injOn hr ha) (fun x => ENNReal.ofReal x⁻¹ * H x)
  rw [exponent_image_Ici hr ha] at h
  rw [h]
  apply lintegral_congr_ae
  apply ae_restrict_of_forall_mem measurableSet_Ici
  intro t ht
  have ht0 := ha.trans_le ht
  have hx := nextExponent_pos hr ht0
  have heq : |(-r / (t + 1)^2)| * (nextExponent r t)⁻¹ = 1 / (t + 1) := by
    have hj := harmonic_jacobian hr ht0
    rw [(exponent_hasDerivAt (r := r) ht0).deriv] at hj
    simpa only [div_eq_mul_inv] using hj
  dsimp only
  rw [← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _), heq]

theorem inverseRatio_measurable (r : ℝ) : Measurable (inverseRatio r) :=
  (measurable_const.div measurable_id).sub_const 1

theorem inverse_lintegral_substitution {r a : ℝ} (hr : 0 < r) (ha : 0 < a)
    (H : ℝ → ℝ≥0∞) :
    (∫⁻ t in Ici a, ENNReal.ofReal (1 / (t + 1)) * H t) =
      ∫⁻ x in Ioc 0 (nextExponent r a), ENNReal.ofReal x⁻¹ * H (inverseRatio r x) := by
  calc
    _ = ∫⁻ t in Ici a, ENNReal.ofReal (1 / (t + 1)) * H (inverseRatio r (nextExponent r t)) := by
      apply lintegral_congr_ae
      apply ae_restrict_of_forall_mem measurableSet_Ici
      intro t ht
      dsimp only
      rw [inverseRatio, inverse_exponent hr (ha.trans_le ht)]
    _ = _ := harmonic_lintegral_substitution hr ha (fun x => H (inverseRatio r x))

theorem exponentMeasure_map {r a : ℝ} (hr : 0 < r) (ha : 0 < a) :
    (exponentMeasure (nextExponent r a)).map (inverseRatio r) = ratioMeasure a := by
  apply Measure.ext_of_lintegral
  intro H hH
  rw [lintegral_map hH (inverseRatio_measurable r)]
  unfold ratioMeasure exponentMeasure
  rw [lintegral_withDensity_eq_lintegral_mul _ (f := fun x : ℝ => ENNReal.ofReal x⁻¹)
      (g := fun x : ℝ => H (inverseRatio r x)) (by fun_prop) (hH.comp (inverseRatio_measurable r)),
    lintegral_withDensity_eq_lintegral_mul _ (f := fun t : ℝ => ENNReal.ofReal (1 / (t + 1)))
      (g := H) (by fun_prop) hH]
  exact (inverse_lintegral_substitution hr ha H).symm

theorem ratioMeasure_map_update {β : Type*} [MeasurableSpace β]
    {r a : ℝ} (hr : 0 < r) (ha : 0 < a) (U : ℝ → β) (hU : Measurable U) :
    (ratioMeasure a).map U =
      (exponentMeasure (nextExponent r a)).map (fun x => U (inverseRatio r x)) := by
  rw [← exponentMeasure_map hr ha, Measure.map_map hU (inverseRatio_measurable r)]
  rfl

end NumberTheoryLean.HarmonicExponentMeasure

end

section

namespace NumberTheoryLean.HarmonicExponentRows

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostGrouping
open HarmonicExponentMeasure HarmonicKernelDensities HarmonicWeightKernel
open ArrivalKernelGeometry AdmittedHarmonicPaths RegeneratingInverseBands
open Erdos970Dependency.OrdinaryKernelInvariance

 theorem exponentMeasure_restrict (b : ℝ) {ell : ℝ} (hell : 0 ≤ ell) :
    (exponentMeasure b).restrict (Ioi ell) =
      (volume.restrict (Ioc ell b)).withDensity (fun x : ℝ => ENNReal.ofReal x⁻¹) := by
  unfold exponentMeasure
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
  congr 2
  ext x
  simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
  constructor
  · rintro ⟨hx, _, hu⟩; exact ⟨hx, hu⟩
  · intro hx; exact ⟨hx.1, lt_of_le_of_lt hell hx.1, hx.2⟩

theorem exponentMeasure_ae_interval (b : ℝ) :
    ∀ᵐ x ∂exponentMeasure b, x ∈ Ioc 0 b := by
  unfold exponentMeasure
  rw [ae_withDensity_iff (by fun_prop : Measurable (fun x : ℝ => ENNReal.ofReal x⁻¹))]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with x hx
  intro _
  exact hx

theorem accepted_update_measure {β : Type*} [MeasurableSpace β]
    {r a ell : ℝ} (hr : 0 < r) (ha : 0 < a) (hell : 0 ≤ ell)
    (U : ℝ → β) (hU : Measurable U) (A : Set β) (hA : MeasurableSet A)
    (hcut : ∀ t, a ≤ t → (U t ∈ A ↔ ell < nextExponent r t)) :
    ((ratioMeasure a).map U).restrict A =
      ((volume.restrict (Ioc ell (nextExponent r a))).withDensity
        (fun x : ℝ => ENNReal.ofReal x⁻¹)).map (fun x => U (inverseRatio r x)) := by
  rw [ratioMeasure_map_update hr ha U hU,
    Measure.restrict_map (f := fun x => U (inverseRatio r x)) (hU.comp (inverseRatio_measurable r)) hA]
  have hEq : (fun x => U (inverseRatio r x)) ⁻¹' A =ᵐ[exponentMeasure (nextExponent r a)] Ioi ell := by
    filter_upwards [exponentMeasure_ae_interval (nextExponent r a)] with x hx
    obtain ⟨t, ht, rfl⟩ := (exponent_image_Ici hr ha).symm.subset hx
    apply propext
    change U (inverseRatio r (nextExponent r t)) ∈ A ↔ ell < nextExponent r t
    rw [inverseRatio, HarmonicChangeOfVariable.inverse_exponent hr (ha.trans_le ht)]
    exact hcut t ht
  rw [Measure.restrict_congr_set hEq, exponentMeasure_restrict _ hell]

theorem harmonic_even_ratioMeasure (s : EvenState) (T : ℝ) :
    harmonicKernel (.inl s, T) = (ratioMeasure (s.1 - 1)).map (evenUpdateReal T) := by
  rw [harmonic_even_measure]
  unfold harmonicRatioDensity
  rw [withDensity_indicator measurableSet_Ici]
  rfl

theorem harmonic_odd_ratioMeasure (s : OddState) (T : ℝ) :
    harmonicKernel (.inr s, T) = (ratioMeasure (max 2 (s.1 - 1))).map (oddUpdateReal T) := by
  rw [harmonic_odd_measure]
  unfold harmonicRatioDensity
  rw [withDensity_indicator measurableSet_Ici]
  rfl

theorem evenUpdate_exponent (v T : ℝ) (s : EvenState) {t : ℝ} (ht : s.1 - 1 ≤ t) :
    currentExponent v (evenUpdateReal T t) = nextExponent (Real.exp (v - T)) t := by
  have hratio : stateRatio (.inr (oddLift t)) = t := by
    change max (95 / 100 : ℝ) t = t
    apply max_eq_right
    linarith [s.2]
  change currentExponent v (.inr (oddLift t), T + cost t) = _
  simpa only [hratio, gapValue] using currentExponent_update v ((.inl s), T) (.inr (oddLift t))

theorem oddUpdate_exponent (v T : ℝ) (s : OddState) {t : ℝ} (ht : max 2 (s.1 - 1) ≤ t) :
    currentExponent v (oddUpdateReal T t) = nextExponent (Real.exp (v - T)) t := by
  have hratio : stateRatio (.inl (evenLift t)) = t := by
    change max (198 / 100 : ℝ) t = t
    apply max_eq_right
    linarith [le_max_left (2 : ℝ) (s.1 - 1)]
  change currentExponent v (.inl (evenLift t), T + cost t) = _
  simpa only [hratio, gapValue] using currentExponent_update v ((.inr s), T) (.inl (evenLift t))

theorem admitted_even_exponent_row (v T : ℝ) (s : EvenState) {ell : ℝ} (hell : 0 ≤ ell) :
    admittedHarmonic v ell (.inl s, T) =
      ((volume.restrict (Ioc ell (Real.exp (v - T) / s.1))).withDensity
        (fun x : ℝ => ENNReal.ofReal x⁻¹)).map
          (fun x => evenUpdateReal T (inverseRatio (Real.exp (v - T)) x)) := by
  rw [admittedHarmonic, Kernel.restrict_apply, harmonic_even_ratioMeasure]
  have h := accepted_update_measure (Real.exp_pos (v - T))
    (by linarith [s.2] : 0 < s.1 - 1) hell (evenUpdateReal T) (evenUpdateReal_measurable T)
    (arrivalSet v ell) (arrivalSet_measurable v ell) (fun t ht => by
      change ell < currentExponent v (evenUpdateReal T t) ↔ _
      rw [evenUpdate_exponent v T s ht])
  simpa only [nextExponent, sub_add_cancel] using h

theorem admitted_odd_exponent_row (v T : ℝ) (s : OddState) {ell : ℝ} (hell : 0 ≤ ell) :
    admittedHarmonic v ell (.inr s, T) =
      ((volume.restrict (Ioc ell (nextExponent (Real.exp (v - T)) (max 2 (s.1 - 1))))).withDensity
        (fun x : ℝ => ENNReal.ofReal x⁻¹)).map
          (fun x => oddUpdateReal T (inverseRatio (Real.exp (v - T)) x)) := by
  rw [admittedHarmonic, Kernel.restrict_apply, harmonic_odd_ratioMeasure]
  exact accepted_update_measure (Real.exp_pos (v - T))
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_left _ _)) hell
    (oddUpdateReal T) (oddUpdateReal_measurable T) (arrivalSet v ell) (arrivalSet_measurable v ell)
    (fun t ht => by
      change ell < currentExponent v (oddUpdateReal T t) ↔ _
      rw [oddUpdate_exponent v T s ht])

end NumberTheoryLean.HarmonicExponentRows

end

section

namespace NumberTheoryLean.AdmittedExponentMarginal

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostGrouping
open HarmonicExponentMeasure HarmonicExponentRows HarmonicKernelDensities
open ArrivalKernelGeometry AdmittedHarmonicPaths

 theorem inverse_update_marginal {β : Type*} [MeasurableSpace β]
    {r a ell : ℝ} (hr : 0 < r) (ha : 0 < a) (hell : 0 ≤ ell)
    (U : ℝ → β) (hU : Measurable U) (V : β → ℝ) (hV : Measurable V)
    (hVU : ∀ t, a ≤ t → V (U t) = nextExponent r t) :
    ((((volume.restrict (Ioc ell (nextExponent r a))).withDensity
      (fun x : ℝ => ENNReal.ofReal x⁻¹)).map (fun x => U (inverseRatio r x))).map V) =
      (volume.restrict (Ioc ell (nextExponent r a))).withDensity (fun x : ℝ => ENNReal.ofReal x⁻¹) := by
  let μ := (volume.restrict (Ioc ell (nextExponent r a))).withDensity (fun x : ℝ => ENNReal.ofReal x⁻¹)
  have hs : ∀ᵐ x ∂μ, x ∈ Ioc ell (nextExponent r a) :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioc)
  have hEq : (V ∘ (fun x => U (inverseRatio r x))) =ᵐ[μ] id := by
    filter_upwards [hs] with x hx
    have hx' : x ∈ Ioc 0 (nextExponent r a) := ⟨lt_of_le_of_lt hell hx.1, hx.2⟩
    obtain ⟨t, ht, rfl⟩ := (exponent_image_Ici hr ha).symm.subset hx'
    change V (U (inverseRatio r (nextExponent r t))) = nextExponent r t
    rw [inverseRatio, HarmonicChangeOfVariable.inverse_exponent hr (ha.trans_le ht)]
    exact hVU t ht
  rw [Measure.map_map (f := fun x => U (inverseRatio r x)) hV (hU.comp (inverseRatio_measurable r))]
  exact (Measure.map_congr hEq).trans Measure.map_id

theorem admitted_even_exponent_marginal (v T : ℝ) (s : EvenState) {ell : ℝ} (hell : 0 ≤ ell) :
    (admittedHarmonic v ell (.inl s, T)).map (currentExponent v) =
      ErdosPrimeInputs.HarmonicPrefixKernel.kernel ell (currentExponent v (.inl s, T)) := by
  rw [admitted_even_exponent_row v T s hell, ErdosPrimeInputs.HarmonicPrefixKernel.kernel_eq_restrict]
  have h := inverse_update_marginal (Real.exp_pos (v - T))
    (by linarith [s.2] : 0 < s.1 - 1) hell (evenUpdateReal T) (evenUpdateReal_measurable T)
    (currentExponent v) (currentExponent_measurable v) (fun t ht => evenUpdate_exponent v T s ht)
  simpa only [nextExponent, sub_add_cancel, currentExponent, RegeneratingInverseBands.gapValue,
    stateRatio, Sum.elim_inl] using h

theorem admitted_odd_exponent_marginal (v T : ℝ) (s : OddState) {ell : ℝ} (hell : 0 ≤ ell) :
    (admittedHarmonic v ell (.inr s, T)).map (currentExponent v) =
      ErdosPrimeInputs.HarmonicPrefixKernel.kernel ell
        (nextExponent (Real.exp (v - T)) (max 2 (s.1 - 1))) := by
  rw [admitted_odd_exponent_row v T s hell, ErdosPrimeInputs.HarmonicPrefixKernel.kernel_eq_restrict]
  exact inverse_update_marginal (Real.exp_pos (v - T))
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_left _ _)) hell
    (oddUpdateReal T) (oddUpdateReal_measurable T) (currentExponent v) (currentExponent_measurable v)
    (fun t ht => oddUpdate_exponent v T s ht)

theorem harmonic_cutoff_mono (ell : ℝ) {a b : ℝ} (hab : a ≤ b) :
    ErdosPrimeInputs.HarmonicPrefixKernel.kernel ell a ≤
      ErdosPrimeInputs.HarmonicPrefixKernel.kernel ell b := by
  rw [ErdosPrimeInputs.HarmonicPrefixKernel.kernel_eq_restrict,
    ErdosPrimeInputs.HarmonicPrefixKernel.kernel_eq_restrict,
    ← withDensity_indicator measurableSet_Ioc, ← withDensity_indicator measurableSet_Ioc]
  apply withDensity_mono
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : x ∈ Ioc ell a
  · have hx' : x ∈ Ioc ell b := ⟨hx.1, hx.2.trans hab⟩
    rw [indicator_of_mem hx, indicator_of_mem hx']
  · rw [indicator_of_notMem hx]
    exact zero_le

theorem admitted_exponent_marginal_le (v : ℝ) {ell : ℝ} (hell : 0 ≤ ell) (z : CostState) :
    (admittedHarmonic v ell z).map (currentExponent v) ≤
      ErdosPrimeInputs.HarmonicPrefixKernel.kernel ell (currentExponent v z) := by
  rcases z with ⟨s, T⟩
  cases s with
  | inl s => exact (admitted_even_exponent_marginal v T s hell).le
  | inr s =>
    rw [admitted_odd_exponent_marginal v T s hell]
    apply harmonic_cutoff_mono
    exact exponent_le_cutoff (i := .odd) (s := s.1) s.2 le_rfl (Real.exp_pos (v - T))

end NumberTheoryLean.AdmittedExponentMarginal

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

namespace NumberTheoryLean.CemeteryPowers

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open CemeteryKernel

variable {α : Type*} [MeasurableSpace α]

theorem liftReward_measurable {F : α → ℝ≥0∞} (hF : Measurable F) : Measurable (liftReward F) :=
  hF.sumElim measurable_const

theorem row_lift (K : Kernel α α) {F : α → ℝ≥0∞} (hF : Measurable F) (q : Space α) :
    (∫⁻ y,liftReward F y ∂complete K q) = liftReward (fun z => ∫⁻ y,F y ∂K z) q := by
  cases q with
  | inl z =>
    rw [complete_live,liveRow_apply,lintegral_add_measure,
      lintegral_map (liftReward_measurable hF) measurable_inl,
      lintegral_smul_measure,lintegral_dirac' _ (liftReward_measurable hF)]
    simp only [liftReward,Sum.elim_inl,dead,Sum.elim_inr,smul_eq_mul,mul_zero,add_zero]
  | inr u =>
    cases u
    change (∫⁻ y,liftReward F y ∂Measure.dirac dead) = 0
    rw [lintegral_dirac' _ (liftReward_measurable hF)]
    rfl

theorem power_lift (K : Kernel α α) {F : α → ℝ≥0∞} (hF : Measurable F) (n : ℕ) (q : Space α) :
    (∫⁻ y,liftReward F y ∂((complete K)^n) q) = liftReward (fun z => ∫⁻ y,F y ∂(K^n) z) q := by
  induction n generalizing q with
  | zero =>
    change (∫⁻ y,liftReward F y ∂Measure.dirac q) = _
    rw [lintegral_dirac' _ (liftReward_measurable hF)]
    cases q with
    | inl z =>
      change F z = ∫⁻ y,F y ∂Measure.dirac z
      rw [lintegral_dirac' _ hF]
    | inr u => rfl
  | succ n ih =>
    have hp : (complete K)^(n+1) = ((complete K)^n) ∘ₖ complete K := pow_succ _ _
    have hl : K^(n+1) = (K^n) ∘ₖ K := pow_succ _ _
    rw [hp,Kernel.lintegral_comp _ _ _ (liftReward_measurable hF)]
    calc
      _ = ∫⁻ y,liftReward (fun z => ∫⁻ a,F a ∂(K^n) z) y ∂complete K q := lintegral_congr ih
      _ = liftReward (fun y => ∫⁻ z,∫⁻ a,F a ∂(K^n) z ∂K y) q := row_lift K hF.lintegral_kernel q
      _ = _ := by
        cases q with
        | inl z =>
          change _ = ∫⁻ y,F y ∂(K^(n+1)) z
          rw [hl,Kernel.lintegral_comp _ _ _ hF]
          rfl
        | inr u => rfl

end NumberTheoryLean.CemeteryPowers

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

namespace NumberTheoryLean.ActualProcessCoupling

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ContinuousKilledBins MeshRatioLabels KernelCouplingLift KernelBinConditioning

instance continuousParent_isMarkov (w ell S : ℝ) (start : Node) (v : ℝ) :
    IsMarkovKernel (continuousParent w ell S start v) := by unfold continuousParent; infer_instance

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

end NumberTheoryLean.ActualCouplingFinite

end

section

namespace NumberTheoryLean.ActualCouplingUpdates

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ActualCouplingSupport ContinuousKilledBins
open LowStateHorizon ArrivalKernelGeometry RegeneratingInverseBands
open PrimeTiltGeometry KernelDensityBridge PairedCostGrouping

variable {w ell S : ℝ} {start : Node}

theorem side_set_measurable (i : Side) : MeasurableSet {s : State | stateSide s = i} := by
  cases i <;> apply measurableSet_sum_iff.mpr <;> simp [stateSide]

end NumberTheoryLean.ActualCouplingUpdates

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FlaggedSourceStart
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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

theorem row_update_measurable {Bad : α → Prop} (hBad : MeasurableSet {x | Bad x}) (b : Bool) :
    Measurable (fun y : α => (y,b || badBit Bad y)) := by
  have hor : Measurable (fun p : Bool × Bool => p.1 || p.2) := measurable_of_countable _
  exact measurable_id.prodMk (hor.comp (measurable_const.prodMk (badBit_measurable hBad)))

theorem failed_measurable : MeasurableSet (failed (α:=α)) :=
  measurable_snd (measurableSet_singleton true)

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



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SuccessfulRewardComparison
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SuccessfulRewardComparison

open _root_.Set _root_.MeasureTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualFlagInvariant DerivativeWeights
open RegeneratingInverseBands InvariantInverseWeights ArrivalKernelGeometry

theorem stateWeight_eq (s : State) : stateWeight s = weight (stateSide s) (stateRatio s) := by
  cases s <;> rfl

end NumberTheoryLean.SuccessfulRewardComparison

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_CompactTestMeasurable
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.CompactTestMeasurable

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open CompactTestGeometry RegeneratingInverseBands ActualCouplingUpdates ArrivalKernelGeometry

variable {w ell S : ℝ} {start : Node}

theorem continuousTest_measurable (v : ℝ) (F : Side → ℝ×ℝ → ℝ) (hF : ∀ i,Measurable (F i)) :
    Measurable (continuousTest v F) := by
  have hcoord : Measurable (fun z : CostState => (gapValue v z,stateRatio z.1)) :=
    (gapValue_measurable v).prodMk (stateRatio_measurable.comp measurable_fst)
  have hside : MeasurableSet {z : CostState | stateSide z.1 = .even} :=
    measurable_fst (side_set_measurable .even)
  have heq : (fun z : CostState => F (stateSide z.1) (gapValue v z,stateRatio z.1)) =
      (fun z => if stateSide z.1 = .even then F .even (gapValue v z,stateRatio z.1)
        else F .odd (gapValue v z,stateRatio z.1)) := by
    funext z
    rcases z with ⟨s,t⟩
    cases s <;> rfl
  have hb : Measurable (fun z : CostState => F (stateSide z.1) (gapValue v z,stateRatio z.1)) := by
    rw [heq]
    exact Measurable.ite hside ((hF .even).comp hcoord) ((hF .odd).comp hcoord)
  exact hb.sumElim measurable_const

section Generic
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem bounded_integrable [IsFiniteMeasure μ] {f : α → ℝ} (hf : Measurable f)
    {A : ℝ} (hb : ∀ x,|f x| ≤ A) : Integrable f μ := by
  refine (integrable_const A).mono' hf.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb x)

end Generic

end NumberTheoryLean.CompactTestMeasurable

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_LogSquaredDecay
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosPrimeInputs.LogSquaredDecay

open Filter
open scoped Topology

lemma power_exponential_saving {c : ℝ} (hc : 0 < c) (p A : ℝ) : ∀ᶠ B : ℝ in atTop,
    B^p * Real.exp (-c*((Real.log B)^2/2)) ≤ B^(-A) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 (2*(A+p)/c)))] with B hB hL
  have hB0 : 0<B := by linarith
  have hL0 : 0≤Real.log B := le_trans zero_le_one ((le_max_left _ _).trans hL)
  have ht : 2*(A+p)≤Real.log B*c := (div_le_iff₀ hc).mp ((le_max_right _ _).trans hL)
  have hm := mul_le_mul_of_nonneg_right ht hL0
  have he : Real.log B*p + (-c*((Real.log B)^2/2)) ≤ Real.log B*(-A) := by nlinarith
  calc
    _ = Real.exp (Real.log B*p + (-c*((Real.log B)^2/2))) := by
      rw [Real.exp_add,Real.rpow_def_of_pos hB0]
    _ ≤ Real.exp (Real.log B*(-A)) := Real.exp_le_exp.mpr he
    _ = _ := (Real.rpow_def_of_pos hB0 (-A)).symm

lemma constant_power_saving {c : ℝ} (hc : 0 < c) (C p A : ℝ) : ∀ᶠ B : ℝ in atTop,
    C*B^p*Real.exp (-c*((Real.log B)^2/2)) ≤ (1/2)*B^(-A) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),eventually_ge_atTop (2*C),
    power_exponential_saving hc (p+1) A] with B hB hC hs
  have hB0 : 0<B := by linarith
  have hcB : C≤B/2 := by linarith
  calc
    _ ≤ (B/2)*B^p*Real.exp (-c*((Real.log B)^2/2)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcB (Real.rpow_nonneg hB0.le _)) (Real.exp_pos _).le
    _ = (1/2)*(B^(p+1)*Real.exp (-c*((Real.log B)^2/2))) := by
      rw [Real.rpow_add hB0,Real.rpow_one]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (by norm_num)

lemma half_floor_bound (S : ℝ) :
    (1/2:ℝ)^⌊S/2⌋₊ ≤ 2*Real.exp (-Real.log 2*(S/2)) := by
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hfloor := Nat.lt_floor_add_one (S/2)
  have hexponent : (⌊S/2⌋₊:ℝ)*(-Real.log 2) ≤ Real.log 2-Real.log 2*(S/2) := by
    nlinarith
  have hhalf : (1/2:ℝ)=Real.exp (-Real.log 2) := by
    rw [Real.exp_neg,Real.exp_log (by norm_num)]
    norm_num
  calc
    _ = Real.exp ((⌊S/2⌋₊:ℝ)*(-Real.log 2)) := by rw [Real.exp_nat_mul,← hhalf]
    _ ≤ Real.exp (Real.log 2-Real.log 2*(S/2)) := Real.exp_le_exp.mpr hexponent
    _ = _ := by rw [sub_eq_add_neg,Real.exp_add,Real.exp_log (by norm_num),neg_mul]

end ErdosPrimeInputs.LogSquaredDecay

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_HighPrefixState
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.ErdosPrimeInputs.HighPrefixKernel.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosPrimeInputs.HarmonicPrefixTilt

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal
open WeightedKernelMass HarmonicPrefixKernel

lemma squareBoundE_measurable (ell : ℝ) : Measurable (squareBoundE ell) := by
  unfold squareBoundE bound
  fun_prop

lemma linear_lintegral {ell B : ℝ} (hell : 0<ell) (hB : ell≤B) :
    (∫⁻ t in Ioc ell B, ENNReal.ofReal (t/ell^2)) =
      ENNReal.ofReal (((B^2-ell^2)/2)/ell^2) := by
  have hi : IntegrableOn (fun t : ℝ => t/ell^2) (Ioc ell B) :=
    ((continuous_id.div_const (ell^2)).continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hn : ∀ᵐ t ∂volume.restrict (Ioc ell B), 0≤t/ell^2 := by
    apply ae_restrict_of_forall_mem measurableSet_Ioc
    intro t ht
    exact div_nonneg (hell.le.trans ht.1.le) (sq_nonneg _)
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn,← intervalIntegral.integral_of_le hB]
  simp only [div_eq_mul_inv,intervalIntegral.integral_mul_const,_root_.integral_id]

lemma harmonic_square_integral {ell B : ℝ} (hell : 0<ell) (hB : ell≤B) :
    (∫⁻ t, squareBoundE ell t ∂kernel ell B) =
      ENNReal.ofReal (((B^2-ell^2)/2)/ell^2) := by
  rw [kernel_lintegral ell B (squareBoundE_measurable ell)]
  calc
    _ = ∫⁻ t in Ioc ell B, ENNReal.ofReal (t/ell^2) := by
      apply lintegral_congr_ae
      apply ae_restrict_of_forall_mem measurableSet_Ioc
      intro t ht
      have ht0 : 0<t := hell.trans ht.1
      change ENNReal.ofReal (t⁻¹)*ENNReal.ofReal (bound ell t ^ 2) = _
      rw [bound_on hell ht.1.le,← ENNReal.ofReal_mul (inv_nonneg.mpr ht0.le)]
      congr 1
      field_simp
    _ = _ := linear_lintegral hell hB

theorem schur_two {ell : ℝ} (hell : 0<ell) (B : ℝ) :
    1+2*(∫⁻ t, squareBoundE ell t ∂kernel ell B) = squareBoundE ell B := by
  by_cases hB : ell≤B
  · rw [harmonic_square_integral hell hB,squareBoundE,bound_on hell hB]
    have hD : 0≤((B^2-ell^2)/2)/ell^2 := by
      apply div_nonneg
      · apply div_nonneg
        · nlinarith
        · norm_num
      · exact sq_nonneg _
    calc
      _ = ENNReal.ofReal (1+2*(((B^2-ell^2)/2)/ell^2)) := by
        rw [ENNReal.ofReal_add (by norm_num) (mul_nonneg (by norm_num) hD),
          ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2)]
        norm_num
      _ = _ := by
        congr 1
        field_simp
        ring
  · rw [kernel_eq_zero (le_of_not_ge hB),squareBoundE,bound_below hell (le_of_not_ge hB)]
    simp

end ErdosPrimeInputs.HarmonicPrefixTilt

end

section

namespace ErdosPrimeInputs.HarmonicLongPrefixes

open scoped ENNReal
open WeightedKernelMass HarmonicPrefixKernel HarmonicPrefixTilt

lemma half_power_antitone {m n : ℕ} (hmn : m≤n) :
    ((2:ℝ≥0∞)⁻¹)^n ≤ ((2:ℝ≥0∞)⁻¹)^m := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hmn
  have hp : ((2:ℝ≥0∞)⁻¹)^k ≤ 1 := pow_le_one₀ zero_le (by norm_num)
  calc
    _ = ((2:ℝ≥0∞)⁻¹)^m * ((2:ℝ≥0∞)⁻¹)^k := pow_add _ _ _
    _ ≤ ((2:ℝ≥0∞)⁻¹)^m * 1 := mul_le_mul le_rfl hp zero_le zero_le
    _ = _ := mul_one _

lemma unweight_two (a : ℝ≥0∞) (n : ℕ) :
    a = ((2:ℝ≥0∞)⁻¹)^n * ((2:ℝ≥0∞)^n*a) := by
  have hi : (2:ℝ≥0∞)⁻¹*2=1 := ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  calc
    a = 1*a := (one_mul _).symm
    _ = ((2:ℝ≥0∞)⁻¹*2)^n*a := by rw [hi,one_pow]
    _ = _ := by rw [mul_pow,mul_assoc]

theorem weighted_tail_bound (a : ℕ → ℝ≥0∞) (m : ℕ) {W : ℝ≥0∞}
    (hW : (∑' n : ℕ, (2:ℝ≥0∞)^n*a n) ≤ W) :
    tailMass a m ≤ ((2:ℝ≥0∞)⁻¹)^m*W := by
  calc
    _ ≤ ∑' n : ℕ, ((2:ℝ≥0∞)⁻¹)^m*((2:ℝ≥0∞)^n*a n) := by
      apply ENNReal.tsum_le_tsum
      intro n
      by_cases hn : m≤n
      · rw [ite_eq_left hn]
        exact (unweight_two (a n) n).trans_le (mul_le_mul (half_power_antitone hn) le_rfl zero_le zero_le)
      · rw [ite_eq_right hn]
        exact zero_le
    _ = ((2:ℝ≥0∞)⁻¹)^m*(∑' n : ℕ, (2:ℝ≥0∞)^n*a n) := ENNReal.tsum_mul_left
    _ ≤ _ := mul_le_mul le_rfl hW zero_le zero_le

end ErdosPrimeInputs.HarmonicLongPrefixes

end

section

namespace ErdosPrimeInputs.HighPrefixState

open Set MeasureTheory

lemma update_measurable (S : ℝ) : Measurable (Function.uncurry (update S)) := by
  have hf : Measurable (fun x : State × ℝ => x.1.2.2) := by fun_prop
  have hr : Measurable (fun x : State × ℝ => (x.1.2.1-x.2)/x.2) := by fun_prop
  have hset : MeasurableSet {x : State × ℝ | x.1.2.2=true ∨ S<(x.1.2.1-x.2)/x.2} :=
    (hf (measurableSet_singleton true)).union (measurableSet_lt measurable_const hr)
  exact measurable_snd.prodMk ((by fun_prop : Measurable (fun x : State × ℝ => x.1.2.1-x.2)).prodMk
    (Measurable.ite hset measurable_const measurable_const))

lemma update_flag (S : ℝ) (z : State) (t : ℝ) :
    (update S z t).2.2=true ↔ z.2.2=true ∨ S<(z.2.1-t)/t := by
  by_cases h : z.2.2=true ∨ S<(z.2.1-t)/t <;> simp [update,h]

lemma invariant_measurable (ell S : ℝ) (n : ℕ) : MeasurableSet {z : State | Invariant ell S n z} := by
  have hf : Measurable (fun z : State => z.2.2) := measurable_snd.comp measurable_snd
  have hg : Measurable (fun z : State => z.2.1) := measurable_fst.comp measurable_snd
  have hb : MeasurableSet {z : State | ell≤z.1} := measurableSet_le measurable_const measurable_fst
  have hh : MeasurableSet {z : State | z.2.2=true} := hf (measurableSet_singleton true)
  have hr : MeasurableSet {z : State | (S-(n:ℝ))*z.1<z.2.1} :=
    measurableSet_lt (measurable_const.mul measurable_fst) hg
  simpa only [Invariant,imp_iff_not_or] using! hb.inter (hh.compl.union hr)

lemma initial_invariant {ell S B R : ℝ} (hell : 0<ell) (hB : ell≤B) :
    Invariant ell S 0 (initial S B R) := by
  have hB0 : 0<B := hell.trans_le hB
  refine ⟨hB,?_⟩
  intro hf
  have hhigh : S<R/B := by
    by_contra hn
    simp [initial,hn] at hf
  have h := (lt_div_iff₀ hB0).mp hhigh
  simpa only [Nat.cast_zero,sub_zero,initial] using! h

lemma update_invariant {ell S : ℝ} (hell : 0<ell) (n : ℕ) (z : State) (t : ℝ)
    (hz : Invariant ell S n z) (ht : ell<t ∧ t≤z.1) (hn : (n:ℝ)≤S) :
    Invariant ell S (n+1) (update S z t) := by
  have ht0 : 0<t := hell.trans ht.1
  refine ⟨ht.1.le,?_⟩
  intro hf
  have hcases := (update_flag S z t).mp hf
  change (S-((n+1:ℕ):ℝ))*t<z.2.1-t
  push_cast
  rcases hcases with hold | hnew
  · have hgap := hz.2 hold
    have hmul := mul_le_mul_of_nonneg_left ht.2 (sub_nonneg.mpr hn)
    nlinarith
  · have hgap := (lt_div_iff₀ ht0).mp hnew
    have hn0 : 0≤(n:ℝ)+1 := by positivity
    nlinarith [mul_nonneg hn0 ht0.le]

theorem short_high_gap {ell S : ℝ} (hell : 0<ell) (n : ℕ) (z : State)
    (hz : Invariant ell S n z) (hf : z.2.2=true) (hn : (n:ℝ)≤S/2) :
    S*ell/2<z.2.1 := by
  have hn0 : 0≤(n:ℝ) := Nat.cast_nonneg _
  have hS0 : 0≤S/2 := le_trans hn0 hn
  have hcoef : S/2≤S-(n:ℝ) := by linarith
  calc
    S*ell/2=(S/2)*ell := by ring
    _ ≤ (S-(n:ℝ))*z.1 := mul_le_mul hcoef hz.1 hell.le (hS0.trans hcoef)
    _ < z.2.1 := hz.2 hf

end ErdosPrimeInputs.HighPrefixState

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_HighPrefixKernel
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosPrimeInputs.HighPrefixKernel

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open WeightedKernelMass HarmonicPrefixKernel HarmonicPrefixTilt HarmonicLongPrefixes HighPrefixState

lemma update_at_measurable (S : ℝ) (z : State) : Measurable (update S z) :=
  (update_measurable S).of_uncurry_left

theorem kernel_eq_map (ell S : ℝ) (z : State) :
    kernel ell S z = (HarmonicPrefixKernel.kernel ell z.1).map (update S z) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [kernel,Kernel.map_apply _ (update_measurable S),lintegral_map hf (update_measurable S)]
  have hg : Measurable (fun p : State × ℝ => f (update S p.1 p.2)) := hf.comp (update_measurable S)
  calc
    _ = ∫⁻ t, f (update S z t) ∂HarmonicPrefixKernel.kernel ell z.1 :=
      Kernel.lintegral_id_prod (f := fun p : State × ℝ => f (update S p.1 p.2)) hg _ z
    _ = _ := (lintegral_map hf (update_at_measurable S z)).symm

lemma harmonic_ae_interval (ell B : ℝ) :
    ∀ᵐ t ∂HarmonicPrefixKernel.kernel ell B, t ∈ Ioc ell B := by
  rw [HarmonicPrefixKernel.kernel_eq_restrict,
    ae_withDensity_iff (by fun_prop : Measurable (fun t : ℝ => ENNReal.ofReal (t⁻¹)))]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
  intro _
  exact ht

theorem ae_update (ell S : ℝ) (z : State) {P : State → Prop}
    (hP : MeasurableSet {w | P w}) (h : ∀ t ∈ Ioc ell z.1, P (update S z t)) :
    ∀ᵐ w ∂kernel ell S z, P w := by
  rw [kernel_eq_map]
  apply (ae_map_iff (update_at_measurable S z).aemeasurable hP).mpr
  exact (harmonic_ae_interval ell z.1).mono (fun t ht => h t ht)

lemma state_schur_two {ell : ℝ} (hell : 0<ell) (S : ℝ) (z : State) :
    1+2*(∫⁻ w, squareBoundE ell w.1 ∂kernel ell S z) = squareBoundE ell z.1 := by
  rw [kernel_eq_map]
  have hf : Measurable (fun w : State => squareBoundE ell w.1) := (squareBoundE_measurable ell).comp measurable_fst
  rw [lintegral_map (f := fun w : State => squareBoundE ell w.1) hf (update_at_measurable S z)]
  exact schur_two hell z.1

theorem weighted_mass {ell B : ℝ} (hell : 0<ell) (hB : ell≤B) (S R : ℝ) :
    (∑' n : ℕ, (2:ℝ≥0∞)^n*mass (kernel ell S) n (initial S B R)) ≤ ENNReal.ofReal ((B/ell)^2) := by
  have h := weighted_total_bound (kernel ell S) 2 (fun z : State => squareBoundE ell z.1)
    (fun z => (state_schur_two hell S z).le) (initial S B R)
  simpa only [initial,squareBoundE,bound_on hell hB] using h

theorem ae_invariant {ell B : ℝ} (hell : 0<ell) (hB : ell≤B) (S R : ℝ) :
    ∀ n : ℕ, (n:ℝ)≤S →
      ∀ᵐ z ∂(kernel ell S ^ n) (initial S B R), Invariant ell S n z := by
  intro n
  induction n with
  | zero =>
    intro _
    change ∀ᵐ z ∂Measure.dirac (initial S B R), Invariant ell S 0 z
    exact (ae_dirac_iff (invariant_measurable ell S 0)).mpr (initial_invariant hell hB)
  | succ n ih =>
    intro hn
    have hn' : (n:ℝ)≤S := by push_cast at hn <;> linarith
    rw [pow_succ']
    apply Kernel.ae_comp_of_ae_ae (invariant_measurable ell S (n+1))
    filter_upwards [ih hn'] with z hz
    exact ae_update ell S z (invariant_measurable ell S (n+1))
      (fun t ht => update_invariant hell n z t hz ht hn')

end ErdosPrimeInputs.HighPrefixKernel

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_HighPrefixBounds
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosPrimeInputs.HighPrefixBounds

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal
open WeightedKernelMass HarmonicLongPrefixes HighPrefixState
open HighPrefixKernel

lemma low_high_zero {ell S B R K : ℝ} (hell : 0<ell) (hB : ell≤B)
    (n m : ℕ) (hm : (m:ℝ)≤S/2) (hn : n < m) (hK : K≤S*ell/2) :
    (kernel ell S ^ n) (initial S B R) {z | z.2.2=true ∧ z.2.1≤K} = 0 := by
  have hnm : (n:ℝ) < m := by exact_mod_cast hn
  have hnS : (n:ℝ)≤S := by nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hAE : ∀ᵐ z ∂(kernel ell S ^ n) (initial S B R), ¬(z.2.2=true ∧ z.2.1≤K) := by
    filter_upwards [ae_invariant hell hB S R n hnS] with z hz
    intro hbad
    have hgap := short_high_gap hell n z hz hbad.1 (hnm.le.trans hm)
    exact (not_lt_of_ge (hbad.2.trans hK)) hgap
  simpa only [not_not] using ae_iff.mp hAE

theorem low_high_bound {ell S B R K : ℝ} (hell : 0<ell) (hB : ell≤B)
    (m : ℕ) (hm : (m:ℝ)≤S/2) (hK : K≤S*ell/2) :
    lowHighMass ell S B R K ≤ ((2:ℝ≥0∞)⁻¹)^m*ENNReal.ofReal ((B/ell)^2) := by
  have htail : lowHighMass ell S B R K ≤ tailMass (fun n => mass (kernel ell S) n (initial S B R)) m := by
    apply ENNReal.tsum_le_tsum
    intro n
    by_cases hn : m≤n
    · rw [ite_eq_left hn]
      exact measure_mono (subset_univ _)
    · rw [ite_eq_right hn,low_high_zero hell hB n m hm (Nat.lt_of_not_ge hn) hK]
  exact htail.trans (weighted_tail_bound _ m (weighted_mass hell hB S R))

end ErdosPrimeInputs.HighPrefixBounds

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_ContinuousHighRemoval
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosPrimeInputs.ContinuousHighRemoval

open Filter
open scoped ENNReal Topology
open HighPrefixBounds LogSquaredDecay

lemma tail_coefficient_eq (ell B : ℝ) (m : ℕ) :
    ((2:ℝ≥0∞)⁻¹)^m*ENNReal.ofReal ((B/ell)^2) =
      ENNReal.ofReal ((1/2:ℝ)^m*(B/ell)^2) := by
  have hh : (2:ℝ≥0∞)⁻¹=ENNReal.ofReal (1/2:ℝ) := by
    rw [one_div,ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ)<2)]
    norm_num
  rw [hh,← ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤1/2),
    ← ENNReal.ofReal_mul (pow_nonneg (by norm_num : (0:ℝ)≤1/2) m)]

lemma tail_coefficient_bound {ell B : ℝ} (hell : 1≤ell) (hB : ell≤B) :
    ((2:ℝ≥0∞)⁻¹)^⌊(Real.log B)^2/2⌋₊ * ENNReal.ofReal ((B/ell)^2) ≤
      ENNReal.ofReal (2*B^2*Real.exp (-Real.log 2*((Real.log B)^2/2))) := by
  rw [tail_coefficient_eq]
  apply ENNReal.ofReal_le_ofReal
  have hB0 : 0≤B := zero_le_one.trans (hell.trans hB)
  have hell0 : 0<ell := zero_lt_one.trans_le hell
  have hr0 : 0≤B/ell := div_nonneg hB0 hell0.le
  have hr : B/ell≤B := div_le_self hB0 hell
  have hsq : (B/ell)^2≤B^2 := by
    simpa only [pow_two] using mul_le_mul hr hr hr0 hB0
  calc
    _ ≤ (2*Real.exp (-Real.log 2*((Real.log B)^2/2)))*B^2 :=
      mul_le_mul (half_floor_bound ((Real.log B)^2)) hsq (sq_nonneg _) (by positivity)
    _ = _ := by ring

lemma tail_saving (A : ℝ) : ∀ᶠ B : ℝ in atTop,
    2*B^2*Real.exp (-Real.log 2*((Real.log B)^2/2)) ≤ (1/2)*B^(-A) := by
  simpa only [Real.rpow_two] using
    constant_power_saving (Real.log_pos (by norm_num : (1:ℝ)<2)) 2 2 A

theorem low_gap_high_removal (K A : ℝ) : ∀ᶠ B : ℝ in atTop,
    ∀ ell : ℝ, 1≤ell → ell≤B → ∀ R : ℝ,
      lowHighMass ell ((Real.log B)^2) B R K ≤ ENNReal.ofReal (B^(-A)) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),tail_saving A,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 (2*K+1)))] with B hB1 htail hlog
  intro ell hell hB R
  have hell0 : 0<ell := zero_lt_one.trans_le hell
  have hS : 0≤(Real.log B)^2 := sq_nonneg _
  have hm : (⌊(Real.log B)^2/2⌋₊:ℝ)≤(Real.log B)^2/2 := Nat.floor_le (by positivity)
  have hl1 : 1≤Real.log B := (le_max_left _ _).trans hlog
  have hlK : 2*K+1≤Real.log B := (le_max_right _ _).trans hlog
  have hK : K≤(Real.log B)^2*ell/2 := by
    have hmul := mul_le_mul_of_nonneg_left hell hS
    nlinarith
  calc
    _ ≤ ((2:ℝ≥0∞)⁻¹)^⌊(Real.log B)^2/2⌋₊*ENNReal.ofReal ((B/ell)^2) :=
      low_high_bound hell0 hB _ hm hK
    _ ≤ ENNReal.ofReal (2*B^2*Real.exp (-Real.log 2*((Real.log B)^2/2))) := tail_coefficient_bound hell hB
    _ ≤ ENNReal.ofReal ((1/2)*B^(-A)) := ENNReal.ofReal_le_ofReal htail
    _ ≤ ENNReal.ofReal (B^(-A)) := ENNReal.ofReal_le_ofReal (by
      have hh := Real.rpow_nonneg (show 0≤B by linarith) (-A)
      nlinarith)

end ErdosPrimeInputs.ContinuousHighRemoval

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SignedCompletedPowers
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SignedCompletedPowers

open _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open CemeteryKernel CompactTestMeasurable

variable {α : Type*} [MeasurableSpace α]

theorem finite_kernel_power (K : Kernel α α) [IsFiniteKernel K] (n : ℕ) : IsFiniteKernel (K^n) := by
  induction n with
  | zero => change IsFiniteKernel (Kernel.id : Kernel α α); infer_instance
  | succ n ih =>
    let := ih
    have hp : K^(n+1) = (K^n) ∘ₖ K := pow_succ _ _
    rw [hp]
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem liftReal_measurable {F : α → ℝ} (hF : Measurable F) : Measurable (liftReal F) := hF.sumElim measurable_const

theorem real_power_lift (K : Kernel α α) (n : ℕ) (x : α)
    [IsFiniteMeasure (((complete K)^n) (.inl x))] [IsFiniteMeasure ((K^n) x)]
    {F : α → ℝ} (hF : Measurable F) {A : ℝ} (hA : 0 ≤ A) (hbound : ∀ y,|F y| ≤ A) :
    (∫ y,liftReal F y ∂((complete K)^n) (.inl x)) = ∫ y,F y ∂(K^n) x := by
  have hL : ∀ y : Space α,|liftReal F y| ≤ A := by
    intro y
    cases y with
    | inl a => exact hbound a
    | inr u => simpa only [liftReal,Sum.elim_inr,abs_zero] using hA
  have hIl : Integrable (liftReal F) (((complete K)^n) (.inl x)) := bounded_integrable (liftReal_measurable hF) hL
  have hIr : Integrable F ((K^n) x) := bounded_integrable hF hbound
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hIl,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hIr]
  have hp : (fun y : Space α => ENNReal.ofReal (liftReal F y)) = CemeteryPowers.liftReward (fun y => ENNReal.ofReal (F y)) := by
    funext y
    cases y <;> simp [liftReal,CemeteryPowers.liftReward]
  have hn : (fun y : Space α => ENNReal.ofReal (-liftReal F y)) = CemeteryPowers.liftReward (fun y => ENNReal.ofReal (-F y)) := by
    funext y
    cases y <;> simp [liftReal,CemeteryPowers.liftReward]
  rw [hp,hn,CemeteryPowers.power_lift K (F:=fun y => ENNReal.ofReal (F y)) (ENNReal.measurable_ofReal.comp hF),
    CemeteryPowers.power_lift K (F:=fun y => ENNReal.ofReal (-F y)) (ENNReal.measurable_ofReal.comp hF.neg)]
  rfl

open FinitePathMeasures ContinuousKilledBins LowStateHorizon

theorem continuous_signed_power (v ell S : ℝ) (n : ℕ) (z : CostState)
    {F : CostState → ℝ} (hF : Measurable F) {A : ℝ} (hA : 0 ≤ A) (hbound : ∀ y,|F y| ≤ A) :
    (∫ y,liftReal F y ∂((continuousChain v ell S)^n) (.inl z)) =
      ∫ y,F y ∂((lowKernel costKernel v ell S)^n) z := by
  let : IsFiniteKernel (lowKernel costKernel v ell S) := by unfold lowKernel; infer_instance
  let := finite_kernel_power (lowKernel costKernel v ell S) n
  let := finite_kernel_power (continuousChain v ell S) n
  let : IsFiniteMeasure (((complete (lowKernel costKernel v ell S))^n) (.inl z)) := by
    change IsFiniteMeasure (((continuousChain v ell S)^n) (.inl z))
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  exact real_power_lift (lowKernel costKernel v ell S) n z hF hA hbound

end NumberTheoryLean.SignedCompletedPowers

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FlaggedHarmonicPaths
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.continuousParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.ContinuousKilledBins.continuousChain_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.FlaggedHarmonicPaths

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathMeasures PairedCostGrouping ArrivalKernelGeometry
open AdmittedHarmonicPaths AdmittedExponentMarginal RegeneratingInverseBands

theorem flagUpdate_joint_measurable (S : ℝ) :
    Measurable (fun p : FlagState × CostState => flagUpdate S p.1.2 p.2) := by
  have hb : Measurable (fun p : FlagState × CostState => p.1.2) := by fun_prop
  have hr : Measurable (fun p : FlagState × CostState => stateRatio p.2.1) := stateRatio_measurable.comp (measurable_fst.comp measurable_snd)
  exact measurable_snd.prodMk (Measurable.ite
    ((hb (measurableSet_singleton true)).union (measurableSet_lt measurable_const hr))
    measurable_const measurable_const)

theorem flagUpdate_measurable (S : ℝ) (b : Bool) : Measurable (flagUpdate S b) := by
  have hr : Measurable (fun y : CostState => stateRatio y.1) := stateRatio_measurable.comp measurable_fst
  have hb : Measurable (fun _ : CostState => b) := measurable_const
  exact measurable_id.prodMk (Measurable.ite
    ((hb (measurableSet_singleton true)).union (measurableSet_lt measurable_const hr))
    measurable_const measurable_const)

theorem kernel_eq_map (v ell S : ℝ) (z : FlagState) :
    kernel v ell S z = (admittedHarmonic v ell z.1).map (flagUpdate S z.2) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [kernel, Kernel.map_apply _ (flagUpdate_joint_measurable S),
    lintegral_map hf (flagUpdate_joint_measurable S)]
  calc
    _ = ∫⁻ y, f (flagUpdate S z.2 y) ∂admittedHarmonic v ell z.1 :=
      Kernel.lintegral_id_prod (f := fun p : FlagState × CostState => f (flagUpdate S p.1.2 p.2))
        (hf.comp (flagUpdate_joint_measurable S)) _ z
    _ = _ := (lintegral_map hf (flagUpdate_measurable S z.2)).symm

theorem coordinates_measurable (v : ℝ) : Measurable (coordinates v) :=
  ((currentExponent_measurable v).comp measurable_fst).prodMk
    (((gapValue_measurable v).comp measurable_fst).prodMk measurable_snd)

theorem gap_div_currentExponent (v : ℝ) (z : CostState) :
    gapValue v z / currentExponent v z = stateRatio z.1 := by
  unfold currentExponent
  have hr : gapValue v z ≠ 0 := (Real.exp_pos _).ne'
  field_simp

theorem initial_coordinates (v S : ℝ) (z : CostState) :
    coordinates v (initial S z) = ErdosPrimeInputs.HighPrefixState.initial S
      (currentExponent v z) (gapValue v z) := by
  simp only [coordinates, initial, ErdosPrimeInputs.HighPrefixState.initial, gap_div_currentExponent]

theorem coordinates_update (v S : ℝ) (z : FlagState) (y : CostState)
    (hflow : gapValue v z.1 = gapValue v y + currentExponent v y) :
    coordinates v (flagUpdate S z.2 y) =
      ErdosPrimeInputs.HighPrefixState.update S (coordinates v z) (currentExponent v y) := by
  have hrem : gapValue v z.1 - currentExponent v y = gapValue v y := by linarith
  have hratio : (gapValue v z.1 - currentExponent v y) / currentExponent v y = stateRatio y.1 := by
    rw [hrem, gap_div_currentExponent]
  simp only [coordinates, flagUpdate, ErdosPrimeInputs.HighPrefixState.update, hrem]
  rw [gap_div_currentExponent]

theorem kernel_map_coordinates (v ell S : ℝ) (z : FlagState) :
    (kernel v ell S z).map (coordinates v) =
      ((admittedHarmonic v ell z.1).map (currentExponent v)).map
        (ErdosPrimeInputs.HighPrefixState.update S (coordinates v z)) := by
  rw [kernel_eq_map, Measure.map_map (coordinates_measurable v) (flagUpdate_measurable S z.2),
    Measure.map_map (ErdosPrimeInputs.HighPrefixKernel.update_at_measurable S (coordinates v z))
      (currentExponent_measurable v)]
  apply Measure.map_congr
  have hflow : ∀ᵐ y ∂admittedHarmonic v ell z.1,
      gapValue v z.1 = gapValue v y + currentExponent v y := by
    rw [admittedHarmonic, Kernel.restrict_apply]
    exact ae_restrict_of_ae (harmonicKernel_gap_flow v z.1)
  filter_upwards [hflow] with y hy
  exact coordinates_update v S z y hy

theorem kernel_map_coordinates_le (v S : ℝ) {ell : ℝ} (hell : 0 ≤ ell) (z : FlagState) :
    (kernel v ell S z).map (coordinates v) ≤
      ErdosPrimeInputs.HighPrefixKernel.kernel ell S (coordinates v z) := by
  rw [kernel_map_coordinates, ErdosPrimeInputs.HighPrefixKernel.kernel_eq_map]
  exact Measure.map_mono (admitted_exponent_marginal_le v hell z.1)
    (ErdosPrimeInputs.HighPrefixKernel.update_at_measurable S (coordinates v z))

end NumberTheoryLean.FlaggedHarmonicPaths

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_AdmittedHighRemoval
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.continuousParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.ContinuousKilledBins.continuousChain_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.AdmittedHighRemoval

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathMeasures ArrivalKernelGeometry AdmittedHarmonicPaths
open RegeneratingInverseBands FlaggedHarmonicPaths KernelMappedDomination

theorem pow_map_coordinates_le (v S : ℝ) {ell : ℝ} (hell : 0 ≤ ell) (n : ℕ) (z : FlagState) :
    (((FlaggedHarmonicPaths.kernel v ell S)^n) z).map (coordinates v) ≤
      ((ErdosPrimeInputs.HighPrefixKernel.kernel ell S)^n) (coordinates v z) :=
  mapped_pow_le _ _ (coordinates v) (coordinates_measurable v)
    (kernel_map_coordinates_le v S hell) n z

theorem low_mass_le_unrestricted (v S : ℝ) {ell : ℝ} (hell : 0 ≤ ell) (z : CostState) (K : ℝ) :
    lowHighMass v ell S z K ≤ ErdosPrimeInputs.HighPrefixBounds.lowHighMass ell S
      (currentExponent v z) (gapValue v z) K := by
  unfold lowHighMass ErdosPrimeInputs.HighPrefixBounds.lowHighMass
  apply ENNReal.tsum_le_tsum
  intro n
  let A : Set ExponentState := {y | y.2.2 = true ∧ y.2.1 ≤ K}
  have hA : MeasurableSet A := by
    exact ((measurable_snd.comp measurable_snd) (measurableSet_singleton true)).inter
      (measurableSet_le (measurable_fst.comp measurable_snd) measurable_const)
  have h := Measure.le_iff.mp (pow_map_coordinates_le v S hell n (initial S z)) A hA
  rw [Measure.map_apply (coordinates_measurable v) hA, initial_coordinates] at h
  exact h

theorem low_gap_high_removal (K A : ℝ) : ∀ᶠ B : ℝ in atTop,
    ∀ v ell : ℝ, ∀ z : CostState, 1 ≤ ell → ell ≤ B → currentExponent v z = B →
      lowHighMass v ell ((Real.log B)^2) z K ≤ ENNReal.ofReal (B^(-A)) := by
  filter_upwards [ErdosPrimeInputs.ContinuousHighRemoval.low_gap_high_removal K A] with B hB
  intro v ell z hell hellB hexp
  calc
    _ ≤ ErdosPrimeInputs.HighPrefixBounds.lowHighMass ell ((Real.log B)^2)
        (currentExponent v z) (gapValue v z) K := low_mass_le_unrestricted v _ (by linarith) z K
    _ ≤ _ := by rw [hexp]; exact hB ell hell hellB (gapValue v z)

end NumberTheoryLean.AdmittedHighRemoval

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

end NumberTheoryLean.FlaggedOccupationBound

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_SubMarkovFlagPowers
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SubMarkovFlagPowers

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open PersistentFailureFlag FlaggedOccupationBound ActualCouplingFinite

variable {α : Type*} [MeasurableSpace α]

theorem marked_eq_map_sfinite (K : Kernel α α) [IsSFiniteKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (z : FlagState α) :
    marked K hBad z = (K z.1).map (fun y => (y,z.2 || badBit Bad y)) := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [marked,Kernel.map_apply _ (update_measurable hBad),lintegral_map hF (update_measurable hBad)]
  calc
    _ = ∫⁻ y,F (y,z.2 || badBit Bad y) ∂K z.1 :=
      Kernel.lintegral_id_prod (f:=fun p : FlagState α × α => F (update Bad p))
        (hF.comp (update_measurable hBad)) _ z
    _ = _ := (lintegral_map hF (row_update_measurable hBad z.2)).symm

theorem marked_map_sfinite (K : Kernel α α) [IsSFiniteKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (z : FlagState α) :
    (marked K hBad z).map Prod.fst = K z.1 := by
  rw [marked_eq_map_sfinite K hBad z,Measure.map_map (f:=fun y => (y,z.2 || badBit Bad y))
    (g:=Prod.fst) measurable_fst (row_update_measurable hBad z.2)]
  exact Measure.map_id

theorem goodSelect_measurable {F : α → ℝ≥0∞} (hF : Measurable F) : Measurable (goodSelect F) :=
  (hF.comp measurable_fst).indicator failed_measurable.compl

theorem good_row_lift (K : Kernel α α) [IsSFiniteKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) {F : α → ℝ≥0∞} (hF : Measurable F) (q : FlagState α) :
    (∫⁻ y,goodSelect F y ∂marked K hBad q) =
      goodSelect (fun x => ∫⁻ y,F y ∂goodKernel K hBad x) q := by
  classical
  rw [marked_eq_map_sfinite K hBad q,lintegral_map (goodSelect_measurable hF) (row_update_measurable hBad q.2)]
  rcases q with ⟨x,b⟩
  cases b with
  | true => simp [goodSelect,failed]
  | false =>
    simp only [goodSelect,failed,mem_compl_iff,mem_ofPred_eq,Bool.false_eq_true,not_false_eq_true,
      indicator_of_mem,Bool.false_or]
    rw [goodKernel,Kernel.restrict_apply,← lintegral_indicator hBad.compl]
    apply lintegral_congr
    intro y
    by_cases hy : Bad y <;> simp [badBit,hy]

theorem good_power_lift (K : Kernel α α) [IsSFiniteKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) {F : α → ℝ≥0∞} (hF : Measurable F)
    (n : ℕ) (q : FlagState α) :
    (∫⁻ y,goodSelect F y ∂((marked K hBad)^n) q) =
      goodSelect (fun x => ∫⁻ y,F y ∂((goodKernel K hBad)^n) x) q := by
  induction n generalizing q with
  | zero =>
    change (∫⁻ y,goodSelect F y ∂Measure.dirac q) = _
    rw [lintegral_dirac' _ (goodSelect_measurable hF)]
    have he : (fun x => ∫⁻ y,F y ∂((goodKernel K hBad)^0) x) = F := by
      funext x
      change (∫⁻ y,F y ∂Measure.dirac x) = F x
      rw [lintegral_dirac' _ hF]
    rw [he]
  | succ n ih =>
    have hp : (marked K hBad)^(n+1) = ((marked K hBad)^n) ∘ₖ marked K hBad := pow_succ _ _
    have hg : (goodKernel K hBad)^(n+1) = ((goodKernel K hBad)^n) ∘ₖ goodKernel K hBad := pow_succ _ _
    rw [hp,Kernel.lintegral_comp _ _ _ (goodSelect_measurable hF)]
    calc
      _ = ∫⁻ y,goodSelect (fun x => ∫⁻ a,F a ∂((goodKernel K hBad)^n) x) y ∂marked K hBad q := lintegral_congr ih
      _ = goodSelect (fun x => ∫⁻ y,∫⁻ a,F a ∂((goodKernel K hBad)^n) y ∂goodKernel K hBad x) q :=
        good_row_lift K hBad hF.lintegral_kernel q
      _ = _ := by
        have he : (fun x => ∫⁻ y,∫⁻ a,F a ∂((goodKernel K hBad)^n) y ∂goodKernel K hBad x) =
            (fun x => ∫⁻ a,F a ∂((goodKernel K hBad)^(n+1)) x) := by
          funext x
          rw [hg,Kernel.lintegral_comp _ _ _ hF]
        rw [he]

theorem finite_integral_partition (K : Kernel α α) [IsSFiniteKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) {F : α → ℝ≥0∞} (hF : Measurable F) (n : ℕ) (x : α) :
    (∫⁻ y,F y ∂(K^n) x) = (∫⁻ y,F y ∂((goodKernel K hBad)^n) x)+
      (∫⁻ y,selected F y ∂((marked K hBad)^n) (x,false)) := by
  classical
  have hmap := map_power_of_step (marked K hBad) K measurable_fst (marked_map_sfinite K hBad) n (x,false)
  rw [← hmap,lintegral_map hF measurable_fst]
  have he : (fun y : FlagState α => F y.1) = fun y => goodSelect F y+selected F y := by
    funext y
    rcases y with ⟨z,b⟩
    cases b <;> simp [goodSelect,selected,failed]
  rw [he,lintegral_add_left (goodSelect_measurable hF),good_power_lift K hBad hF]
  simp [goodSelect,failed]

end NumberTheoryLean.SubMarkovFlagPowers

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_ContinuousHighPartition
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ContinuousHighPartition

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathMeasures RegeneratingInverseBands ArrivalKernelGeometry
open AdmittedHarmonicPaths LowStateHorizon SubMarkovFlagPowers
open PersistentFailureFlag FlaggedOccupationBound

theorem good_admitted_eq_low (K : Kernel CostState CostState) (v ell S : ℝ) :
    goodKernel (K.restrict (arrivalSet_measurable v ell)) (high_measurable S) = lowKernel K v ell S := by
  ext z : 1
  simp only [goodKernel,lowKernel,Kernel.restrict_apply,Measure.restrict_restrict (high_measurable S).compl]
  congr 1
  ext y
  simp only [lowDomain,mem_inter_iff,mem_compl_iff,mem_ofPred_eq,high,not_lt]
  exact and_comm

theorem marked_harmonic_eq (v ell S : ℝ) :
    marked (admittedHarmonic v ell) (high_measurable S) = FlaggedHarmonicPaths.kernel v ell S := by
  ext z : 1
  rw [marked_eq_map_sfinite,FlaggedHarmonicPaths.kernel_eq_map]
  congr 1
  funext y
  by_cases hy : S < stateRatio y.1 <;>
    cases z.2 <;> simp [FlaggedHarmonicPaths.flagUpdate,badBit,high,hy]

theorem harmonic_high_compact_bound (v ell S : ℝ) (z : CostState) {F : CostState → ℝ≥0∞}
    {D : ℝ≥0∞} (hD : D ≠ ∞) {K : ℝ} (hbound : ∀ y,F y ≤ D)
    (hsupport : ∀ y,K < gapValue v y → F y=0) :
    (∑' n : ℕ,∫⁻ y,selected F y ∂((FlaggedHarmonicPaths.kernel v ell S)^n) (FlaggedHarmonicPaths.initial S z)) ≤
      D*AdmittedHighRemoval.lowHighMass v ell S z K := by
  have hA : MeasurableSet {y : CostState×Bool | y.2=true ∧ gapValue v y.1 ≤ K} :=
    (measurable_snd (measurableSet_singleton true)).inter
      (measurableSet_le ((gapValue_measurable v).comp measurable_fst) measurable_const)
  have hpoint : ∀ y : CostState×Bool,selected F y ≤
      D*{y : CostState×Bool | y.2=true ∧ gapValue v y.1 ≤ K}.indicator (fun _ => (1:ℝ≥0∞)) y := by
    rintro ⟨y,b⟩
    cases b with
    | false => simp [selected,failed]
    | true =>
      by_cases hy : gapValue v y ≤ K
      · simp [selected,failed,hy,hbound y]
      · simp [selected,failed,hy,hsupport y (lt_of_not_ge hy)]
  unfold AdmittedHighRemoval.lowHighMass
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro n
  calc
    _ ≤ ∫⁻ y,D*{y : CostState×Bool | y.2=true ∧ gapValue v y.1 ≤ K}.indicator (fun _ => (1:ℝ≥0∞)) y
        ∂((FlaggedHarmonicPaths.kernel v ell S)^n) (FlaggedHarmonicPaths.initial S z) := lintegral_mono hpoint
    _ = _ := by rw [lintegral_const_mul' _ _ hD,lintegral_indicator hA,setLIntegral_const,one_mul]

end NumberTheoryLean.ContinuousHighPartition

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FlagMeasurePartition
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.FlagMeasurePartition

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open PersistentFailureFlag FlaggedOccupationBound SubMarkovFlagPowers

variable {α : Type*} [MeasurableSpace α]

theorem power_measure_partition (K : Kernel α α) [IsSFiniteKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (n : ℕ) (x : α) :
    (K^n) x = ((goodKernel K hBad)^n) x+highPart K hBad n x := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_add_measure,highPart,lintegral_map hF measurable_fst,
    ← lintegral_indicator failed_measurable]
  exact finite_integral_partition K hBad hF n x

theorem signed_power_difference (K : Kernel α α) [IsSFiniteKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (n : ℕ) (x : α) {F : α → ℝ}
    (hF : Measurable F) (hI : Integrable F ((K^n) x)) :
    ENNReal.ofReal |(∫ y,F y ∂(K^n) x)-(∫ y,F y ∂((goodKernel K hBad)^n) x)| ≤
      ∫⁻ y,selected (fun a => ENNReal.ofReal |F a|) y ∂((marked K hBad)^n) (x,false) := by
  have he := power_measure_partition K hBad n x
  have hl : ((goodKernel K hBad)^n) x ≤ (K^n) x := by rw [he]; exact Measure.le_add_right le_rfl
  have hh : highPart K hBad n x ≤ (K^n) x := by rw [he]; exact Measure.le_add_left le_rfl
  have hIl := hI.mono_measure hl
  have hIh := hI.mono_measure hh
  have hid : (∫ y,F y ∂(K^n) x)-(∫ y,F y ∂((goodKernel K hBad)^n) x) = ∫ y,F y ∂highPart K hBad n x := by
    rw [he,integral_add_measure hIl hIh]
    ring
  rw [hid]
  have h := enorm_integral_le_lintegral_enorm (μ:=highPart K hBad n x) F
  simp only [Real.enorm_eq_ofReal_abs] at h
  rw [highPart,lintegral_map (f:=fun a => ENNReal.ofReal |F a|) (ENNReal.measurable_ofReal.comp hF.abs) measurable_fst,
    ← lintegral_indicator failed_measurable] at h
  exact h

theorem signed_finite_difference (K : Kernel α α) [IsSFiniteKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (N : ℕ) (x : α) {F : α → ℝ}
    (hF : Measurable F) (hI : ∀ n ∈ range N,Integrable F ((K^n) x)) :
    ENNReal.ofReal |(∑ n ∈ range N,∫ y,F y ∂(K^n) x)-
      (∑ n ∈ range N,∫ y,F y ∂((goodKernel K hBad)^n) x)| ≤
      ∑ n ∈ range N,∫⁻ y,selected (fun a => ENNReal.ofReal |F a|) y ∂((marked K hBad)^n) (x,false) := by
  rw [← Finset.sum_sub_distrib]
  refine (ENNReal.ofReal_le_ofReal (Finset.abs_sum_le_sum_abs _ _)).trans ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)]
  exact Finset.sum_le_sum (fun n hn => signed_power_difference K hBad n x hF (hI n hn))

end NumberTheoryLean.FlagMeasurePartition

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_FiniteAdmittedOccupation
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.OriginalHarmonicOccupation

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathMeasures AdmittedHarmonicPaths ArrivalKernelGeometry
open KernelExitBarrier KernelWeightTransform HarmonicWeightKernel
open InvariantInverseWeights CostPrefixTransport RegeneratingInverseBands

theorem scaled_harmonic_weight (v : ℝ) (z : CostState) :
    ENNReal.ofReal ((Real.exp v)^2) * harmonicWeight z = gapSquaredWeight v z := by
  change ENNReal.ofReal ((Real.exp v)^2) * ENNReal.ofReal (Real.exp (-2*z.2) / stateWeight z.1) = _
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 1
  change (Real.exp v)^2 * (Real.exp (-2*z.2) / stateWeight z.1) = (Real.exp (v-z.2))^2 / stateWeight z.1
  rw [← mul_div_assoc]
  congr 1
  rw [pow_two, ← Real.exp_add, ← Real.exp_add, pow_two, ← Real.exp_add]
  congr 1
  ring

theorem scaled_ratio (v : ℝ) (s : State) (z : CostState) :
    ENNReal.ofReal ((Real.exp v)^2 / stateWeight s) * (harmonicWeight z / harmonicWeight (s,0)) =
      gapSquaredWeight v z := by
  rw [div_eq_mul_inv (harmonicWeight z) (harmonicWeight (s,0)), initial_weight_inv]
  calc
    _ = (ENNReal.ofReal ((Real.exp v)^2 / stateWeight s) * ENNReal.ofReal (stateWeight s)) * harmonicWeight z := by ring
    _ = ENNReal.ofReal ((Real.exp v)^2) * harmonicWeight z := by
      rw [← ENNReal.ofReal_mul (div_nonneg (sq_nonneg _) (stateWeight_pos s).le),
        div_mul_cancel₀ _ (stateWeight_pos s).ne']
    _ = _ := scaled_harmonic_weight v z

end NumberTheoryLean.OriginalHarmonicOccupation

end

section

namespace NumberTheoryLean.FiniteAdmittedOccupation

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathMeasures LowStateHorizon AdmittedHarmonicPaths ArrivalKernelGeometry
open OriginalHarmonicOccupation SignedCompletedPowers CompactTestMeasurable
open ContinuousHighPartition SubMarkovFlagPowers FlagMeasurePartition FlaggedOccupationBound

theorem occupation_eq_finite (K : Kernel CostState CostState) (z : CostState) (N : ℕ)
    (hzero : ∀ n,N ≤ n → (K^n) z = 0) : occupation K z = ∑ n ∈ range N,(K^n) z := by
  apply Measure.ext
  intro B hB
  rw [occupation,Kernel.sum_apply' _ _ hB,Measure.finsetSum_apply]
  apply tsum_eq_sum
  intro n hn
  have hN : N ≤ n := by
    have hh : ¬n < N := by simpa only [Finset.mem_range] using hn
    omega
  rw [hzero n hN]
  simp

theorem occupation_integral_eq_finite (K : Kernel CostState CostState) [IsFiniteKernel K]
    (z : CostState) (N : ℕ) (hzero : ∀ n,N ≤ n → (K^n) z = 0)
    {F : CostState → ℝ} (hF : Measurable F) {A : ℝ} (hbound : ∀ y,|F y| ≤ A) :
    (∫ y,F y ∂occupation K z) = ∑ n ∈ range N,∫ y,F y ∂(K^n) z := by
  rw [occupation_eq_finite K z N hzero]
  apply integral_finsetSum_measure
  intro n _hn
  let := finite_kernel_power K n
  exact bounded_integrable hF hbound

theorem admitted_low_signed_error (v ell S B : ℝ) (hell : 1 ≤ ell) (hS : 0 < S) (hB : 0 < B)
    (s : State) (hs : stateRatio s ≤ S)
    (hgap : RegeneratingInverseBands.gapValue v (s,0) ≤ (23/10:ℝ)*B)
    {F : CostState → ℝ} (hF : Measurable F) {A : ℝ} (hbound : ∀ y,|F y| ≤ A) :
    ENNReal.ofReal |(∫ y,F y ∂occupation (admittedTilted v ell) (s,0))-
      (∫ y,F y ∂occupation (lowKernel costKernel v ell S) (s,0))| ≤
      ∑' n : ℕ,∫⁻ y,selected (fun a => ENNReal.ofReal |F a|) y
        ∂((tiltedFlagged v ell S)^n) (FlaggedHarmonicPaths.initial S (s,0)) := by
  let M := ⌈RegeneratingInverseBands.gapValue v (s,0)/ell⌉₊
  let N := sourceHorizon S B
  let T := max M N
  have hfullzero : ∀ n,T ≤ n → ((admittedTilted v ell)^n) (s,0) = 0 := by
    intro n hn
    exact admitted_tilted_finite_height v (by linarith) (s,0) n ((le_max_left _ _).trans hn)
  have hlowzero : ∀ n,T ≤ n → ((lowKernel costKernel v ell S)^n) (s,0) = 0 := by
    intro n hn
    exact tilted_source_horizon v ell S B hell hS hB (s,0) hgap n ((le_max_right _ _).trans hn)
  let : IsFiniteKernel (lowKernel costKernel v ell S) := by unfold lowKernel; infer_instance
  rw [occupation_integral_eq_finite _ _ T hfullzero hF hbound,
    occupation_integral_eq_finite _ _ T hlowzero hF hbound]
  have hI : ∀ n ∈ range T,Integrable F (((admittedTilted v ell)^n) (s,0)) := by
    intro n _hn
    let := finite_kernel_power (admittedTilted v ell) n
    exact bounded_integrable hF hbound
  have h := signed_finite_difference (admittedTilted v ell) (high_measurable S) T (s,0) hF hI
  have he : goodKernel (admittedTilted v ell) (high_measurable S) = lowKernel costKernel v ell S :=
    good_admitted_eq_low costKernel v ell S
  rw [he] at h
  have hinit : FlaggedHarmonicPaths.initial S (s,0) = ((s,0),false) := by
    simp only [FlaggedHarmonicPaths.initial,ite_eq_right (not_lt.mpr hs)]
  rw [hinit]
  exact h.trans (ENNReal.sum_le_tsum (range T))

theorem low_occupation_integral_eq_source_sum (v ell S B : ℝ) (hell : 1 ≤ ell) (hS : 0 < S) (hB : 0 < B)
    (z : CostState) (hgap : RegeneratingInverseBands.gapValue v z ≤ (23/10:ℝ)*B)
    {F : CostState → ℝ} (hF : Measurable F) {A : ℝ} (hbound : ∀ y,|F y| ≤ A) :
    (∫ y,F y ∂occupation (lowKernel costKernel v ell S) z) =
      ∑ n ∈ range (sourceHorizon S B),∫ y,F y ∂((lowKernel costKernel v ell S)^n) z := by
  let : IsFiniteKernel (lowKernel costKernel v ell S) := by unfold lowKernel; infer_instance
  exact occupation_integral_eq_finite _ _ _ (tilted_source_horizon v ell S B hell hS hB z hgap) hF hbound

end NumberTheoryLean.FiniteAdmittedOccupation

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FlaggedHarmonicTransform
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.FlagWeightConjugation
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open KernelWeightTransform PersistentFailureFlag SubMarkovFlagPowers FlaggedOccupationBound

variable {α : Type*} [MeasurableSpace α]

theorem marked_conjugate (K : Kernel α α) [IsSFiniteKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (w : PositiveWeight α) :
    marked (conjugate K w) hBad = conjugate (marked K hBad) (flagWeight w) := by
  ext z : 1
  apply Measure.ext_of_lintegral
  intro F hF
  have hRow := row_update_measurable hBad z.2
  rw [marked_eq_map_sfinite,lintegral_map hF hRow,
    conjugate_lintegral K w z.1 (F := fun y => F (y,z.2 || badBit Bad y)) (hF.comp hRow),
    conjugate_lintegral (marked K hBad) (flagWeight w) z hF,
    marked_eq_map_sfinite,
    lintegral_map (f := fun b : FlagState α => flagWeight w b / flagWeight w z * F b)
      (((flagWeight w).measurable_value.div measurable_const).mul hF) hRow]
  rfl

end NumberTheoryLean.FlagWeightConjugation

end

section

namespace NumberTheoryLean.FlaggedHarmonicTransform

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathMeasures AdmittedHarmonicPaths HarmonicWeightKernel
open KernelWeightTransform FlagWeightConjugation PersistentFailureFlag
open FlaggedOccupationBound ContinuousHighPartition OriginalHarmonicOccupation

theorem actual_marked_transform (v ell S : ℝ) :
    FlaggedHarmonicPaths.kernel v ell S = conjugate (tiltedFlagged v ell S) (flagWeight harmonicWeight) := by
  rw [← marked_harmonic_eq,admitted_weight_transform,marked_conjugate]
  rfl

theorem scaled_high_integral (v ell S : ℝ) (s : State) (b : Bool) (n : ℕ)
    {F : CostState → ℝ≥0∞} (hF : Measurable F) :
    ENNReal.ofReal ((Real.exp v)^2/InvariantInverseWeights.stateWeight s)*
      (∫⁻ y,selected F y ∂((FlaggedHarmonicPaths.kernel v ell S)^n) ((s,0),b)) =
      ∫⁻ y,selected (fun z => gapSquaredWeight v z*F z) y ∂((tiltedFlagged v ell S)^n) ((s,0),b) := by
  rw [actual_marked_transform,conjugate_pow,conjugate_lintegral _ (flagWeight harmonicWeight) _ (selected_measurable hF),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  rintro ⟨z,b'⟩
  cases b' with
  | false => simp only [selected_false,mul_zero]
  | true =>
    simp only [selected_true]
    change ENNReal.ofReal ((Real.exp v)^2/InvariantInverseWeights.stateWeight s)*
      ((harmonicWeight z/harmonicWeight (s,0))*F z) = gapSquaredWeight v z*F z
    rw [← mul_assoc,scaled_ratio]

theorem high_inverse_compact_le (v ell S : ℝ) (s : State)
    {F : CostState → ℝ≥0∞} (hF : Measurable F) {D : ℝ≥0∞} (hD : D ≠ ∞) {K : ℝ}
    (hbound : ∀ z,F z ≤ D) (hsupport : ∀ z,K < RegeneratingInverseBands.gapValue v z → F z=0) :
    (∑' n : ℕ,∫⁻ y,selected (fun z => gapSquaredWeight v z*F z) y
      ∂((tiltedFlagged v ell S)^n) (FlaggedHarmonicPaths.initial S (s,0))) ≤
      ENNReal.ofReal ((Real.exp v)^2/InvariantInverseWeights.stateWeight s)*D*
        AdmittedHighRemoval.lowHighMass v ell S (s,0) K := by
  have he : (∑' n : ℕ,∫⁻ y,selected (fun z => gapSquaredWeight v z*F z) y
      ∂((tiltedFlagged v ell S)^n) (FlaggedHarmonicPaths.initial S (s,0))) =
      ENNReal.ofReal ((Real.exp v)^2/InvariantInverseWeights.stateWeight s)*
        (∑' n : ℕ,∫⁻ y,selected F y ∂((FlaggedHarmonicPaths.kernel v ell S)^n)
          (FlaggedHarmonicPaths.initial S (s,0))) := by
    rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro n
    exact (scaled_high_integral v ell S s (if S < stateRatio s then true else false) n hF).symm
  rw [he,mul_assoc]
  exact mul_le_mul_of_nonneg_left (harmonic_high_compact_bound v ell S (s,0) hD hbound hsupport) zero_le

end NumberTheoryLean.FlaggedHarmonicTransform

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_CorrectedCompactTransfer
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.CompactInverseTest

open _root_.Set
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open DerivativeWeights CompactTestGeometry SignedCompactTransfer InvariantInverseWeights

theorem valid_lower (i : Side) (s : ℝ) : Valid i s ↔ lowerRatio i ≤ s := by cases i <;> rfl

theorem safeWeight_pos (i : Side) (s : ℝ) : 0 < safeWeight i s :=
  weight_pos ((valid_lower _ _).mpr (le_max_left _ _))

theorem safeWeight_eq {i : Side} {s : ℝ} (hs : Valid i s) : safeWeight i s = weight i s := by
  unfold safeWeight
  rw [max_eq_right ((valid_lower _ _).mp hs)]

theorem safeWeight_continuous (i : Side) : Continuous (safeWeight i) := by
  cases i with
  | even =>
    apply continuous_iff_continuousAt.mpr
    intro x
    have hx : 1 < max (198/100:ℝ) x := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    exact (phiEven_continuousAt hx).comp (continuous_const.max continuous_id).continuousAt
  | odd => exact phiOdd_continuous.comp (continuous_const.max continuous_id)

theorem inverseTest_continuous {H : Side → ℝ×ℝ → ℝ} (hH : ∀ i,Continuous (H i)) (i : Side) :
    Continuous (inverseTest H i) :=
  ((continuous_fst.pow 2).mul (hH i)).div ((safeWeight_continuous i).comp continuous_snd)
    (fun x => (safeWeight_pos i x.2).ne')

theorem inverseTest_compact {H : Side → ℝ×ℝ → ℝ} (hH : ∀ i,HasCompactSupport (H i)) (i : Side) :
    HasCompactSupport (inverseTest H i) := by
  have he : inverseTest H i = (fun x : ℝ×ℝ => x.1^2/safeWeight i x.2)*(H i) := by
    funext x
    dsimp [inverseTest]
    ring
  rw [he]
  exact (hH i).mul_left

theorem inverseTest_bounded {H : Side → ℝ×ℝ → ℝ}
    (hH : ∀ i,Continuous (H i)) (hcompact : ∀ i,HasCompactSupport (H i)) :
    ∃ A : ℝ,0 ≤ A ∧ ∀ i x,|inverseTest H i x| ≤ A := by
  obtain ⟨Ae,he⟩ := (inverseTest_continuous hH .even).bounded_above_of_compact_support (inverseTest_compact hcompact .even)
  obtain ⟨Ao,ho⟩ := (inverseTest_continuous hH .odd).bounded_above_of_compact_support (inverseTest_compact hcompact .odd)
  refine ⟨max 0 (max Ae Ao),le_max_left _ _,?_⟩
  intro i x
  cases i with
  | even =>
    have hx : |inverseTest H .even x| ≤ Ae := by simpa only [Real.norm_eq_abs] using he x
    exact hx.trans ((le_max_left _ _).trans (le_max_right _ _))
  | odd =>
    have hx : |inverseTest H .odd x| ≤ Ao := by simpa only [Real.norm_eq_abs] using ho x
    exact hx.trans ((le_max_right _ _).trans (le_max_right _ _))

theorem inverseTest_eq {H : Side → ℝ×ℝ → ℝ} {i : Side} {r s : ℝ} (hs : Valid i s) :
    inverseTest H i (r,s) = r^2*H i (r,s)/weight i s := by
  simp only [inverseTest,safeWeight_eq hs]

end NumberTheoryLean.CompactInverseTest

end

section

namespace NumberTheoryLean.ContinuousCompactHighError

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathMeasures CompactTestGeometry CompactTestMeasurable CompactInverseTest
open RegeneratingInverseBands InvariantInverseWeights OriginalHarmonicOccupation
open ContinuousHighPartition FlaggedHarmonicTransform FiniteAdmittedOccupation
open LowStateHorizon AdmittedHarmonicPaths

theorem baseReward_measurable (v : ℝ) {H : FinitePathGeometry.Side → ℝ×ℝ → ℝ}
    (hH : ∀ i,Continuous (H i)) : Measurable (baseReward v H) :=
  (continuousTest_measurable v H (fun i => (hH i).measurable)).comp measurable_inl

theorem inverseReward_measurable (v : ℝ) {H : FinitePathGeometry.Side → ℝ×ℝ → ℝ}
    (hH : ∀ i,Continuous (H i)) : Measurable (inverseReward v H) :=
  (continuousTest_measurable v (inverseTest H) (fun i => (inverseTest_continuous hH i).measurable)).comp measurable_inl

theorem inverseReward_abs (v : ℝ) (H : FinitePathGeometry.Side → ℝ×ℝ → ℝ) (z : CostState) :
    ENNReal.ofReal |inverseReward v H z| = gapSquaredWeight v z*ENNReal.ofReal |baseReward v H z| := by
  have hs := stateRatio_valid z.1
  change ENNReal.ofReal |inverseTest H (stateSide z.1) (gapValue v z,stateRatio z.1)| = _
  rw [inverseTest_eq hs,← SuccessfulRewardComparison.stateWeight_eq]
  unfold gapSquaredWeight baseReward
  rw [abs_div,abs_mul,abs_of_nonneg (sq_nonneg _),abs_of_pos (stateWeight_pos z.1),
    ← ENNReal.ofReal_mul (div_nonneg (sq_nonneg _) (stateWeight_pos z.1).le)]
  congr 1
  ring

theorem phase_compact_bound {H : FinitePathGeometry.Side → ℝ×ℝ → ℝ}
    (hH : ∀ i,Continuous (H i)) (hcompact : ∀ i,HasCompactSupport (H i)) :
    ∃ A : ℝ,0 ≤ A ∧ ∀ i x,|H i x| ≤ A := by
  obtain ⟨Ae,he⟩ := (hH .even).bounded_above_of_compact_support (hcompact .even)
  obtain ⟨Ao,ho⟩ := (hH .odd).bounded_above_of_compact_support (hcompact .odd)
  refine ⟨max 0 (max Ae Ao),le_max_left _ _,?_⟩
  intro i x
  cases i with
  | even =>
    have hx : |H .even x| ≤ Ae := by simpa only [Real.norm_eq_abs] using he x
    exact hx.trans ((le_max_left _ _).trans (le_max_right _ _))
  | odd =>
    have hx : |H .odd x| ≤ Ao := by simpa only [Real.norm_eq_abs] using ho x
    exact hx.trans ((le_max_right _ _).trans (le_max_right _ _))

theorem compact_high_error_bound {H : FinitePathGeometry.Side → ℝ×ℝ → ℝ}
    (hH : ∀ i,Continuous (H i)) (hcompact : ∀ i,HasCompactSupport (H i))
    {K : ℝ} (hsupport : ∀ i : FinitePathGeometry.Side,∀ r s : ℝ,K < r → H i (r,s)=0) :
    ∃ A : ℝ,0 ≤ A ∧ ∀ v ell S B : ℝ,1 ≤ ell → 0 < S → 0 < B →
      ∀ s : State,stateRatio s ≤ S → gapValue v (s,0) ≤ (23/10:ℝ)*B →
      ENNReal.ofReal |(∫ z,inverseReward v H z ∂occupation (admittedTilted v ell) (s,0))-
        (∫ z,inverseReward v H z ∂occupation (lowKernel costKernel v ell S) (s,0))| ≤
        ENNReal.ofReal ((Real.exp v)^2/stateWeight s)*ENNReal.ofReal A*
          AdmittedHighRemoval.lowHighMass v ell S (s,0) K := by
  obtain ⟨A,hA,hbase⟩ := phase_compact_bound hH hcompact
  obtain ⟨D,hD,hinverse⟩ := inverseTest_bounded hH hcompact
  refine ⟨A,hA,?_⟩
  intro v ell S B hell hS hB s hs hgap
  have hG : ∀ z : CostState,|inverseReward v H z| ≤ D := fun z => hinverse _ _
  have herr := admitted_low_signed_error v ell S B hell hS hB s hs hgap (inverseReward_measurable v hH) hG
  have hbaseM : Measurable (fun z => ENNReal.ofReal |baseReward v H z|) :=
    ENNReal.measurable_ofReal.comp (baseReward_measurable v hH).abs
  have hb : ∀ z : CostState,ENNReal.ofReal |baseReward v H z| ≤ ENNReal.ofReal A :=
    fun z => ENNReal.ofReal_le_ofReal (hbase _ _)
  have hz : ∀ z : CostState,K < gapValue v z → ENNReal.ofReal |baseReward v H z| = 0 := by
    intro z hz
    simp [baseReward,hsupport _ _ _ hz]
  have hhigh := high_inverse_compact_le v ell S s hbaseM ENNReal.ofReal_ne_top hb hz
  have he : (fun z : CostState => ENNReal.ofReal |inverseReward v H z|) =
      (fun z => gapSquaredWeight v z*ENNReal.ofReal |baseReward v H z|) := funext (inverseReward_abs v H)
  rw [he] at herr
  exact herr.trans hhigh

end NumberTheoryLean.ContinuousCompactHighError

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourceLowRemoval
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SourceLowRemoval

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathMeasures TransitionKernels FinitePathGeometry DerivativeWeights
open RegeneratingInverseBands InvariantInverseWeights ArrivalKernelGeometry
open ContinuousCompactHighError OriginalHarmonicOccupation AdmittedHarmonicPaths LowStateHorizon

theorem scaleConstant_pos : 0 < scaleConstant := by
  unfold scaleConstant
  exact div_pos (by norm_num) (phiEven_pos (by norm_num))

theorem source_scale_upper {v B : ℝ} (hB : 0 < B) (s : EvenState) (hs : s.1 ≤ 23/10)
    (hcut : currentExponent v (.inl s,0) = B) :
    (Real.exp v)^2/stateWeight (.inl s) ≤ scaleConstant*B^2 ∧ gapValue v (.inl s,0) ≤ (23/10:ℝ)*B := by
  have hs0 : 0 < s.1 := by linarith [s.2]
  have he : Real.exp v = B*s.1 := by
    change Real.exp (v-0)/s.1 = B at hcut
    rw [sub_zero] at hcut
    exact (div_eq_iff hs0.ne').mp hcut
  have hupper : Real.exp v ≤ (23/10:ℝ)*B := by rw [he]; nlinarith
  have hsq : (Real.exp v)^2 ≤ (23/10:ℝ)^2*B^2 := by nlinarith [Real.exp_pos v]
  have hφ : 0 < phiEven s.1 := phiEven_pos (by linarith [s.2])
  have hφend : 0 < phiEven (23/10) := phiEven_pos (by norm_num)
  have hmono : phiEven (23/10) ≤ phiEven s.1 :=
    TwoStepDensityBounds.weight_antitone (i:=.even) s.2 (by norm_num [Valid]) hs
  have hinv := one_div_le_one_div_of_le hφend hmono
  refine ⟨?_,?_⟩
  · change (Real.exp v)^2/phiEven s.1 ≤ _
    calc
      _ = (Real.exp v)^2*(1/phiEven s.1) := by ring
      _ ≤ ((23/10:ℝ)^2*B^2)*(1/phiEven (23/10)) := mul_le_mul hsq hinv (by positivity) (by positivity)
      _ = _ := by unfold scaleConstant; ring
  · simpa only [gapValue,sub_zero] using hupper

theorem source_low_removal {H : Side → ℝ×ℝ → ℝ}
    (hH : ∀ i,Continuous (H i)) (hcompact : ∀ i,HasCompactSupport (H i))
    {K : ℝ} (hsupport : ∀ i : Side,∀ r s : ℝ,K < r → H i (r,s)=0) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ᶠ B : ℝ in atTop,∀ v ell : ℝ,∀ s : EvenState,
      (199/100:ℝ) ≤ s.1 → s.1 ≤ 23/10 → 1 ≤ ell → ell ≤ B → currentExponent v (.inl s,0)=B →
      |(∫ z,inverseReward v H z ∂occupation (admittedTilted v ell) (.inl s,0))-
        (∫ z,inverseReward v H z ∂occupation (lowKernel costKernel v ell ((Real.log B)^2)) (.inl s,0))| ≤ C/B := by
  obtain ⟨A,hA,herror⟩ := compact_high_error_bound hH hcompact hsupport
  refine ⟨scaleConstant*A,mul_nonneg scaleConstant_pos.le hA,?_⟩
  filter_upwards [AdmittedHighRemoval.low_gap_high_removal K 3,
    eventually_ge_atTop (Real.exp 2)] with B hrem hBexp
  intro v ell s _hsL hsU hell hellB hcut
  have hB : 0 < B := (Real.exp_pos 2).trans_le hBexp
  have hlogB : 2 ≤ Real.log B := by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 2) hBexp
  have hS : 0 < (Real.log B)^2 := by nlinarith
  have hsS : stateRatio (.inl s) ≤ (Real.log B)^2 := by change s.1 ≤ _; nlinarith
  have hscale := source_scale_upper hB s hsU hcut
  have herr := herror v ell ((Real.log B)^2) B hell hS hB (.inl s) hsS hscale.2
  have hhigh := hrem v ell (.inl s,0) hell hellB hcut
  have hsourceScale : ENNReal.ofReal ((Real.exp v)^2/stateWeight (.inl s)) ≤
      ENNReal.ofReal (scaleConstant*B^2) := ENNReal.ofReal_le_ofReal hscale.1
  have hscaled := mul_le_mul hsourceScale (le_refl (ENNReal.ofReal A)) zero_le zero_le
  have hbound := herr.trans (mul_le_mul hscaled hhigh zero_le zero_le)
  have hid : ENNReal.ofReal (scaleConstant*B^2)*ENNReal.ofReal A*ENNReal.ofReal (B^(-(3:ℝ))) =
      ENNReal.ofReal ((scaleConstant*A)/B) := by
    rw [← ENNReal.ofReal_mul (mul_nonneg scaleConstant_pos.le (sq_nonneg B)),
      ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg scaleConstant_pos.le (sq_nonneg B)) hA)]
    congr 1
    rw [Real.rpow_neg hB.le,Real.rpow_ofNat]
    field_simp
  rw [hid] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff (div_nonneg (mul_nonneg scaleConstant_pos.le hA) hB.le)).mp hbound

end NumberTheoryLean.SourceLowRemoval

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_RetainedOccupationLimit
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.CompactLogOccupationTest

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped ENNReal Topology
open FinitePathGeometry FinitePathMeasures TransitionKernels CompactInverseTest
open CompactTestGeometry CompactTestMeasurable ActualCouplingUpdates
open CycleResponse AdmissibleCycleTests ArrivalKernelGeometry RegeneratingInverseBands
open NormalizedOccupationLimit EvenStartOccupation

theorem logTest_measurable {H : Side → ℝ×ℝ → ℝ} (hH : ∀ i,Continuous (H i)) : Measurable (logTest H) := by
  have hcoord : Measurable (fun x : ℝ×State => (Real.exp x.1,stateRatio x.2)) :=
    (Real.measurable_exp.comp measurable_fst).prodMk (stateRatio_measurable.comp measurable_snd)
  have hside : MeasurableSet {x : ℝ×State | stateSide x.2 = .even} :=
    measurable_snd (side_set_measurable .even)
  have heq : logTest H = (fun x => if stateSide x.2 = .even then inverseTest H .even (Real.exp x.1,stateRatio x.2)
      else inverseTest H .odd (Real.exp x.1,stateRatio x.2)) := by
    funext x
    rcases x with ⟨u,s⟩
    cases s <;> rfl
  rw [heq]
  exact Measurable.ite hside ((inverseTest_continuous hH .even).measurable.comp hcoord)
    ((inverseTest_continuous hH .odd).measurable.comp hcoord)

theorem logTest_continuous_shift {H : Side → ℝ×ℝ → ℝ} (hH : ∀ i,Continuous (H i)) (s : State) :
    Continuous (fun u => logTest H (u,s)) := by
  change Continuous (fun u : ℝ => inverseTest H (stateSide s) (Real.exp u,stateRatio s))
  exact (inverseTest_continuous hH (stateSide s)).comp (Real.continuous_exp.prodMk continuous_const)

theorem logTest_compact_bound {H : Side → ℝ×ℝ → ℝ}
    (hH : ∀ i,Continuous (H i)) (hcompact : ∀ i,HasCompactSupport (H i))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hsupport : ∀ i : Side,∀ r s : ℝ,r < a ∨ b < r → H i (r,s)=0) : HasCompactBound (logTest H) := by
  obtain ⟨A,hA,hbound⟩ := inverseTest_bounded hH hcompact
  let M := |Real.log a|+|Real.log b|+1
  have hM : 0 ≤ M := by dsimp [M] <;> positivity
  refine ⟨A,M,hA,hM,?_,?_⟩
  · intro x
    simpa only [logTest,Real.norm_eq_abs] using hbound (stateSide x.2) (Real.exp x.1,stateRatio x.2)
  · rintro ⟨u,s⟩ hu
    have hcase : u < Real.log a ∨ Real.log b < u := by
      by_contra hn
      push Not at hn
      have hlo := neg_abs_le (Real.log a)
      have hup := le_abs_self (Real.log b)
      have hle : |u| ≤ M := abs_le.mpr ⟨by dsimp [M] <;> linarith [abs_nonneg (Real.log b)],by dsimp [M] <;> linarith [abs_nonneg (Real.log a)]⟩
      exact (not_lt_of_ge hle) hu
    have hzero : H (stateSide s) (Real.exp u,stateRatio s) = 0 := by
      apply hsupport
      rcases hcase with h | h
      · exact Or.inl (by simpa only [Real.exp_log ha] using Real.exp_lt_exp.mpr h)
      · exact Or.inr (by simpa only [Real.exp_log hb] using Real.exp_lt_exp.mpr h)
    simp [logTest,inverseTest,hzero]

theorem logTest_admissible {H : Side → ℝ×ℝ → ℝ}
    (hH : ∀ i,Continuous (H i)) (hcompact : ∀ i,HasCompactSupport (H i))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hsupport : ∀ i : Side,∀ r s : ℝ,r < a ∨ b < r → H i (r,s)=0) : Admissible (logTest H) :=
  Admissible.base (logTest_measurable hH) (logTest_continuous_shift hH)
    (logTest_compact_bound hH hcompact ha hb hsupport)

theorem arrivalTest_admissible {H : Side → ℝ×ℝ → ℝ}
    (hH : ∀ i,Continuous (H i)) (hcompact : ∀ i,HasCompactSupport (H i))
    {a b ell : ℝ} (ha : 0 < a) (hb : 0 < b) (hell : 0 < ell)
    (hsupport : ∀ i : Side,∀ r s : ℝ,r < a ∨ b < r → H i (r,s)=0) : Admissible (arrivalTest ell H) :=
  (logTest_admissible hH hcompact ha hb hsupport).arrival ell hell

theorem source_inverse_log_limit {H : Side → ℝ×ℝ → ℝ}
    (hH : ∀ i,Continuous (H i)) (hcompact : ∀ i,HasCompactSupport (H i))
    {a b ell : ℝ} (ha : 0 < a) (hb : 0 < b) (hell : 0 < ell)
    (hsupport : ∀ i : Side,∀ r s : ℝ,r < a ∨ b < r → H i (r,s)=0) :
    ∀ ε : ℝ,0 < ε → ∃ V : ℝ,∀ v : ℝ,V ≤ v → ∀ s : EvenState,
      (199/100:ℝ) ≤ s.1 → s.1 ≤ 23/10 →
      ‖evenResponse (arrivalTest ell H) s v-invariantAverage (arrivalTest ell H)‖ < ε :=
  source_compact_occupation_limit (arrivalTest_admissible hH hcompact ha hb hell hsupport)

end NumberTheoryLean.CompactLogOccupationTest

end

section

namespace NumberTheoryLean.ContinuousOccupationIdentification

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathMeasures TransitionKernels CompactInverseTest CompactLogOccupationTest
open CycleResponse AdmissibleCycleTests EvenStartOccupation OriginalHarmonicOccupation
open CostPrefixTransport OccupationDecomposition ContinuousCompactHighError
open CompactTestGeometry CompactTestMeasurable FiniteAdmittedOccupation SignedCompletedPowers
open AdmittedHarmonicPaths ArrivalKernelGeometry LowStateHorizon SignedCompactTransfer

theorem low_occupation_eq_expectation {H : FinitePathGeometry.Side → ℝ×ℝ → ℝ}
    (hH : ∀ i,Continuous (H i)) (hcompact : ∀ i,HasCompactSupport (H i))
    (v ell S B : ℝ) (hell : 1 ≤ ell) (hS : 0 < S) (hB : 0 < B)
    (z : CostState) (hgap : RegeneratingInverseBands.gapValue v z ≤ (23/10:ℝ)*B) :
    (∫ y,inverseReward v H y ∂occupation (lowKernel costKernel v ell S) z) =
      continuousExpectation (inverseTest H) v ell S z (sourceHorizon S B) := by
  obtain ⟨A,hA,hbound⟩ := inverseTest_bounded hH hcompact
  have hG : ∀ y : CostState,|inverseReward v H y| ≤ A := fun y => hbound _ _
  have hm := inverseReward_measurable v hH
  rw [low_occupation_integral_eq_source_sum v ell S B hell hS hB z hgap hm hG]
  apply Finset.sum_congr rfl
  intro n _hn
  have he : liftReal (inverseReward v H) = continuousTest v (inverseTest H) := by
    funext y
    cases y <;> rfl
  rw [← he]
  exact (continuous_signed_power v ell S n z hm hA hG).symm

end NumberTheoryLean.ContinuousOccupationIdentification

end

section

namespace NumberTheoryLean.ContinuousLowOccupationLimit

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped Topology
open FinitePathGeometry FinitePathMeasures TransitionKernels CompactInverseTest
open CompactLogOccupationTest SourceLowRemoval ContinuousOccupationIdentification
open ContinuousCompactHighError RegeneratingInverseBands ArrivalKernelGeometry
open OriginalHarmonicOccupation AdmittedHarmonicPaths LowStateHorizon
open SignedCompactTransfer NormalizedOccupationLimit EvenStartOccupation

theorem source_continuous_low_limit_jb247_oai {H : Side → ℝ×ℝ → ℝ}
    (hH : ∀ i,Continuous (H i)) (hcompact : ∀ i,HasCompactSupport (H i))
    {a b ell : ℝ} (ha : 0 < a) (hb : 0 < b) (hell : 1 ≤ ell)
    (hsupport : ∀ i : Side,∀ r s : ℝ,r < a ∨ b < r → H i (r,s)=0) :
    ∀ ε : ℝ,0 < ε → ∃ B₀ : ℝ,0 < B₀ ∧ ∀ B : ℝ,B₀ ≤ B → ∀ v : ℝ,∀ s : EvenState,
      (199/100:ℝ) ≤ s.1 → s.1 ≤ 23/10 → currentExponent v (.inl s,0)=B →
      |continuousExpectation (inverseTest H) v ell ((Real.log B)^2) (.inl s,0)
        (sourceHorizon ((Real.log B)^2) B)-invariantAverage (arrivalTest ell H)| ≤ ε := by
  intro ε hε
  obtain ⟨C,hC,hremove⟩ := source_low_removal hH hcompact (K:=b) (fun i r s h => hsupport i r s (Or.inr h))
  obtain ⟨BR,hBR⟩ := eventually_atTop.mp hremove
  obtain ⟨V,hV⟩ := source_inverse_log_limit hH hcompact ha hb (show 0 < ell by linarith) hsupport (ε/2) (by linarith)
  let B₀ := max BR (max (Real.exp 2) (max (ell+1) (max (Real.exp V) (2*C/ε))))
  have hExpB₀ : Real.exp 2 ≤ B₀ := (le_max_left _ _).trans (le_max_right _ _)
  refine ⟨B₀,(Real.exp_pos 2).trans_le hExpB₀,?_⟩
  intro B hB v s hsL hsU hcut
  have hBR' : BR ≤ B := (le_max_left _ _).trans hB
  have hBexp : Real.exp 2 ≤ B := hExpB₀.trans hB
  have hBell : ell+1 ≤ B :=
    (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)).trans hB
  have hBV : Real.exp V ≤ B :=
    (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)).trans hB
  have hBC : 2*C/ε ≤ B :=
    (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)).trans hB
  have hBp : 0 < B := (Real.exp_pos 2).trans_le hBexp
  have hlogB : 2 ≤ Real.log B := by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 2) hBexp
  have hS : 0 < (Real.log B)^2 := by nlinarith
  have hstart : (.inl s,0) ∈ arrivalSet v ell := by change ell < currentExponent v (.inl s,0); rw [hcut]; linarith
  have hv : V ≤ v := by
    have he : Real.exp v = B*s.1 := by
      change Real.exp (v-0)/s.1=B at hcut
      rw [sub_zero] at hcut
      exact (div_eq_iff (show s.1 ≠ 0 by linarith [s.2])).mp hcut
    apply Real.exp_le_exp.mp
    rw [he]
    have hBmul : B ≤ B*s.1 := by nlinarith
    exact hBV.trans hBmul
  have hfull := full_admitted_eq_response_jb247 hH hcompact ha hb (show 0 < ell by linarith) hsupport s v hstart
  have hscale := source_scale_upper hBp s hsU hcut
  have hlow := low_occupation_eq_expectation hH hcompact v ell ((Real.log B)^2) B hell hS hBp (.inl s,0) hscale.2
  have hrem := hBR B hBR' v ell s hsL hsU hell (by linarith) hcut
  rw [hfull,hlow] at hrem
  have hsmall : C/B ≤ ε/2 := by
    apply (div_le_iff₀ hBp).mpr
    have hh := (div_le_iff₀ hε).mp hBC
    nlinarith
  have hlimit := hV v hv s hsL hsU
  rw [Real.norm_eq_abs] at hlimit
  have htri := abs_sub_le
    (continuousExpectation (inverseTest H) v ell ((Real.log B)^2) (.inl s,0) (sourceHorizon ((Real.log B)^2) B))
    (evenResponse (arrivalTest ell H) s v) (invariantAverage (arrivalTest ell H))
  rw [abs_sub_comm _ (evenResponse (arrivalTest ell H) s v)] at htri
  linarith

end NumberTheoryLean.ContinuousLowOccupationLimit

end

end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.NumberTheoryLean.ContinuousLowOccupationLimit.source_continuous_low_limit_jb247_oai := @OAI.Erdos970.NumberTheoryLean.ContinuousLowOccupationLimit.source_continuous_low_limit_jb247_oai
