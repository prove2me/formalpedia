-- Prove2me | solution 1 for OAI.Erdos970.NumberTheoryLean.RegenerationBandBounds.regeneration_uniform_band_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:00:43.740711+00:00
-- url     : https://prove2.me/submissions/ef740a7b-a6ad-4c76-a23e-08a4862ddedc

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompMap
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Lattice
import Definitions.Def_OAIQ247J010

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FiniteHistorySupport
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.FinitePathGeometry

open Set
open DerivativeWeights TransitionKernels

theorem cost_pos {t : ℝ} (ht : 0 < t) : 0 < cost t := by
  unfold cost
  exact Real.log_pos (by have h : 0 < 1 / t := one_div_pos.mpr ht; linarith)

end NumberTheoryLean.FinitePathGeometry



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_RegenerationDrift
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedPairKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.RegenerativeOddOccupation.ratioVisits_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.CostReturnLaw.costCaptured_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostReturnLaw.costKilled_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostReturnLaw.costKilled_pow_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostReturnLaw.firstReturn_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostReturnLaw.returnLaw_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.CycleConvolutionLaw.returnLaw_pow_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.CycleOccupation.pairSampling_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.CycleRegeneration.cycleJointLaw_isProbabilityMeasure _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.InitialRegeneration.hitOrReturn_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.KernelDensityBridge.oddTwoStep_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PairedCostProcess.pairedCostKernel_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.PairedCostProcess.pairedDraws_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.PairedHitting.pairedKilled_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PairedHitting.pairedKilled_pow_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PairedHitting.pairedOdd_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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

theorem stateKernel_regeneration (s : OddState) (hs : s.1 ≤ 3) :
    stateKernel (.inr s) = stateKernel (.inr regenerationState) := by
  change oddBranch s = oddBranch regenerationState
  rw [oddBranch, Kernel.map_apply _ measurable_inl, Kernel.map_apply _ measurable_inl,
    oddToEven, Kernel.comapRight_apply, Kernel.comapRight_apply, oddKernel_regeneration s hs]

theorem costKernel_regeneration (s : OddState) (hs : s.1 ≤ 3) (T : ℝ) :
    costKernel (.inr s, T) = costKernel (.inr regenerationState, T) := by
  ext B hB
  rw [costKernel_apply _ hB, costKernel_apply _ hB]
  exact congrArg (fun μ : Measure State => μ {t | (t, T + FinitePathGeometry.cost (stateRatio t)) ∈ B})
    (stateKernel_regeneration s hs)

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

theorem phiOdd_integrableOn : IntegrableOn phiOdd (Ici (1 : ℝ)) := by
  obtain ⟨D, U, _, hU, hb⟩ := weights_exp_majorant
  exact integrableOn_Ici_of_exp_tail phiOdd_continuous.measurable phiOdd_continuous.continuousOn
    (fun s _ ↦ (phiOdd_pos s).le) (show (1 : ℝ) ≤ U by linarith) (fun s hs ↦ (hb s hs).2)

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_MarkedVisitGeometry
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.RegenerativeOddOccupation.ratioVisits_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.CycleConvolutionLaw.returnLaw_pow_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.CycleOccupation.pairSampling_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.CycleRegeneration.cycleJointLaw_isProbabilityMeasure _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.InitialRegeneration.hitOrReturn_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.PairedCostProcess

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures KernelDensityBridge
open JointMinorization RegenerationTails PairedHitting

theorem pairedDraws_regeneration (s : OddState) (hs : s.1 ≤ 3) :
    pairedDraws s = pairedDraws regenerationState := by
  have hf : oddToEven s = oddToEven regenerationState := by
    rw [oddToEven, Kernel.comapRight_apply, Kernel.comapRight_apply, oddKernel_regeneration s hs]
  ext B hB
  rw [pairedDraws, Kernel.compProd_apply hB, Kernel.compProd_apply hB]
  change (∫⁻ t : EvenState, evenToOdd t (Prod.mk t ⁻¹' B) ∂oddToEven s) =
    ∫⁻ t : EvenState, evenToOdd t (Prod.mk t ⁻¹' B) ∂oddToEven regenerationState
  rw [hf]

theorem pairedCost_regeneration (s : OddState) (hs : s.1 ≤ 3) (T : ℝ) :
    pairedCostKernel (s, T) = pairedCostKernel (regenerationState, T) := by
  ext B hB
  rw [pairedCostKernel_apply _ hB, pairedCostKernel_apply _ hB]
  exact congrArg (fun μ : Measure (EvenState × OddState) =>
    μ {x | (x.2, T + cost x.1.1 + cost x.2.1) ∈ B}) (pairedDraws_regeneration s hs)

theorem pairedCost_translation (s : OddState) (T a : ℝ) :
    (pairedCostKernel (s, T)).map (shiftCost a) = pairedCostKernel (s, T + a) := by
  ext B hB
  rw [Measure.map_apply (shiftCost_measurable a) hB,
    pairedCostKernel_apply _ ((shiftCost_measurable a) hB), pairedCostKernel_apply _ hB]
  congr 1
  ext x
  change (x.2, (T + cost x.1.1 + cost x.2.1) + a) ∈ B ↔
    (x.2, (T + a) + cost x.1.1 + cost x.2.1) ∈ B
  have heq : (T + cost x.1.1 + cost x.2.1) + a = (T + a) + cost x.1.1 + cost x.2.1 := by ring
  rw [heq]

end NumberTheoryLean.PairedCostProcess

end

section

namespace NumberTheoryLean.CostReturnLaw

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Topology
open TransitionKernels PairedHitting PairedBlockContraction PairedCostProcess

theorem costCaptured_off_returnSet (z : OddCost) : costCaptured z returnSetᶜ = 0 := by
  rw [costCaptured, Kernel.restrict_apply' _ _ _ returnSet_measurable.compl, compl_inter_self, measure_empty]

theorem firstReturn_off_returnSet (n : ℕ) (z : OddCost) : firstReturn n z returnSetᶜ = 0 := by
  rw [firstReturn, Kernel.comp_apply' _ _ _ returnSet_measurable.compl]
  simp only [costCaptured_off_returnSet, lintegral_zero]

theorem returnLaw_off_returnSet (z : OddCost) : returnLaw z returnSetᶜ = 0 := by
  rw [returnLaw, Kernel.sum_apply' _ _ returnSet_measurable.compl]
  simp only [firstReturn_off_returnSet, tsum_zero]

end NumberTheoryLean.CostReturnLaw

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_PairedCostGrouping
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.RegenerativeOddOccupation.ratioVisits_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.CycleConvolutionLaw.returnLaw_pow_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.CycleOccupation.pairSampling_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.CycleRegeneration.cycleJointLaw_isProbabilityMeasure _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.InitialRegeneration.hitOrReturn_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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

theorem pairedCost_lintegral (z : OddCost) {H : OddCost → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ y, H y ∂pairedCostKernel z) =
      ∫⁻ t : EvenState, ∫⁻ u : OddState, H (u, z.2 + cost t.1 + cost u.1) ∂evenToOdd t ∂oddToEven z.1 := by
  have hm : Measurable (fun x : EvenState × OddState => (x.2, z.2 + cost x.1.1 + cost x.2.1)) :=
    measurable_snd.prodMk ((measurable_const.add (cost_measurable.comp (measurable_subtype_coe.comp measurable_fst))).add
      (cost_measurable.comp (measurable_subtype_coe.comp measurable_snd)))
  have heq : pairedCostKernel z = (pairedDraws z.1).map (fun x => (x.2, z.2 + cost x.1.1 + cost x.2.1)) := by
    ext B hB
    rw [pairedCostKernel_apply _ hB, Measure.map_apply hm hB]
    rfl
  rw [heq, lintegral_map hH hm, pairedDraws,
    Kernel.lintegral_compProd _ _ _ (f := fun x : EvenState × OddState => H (x.2, z.2 + cost x.1.1 + cost x.2.1)) (hH.comp hm)]
  rfl

theorem pairedCost_full_grouping (z : OddCost) :
    (pairedCostKernel z).map embedOdd = (costKernel ^ 2) (embedOdd z) := by
  apply Measure.ext_of_lintegral
  intro H hH
  have hp : costKernel ^ 2 = costKernel ∘ₖ costKernel := by
    rw [pow_two]
    rfl
  rw [lintegral_map hH embedOdd_measurable,
    pairedCost_lintegral z (H := fun x => H (embedOdd x)) (hH.comp embedOdd_measurable),
    hp, Kernel.lintegral_comp _ _ _ hH]
  have hJ : Measurable (fun y : CostState => ∫⁻ w, H w ∂costKernel y) := hH.lintegral_kernel
  change (∫⁻ t : EvenState, ∫⁻ u : OddState, H (.inr u, z.2 + cost t.1 + cost u.1) ∂evenToOdd t ∂oddToEven z.1) = _
  simp only [embedOdd]
  rw [costKernel_odd_lintegral z.1 z.2 (H := fun y : CostState => ∫⁻ w, H w ∂costKernel y) hJ]
  apply lintegral_congr
  intro t
  exact (costKernel_even_lintegral t (z.2 + cost t.1) hH).symm

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_KernelPotential
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.KernelPotential

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

theorem compose_mono_left {B C : Kernel α β} (h : B ≤ C) (K : Kernel γ α) :
    B ∘ₖ K ≤ C ∘ₖ K := by
  intro a
  apply Measure.le_iff.mpr
  intro s hs
  rw [Kernel.comp_apply' _ _ _ hs, Kernel.comp_apply' _ _ _ hs]
  exact lintegral_mono (fun x => h x s)

theorem compose_finset_sum_left (I : Finset ℕ) (B : ℕ → Kernel α β) (K : Kernel γ α) :
    (∑ n ∈ I, B n) ∘ₖ K = ∑ n ∈ I, B n ∘ₖ K := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert n I hn ih => simp only [Finset.sum_insert hn, Kernel.comp_add_left, ih]

theorem power_comp_succ (B : Kernel α β) (K : Kernel α α) (n : ℕ) :
    B ∘ₖ (K ^ (n + 1)) = (B ∘ₖ (K ^ n)) ∘ₖ K := by
  rw [pow_succ]
  exact (Kernel.comp_assoc B (K ^ n) K).symm

theorem potential_unfold (B : Kernel α β) (K : Kernel α α) :
    potential B K = B + (potential B K) ∘ₖ K := by
  unfold potential
  rw [Kernel.comp_sum_left]
  ext a s hs
  rw [Kernel.sum_apply' _ _ hs, add_apply, Measure.add_apply, Kernel.sum_apply' _ _ hs,
    tsum_eq_zero_add' ENNReal.summable]
  have hz : B ∘ₖ (K ^ 0) = B := Kernel.comp_id B
  simp only [hz, power_comp_succ]

theorem potential_le_of_super (B : Kernel α β) (K : Kernel α α) (S : Kernel α β)
    (hS : B + S ∘ₖ K ≤ S) : potential B K ≤ S := by
  have hfin : ∀ n : ℕ, (∑ j ∈ Finset.range n, B ∘ₖ (K ^ j)) ≤ S := by
    intro n
    induction n with
    | zero => simp only [Finset.range_zero, Finset.sum_empty]; exact bot_le
    | succ n ih =>
      rw [Finset.sum_range_succ']
      have hz : B ∘ₖ (K ^ 0) = B := Kernel.comp_id B
      simp only [hz, power_comp_succ]
      rw [← compose_finset_sum_left]
      calc
        _ = B + (∑ j ∈ Finset.range n, B ∘ₖ (K ^ j)) ∘ₖ K := add_comm _ _
        _ ≤ B + S ∘ₖ K := fun a => add_le_add le_rfl ((compose_mono_left ih K) a)
        _ ≤ S := hS
  intro a
  apply Measure.le_iff.mpr
  intro s hs
  rw [potential, Kernel.sum_apply' _ _ hs, ENNReal.tsum_eq_iSup_nat]
  apply iSup_le
  intro n
  have h := hfin n a s
  rwa [Kernel.finsetSum_apply'] at h

theorem potential_add (B C : Kernel α β) (K : Kernel α α) :
    potential (B + C) K = potential B K + potential C K := by
  unfold potential
  simp_rw [Kernel.comp_add_left]
  exact Kernel.sum_add _ _

theorem potential_comp_left (B : Kernel α β) (C : Kernel β γ) (K : Kernel α α) :
    potential (C ∘ₖ B) K = C ∘ₖ (potential B K) := by
  unfold potential
  rw [Kernel.comp_sum_right]
  congr 1
  funext n
  exact Kernel.comp_assoc C B (K ^ n)

theorem first_capture_decomposition (B : Kernel α β) (Q H : Kernel α α) :
    potential B (Q + H) = potential (potential B Q) (potential H Q) := by
  let P := potential B (Q + H)
  let O := potential B Q
  let R := potential H Q
  let S := potential O R
  have hP : P = B + P ∘ₖ (Q + H) := potential_unfold B (Q + H)
  have hO : O = B + O ∘ₖ Q := potential_unfold B Q
  have hR : R = H + R ∘ₖ Q := potential_unfold H Q
  have hS : S = O + S ∘ₖ R := potential_unfold O R
  have hSeq : B + S ∘ₖ (Q + H) = S := by
    calc
      _ = B + S ∘ₖ Q + S ∘ₖ H := by rw [Kernel.comp_add_right]; abel
      _ = B + (O + S ∘ₖ R) ∘ₖ Q + S ∘ₖ H := by rw [← hS]
      _ = (B + O ∘ₖ Q) + S ∘ₖ (H + R ∘ₖ Q) := by
        rw [Kernel.comp_add_left, Kernel.comp_add_right, ← Kernel.comp_assoc]
        abel
      _ = O + S ∘ₖ R := by rw [← hO, ← hR]
      _ = S := hS.symm
  have hPS : P ≤ S := potential_le_of_super B (Q + H) S hSeq.le
  have hPsuper : (B + P ∘ₖ H) + P ∘ₖ Q ≤ P := by
    have heq : (B + P ∘ₖ H) + P ∘ₖ Q = P := by
      calc
        _ = B + P ∘ₖ (Q + H) := by rw [Kernel.comp_add_right]; abel
        _ = P := hP.symm
    exact heq.le
  have hOR : O + P ∘ₖ R ≤ P := by
    have h := potential_le_of_super (B + P ∘ₖ H) Q P hPsuper
    rw [potential_add, potential_comp_left] at h
    exact h
  have hSP : S ≤ P := potential_le_of_super O R P hOR
  exact le_antisymm hPS hSP

end NumberTheoryLean.KernelPotential

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

end Erdos970Dependency.StateKernelInvariance

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
-- module Solutions.OAIQ247_JB.Supercritical_Renewal
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

/-!
# A renewal mini-library

Paper §7 concludes `lem:nd-gaussian-renewal` with the *key renewal theorem for
directly Riemann integrable functions on the whole line* (Feller, *An Introduction
to Probability Theory and its Applications* vol. 2, §XI.9 (9.2) and §XI.1
(1.10)--(1.17); Gut, *Stopped Random Walks*, Thm. 6.6 and Rem. 6.4).

Mathlib v4.32.0 contains **no renewal theory at all** — the identifiers
`renewal`, `Blackwell`, `directly Riemann`, `ladder` and `random walk` do not
occur anywhere in the library. It does, however, provide the convolution of
measures `MeasureTheory.Measure.conv` (notation `∗`, the pushforward of
`μ.prod ν` under `+`) together with associativity, commutativity, the `dirac 0`
unit laws, `SFinite`/`IsProbabilityMeasure` instances and the integral formulas
`MeasureTheory.integral_conv` / `Measure.lintegral_conv`. That is the substrate
this file is built on.

This module is deliberately a **leaf**: it depends only on Mathlib, never on the
rest of `AbsorptionCutoff`. The chapter-specific bridge — instantiating everything here
at the Cramér-tilted increment law `μ̂_{A,N}` — lives in
`AbsorptionCutoff.Supercritical.StationaryEquation`.

## Main definitions

* `Renewal.convPow`: the convolution power `μ^{*n}`, the law of the random walk
  step `S_n = Z_1 + ⋯ + Z_n`.
* `Renewal.renewalMeasure`: the renewal measure `U = ∑_{n ≥ 0} μ^{*n}`.
* `Renewal.abelRenewalMeasure`: the Abel-discounted renewal measure
  `U_r = ∑_{n ≥ 0} rⁿ μ^{*n}`, the regularization used to identify Blackwell's
  constant `1/m̂`.
* `Renewal.expTransform`: the `ℝ≥0∞`-valued exponential transform
  `∫ e^{-θz} dμ`, which turns convolution into multiplication.

## Main results

* `Renewal.renewalMeasure_le_of_expTransform`: the explicit geometric left-tail
  bound `U(s) ≤ e^{θb}/(1 - ∫ e^{-θz}dμ)` for `s ⊆ (-∞, b]`, from which
* `Renewal.renewalMeasure_lt_top_of_expTransform_lt_one` and
  `Renewal.renewalMeasure_Icc_lt_top`: local finiteness of `U`.
* `Renewal.driNorm`: the directly-Riemann-integrable norm
  `∑_{k∈ℤ} sup_{[k,k+1]} g`, and `Renewal.tsum_lintegral_comp_sub_le`: a uniform
  bound `C` on the `U`-mass of unit cells gives `∑ₙ∫g(y−s)dμ^{*n} ≤ C‖g‖_DRI`.
* `Renewal.lintegral_le_driNorm`: `‖·‖_{L¹} ≤ ‖·‖_DRI`, whence
  `Renewal.integrable_of_driNorm` and `Renewal.norm_integral_sub_le_driNorm`.
* `Renewal.exists_hasCompactSupport_driNorm_sub_lt`: a continuous kernel of
  finite d.R.i. norm is `‖·‖_DRI`-approximable by continuous compactly supported
  ones.
* `Renewal.summable_integral_comp_sub_of_driNorm` and
  `Renewal.norm_tsum_integral_comp_sub_sub_le`: the smoothed renewal series of a
  kernel with finite d.R.i. norm converges absolutely, and two kernels' series
  differ by at most `C‖z−w‖_DRI` uniformly in `y`.

## Development plan

1. the convolution power `μ^{*n}` and the renewal measure `U` (this file);
2. Blackwell's renewal theorem;
3. the key renewal theorem for directly Riemann integrable functions on the line;
4. the paper's abstract measure-valued form
   (`eq:nd-abstract-renewal-equation` → `eq:nd-abstract-renewal-limit`).

The smoothing kernel (`unitBox`, `triangle`, `sincSq` and their Fourier
identities) lives in the sibling leaf module
`AbsorptionCutoff.Supercritical.RenewalKernel`, split off purely for build time.
-/

open MeasureTheory
open scoped ENNReal NNReal FourierTransform

namespace AbsorptionCutoff

namespace Renewal

variable {M : Type*} [AddMonoid M] [MeasurableSpace M]

lemma convPow_succ (μ : Measure M) (n : ℕ) : convPow μ (n + 1) = convPow μ n ∗ μ := rfl

instance instSFiniteConvPow (μ : Measure M) [SFinite μ] (n : ℕ) : SFinite (convPow μ n) := by
  induction n with
  | zero => rw [convPow_zero]; infer_instance
  | succ n ih => rw [convPow_succ]; exact Measure.sfinite_conv_of_sfinite _ _

instance instIsProbabilityMeasureConvPow [MeasurableAdd₂ M] (μ : Measure M)
    [IsProbabilityMeasure μ] (n : ℕ) : IsProbabilityMeasure (convPow μ n) := by
  induction n with
  | zero => rw [convPow_zero]; infer_instance
  | succ n ih => rw [convPow_succ]; exact Measure.probabilitymeasure_of_probabilitymeasures_conv _ _

@[simp]
lemma convPow_one [MeasurableAdd₂ M] (μ : Measure M) [SFinite μ] : convPow μ 1 = μ := by
  rw [convPow_succ, convPow_zero, Measure.dirac_zero_conv]

/-- Peeling the first increment instead of the last one. -/
lemma convPow_succ' [MeasurableAdd₂ M] (μ : Measure M) [SFinite μ] (n : ℕ) :
    convPow μ (n + 1) = μ ∗ convPow μ n := by
  induction n with
  | zero => rw [convPow_succ, convPow_zero, Measure.dirac_zero_conv, Measure.conv_dirac_zero]
  | succ n ih =>
      calc convPow μ (n + 1 + 1) = convPow μ (n + 1) ∗ μ := convPow_succ _ _
        _ = (μ ∗ convPow μ n) ∗ μ := by rw [ih]
        _ = μ ∗ (convPow μ n ∗ μ) := Measure.conv_assoc _ _ _
        _ = μ ∗ convPow μ (n + 1) := by rw [← convPow_succ]

lemma renewalMeasure_apply (μ : Measure M) {s : Set M} (hs : MeasurableSet s) :
    renewalMeasure μ s = ∑' n, convPow μ n s := Measure.sum_apply _ hs

/-!
### The Abel-discounted renewal measure

Identifying Blackwell's constant `1/m̂` is done by *Abel regularization*: the
undiscounted resolvent `(1 - χ(-2πt))⁻¹` has a genuine pole at the origin, and a
symmetric principal-value treatment of it sees only half the boundary mass,
producing `1/(2m̂)`. Discounting by `rⁿ` for `0 < r < 1` moves the pole off the
real axis — `1 - rχ(-2πt)` is bounded away from zero — and the model denominator
`(1-r) + 2π i r m̂ t` has a *one-sided* exponential inverse transform, which is
what supplies the missing half. The limits are then taken in the order `r ↑ 1` at
fixed `y`, and only afterwards `y → ∞`; see `A4G4_BLACKWELL_PROOF_NOTE.tex` §3.

The discounted measure is scaled in `ℝ≥0∞`, so it stays a genuine (nonnegative)
measure and `abelRenewalMeasure_mono` holds. That monotonicity in `r` is not
cosmetic: it is what licenses monotone convergence from the discounted series
back to the actual renewal series at `r = 1`.
-/

/-!
### Local finiteness of the renewal measure

For a general random walk drifting to `+∞`, local finiteness of `U` is proved by
a ladder-height decomposition. Here we do not need that generality: the increment
law the chapter supplies is the *Cramér tilt* `μ̂_{A,N}`, and the tilt comes with
a whole interval of finite exponential moments. Concretely, for
`0 < θ < β_{A,N}`,

  `∫ e^{-θ z} μ̂_{A,N}(dz) = ℳ_{A,N}(β_{A,N} - θ) < 1`,

the strict inequality being `gaussianTransferMoment_lt_one_of_lt_cramerExponent`
in `AbsorptionCutoff.Supercritical.StationaryEquation`. A Chernoff bound then makes the
convolution powers decay *geometrically* on every half-line `(-∞, b]`, so `U` is
finite there — much stronger than local finiteness, and enough for everything
downstream.

The transform is taken with values in `ℝ≥0∞` so that no integrability side
conditions are needed; the real-valued identification against `ℳ_{A,N}` is done
where the transform is applied.
-/

lemma expTransform_def (θ : ℝ) (μ : Measure ℝ) :
    expTransform θ μ = ∫⁻ z, ENNReal.ofReal (Real.exp (-(θ * z))) ∂μ := rfl

@[simp]
lemma expTransform_dirac_zero (θ : ℝ) : expTransform θ (Measure.dirac 0) = 1 := by
  rw [expTransform_def, lintegral_dirac' _ (by fun_prop)]
  simp

/-- The exponential transform turns convolution into multiplication. -/
lemma expTransform_conv (θ : ℝ) (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] :
    expTransform θ (ν ∗ μ) = expTransform θ ν * expTransform θ μ := by
  rw [expTransform_def, Measure.lintegral_conv (by fun_prop)]
  have key : ∀ x y : ℝ, ENNReal.ofReal (Real.exp (-(θ * (x + y))))
      = ENNReal.ofReal (Real.exp (-(θ * x))) * ENNReal.ofReal (Real.exp (-(θ * y))) := by
    intro x y
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    ring_nf
  have inner : ∀ x : ℝ, ∫⁻ y, ENNReal.ofReal (Real.exp (-(θ * (x + y)))) ∂μ
      = ENNReal.ofReal (Real.exp (-(θ * x))) * expTransform θ μ := by
    intro x
    simp_rw [key x]
    exact lintegral_const_mul _ (by fun_prop)
  simp_rw [inner]
  exact lintegral_mul_const _ (by fun_prop)

/-- `𝔼 e^{-θ S_n} = (𝔼 e^{-θ Z})^n`. -/
lemma expTransform_convPow (θ : ℝ) (μ : Measure ℝ) [SFinite μ] (n : ℕ) :
    expTransform θ (convPow μ n) = expTransform θ μ ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [convPow_succ, expTransform_conv, ih, pow_succ]

/-- Chernoff bound: a set contained in the half-line `(-∞, b]` has measure at
most `e^{θb}` times the exponential transform. -/
lemma measure_le_expTransform {θ b : ℝ} (hθ : 0 < θ) (ν : Measure ℝ) {s : Set ℝ}
    (hs : MeasurableSet s) (hsb : s ⊆ Set.Iic b) :
    ν s ≤ ENNReal.ofReal (Real.exp (θ * b)) * expTransform θ ν := by
  calc ν s = ∫⁻ _x in s, 1 ∂ν := by simp
    _ ≤ ∫⁻ x in s, ENNReal.ofReal (Real.exp (θ * b))
          * ENNReal.ofReal (Real.exp (-(θ * x))) ∂ν := by
        refine lintegral_mono_ae ((ae_restrict_iff' hs).2 (.of_forall fun x hx => ?_))
        have hxb : x ≤ b := hsb hx
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add, ← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (by nlinarith))
    _ ≤ ENNReal.ofReal (Real.exp (θ * b)) * expTransform θ ν := by
        rw [lintegral_const_mul _ (by fun_prop)]
        exact mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)

/-- **The explicit geometric left-tail bound on the renewal measure.**

If the increment law has exponential transform `λ := ∫ e^{-θz} dμ < 1` at some
`θ > 0`, then on every set contained in a half-line `(-∞, b]`,

  `U(s) ≤ e^{θb} / (1 - λ)`,

with the constant depending on `s` only through `b`. This is the *quantitative*
form of `renewalMeasure_lt_top_of_expTransform_lt_one`; the two-sided uniform
cell bound needs the constant, not just finiteness, because the right-hand tail
bound it is paired with is itself uniform.

No hypothesis on `λ` is needed for the inequality itself — at `λ ≥ 1` the right-hand
side is `∞` — so it is stated unconditionally; `λ < 1` is what makes it useful. -/
theorem renewalMeasure_le_of_expTransform {μ : Measure ℝ} [SFinite μ] {θ : ℝ}
    (hθ : 0 < θ) {s : Set ℝ} (hs : MeasurableSet s) {b : ℝ}
    (hsb : s ⊆ Set.Iic b) :
    renewalMeasure μ s ≤ ENNReal.ofReal (Real.exp (θ * b)) * (1 - expTransform θ μ)⁻¹ := by
  have hbound : ∀ n : ℕ, convPow μ n s
      ≤ ENNReal.ofReal (Real.exp (θ * b)) * expTransform θ μ ^ n := fun n => by
    calc convPow μ n s ≤ ENNReal.ofReal (Real.exp (θ * b)) * expTransform θ (convPow μ n) :=
          measure_le_expTransform hθ _ hs hsb
      _ = ENNReal.ofReal (Real.exp (θ * b)) * expTransform θ μ ^ n := by rw [expTransform_convPow]
  rw [renewalMeasure_apply _ hs]
  refine le_trans (ENNReal.tsum_le_tsum hbound) ?_
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

/-- **The renewal measure of a set is dominated by any kernel bounded below on it.**

If `v(y − ·) ≥ c > 0` on `I`, then `U(I) ≤ (∑ₙ ∫v(y−z)dμ^{*n})/c`.

This is the bridge from the *smoothed* renewal series — which the Abel argument
evaluates — back to the renewal measure of an actual interval, and hence the first
half of the uniform local bound. The comparison is done for each convolution power
separately: `c·μ^{*n}(I) ≤ ∫_I v(y−z)dμ^{*n} ≤ ∫ v(y−z)dμ^{*n}`, the second step
using `v ≥ 0`. Summing needs `ENNReal.ofReal_tsum_of_nonneg` to move the whole
real series into `ℝ≥0∞` at once, since the individual measures are `ℝ≥0∞`-valued
while the integrals are real. -/
theorem renewalMeasure_le_ofReal_tsum_integral {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {v : ℝ → ℝ} (hv0 : ∀ x, 0 ≤ v x) (hvc : Continuous v) {B : ℝ} (hB : ∀ x, v x ≤ B)
    {I : Set ℝ} (hI : MeasurableSet I) {y c : ℝ} (hc : 0 < c)
    (hvI : ∀ z ∈ I, c ≤ v (y - z))
    (hsum : Summable fun n => ∫ z, v (y - z) ∂(convPow μ n)) :
    renewalMeasure μ I ≤ ENNReal.ofReal ((∑' n, ∫ z, v (y - z) ∂(convPow μ n)) / c) := by
  have hterm : ∀ n : ℕ, (convPow μ n) I
      ≤ ENNReal.ofReal ((∫ z, v (y - z) ∂(convPow μ n)) / c) := by
    intro n
    have hint : Integrable (fun z : ℝ => v (y - z)) (convPow μ n) := by
      refine (integrable_const B).mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
      · exact (hvc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      · rw [Real.norm_of_nonneg (hv0 _)]
        exact hB _
    have h1 : ∫ z in I, c ∂(convPow μ n) ≤ ∫ z in I, v (y - z) ∂(convPow μ n) :=
      setIntegral_mono_on (integrable_const c).integrableOn hint.integrableOn hI hvI
    have h2 : ∫ z in I, v (y - z) ∂(convPow μ n) ≤ ∫ z, v (y - z) ∂(convPow μ n) :=
      setIntegral_le_integral hint (Filter.Eventually.of_forall fun z => hv0 _)
    rw [setIntegral_const, smul_eq_mul] at h1
    have hle : ((convPow μ n) I).toReal ≤ (∫ z, v (y - z) ∂(convPow μ n)) / c := by
      rw [le_div_iff₀ hc]
      calc ((convPow μ n) I).toReal * c = c * ((convPow μ n) I).toReal := by ring
        _ ≤ ∫ z, v (y - z) ∂(convPow μ n) := by
            rw [Measure.real] at h1
            linarith
    calc (convPow μ n) I = ENNReal.ofReal ((convPow μ n) I).toReal :=
          (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal ((∫ z, v (y - z) ∂(convPow μ n)) / c) := ENNReal.ofReal_le_ofReal hle
  have hnn : ∀ n : ℕ, 0 ≤ (∫ z, v (y - z) ∂(convPow μ n)) / c :=
    fun n => div_nonneg (integral_nonneg fun z => hv0 _) hc.le
  calc renewalMeasure μ I = ∑' n, (convPow μ n) I := renewalMeasure_apply _ hI
    _ ≤ ∑' n, ENNReal.ofReal ((∫ z, v (y - z) ∂(convPow μ n)) / c) :=
        ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal ((∑' n, ∫ z, v (y - z) ∂(convPow μ n)) / c) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg hnn (hsum.div_const c), tsum_div_const]

/-!
### Nonlatticeness and the characteristic function

The chosen proof route for Blackwell's theorem is Fourier inversion against
smoothing kernels with compactly supported Fourier transform (see
`A4G4_BLACKWELL_PROOF_NOTE.tex`). Nonlatticeness enters that argument
at exactly one point, and in exactly one form: the characteristic function
`χ(t) = ∫ e^{itz} dμ` must avoid the value `1` off the origin, so that
`1 - χ` is bounded away from `0` on the compact set where the transform of the
smoothing kernel lives.
-/

/-- **A nonlattice probability measure has `charFun μ t ≠ 1` for every `t ≠ 0`.**

If `χ(t) = 1` then, taking real parts, `∫ (1 - cos (t z)) dμ = 0`; the integrand
is nonnegative, so `cos (t z) = 1` for `μ`-a.e. `z`, i.e. `μ` is carried by the
lattice `(2π/t) ℤ`, contradicting `Nonlattice`. -/
theorem charFun_ne_one_of_nonlattice {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) {t : ℝ} (ht : t ≠ 0) : charFun μ t ≠ 1 := by
  intro h
  have hint : Integrable (fun x : ℝ => Complex.exp (t * x * Complex.I)) μ := by
    refine Integrable.of_bound (by fun_prop) 1 (Filter.Eventually.of_forall fun x => ?_)
    have : ((t : ℂ) * x * Complex.I) = ((t * x : ℝ) : ℂ) * Complex.I := by push_cast <;> ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  have hcos : Integrable (fun x : ℝ => Real.cos (t * x)) μ := by
    refine Integrable.of_bound (by fun_prop) 1 (Filter.Eventually.of_forall fun x => ?_)
    simpa using Real.abs_cos_le_one (t * x)
  -- The real part of the defining integral of `charFun`.
  have hre : ∫ x, Real.cos (t * x) ∂μ = 1 := by
    have h1 : ∫ x, ((Complex.exp ((t : ℂ) * x * Complex.I)).re) ∂μ = (charFun μ t).re := by
      rw [charFun_apply_real, ← Complex.reCLM_apply,
        ← ContinuousLinearMap.integral_comp_comm _ hint]
      rfl
    have h2 : ∀ x : ℝ, (Complex.exp ((t : ℂ) * x * Complex.I)).re = Real.cos (t * x) := by
      intro x
      have : ((t : ℂ) * x * Complex.I) = ((t * x : ℝ) : ℂ) * Complex.I := by push_cast <;> ring
      rw [this, Complex.exp_ofReal_mul_I_re]
    simp only [h2] at h1
    rw [h1, h]
    simp
  have key : ∫ x, (1 - Real.cos (t * x)) ∂μ = 0 := by
    rw [integral_sub (integrable_const 1) hcos, hre]
    simp
  have hae : ∀ᵐ x ∂μ, Real.cos (t * x) = 1 := by
    have hnn : 0 ≤ᵐ[μ] fun x => 1 - Real.cos (t * x) :=
      Filter.Eventually.of_forall fun x => by simpa using Real.cos_le_one (t * x)
    have := (integral_eq_zero_iff_of_nonneg_ae hnn ((integrable_const 1).sub hcos)).mp key
    filter_upwards [this] with x hx
    simp only [Pi.zero_apply] at hx
    linarith
  -- Hence `μ` is carried by the lattice `(2π/t) ℤ`.
  set S : Set ℝ := {x : ℝ | ∃ k : ℤ, x = 0 + k * (2 * Real.pi / t)} with hS
  have hsub : ∀ᵐ x ∂μ, x ∈ S := by
    filter_upwards [hae] with x hx
    obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff (t * x)).mp hx
    exact ⟨n, by field_simp <;> linarith [hn]⟩
  have hcount : S.Countable := by
    have : S = Set.range (fun k : ℤ => (0 : ℝ) + k * (2 * Real.pi / t)) := by
      ext x; simp [hS, eq_comm]
    rw [this]; exact Set.countable_range _
  exact hμ 0 (2 * Real.pi / t)
    ((prob_compl_eq_zero_iff hcount.measurableSet).mp (ae_iff.mp hsub))

/-- **`1 - charFun μ` is bounded away from `0` on a compact annulus.**

The Fourier proof of Blackwell's theorem integrates `(1 - charFun μ t)⁻¹` against
the transform of the smoothing kernel, which is supported in a compact interval
`[-T,T]`; near the origin the integrand is handled by the pole subtraction, and
on the remaining compact annulus `δ ≤ |t| ≤ T` this lemma keeps it bounded.
Nonlatticeness enters only through `charFun_ne_one_of_nonlattice`, and
compactness upgrades the pointwise nonvanishing to a uniform bound. -/
theorem exists_pos_le_norm_one_sub_charFun {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) {δ : ℝ} (hδ : 0 < δ) (T : ℝ) :
    ∃ c > 0, ∀ t : ℝ, |t| ≤ T → δ ≤ |t| → c ≤ ‖1 - charFun μ t‖ := by
  set K : Set ℝ := Set.Icc (-T) T ∩ {t : ℝ | δ ≤ |t|} with hK
  have hKc : IsCompact K := isCompact_Icc.inter_right (isClosed_le continuous_const continuous_abs)
  have hcont : Continuous fun t : ℝ => ‖1 - charFun μ t‖ :=
    (continuous_const.sub continuous_charFun).norm
  rcases K.eq_empty_or_nonempty with hemp | hne
  · refine ⟨1, one_pos, fun t htT htδ => ?_⟩
    exact absurd (show t ∈ K from ⟨abs_le.mp htT, htδ⟩) (by rw [hemp]; exact Set.notMem_empty t)
  · obtain ⟨t₀, ht₀K, ht₀min⟩ := hKc.exists_isMinOn hne hcont.continuousOn
    have ht₀ne : t₀ ≠ 0 := by
      intro h
      have h' := ht₀K.2
      simp only [Set.mem_setOf_eq, h, abs_zero] at h'
      linarith
    have hpos : 0 < ‖1 - charFun μ t₀‖ := by
      rw [norm_pos_iff, sub_ne_zero]
      exact fun h => charFun_ne_one_of_nonlattice hμ ht₀ne h.symm
    exact ⟨‖1 - charFun μ t₀‖, hpos,
      fun t htT htδ => ht₀min (show t ∈ K from ⟨abs_le.mp htT, htδ⟩)⟩

/-- **The characteristic function of a convolution power is a power**,
`χ_{μ^{*n}} = χ_μ^n`. This is the Fourier counterpart of `expTransform_convPow`,
and it is what turns the renewal measure `U = ∑ₙ μ^{*n}` into the geometric
series `∑ₙ χ^n = (1 - χ)⁻¹` under the Parseval atom below. -/
lemma charFun_convPow (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) (t : ℝ) :
    charFun (convPow μ n) t = (charFun μ t) ^ n := by
  induction n with
  | zero => simp [convPow_zero, charFun_dirac]
  | succ n ih => rw [convPow_succ, charFun_conv, ih, pow_succ]

/-!
### The pole at the origin

`(1 - charFun μ t)⁻¹` blows up at `t = 0`; that pole is precisely what carries
the `1/m̂` of Blackwell's theorem. The three lemmas below quantify it. They are
the only place where the **deliberate hypothesis strengthening** `MemLp id 2 μ`
(a finite second moment, where sharp Feller needs only a finite mean) is used;
`μ̂_{A,N}` has exponential moments, so it costs nothing at the instantiation.
-/

/-- The second-order Taylor expansion of the characteristic function at the
origin: `χ(t) = 1 + i m t - (∫x²) t²/2 + o(t²)`. Specialised from Mathlib's
`taylor_isLittleO_univ` and `taylorWithinEval_charFun_zero` — note the ready-made
`taylor_charFun_two` is stated only for a *standardised* law (mean `0`, variance
`1`) pushed forward along a random variable, so it is not usable here. -/
theorem charFun_taylor {μ : Measure ℝ} [IsProbabilityMeasure μ] (hint : MemLp id 2 μ) :
    (fun t : ℝ => charFun μ t - (1 + ((∫ x, x ∂μ : ℝ) : ℂ) * t * Complex.I
        - ((∫ x, x ^ 2 ∂μ : ℝ) : ℂ) * t ^ 2 / 2)) =o[nhds 0] fun t : ℝ => t ^ 2 := by
  have h := taylor_isLittleO_univ (f := charFun μ) (x₀ := (0 : ℝ)) (n := 2)
    (contDiff_charFun hint)
  simp only [sub_zero] at h
  refine h.congr' ?_ (Filter.EventuallyEq.refl _ _)
  filter_upwards with t
  rw [taylorWithinEval_charFun_zero hint t]
  simp [Finset.sum_range_succ]
  linear_combination (↑t ^ 2 * ↑(∫ x : ℝ, x ^ 2 ∂μ) * (1 / 2) : ℂ) * Complex.I_sq

/-- The quantitative form of the expansion: `1 - χ(t) + i m t = O(t²)` near the
origin. -/
theorem exists_norm_one_sub_charFun_add_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : MemLp id 2 μ) :
    ∃ δ > 0, ∃ K ≥ (0 : ℝ), ∀ t : ℝ, |t| ≤ δ →
      ‖1 - charFun μ t + ((∫ x, x ∂μ : ℝ) : ℂ) * t * Complex.I‖ ≤ K * t ^ 2 := by
  set m : ℝ := ∫ x, x ∂μ with hmdef
  set c : ℝ := ∫ x, x ^ 2 ∂μ with hcdef
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp ((charFun_taylor hint).def one_pos)
  refine ⟨ε / 2, by linarith, 1 + |c| / 2, by positivity, fun t ht => ?_⟩
  have hd : dist t 0 < ε := by
    rw [Real.dist_eq, sub_zero]; linarith [abs_nonneg t]
  have hsmall : ‖charFun μ t - (1 + (m : ℂ) * t * Complex.I - (c : ℂ) * t ^ 2 / 2)‖
      ≤ 1 * ‖t ^ 2‖ := hball hd
  have hkey : (1 : ℂ) - charFun μ t + (m : ℂ) * t * Complex.I
      = -(charFun μ t - (1 + (m : ℂ) * t * Complex.I - (c : ℂ) * t ^ 2 / 2))
        + (c : ℂ) * t ^ 2 / 2 := by ring
  rw [hkey]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_neg]
  have h1 : ‖charFun μ t - (1 + (m : ℂ) * t * Complex.I - (c : ℂ) * t ^ 2 / 2)‖ ≤ t ^ 2 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)] using hsmall
  have h2 : ‖(c : ℂ) * (t : ℂ) ^ 2 / 2‖ = |c| / 2 * t ^ 2 := by
    rw [norm_div, norm_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat]
    rw [← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)]
    ring
  rw [h2]
  linarith

/-!
### The Parseval atom

The workhorse of the Fourier route: convolving a measure with a test function
whose Fourier transform is integrable turns the measure into its characteristic
function. Applied to `ν = μ^{*n}` and summed over `n` — where `charFun_conv`
makes `charFun (μ^{*n}) = (charFun μ)^n` — this is what converts the renewal
measure into the resolvent `(1 - χ)⁻¹` whose pole at the origin carries the
`1/m̂` of Blackwell's theorem.

Mathlib's Fourier convention carries the `2π` in the exponent
(`𝓕 w t = ∫ e^{-2πi t x} w x dx`), while `charFun` does not
(`charFun ν s = ∫ e^{isz} dν`), whence the argument `-(2π t)` below. Both
conventions are kept as they are: `𝓕` is what the inversion theorem and the
Riemann–Lebesgue lemma are stated for, and `charFun` is what `charFun_conv`
is stated for.
-/

/-- **Parseval / inversion for a probability measure against a test function.**

For a test function `w` that is continuous and integrable with integrable Fourier
transform,
`∫ w(y - z) dν(z) = ∫ 𝓕w(t) e^{2πity} χ_ν(-2πt) dt`,
where `χ_ν = charFun ν`. Fourier inversion inside the `ν`-integral, then Fubini
(legitimate because `‖e^{iθ}‖ = 1` and `ν` is finite, so the joint integrand is
dominated by `‖𝓕w(t)‖`). -/
theorem integral_comp_sub_eq_integral_charFun {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {w : ℝ → ℂ} (hwc : Continuous w) (hw : Integrable w) (hFw : Integrable (𝓕 w)) (y : ℝ) :
    ∫ z, w (y - z) ∂ν
      = ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
          * charFun ν (-(2 * Real.pi * t)) := by
  have hinv : ∀ x : ℝ,
      w x = ∫ t : ℝ, Complex.exp ((2 * Real.pi * (t * x) : ℝ) * Complex.I) • 𝓕 w t := by
    intro x
    conv_lhs => rw [← congrFun (hwc.fourierInv_fourier_eq hw hFw) x]
    rw [Real.fourierInv_eq']
    simp only [Real.inner_apply]
  have hprod : Integrable (Function.uncurry
      (fun (z : ℝ) (t : ℝ) =>
        Complex.exp ((2 * Real.pi * (t * (y - z)) : ℝ) * Complex.I) • 𝓕 w t))
      (ν.prod volume) := by
    have hsnd : Integrable (fun p : ℝ × ℝ => 𝓕 w p.2) (ν.prod volume) := hFw.comp_snd ν
    refine (hsnd.norm).mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact ((Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable).mul
        hsnd.aestronglyMeasurable
    · obtain ⟨z, t⟩ := p
      change ‖Complex.exp ((2 * Real.pi * (t * (y - z)) : ℝ) * Complex.I) * 𝓕 w t‖ ≤ ‖𝓕 w t‖
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  calc ∫ z, w (y - z) ∂ν
      = ∫ z, ∫ t : ℝ,
          Complex.exp ((2 * Real.pi * (t * (y - z)) : ℝ) * Complex.I) • 𝓕 w t ∂volume ∂ν :=
        integral_congr_ae (Filter.Eventually.of_forall fun z => hinv (y - z))
    _ = ∫ t : ℝ, ∫ z, Complex.exp ((2 * Real.pi * (t * (y - z)) : ℝ) * Complex.I) • 𝓕 w t ∂ν :=
        integral_integral_swap hprod
    _ = ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
          * charFun ν (-(2 * Real.pi * t)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        simp only [charFun_apply_real, ← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        -- the goal is an un-beta-reduced redex; `rw` cannot see through it
        beta_reduce
        rw [smul_eq_mul, mul_assoc (𝓕 w t), ← Complex.exp_add, mul_comm]
        congr 1
        push_cast
        ring_nf

/-- The Parseval integrand is integrable, uniformly in the power `n`: the
exponential has modulus `1` and `‖charFun‖ ≤ 1`, so `‖𝓕w(t)‖` dominates. -/
lemma integrable_fourier_mul_charFun_pow {μ : Measure ℝ} [IsProbabilityMeasure μ] {w : ℝ → ℂ}
    (hw : Integrable w) (hFw : Integrable (𝓕 w)) (n : ℕ) (y : ℝ) :
    Integrable (fun t : ℝ => 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
        * (charFun μ (-(2 * Real.pi * t))) ^ n) := by
  have hFwc : Continuous (𝓕 w) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hw
  refine hFw.norm.mono' ?_ (Filter.Eventually.of_forall fun t => ?_)
  · exact ((hFwc.mul (Complex.continuous_exp.comp (by fun_prop))).mul
      ((continuous_charFun.comp (by fun_prop)).pow n)).aestronglyMeasurable
  · rw [norm_mul, norm_mul, norm_pow]
    have h1 : ‖Complex.exp ((2 : ℂ) * Real.pi * t * y * Complex.I)‖ = 1 := by
      have hcast : ((2 : ℂ) * Real.pi * t * y * Complex.I)
          = ((2 * Real.pi * t * y : ℝ) : ℂ) * Complex.I := by push_cast <;> ring
      rw [hcast, Complex.norm_exp_ofReal_mul_I]
    rw [h1, mul_one]
    have h2 : ‖charFun μ (-(2 * Real.pi * t))‖ ^ n ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) (norm_charFun_le_one _)
    calc ‖𝓕 w t‖ * ‖charFun μ (-(2 * Real.pi * t))‖ ^ n ≤ ‖𝓕 w t‖ * 1 :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = ‖𝓕 w t‖ := mul_one _

/-!
### The directly-Riemann-integrable norm and the cell error estimate

The key renewal theorem is proved here by *approximation in the d.R.i. norm*
rather than by Feller's route through Blackwell's interval theorem. The whole
mechanism is one inequality: if the renewal measure of every unit cell is at most
`C`, then the entire smoothed renewal series of a kernel `g` is at most
`C · ‖g‖_DRI`, where

  `‖g‖_DRI := ∑_{k ∈ ℤ} sup_{[k, k+1]} g`.

Applied to `g = |z − w|` this bounds the error made by replacing a d.R.i. kernel
`z` with a bandlimited approximation `w`; applied to `g = |z|` it gives absolute
convergence of the series itself.

Everything here is stated in `ℝ≥0∞`, where suprema and sums are total and the
inequality needs no integrability, measurability or finiteness hypotheses at all.
The real-valued consequences are extracted at the point of use.
-/

/-! #### A reference profile of finite d.R.i. norm

`(1+x²)⁻¹` is the profile every far-field estimate is compared against: it has
finite d.R.i. norm, so any kernel dominated by a constant multiple of it has one
too. This is what makes the far cells of a smoothing summable. -/

/-! #### The d.R.i. norm dominates the `L¹` norm

The cells have Lebesgue measure `1`, so `∫g ≤ ∑_k sup_{cell k} g = ‖g‖_DRI`
directly. Two things follow, both needed by the assembly: a kernel of finite
d.R.i. norm is integrable, and `∫` is `‖·‖_DRI`-continuous — so the approximation
that transfers the renewal limit also transfers the constant `∫z` in it. -/

/-! #### The cutoff

The first half of the bandlimited approximation: replace a d.R.i. kernel by a
*compactly supported* one, at a cost equal to the tail of `tendsto_driNorm_tail`.
Multiplying by a continuous plateau, rather than by an indicator, keeps the
approximant continuous, which the convolution step needs. -/

end Renewal

end AbsorptionCutoff
end

section
-- module Solutions.OAIQ247_JB.Supercritical_RenewalAbel
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

/-!
# Blackwell's theorem by Abel-regularized Fourier inversion

The continuation of `AbsorptionCutoff.Supercritical.Renewal` carrying the Abel argument
that identifies Blackwell's constant `1/m̂`. Split off purely for build time,
exactly as `RenewalKernel` was: the base module had reached ~2500 lines and 70 s
per edit-build cycle, which is too slow for the one-lemma loop.

Nothing here is new mathematics relative to the base module; see
`A4G4_BLACKWELL_PROOF_NOTE.tex` for the argument.

## Main results

* `Renewal.tendsto_tsum_integral_comp_sub`: the reference-kernel renewal limit
  `∑ₙ ∫ v(y−z) μ^{*n}(dz) ⟶ (∫v)/m̂`, for a bounded nonnegative continuous
  bandlimited kernel. **This is where Blackwell's constant is identified.**
* `Renewal.tendsto_of_tendsto_sum_integral_comp_sub_bandlimited`: the same limit
  for a general, possibly signed, bandlimited kernel.
-/

open MeasureTheory
open scoped ENNReal NNReal FourierTransform

namespace AbsorptionCutoff

namespace Renewal

/-!
### Discounted (Abel) Parseval

Everything above is restricted to *difference* kernels, because the undiscounted
resolvent `(1 - χ(-2πt))⁻¹` has a pole at the origin and only the first-order
vanishing of `𝓕w` tames it. Discounting removes the pole outright: for
`0 ≤ r < 1` one has `‖rχ‖ ≤ r < 1`, so `1 - rχ` is bounded away from zero on all
of `ℝ` and the geometric series converges *everywhere*, not merely off a null set.

Consequently the discounted Parseval identity (`eq:abel-parseval` of the proof
note) needs no nonlattice hypothesis, no second moment, no bandlimitedness and no
first-order vanishing — only `w` continuous with `w, 𝓕w ∈ L¹`, exactly the
hypotheses under which Fourier inversion holds pointwise for `w`. The dominating
function in the limit is the honest `L¹` function `‖𝓕w‖ (1-r)⁻¹`, in place of the
compactly supported constant `2C` used for difference kernels.
-/

/-- **The truncated discounted Parseval identity**: the discount factor `rⁿ` rides
along with the `n`-th characteristic-function power, so the geometric ratio
becomes `r χ(-2πt)`. -/
theorem sum_pow_integral_comp_sub_eq {μ : Measure ℝ} [IsProbabilityMeasure μ] {w : ℝ → ℂ}
    (hwc : Continuous w) (hw : Integrable w) (hFw : Integrable (𝓕 w)) (r : ℝ) (N : ℕ) (y : ℝ) :
    ∑ n ∈ Finset.range N, (r : ℂ) ^ n * ∫ z, w (y - z) ∂(convPow μ n)
      = ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
          * ∑ n ∈ Finset.range N, ((r : ℂ) * charFun μ (-(2 * Real.pi * t))) ^ n := by
  have hterm : ∀ n ∈ Finset.range N, (r : ℂ) ^ n * ∫ z, w (y - z) ∂(convPow μ n)
      = ∫ t : ℝ, (r : ℂ) ^ n * (𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
          * (charFun μ (-(2 * Real.pi * t))) ^ n) := by
    intro n _
    rw [integral_comp_sub_eq_integral_charFun hwc hw hFw y]
    simp only [charFun_convPow]
    rw [← integral_const_mul]
  rw [Finset.sum_congr rfl hterm,
    ← integral_finsetSum _ (fun n _ => (integrable_fourier_mul_charFun_pow hw hFw n y).const_mul
      ((r : ℂ) ^ n))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  beta_reduce
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [mul_pow]
  ring

/-- **Discounted Parseval** (`eq:abel-parseval`): for `0 ≤ r < 1`,

`∑ₙ rⁿ ∫ w(y−z) μ^{*n}(dz) = ∫ 𝓕w(t) e^{2πity} (1 − r χ(−2πt))⁻¹ dt`,

as a limit of partial sums. Dominated convergence with the `L¹` dominator
`‖𝓕w(t)‖ (1−r)⁻¹`: the partial geometric sums are bounded by `∑ₙ rⁿ = (1−r)⁻¹`
because `‖r χ(−2πt)‖ ≤ r`, and the same bound `r < 1` gives pointwise convergence
of the series to `(1 − r χ)⁻¹` at *every* frequency. There is no singularity in
this identity, which is precisely why the discounted route can see the constant
`1/m̂` that the difference-kernel theorem cannot. -/
theorem tendsto_sum_pow_integral_comp_sub {μ : Measure ℝ} [IsProbabilityMeasure μ] {w : ℝ → ℂ}
    (hwc : Continuous w) (hw : Integrable w) (hFw : Integrable (𝓕 w)) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (y : ℝ) :
    Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, (r : ℂ) ^ n * ∫ z, w (y - z) ∂(convPow μ n))
      Filter.atTop
      (nhds (∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
        * (1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹)) := by
  have hFwc : Continuous (𝓕 w) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hw
  have hexp : ∀ t : ℝ, ‖Complex.exp ((2 : ℂ) * Real.pi * t * y * Complex.I)‖ = 1 := by
    intro t
    have hcast : ((2 : ℂ) * Real.pi * t * y * Complex.I)
        = ((2 * Real.pi * t * y : ℝ) : ℂ) * Complex.I := by push_cast <;> ring
    rw [hcast, Complex.norm_exp_ofReal_mul_I]
  -- the discounted ratio has modulus at most `r`, uniformly in the frequency
  have hnorm : ∀ t : ℝ, ‖(r : ℂ) * charFun μ (-(2 * Real.pi * t))‖ ≤ r := by
    intro t
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0]
    calc r * ‖charFun μ (-(2 * Real.pi * t))‖ ≤ r * 1 :=
          mul_le_mul_of_nonneg_left (norm_charFun_le_one _) hr0
      _ = r := mul_one r
  simp only [sum_pow_integral_comp_sub_eq hwc hw hFw]
  refine tendsto_integral_of_dominated_convergence
    (fun t => ‖𝓕 w t‖ * (1 - r)⁻¹) (fun N => ?_) (hFw.norm.mul_const _) (fun N => ?_) ?_
  · exact ((hFwc.mul (Complex.continuous_exp.comp (by fun_prop))).mul
      (continuous_finsetSum _ fun n _ =>
        (continuous_const.mul (continuous_charFun.comp (by fun_prop))).pow n)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun t => ?_
    rw [norm_mul, norm_mul, hexp t, mul_one]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    calc ‖∑ n ∈ Finset.range N, ((r : ℂ) * charFun μ (-(2 * Real.pi * t))) ^ n‖
        ≤ ∑ n ∈ Finset.range N, r ^ n := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
          rw [norm_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) (hnorm t) n
      _ ≤ (1 - r)⁻¹ := by
          rw [← tsum_geometric_of_lt_one hr0 hr1]
          exact (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum _ (fun i _ => pow_nonneg hr0 i)
  · refine Filter.Eventually.of_forall fun t => ?_
    exact ((hasSum_geometric_of_norm_lt_one
      (lt_of_le_of_lt (hnorm t) hr1)).tendsto_sum_nat).const_mul _

/-!
### The model pole

The discounted resolvent is compared against the *model denominator*
`b_r(t) = (1-r) + 2π i r m̂ t`, which is what the true denominator
`1 - rχ(-2πt)` looks like to first order. The point of the model is that its
inverse Fourier transform can be computed in closed form, and — crucially — the
answer is **one-sided**: the Laplace representation

`((1-r) + 2π i r m̂ t)⁻¹ = ∫_0^∞ e^{-(1-r)s} e^{-2π i r m̂ t s} ds`

integrates only over `s > 0`, so the resulting kernel lives on `(-∞, y]`. That
one-sidedness is exactly the boundary mass a symmetric principal-value treatment
of the undiscounted pole throws away, and it is why this route recovers the full
constant `1/m̂` rather than `1/(2m̂)` (proof note §§2–3).

The Laplace representation itself is a Mathlib gap: `v4.32.0` has
`integrableOn_exp_mul_complex_Ioi` but no evaluation of `∫_0^∞ e^{-bs} ds` for
complex `b`, so `integral_Ioi_cexp_neg_mul` is proved here from the improper
fundamental theorem of calculus.
-/

/-- `∫_0^∞ e^{-bs} ds = b⁻¹` for `Re b > 0`.

Not in Mathlib v4.32.0 for complex `b`. Proved by the improper FTC
`integral_Ioi_of_hasDerivAt_of_tendsto` applied to the primitive
`s ↦ -b⁻¹ e^{-bs}`, whose modulus `‖b⁻¹‖ e^{-(Re b)s}` vanishes at `+∞`. -/
theorem integral_Ioi_cexp_neg_mul {b : ℂ} (hb : 0 < b.re) :
    ∫ s : ℝ in Set.Ioi (0 : ℝ), Complex.exp (-(b * s)) = b⁻¹ := by
  have hb0 : b ≠ 0 := fun h => by simp [h] at hb
  set f : ℝ → ℂ := fun s => -b⁻¹ * Complex.exp (-(b * s)) with hf
  have hderiv : ∀ s ∈ Set.Ioi (0 : ℝ), HasDerivAt f (Complex.exp (-(b * s))) s := by
    intro s _
    have h0 : HasDerivAt (fun s : ℝ => b * (s : ℂ)) b s := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).const_mul b
    have h1 : HasDerivAt (fun s : ℝ => -(b * (s : ℂ))) (-b) s := h0.neg
    have h2 := (h1.cexp).const_mul (-b⁻¹)
    have h3 : -b⁻¹ * (Complex.exp (-(b * s)) * -b) = Complex.exp (-(b * s)) := by field_simp
    rw [← h3]
    exact h2
  have hint : IntegrableOn (fun s : ℝ => Complex.exp (-(b * s))) (Set.Ioi 0) := by
    have := integrableOn_exp_mul_complex_Ioi (a := -b) (by simpa using hb) 0
    simpa [neg_mul] using this
  have hcont : ContinuousWithinAt f (Set.Ici (0 : ℝ)) 0 := by
    apply Continuous.continuousWithinAt
    fun_prop
  have htend : Filter.Tendsto f Filter.atTop (nhds 0) := by
    have hnorm : Filter.Tendsto (fun s : ℝ => ‖f s‖) Filter.atTop (nhds 0) := by
      have hval : ∀ s : ℝ, ‖f s‖ = ‖b⁻¹‖ * Real.exp (-(b.re * s)) := by
        intro s
        rw [hf]
        simp [Complex.norm_exp]
      simp only [hval]
      have h1 : Filter.Tendsto (fun s : ℝ => Real.exp (-(b.re * s))) Filter.atTop (nhds 0) :=
        Real.tendsto_exp_atBot.comp
          (Filter.tendsto_neg_atTop_atBot.comp
            (Filter.Tendsto.const_mul_atTop hb Filter.tendsto_id))
      simpa using h1.const_mul ‖b⁻¹‖
    exact tendsto_zero_iff_norm_tendsto_zero.2 hnorm
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint htend]
  simp [hf]

/-- Pointwise Fourier inversion in the multiplicative form used throughout this
file: `w x = ∫ 𝓕w(t) e^{2πitx} dt`, for `w` continuous with `w, 𝓕w ∈ L¹`.

This is the hypothesis-explicit interface the Abel argument needs; it is the same
computation that opens `integral_comp_sub_eq_integral_charFun`. -/
lemma eq_integral_fourier_mul_exp {w : ℝ → ℂ} (hwc : Continuous w) (hw : Integrable w)
    (hFw : Integrable (𝓕 w)) (x : ℝ) :
    w x = ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * x * Complex.I) := by
  conv_lhs => rw [← congrFun (hwc.fourierInv_fourier_eq hw hFw) x]
  rw [Real.fourierInv_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [Real.inner_apply, smul_eq_mul]
  rw [mul_comm]
  congr 1
  push_cast
  ring_nf

/-- **The model pole is a one-sided exponential average** (`lem:model-pole`,
first identity): for `a > 0` and any `c`,

`∫ 𝓕w(t) e^{2πiyt} (a + 2π i c t)⁻¹ dt = ∫_0^∞ e^{-as} w(y − cs) ds`.

Substitute the Laplace representation `integral_Ioi_cexp_neg_mul` for the
denominator, swap with Fubini (the joint integrand is dominated by
`‖𝓕w(t)‖ e^{-as}`, a product of two integrable functions), and evaluate the
inner frequency integral by pointwise inversion at `y − cs`.

The `s`-integral runs over `(0,∞)` only: at the Abel parameters `a = 1−r`,
`c = r m̂` this is the whole source of the boundary mass. Positivity of `c` is not
needed here; it enters when the substitution `x = y − cs` turns this into an
integral over `(−∞, y]`. -/
theorem integral_fourier_model_pole {w : ℝ → ℂ} (hwc : Continuous w) (hw : Integrable w)
    (hFw : Integrable (𝓕 w)) {a : ℝ} (ha : 0 < a) (c y : ℝ) :
    ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
        * ((a : ℂ) + 2 * Real.pi * c * t * Complex.I)⁻¹
      = ∫ s in Set.Ioi (0 : ℝ), (Real.exp (-(a * s)) : ℂ) * w (y - c * s) := by
  have hFwc : Continuous (𝓕 w) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hw
  set d : ℝ → ℂ := fun t => (a : ℂ) + 2 * Real.pi * c * t * Complex.I with hd
  have hre : ∀ t : ℝ, 0 < (d t).re := by intro t; simpa [hd] using ha
  set G : ℝ → ℝ → ℂ := fun t s => (Real.exp (-(a * s)) : ℂ) *
    (𝓕 w t * Complex.exp (2 * Real.pi * t * (y - c * s) * Complex.I)) with hG
  have hkey : ∀ t s : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
      * Complex.exp (-(d t * s)) = G t s := by
    intro t s
    calc 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I) * Complex.exp (-(d t * s))
        = 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I + -(d t * s)) := by
          rw [mul_assoc, ← Complex.exp_add]
      _ = 𝓕 w t * Complex.exp (((-(a * s) : ℝ) : ℂ)
            + 2 * Real.pi * t * (y - c * s) * Complex.I) := by
          congr 2
          rw [hd]
          push_cast
          ring
      _ = G t s := by
          rw [hG, Complex.exp_add, ← Complex.ofReal_exp]
          ring
  have hstep : ∀ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I) * (d t)⁻¹
      = ∫ s in Set.Ioi (0 : ℝ), G t s := by
    intro t
    rw [← integral_Ioi_cexp_neg_mul (hre t), ← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun s _ => hkey t s
  have hexpint : IntegrableOn (fun s : ℝ => Real.exp (-(a * s))) (Set.Ioi 0) := by
    have := integrableOn_exp_mul_Ioi (a := -a) (by simpa using ha) 0
    simpa [neg_mul] using this
  have hprod : Integrable (Function.uncurry G)
      (volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
    have hdom : Integrable (fun p : ℝ × ℝ => ‖𝓕 w p.1‖ * Real.exp (-(a * p.2)))
        (volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))) := Integrable.mul_prod hFw.norm hexpint
    refine hdom.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact Continuous.aestronglyMeasurable (by rw [hG]; fun_prop)
    · obtain ⟨t, s⟩ := p
      simp only [Function.uncurry_apply_pair, hG, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
      rw [Complex.norm_exp]
      have hz : (2 * (Real.pi : ℂ) * (t : ℂ)
          * ((y : ℂ) - (c : ℂ) * (s : ℂ)) * Complex.I).re = 0 := by simp
      rw [hz]
      simp [mul_comm]
  calc ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I) * (d t)⁻¹
      = ∫ t : ℝ, ∫ s in Set.Ioi (0 : ℝ), G t s :=
        integral_congr_ae (Filter.Eventually.of_forall hstep)
    _ = ∫ s in Set.Ioi (0 : ℝ), ∫ t : ℝ, G t s := integral_integral_swap hprod
    _ = ∫ s in Set.Ioi (0 : ℝ), (Real.exp (-(a * s)) : ℂ) * w (y - c * s) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
        rw [hG, integral_const_mul]
        congr 1
        rw [eq_integral_fourier_mul_exp hwc hw hFw (y - c * s)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        push_cast
        ring_nf

/-- The affine change of variables `x = y - c s` on the whole line, `c > 0`.

Stated for `volume` on `ℝ` via `Measure.integral_comp_mul_left` (the dilation) and
`integral_add_left_eq_self` (the translation); the reflection is absorbed into the
dilation by the *negative* factor `-c`, which avoids needing a
`volume.IsNegInvariant` instance. -/
theorem integral_comp_sub_mul_left (F : ℝ → ℂ) (y : ℝ) {c : ℝ} (hc : 0 < c) :
    ∫ s : ℝ, F (y - c * s) = c⁻¹ • ∫ x : ℝ, F x := by
  have h1 : ∀ s : ℝ, F (y - c * s) = (fun u : ℝ => F (y + u)) ((-c) * s) := by
    intro s; simp only; congr 1; ring
  have h2 : (∫ s : ℝ, F (y - c * s)) = ∫ s : ℝ, (fun u : ℝ => F (y + u)) ((-c) * s) :=
    integral_congr_ae (Filter.Eventually.of_forall h1)
  have h3 := Measure.integral_comp_mul_left (fun u : ℝ => F (y + u)) (-c)
  have h4 : (∫ u : ℝ, F (y + u)) = ∫ x : ℝ, F x := integral_add_left_eq_self F y
  have h5 : |(-c)⁻¹| = c⁻¹ := by rw [abs_inv, abs_neg, abs_of_pos hc]
  rw [h2, h3, h4, h5]

/-- The substitution `x = y - c s`, `c > 0`, turns the one-sided exponential
average over `s > 0` into an integral over the half-line `(-∞, y]`:

`∫_0^∞ e^{-as} w(y − cs) ds = c⁻¹ ∫_{-∞}^y e^{-a(y-x)/c} w(x) dx`.

Both sides are written as full-line integrals of an indicator so that
`integral_comp_sub_mul_left` applies; the two indicator conditions match because
`y − cs < y ↔ s > 0` for `c > 0`. -/
theorem integral_Ioi_exp_comp_sub_eq (w : ℝ → ℂ) {a c : ℝ} (hc : 0 < c) (y : ℝ) :
    ∫ s in Set.Ioi (0 : ℝ), (Real.exp (-(a * s)) : ℂ) * w (y - c * s)
      = c⁻¹ • ∫ x in Set.Iio y, (Real.exp (-(a * (y - x) / c)) : ℂ) * w x := by
  set F : ℝ → ℂ :=
    (Set.Iio y).indicator (fun x => (Real.exp (-(a * (y - x) / c)) : ℂ) * w x) with hF
  have hpt : ∀ s : ℝ, (Set.Ioi (0 : ℝ)).indicator
      (fun s => (Real.exp (-(a * s)) : ℂ) * w (y - c * s)) s = F (y - c * s) := by
    intro s
    by_cases hs : (0 : ℝ) < s
    · have hmem : y - c * s ∈ Set.Iio y := Set.mem_Iio.2 (by nlinarith)
      rw [Set.indicator_of_mem (Set.mem_Ioi.2 hs), hF, Set.indicator_of_mem hmem]
      congr 2
      congr 1
      field_simp
      ring
    · have hmem : y - c * s ∉ Set.Iio y := by
        simp only [Set.mem_Iio, not_lt] at *
        nlinarith
      rw [Set.indicator_of_notMem (by simpa using hs), hF, Set.indicator_of_notMem hmem]
  rw [← integral_indicator measurableSet_Ioi,
    integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_comp_sub_mul_left F y hc, hF, integral_indicator measurableSet_Iio]

/-- **The model pole in closed form** (`eq:model-pole-formula`): for `a, c > 0`,

`∫ 𝓕w(t) e^{2πiyt} (a + 2π i c t)⁻¹ dt
   = c⁻¹ ∫_{-∞}^y e^{-a(y-x)/c} w(x) dx`.

At the Abel parameters `a = 1 − r`, `c = r m̂` the right-hand side is the paper
note's one-sided Laplace kernel; letting `r ↑ 1` at fixed `y` sends the
exponential weight to `1` and leaves `(1/m̂) ∫_{-∞}^y w`. -/
theorem integral_fourier_model_pole_Iio {w : ℝ → ℂ} (hwc : Continuous w) (hw : Integrable w)
    (hFw : Integrable (𝓕 w)) {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (y : ℝ) :
    ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
        * ((a : ℂ) + 2 * Real.pi * c * t * Complex.I)⁻¹
      = c⁻¹ • ∫ x in Set.Iio y, (Real.exp (-(a * (y - x) / c)) : ℂ) * w x := by
  rw [integral_fourier_model_pole hwc hw hFw ha c y, integral_Ioi_exp_comp_sub_eq w hc y]

/-- The exponential weight in the model pole disappears as `r ↑ 1` at fixed `y`.

Dominated convergence on `(-∞, y]` with dominator `‖w‖`: for `0 < r < 1` and
`x < y` the exponent `-(1-r)(y-x)/(rm)` is `≤ 0`, so the weight is bounded by `1`,
and it tends to `1` pointwise because `r ↦ e^{-(1-r)(y-x)/(rm)}` is continuous at
`r = 1` with value `e^0 = 1`. Note the *order of limits*: `y` is fixed here, and
only afterwards is `y → ∞` taken. -/
theorem tendsto_integral_Iio_exp_weight {w : ℝ → ℂ} (hw : Integrable w) {m : ℝ} (hm : 0 < m)
    (y : ℝ) :
    Filter.Tendsto
      (fun r : ℝ => ∫ x in Set.Iio y, (Real.exp (-((1 - r) * (y - x) / (r * m))) : ℂ) * w x)
      (nhdsWithin 1 (Set.Iio 1)) (nhds (∫ x in Set.Iio y, w x)) := by
  have hpos : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio (1 : ℝ)), 0 < r :=
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  have hlt : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio (1 : ℝ)), r < 1 := eventually_mem_nhdsWithin
  refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖w x‖) ?_ ?_
    hw.norm.restrict ?_
  · filter_upwards with r
    exact (Continuous.aestronglyMeasurable (by fun_prop)).mul hw.1.restrict
  · filter_upwards [hpos, hlt] with r hr0 hr1
    filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
    have hxy : x < y := hx
    have hexp : Real.exp (-((1 - r) * (y - x) / (r * m))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have h0 : 0 ≤ (1 - r) * (y - x) / (r * m) := by
        apply div_nonneg
        · nlinarith
        · positivity
      linarith
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
    calc Real.exp (-((1 - r) * (y - x) / (r * m))) * ‖w x‖ ≤ 1 * ‖w x‖ :=
          mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
      _ = ‖w x‖ := one_mul _
  · filter_upwards [ae_restrict_mem measurableSet_Iio] with x _
    have hcont : ContinuousAt (fun r : ℝ => (Real.exp (-((1 - r) * (y - x) / (r * m))) : ℂ)) 1 := by
      apply Complex.continuous_ofReal.continuousAt.comp
      apply Real.continuous_exp.continuousAt.comp
      apply ContinuousAt.neg
      apply ContinuousAt.div (by fun_prop) (by fun_prop)
      simpa using hm.ne'
    have h0 := hcont.tendsto
    have hval : (Real.exp (-((1 - (1 : ℝ)) * (y - x) / (1 * m))) : ℂ) = 1 := by norm_num
    rw [hval] at h0
    have h1 := h0.mono_left (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))
    simpa using h1.mul_const (w x)

/-- **The `r ↑ 1` limit of the model pole** (`eq:model-pole-limit`): at the Abel
parameters `a = 1 − r`, `c = r m̂`,

`∫ 𝓕w(t) e^{2πiyt} ((1−r) + 2π i r m̂ t)⁻¹ dt ⟶ (1/m̂) ∫_{-∞}^y w`

as `r ↑ 1` with `y` held fixed. The limit is taken along `𝓝[<] 1`, on which
`0 < r < 1` holds eventually — exactly the hypotheses
`integral_fourier_model_pole_Iio` needs.

**The order of the two limits is not interchangeable.** First `r ↑ 1` at fixed
`y`, as here; only then `y → ∞`, which turns `∫_{-∞}^y w` into `∫ w` and produces
the constant `(∫w)/m̂`. Swapping them loses the boundary mass and yields
`1/(2m̂)`. -/
theorem tendsto_integral_fourier_model_pole {w : ℝ → ℂ} (hwc : Continuous w) (hw : Integrable w)
    (hFw : Integrable (𝓕 w)) {m : ℝ} (hm : 0 < m) (y : ℝ) :
    Filter.Tendsto (fun r : ℝ => ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
        * (((1 - r : ℝ) : ℂ) + 2 * Real.pi * ((r * m : ℝ) : ℂ) * t * Complex.I)⁻¹)
      (nhdsWithin 1 (Set.Iio 1)) (nhds (m⁻¹ • ∫ x in Set.Iio y, w x)) := by
  have hpos : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio (1 : ℝ)), 0 < r :=
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  have hlt : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio (1 : ℝ)), r < 1 := eventually_mem_nhdsWithin
  have hscal : Filter.Tendsto (fun r : ℝ => ((r * m)⁻¹ : ℝ))
      (nhdsWithin 1 (Set.Iio (1 : ℝ))) (nhds m⁻¹) := by
    have hc : ContinuousAt (fun r : ℝ => (r * m)⁻¹) 1 := by
      apply ContinuousAt.inv₀ (by fun_prop)
      simpa using hm.ne'
    simpa using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))
  have heq : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio (1 : ℝ)),
      (∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
        * (((1 - r : ℝ) : ℂ) + 2 * Real.pi * ((r * m : ℝ) : ℂ) * t * Complex.I)⁻¹)
      = (r * m)⁻¹ • ∫ x in Set.Iio y, (Real.exp (-((1 - r) * (y - x) / (r * m))) : ℂ) * w x := by
    filter_upwards [hpos, hlt] with r hr0 hr1
    exact integral_fourier_model_pole_Iio hwc hw hFw (by linarith) (by positivity) y
  refine (Filter.tendsto_congr' heq).mpr ?_
  exact hscal.smul (tendsto_integral_Iio_exp_weight hw hm y)

/-!
### Uniform lower bounds on the two denominators

The comparison of the discounted resolvent with the model pole
(`lem:uniform-pole-correction`) rests on the *matching* lower bounds

`‖1 - rχ(u)‖ ≥ c((1-r) + |u|)`,  `‖(1-r) + 2π i r m̂ t‖ ≥ c((1-r) + |t|)`,

valid near the origin and uniformly in `r ∈ [1/2, 1]`. Both are proved the same
way, from `‖z‖ ≥ max(Re z, |Im z|) ≥ (Re z + |Im z|)/2`:

* the real part supplies the `(1-r)` — for the discounted denominator because
  `Re(1 - rχ) = (1-r) + r(1 - Re χ) ≥ 1-r`, using only `Re χ ≤ ‖χ‖ ≤ 1`;
* the imaginary part supplies the `|u|`, from the first-order behaviour
  `Im(1 - χ(u)) = -m̂u + O(u²)`.

The second bullet needs an *imaginary-part* refinement of the A-4f expansion:
`exists_le_norm_one_sub_charFun` bounds the modulus from below, which is not
enough here, because the real part is what carries `(1-r)` and the two
contributions must be separated.
-/

/-- The imaginary part of `1 - charFun μ` has a simple zero at the origin:
`|Im(1 - χ(u))| ≥ (m̂/2)|u|` near `0`, where `m̂ = ∫x dμ > 0`.

Refines `exists_le_norm_one_sub_charFun` (a modulus bound) to the imaginary part,
which is what the Abel comparison needs. Same proof: `|Im z| ≤ ‖z‖` applied to
the `O(u²)` remainder of `exists_norm_one_sub_charFun_add_le`, then the linear
term dominates for `|u|` small. -/
theorem exists_le_abs_im_one_sub_charFun {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ) :
    ∃ δ > 0, ∀ u : ℝ, |u| ≤ δ →
      (∫ x, x ∂μ) / 2 * |u| ≤ |((1 : ℂ) - charFun μ u).im| := by
  set m : ℝ := ∫ x, x ∂μ with hmdef
  obtain ⟨δ, hδ, K, hK, hbound⟩ := exists_norm_one_sub_charFun_add_le hint
  have hK1 : (0 : ℝ) < K + 1 := by linarith
  refine ⟨min δ (m / (2 * (K + 1))), lt_min hδ (by positivity), fun u hu => ?_⟩
  have hu1 : |u| ≤ δ := le_trans hu (min_le_left _ _)
  have hu2 : |u| ≤ m / (2 * (K + 1)) := le_trans hu (min_le_right _ _)
  have hb := hbound u hu1
  have him : |((1 : ℂ) - charFun μ u).im + m * u| ≤ K * u ^ 2 := by
    have h1 : ((1 : ℂ) - charFun μ u + (m : ℂ) * (u : ℂ) * Complex.I).im
        = ((1 : ℂ) - charFun μ u).im + m * u := by simp
    calc |((1 : ℂ) - charFun μ u).im + m * u|
        = |((1 : ℂ) - charFun μ u + (m : ℂ) * (u : ℂ) * Complex.I).im| := by rw [h1]
      _ ≤ ‖(1 : ℂ) - charFun μ u + (m : ℂ) * (u : ℂ) * Complex.I‖ := Complex.abs_im_le_norm _
      _ ≤ K * u ^ 2 := hb
  have habs : K * u ^ 2 ≤ m / 2 * |u| := by
    have hsq : u ^ 2 = |u| * |u| := by rw [← sq_abs u, sq]
    have hmul := mul_le_mul_of_nonneg_left hu2 hK1.le
    have hval : (K + 1) * (m / (2 * (K + 1))) = m / 2 := by field_simp
    rw [hval] at hmul
    calc K * u ^ 2 ≤ (K + 1) * u ^ 2 := by nlinarith [sq_nonneg u]
      _ = ((K + 1) * |u|) * |u| := by rw [hsq]; ring
      _ ≤ (m / 2) * |u| := mul_le_mul_of_nonneg_right hmul (abs_nonneg u)
  have hmu : |m * u| = m * |u| := by rw [abs_mul, abs_of_pos hm]
  have h2 : |m * u| - |((1 : ℂ) - charFun μ u).im| ≤ |((1 : ℂ) - charFun μ u).im + m * u| := by
    calc |m * u| - |((1 : ℂ) - charFun μ u).im|
        = |m * u| - |-((1 : ℂ) - charFun μ u).im| := by rw [abs_neg]
      _ ≤ |m * u - -((1 : ℂ) - charFun μ u).im| := abs_sub_abs_le_abs_sub _ _
      _ = |((1 : ℂ) - charFun μ u).im + m * u| := by rw [sub_neg_eq_add, add_comm]
  rw [hmu] at h2
  linarith

/-- **The discounted denominator is bounded below by `c((1-r) + |u|)`** near the
origin, uniformly for `r ∈ [1/2, 1]` (`eq:true-denominator-lower`).

The real part gives `(1-r)` and the imaginary part gives `|u|`; discounting is
exactly what makes the bound survive at `u = 0`, where the undiscounted
denominator vanishes. -/
theorem exists_le_norm_one_sub_smul_charFun {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ) :
    ∃ δ > 0, ∀ r : ℝ, 1 / 2 ≤ r → r ≤ 1 → ∀ u : ℝ, |u| ≤ δ →
      min 1 ((∫ x, x ∂μ) / 4) / 2 * ((1 - r) + |u|) ≤ ‖1 - (r : ℂ) * charFun μ u‖ := by
  set m : ℝ := ∫ x, x ∂μ with hmdef
  obtain ⟨δ, hδ, him⟩ := exists_le_abs_im_one_sub_charFun hint hm
  refine ⟨δ, hδ, fun r hr hr1 u hu => ?_⟩
  have hr0 : (0 : ℝ) ≤ r := by linarith
  set z : ℂ := 1 - (r : ℂ) * charFun μ u with hz
  have hrec : (1 - r) ≤ z.re := by
    have h1 : (charFun μ u).re ≤ 1 := le_trans (Complex.re_le_norm _) (norm_charFun_le_one _)
    have h2 : z.re = 1 - r * (charFun μ u).re := by simp [hz]
    rw [h2]
    nlinarith
  have hrez : (1 - r) ≤ ‖z‖ := le_trans hrec (Complex.re_le_norm _)
  have himz : m / 4 * |u| ≤ ‖z‖ := by
    have h3 : z.im = r * ((1 : ℂ) - charFun μ u).im := by simp [hz]
    have h4 : |z.im| = r * |((1 : ℂ) - charFun μ u).im| := by
      rw [h3, abs_mul, abs_of_nonneg hr0]
    have h5 : m / 2 * |u| ≤ |((1 : ℂ) - charFun μ u).im| := by
      rw [hmdef]; exact him u hu
    have h6 : m / 4 * |u| ≤ r * (m / 2 * |u|) := by
      have h7 := mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ r - 1 / 2) hm.le) (abs_nonneg u)
      nlinarith
    calc m / 4 * |u| ≤ r * (m / 2 * |u|) := h6
      _ ≤ r * |((1 : ℂ) - charFun μ u).im| := mul_le_mul_of_nonneg_left h5 hr0
      _ = |z.im| := h4.symm
      _ ≤ ‖z‖ := Complex.abs_im_le_norm _
  have hmin1 : min 1 (m / 4) ≤ 1 := min_le_left _ _
  have hmin2 : min 1 (m / 4) ≤ m / 4 := min_le_right _ _
  have h1r : 0 ≤ 1 - r := by linarith
  calc min 1 (m / 4) / 2 * ((1 - r) + |u|)
      = (min 1 (m / 4) * (1 - r) + min 1 (m / 4) * |u|) / 2 := by ring
    _ ≤ ((1 - r) + m / 4 * |u|) / 2 := by
        have ha : min 1 (m / 4) * (1 - r) ≤ 1 * (1 - r) :=
          mul_le_mul_of_nonneg_right hmin1 h1r
        have hb : min 1 (m / 4) * |u| ≤ m / 4 * |u| :=
          mul_le_mul_of_nonneg_right hmin2 (abs_nonneg u)
        rw [one_mul] at ha
        linarith
    _ ≤ ‖z‖ := by linarith

/-- **The model denominator obeys the same lower bound**
(`eq:model-denominator-lower`), and unconditionally in `t`: no expansion is
involved, the real part *is* `1-r` and the imaginary part *is* `2π r m̂ t`. -/
theorem le_norm_model_denominator {m : ℝ} (hm : 0 < m) {r : ℝ} (hr : 1 / 2 ≤ r) (hr1 : r ≤ 1)
    (t : ℝ) :
    min 1 (Real.pi * m) / 2 * ((1 - r) + |t|)
      ≤ ‖((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ) * (t : ℂ) * Complex.I‖ := by
  set z : ℂ := ((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ) * (t : ℂ) * Complex.I
    with hz
  have hr0 : (0 : ℝ) ≤ r := by linarith
  have hre : z.re = 1 - r := by simp [hz]
  have him : z.im = 2 * Real.pi * (r * m) * t := by simp [hz]
  have hrez : (1 - r) ≤ ‖z‖ := by rw [← hre]; exact Complex.re_le_norm _
  have himz : Real.pi * m * |t| ≤ ‖z‖ := by
    have h4 : |z.im| = 2 * Real.pi * (r * m) * |t| := by
      rw [him, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi * (r * m))]
    have h6 : Real.pi * m * |t| ≤ 2 * Real.pi * (r * m) * |t| := by
      have h7 := mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ r - 1 / 2)
        (mul_nonneg Real.pi_pos.le hm.le)) (abs_nonneg t)
      nlinarith
    calc Real.pi * m * |t| ≤ 2 * Real.pi * (r * m) * |t| := h6
      _ = |z.im| := h4.symm
      _ ≤ ‖z‖ := Complex.abs_im_le_norm _
  have hmin1 : min 1 (Real.pi * m) ≤ 1 := min_le_left _ _
  have hmin2 : min 1 (Real.pi * m) ≤ Real.pi * m := min_le_right _ _
  have h1r : 0 ≤ 1 - r := by linarith
  calc min 1 (Real.pi * m) / 2 * ((1 - r) + |t|)
      = (min 1 (Real.pi * m) * (1 - r) + min 1 (Real.pi * m) * |t|) / 2 := by ring
    _ ≤ ((1 - r) + Real.pi * m * |t|) / 2 := by
        have ha : min 1 (Real.pi * m) * (1 - r) ≤ 1 * (1 - r) :=
          mul_le_mul_of_nonneg_right hmin1 h1r
        have hb : min 1 (Real.pi * m) * |t| ≤ Real.pi * m * |t| :=
          mul_le_mul_of_nonneg_right hmin2 (abs_nonneg t)
        rw [one_mul] at ha
        linarith
    _ ≤ ‖z‖ := by linarith

/-- **The corrected resolvent is bounded near the origin, uniformly in `r`**
(`lem:uniform-pole-correction`, the small-frequency regime): for `1/2 ≤ r < 1`
and `|t| ≤ δ`,

`‖(1 - rχ(-2πt))⁻¹ - ((1-r) + 2π i r m̂ t)⁻¹‖ ≤ C`

with `δ, C` independent of `r`.

The two denominators differ by exactly `r q(t)`, where
`q(t) = 1 - χ(-2πt) - 2π i m̂ t` is the second-order remainder of the
characteristic function, so `‖q(t)‖ = O(t²)`; each denominator is
`≳ (1-r) + |t|` by the two lemmas above, so the quotient is
`≲ t²/((1-r)+|t|)² ≤ 1`. Note where the uniformity comes from: the `(1-r)` in the
lower bounds is *added* to `|t|`, never needed, and the `t²` in the numerator is
dominated by `|t|²` alone. -/
theorem exists_bound_pole_correction_near {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ) :
    ∃ δ > 0, ∃ C : ℝ, ∀ r : ℝ, 1 / 2 ≤ r → r < 1 → ∀ t : ℝ, |t| ≤ δ →
      ‖(1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹
        - (((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * (((r * (∫ x, x ∂μ)) : ℝ) : ℂ)
            * (t : ℂ) * Complex.I)⁻¹‖ ≤ C := by
  set m : ℝ := ∫ x, x ∂μ with hmdef
  obtain ⟨δ₁, hδ₁, K, hK, hq⟩ := exists_norm_one_sub_charFun_add_le hint
  obtain ⟨δ₂, hδ₂, hlow1⟩ := exists_le_norm_one_sub_smul_charFun hint hm
  set c₁ : ℝ := min 1 (m / 4) / 2 with hc₁def
  set c₂ : ℝ := min 1 (Real.pi * m) / 2 with hc₂def
  have hc₁ : 0 < c₁ := by
    rw [hc₁def]
    have h : 0 < min 1 (m / 4) := lt_min one_pos (by positivity)
    linarith
  have hc₂ : 0 < c₂ := by
    rw [hc₂def]
    have h : 0 < min 1 (Real.pi * m) := lt_min one_pos (by positivity)
    linarith
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  refine ⟨min δ₁ δ₂ / (2 * Real.pi), by positivity, 4 * Real.pi ^ 2 * K / (c₁ * c₂),
    fun r hr hr1 t ht => ?_⟩
  have hr0 : (0 : ℝ) ≤ r := by linarith
  set u : ℝ := -(2 * Real.pi * t) with hu_def
  have habsu : |u| = 2 * Real.pi * |t| := by
    rw [hu_def, abs_neg, abs_mul, abs_of_pos h2π]
  have hu : |u| ≤ min δ₁ δ₂ := by
    rw [habsu]
    calc 2 * Real.pi * |t| ≤ 2 * Real.pi * (min δ₁ δ₂ / (2 * Real.pi)) :=
          mul_le_mul_of_nonneg_left ht h2π.le
      _ = min δ₁ δ₂ := by field_simp
  have hu1 : |u| ≤ δ₁ := le_trans hu (min_le_left _ _)
  have hu2 : |u| ≤ δ₂ := le_trans hu (min_le_right _ _)
  set d₁ : ℂ := 1 - (r : ℂ) * charFun μ u with hd₁def
  set d₂ : ℂ := ((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ) * (t : ℂ) * Complex.I
    with hd₂def
  have hn1 : c₁ * ((1 - r) + |t|) ≤ ‖d₁‖ := by
    have habs : |t| ≤ |u| := by
      rw [habsu]; nlinarith [abs_nonneg t, Real.pi_gt_three]
    have hstep : c₁ * ((1 - r) + |t|) ≤ c₁ * ((1 - r) + |u|) :=
      mul_le_mul_of_nonneg_left (by linarith) hc₁.le
    exact le_trans hstep (hlow1 r hr hr1.le u hu2)
  have hn2 : c₂ * ((1 - r) + |t|) ≤ ‖d₂‖ := le_norm_model_denominator hm hr hr1.le t
  have hsum : 0 < (1 - r) + |t| := by
    have h0 : 0 < 1 - r := by linarith
    linarith [abs_nonneg t]
  have hd₁ne : d₁ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn1
    nlinarith
  have hd₂ne : d₂ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn2
    nlinarith
  have hdiff : d₂ - d₁ = -((r : ℂ) * (1 - charFun μ u + (m : ℂ) * (u : ℂ) * Complex.I)) := by
    rw [hd₁def, hd₂def, hu_def]
    push_cast
    ring
  have hnq : ‖d₂ - d₁‖ ≤ 4 * Real.pi ^ 2 * K * t ^ 2 := by
    rw [hdiff, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0]
    have h1 : ‖1 - charFun μ u + (m : ℂ) * (u : ℂ) * Complex.I‖ ≤ K * u ^ 2 := hq u hu1
    have h2 : u ^ 2 = 4 * Real.pi ^ 2 * t ^ 2 := by rw [hu_def]; ring
    calc r * ‖1 - charFun μ u + (m : ℂ) * (u : ℂ) * Complex.I‖
        ≤ 1 * (K * u ^ 2) := mul_le_mul hr1.le h1 (norm_nonneg _) zero_le_one
      _ = 4 * Real.pi ^ 2 * K * t ^ 2 := by rw [one_mul, h2]; ring
  have hprod : c₁ * c₂ * t ^ 2 ≤ ‖d₁ * d₂‖ := by
    rw [norm_mul]
    have hle : t ^ 2 ≤ ((1 - r) + |t|) ^ 2 := by
      calc t ^ 2 = |t| ^ 2 := (sq_abs t).symm
        _ ≤ ((1 - r) + |t|) ^ 2 := pow_le_pow_left₀ (abs_nonneg t) (by linarith) 2
    calc c₁ * c₂ * t ^ 2 ≤ c₁ * c₂ * ((1 - r) + |t|) ^ 2 :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = (c₁ * ((1 - r) + |t|)) * (c₂ * ((1 - r) + |t|)) := by ring
      _ ≤ ‖d₁‖ * ‖d₂‖ := mul_le_mul hn1 hn2 (by positivity) (norm_nonneg _)
  have hprodpos : 0 < ‖d₁ * d₂‖ := by
    rw [norm_mul]
    have h1 : 0 < ‖d₁‖ := by rw [norm_pos_iff]; exact hd₁ne
    have h2 : 0 < ‖d₂‖ := by rw [norm_pos_iff]; exact hd₂ne
    positivity
  rw [inv_sub_inv hd₁ne hd₂ne, norm_div, div_le_iff₀ hprodpos]
  calc ‖d₂ - d₁‖ ≤ 4 * Real.pi ^ 2 * K * t ^ 2 := hnq
    _ = 4 * Real.pi ^ 2 * K / (c₁ * c₂) * (c₁ * c₂ * t ^ 2) := by field_simp
    _ ≤ 4 * Real.pi ^ 2 * K / (c₁ * c₂) * ‖d₁ * d₂‖ :=
        mul_le_mul_of_nonneg_left hprod (by positivity)

/-- **Uniform pole correction** (`lem:uniform-pole-correction`,
`eq:uniform-correction-bound`): for every band `[-T,T]` there are `r₀ < 1` and
`C < ∞` with

`‖(1 - rχ(-2πt))⁻¹ - ((1-r) + 2π i r m̂ t)⁻¹‖ ≤ C`,  `r₀ ≤ r < 1`, `|t| ≤ T`.

Two regimes. Near the origin this is `exists_bound_pole_correction_near`. On the
compact annulus `δ ≤ |t| ≤ T` neither denominator is small: nonlatticeness gives
`‖1 - χ(-2πt)‖ ≥ c` there (`exists_pos_le_norm_one_sub_charFun`), and
`1 - rχ = (1 - χ) + (1-r)χ` with `‖χ‖ ≤ 1` costs at most `1 - r ≤ c/2` once
`r ≥ 1 - c/2`; the model denominator is bounded below by `c₂δ` by
`le_norm_model_denominator`. So each term is bounded separately there — no
cancellation is needed away from the origin.

This is the last `μ`-dependent estimate of the Abel route; everything downstream
(the reference kernel, general bandlimited kernels, the local bound) uses it as a
black box together with the model-pole limit
`tendsto_integral_fourier_model_pole`. -/
theorem exists_bound_pole_correction_uniform {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ) (T : ℝ) :
    ∃ r₀ : ℝ, 1 / 2 ≤ r₀ ∧ r₀ < 1 ∧ ∃ C : ℝ, ∀ r : ℝ, r₀ ≤ r → r < 1 → ∀ t : ℝ, |t| ≤ T →
      ‖(1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹
        - (((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * (((r * (∫ x, x ∂μ)) : ℝ) : ℂ)
            * (t : ℂ) * Complex.I)⁻¹‖ ≤ C := by
  set m : ℝ := ∫ x, x ∂μ with hmdef
  obtain ⟨δ, hδ, C₁, hnear⟩ := exists_bound_pole_correction_near hint hm
  obtain ⟨c, hc, hann⟩ :=
    exists_pos_le_norm_one_sub_charFun hμ (show (0 : ℝ) < 2 * Real.pi * δ by positivity)
      (2 * Real.pi * T)
  set c₂ : ℝ := min 1 (Real.pi * m) / 2 with hc₂def
  have hc₂ : 0 < c₂ := by
    rw [hc₂def]
    have h : 0 < min 1 (Real.pi * m) := lt_min one_pos (by positivity)
    linarith
  have hcδ : (0 : ℝ) < c₂ * δ := by positivity
  refine ⟨max (1 / 2) (1 - c / 2), le_max_left _ _, max_lt (by norm_num) (by linarith),
    max C₁ (2 / c + 1 / (c₂ * δ)), fun r hr hr1 t ht => ?_⟩
  have hr12 : 1 / 2 ≤ r := le_trans (le_max_left _ _) hr
  by_cases hcase : |t| ≤ δ
  · exact le_trans (hnear r hr12 hr1 t hcase) (le_max_left _ _)
  · rw [not_le] at hcase
    have h1r : 1 - r ≤ c / 2 := by
      have h := le_trans (le_max_right _ _) hr
      linarith
    have h1r0 : (0 : ℝ) ≤ 1 - r := by linarith
    set u : ℝ := -(2 * Real.pi * t) with hu_def
    have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
    have habsu : |u| = 2 * Real.pi * |t| := by
      rw [hu_def, abs_neg, abs_mul, abs_of_pos h2π]
    have hcu : c ≤ ‖1 - charFun μ u‖ := by
      refine hann u ?_ ?_
      · rw [habsu]; exact mul_le_mul_of_nonneg_left ht h2π.le
      · rw [habsu]; exact mul_le_mul_of_nonneg_left hcase.le h2π.le
    set d₁ : ℂ := 1 - (r : ℂ) * charFun μ u with hd₁def
    set d₂ : ℂ := ((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ) * (t : ℂ) * Complex.I
      with hd₂def
    have hn1 : c / 2 ≤ ‖d₁‖ := by
      have hAB : (1 : ℂ) - charFun μ u = d₁ - ((1 - r : ℝ) : ℂ) * charFun μ u := by
        rw [hd₁def]; push_cast <;> ring
      have hnc : ‖((1 - r : ℝ) : ℂ) * charFun μ u‖ ≤ 1 - r := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h1r0]
        calc (1 - r) * ‖charFun μ u‖ ≤ (1 - r) * 1 :=
              mul_le_mul_of_nonneg_left (norm_charFun_le_one _) h1r0
          _ = 1 - r := mul_one _
      have h := norm_sub_le d₁ (((1 - r : ℝ) : ℂ) * charFun μ u)
      rw [← hAB] at h
      linarith
    have hn2 : c₂ * δ ≤ ‖d₂‖ := by
      have h := le_norm_model_denominator hm hr12 hr1.le t
      have hstep : c₂ * δ ≤ c₂ * ((1 - r) + |t|) :=
        mul_le_mul_of_nonneg_left (by linarith) hc₂.le
      exact le_trans hstep h
    have hb1 : ‖d₁⁻¹‖ ≤ 2 / c := by
      rw [norm_inv]
      have hval : (c / 2)⁻¹ = 2 / c := by field_simp
      rw [← hval]
      exact inv_anti₀ (by positivity) hn1
    have hb2 : ‖d₂⁻¹‖ ≤ 1 / (c₂ * δ) := by
      rw [norm_inv]
      have hval : (c₂ * δ)⁻¹ = 1 / (c₂ * δ) := by field_simp
      rw [← hval]
      exact inv_anti₀ hcδ hn2
    calc ‖d₁⁻¹ - d₂⁻¹‖ ≤ ‖d₁⁻¹‖ + ‖d₂⁻¹‖ := norm_sub_le _ _
      _ ≤ 2 / c + 1 / (c₂ * δ) := add_le_add hb1 hb2
      _ ≤ max C₁ (2 / c + 1 / (c₂ * δ)) := le_max_right _ _

/-- **The corrected resolvent converges pointwise off the origin**
(`eq:correction-pointwise-limit`): for `t ≠ 0`,

`D_r(t) ⟶ D₁(t) = (1 - χ(-2πt))⁻¹ - (2π i m̂ t)⁻¹`  as `r ↑ 1`.

Both `r = 1` denominators are nonzero — the first by nonlatticeness
(`charFun_ne_one_of_nonlattice`), the second because `m̂, t ≠ 0` — so this is just
continuity of `z ↦ z⁻¹` away from the origin, evaluated at `r = 1` and restricted
to the filter `𝓝[<] 1`. Together with the uniform bound
`exists_bound_pole_correction_uniform` this is what feeds dominated convergence in
`r` on the compact frequency band. -/
theorem tendsto_pole_correction {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : Nonlattice μ)
    (hm : 0 < ∫ x, x ∂μ) {t : ℝ} (ht : t ≠ 0) :
    Filter.Tendsto (fun r : ℝ => (1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹
        - (((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * (((r * (∫ x, x ∂μ)) : ℝ) : ℂ)
            * (t : ℂ) * Complex.I)⁻¹)
      (nhdsWithin 1 (Set.Iio 1))
      (nhds ((1 - charFun μ (-(2 * Real.pi * t)))⁻¹
        - (2 * (Real.pi : ℂ) * ((∫ x, x ∂μ : ℝ) : ℂ) * (t : ℂ) * Complex.I)⁻¹)) := by
  set m : ℝ := ∫ x, x ∂μ with hmdef
  have htne : -(2 * Real.pi * t) ≠ 0 := by simp [Real.pi_ne_zero, ht]
  have hd1 : (1 : ℂ) - charFun μ (-(2 * Real.pi * t)) ≠ 0 := by
    rw [sub_ne_zero]
    exact fun h => charFun_ne_one_of_nonlattice hμ htne h.symm
  have hd2 : 2 * (Real.pi : ℂ) * (m : ℂ) * (t : ℂ) * Complex.I ≠ 0 := by
    have h1 : (Real.pi : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
    have h2 : (m : ℂ) ≠ 0 := by simpa using hm.ne'
    have h3 : (t : ℂ) ≠ 0 := by simpa using ht
    simp [h1, h2, h3, Complex.I_ne_zero]
  have hcont : ContinuousAt (fun r : ℝ => (1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹
      - (((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ)
          * (t : ℂ) * Complex.I)⁻¹) 1 := by
    refine ContinuousAt.sub (ContinuousAt.inv₀ (by fun_prop) ?_)
      (ContinuousAt.inv₀ (by fun_prop) ?_)
    · simpa using hd1
    · push_cast
      simpa using hd2
  have h0 := hcont.tendsto
  have hval : (1 - ((1 : ℝ) : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹
      - ((((1 : ℝ) - (1 : ℝ) : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * (((1 : ℝ) * m : ℝ) : ℂ)
          * (t : ℂ) * Complex.I)⁻¹
      = (1 - charFun μ (-(2 * Real.pi * t)))⁻¹
        - (2 * (Real.pi : ℂ) * (m : ℂ) * (t : ℂ) * Complex.I)⁻¹ := by
    push_cast
    norm_num
  rw [hval] at h0
  exact h0.mono_left (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))

/-!
### Splitting the discounted resolvent

At *fixed* `r < 1` both denominators are bounded below by `1 - r` **everywhere** —
`‖1 - rχ‖ ≥ 1 - ‖rχ‖ ≥ 1 - r` and `‖(1-r) + 2π i r m̂ t‖ ≥ Re = 1 - r` — with no
hypothesis on `μ` and no appeal to the delicate small-`t` estimates. That crude
bound is all that is needed to make each of the three integrands below `L¹`
(dominated by `(1-r)⁻¹‖𝓕w‖`) and continuous, hence to split

`∫ 𝓕w e^{2πiyt}(1 - rχ(-2πt))⁻¹ dt = ∫ 𝓕w e^{2πiyt}D_r dt + M_r(y)`.

The uniform-in-`r` estimates of A-4g-4b are *not* used here; they are needed only
when `r ↑ 1`, where these bounds degenerate. -/

/-- `‖1 - rχ(u)‖ ≥ 1 - r`, for every frequency: the discounted denominator cannot
degenerate at fixed `r < 1`, because `‖χ‖ ≤ 1`. -/
theorem le_norm_one_sub_smul_charFun (μ : Measure ℝ) [IsProbabilityMeasure μ] {r : ℝ}
    (hr0 : 0 ≤ r) (u : ℝ) : 1 - r ≤ ‖1 - (r : ℂ) * charFun μ u‖ := by
  have h1 : ‖(r : ℂ) * charFun μ u‖ ≤ r := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0]
    calc r * ‖charFun μ u‖ ≤ r * 1 := mul_le_mul_of_nonneg_left (norm_charFun_le_one _) hr0
      _ = r := mul_one r
  have h2 := norm_sub_norm_le (1 : ℂ) ((r : ℂ) * charFun μ u)
  simp only [norm_one] at h2
  linarith

/-- `‖(1-r) + 2π i r m̂ t‖ ≥ 1 - r`, for every frequency: the real part *is*
`1 - r`. -/
theorem le_norm_model_denominator_re {m : ℝ} (r : ℝ) (t : ℝ) :
    1 - r ≤ ‖((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ) * (t : ℂ)
      * Complex.I‖ := by
  set z : ℂ := ((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ) * (t : ℂ) * Complex.I
    with hz
  have hre : z.re = 1 - r := by simp [hz]
  rw [← hre]
  exact Complex.re_le_norm _

/-- The discounted Parseval integrand is `L¹` at fixed `r < 1`, dominated by
`(1-r)⁻¹‖𝓕w‖`. -/
theorem integrable_fourier_mul_discounted_resolvent {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {w : ℝ → ℂ} (hw : Integrable w) (hFw : Integrable (𝓕 w)) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (y : ℝ) :
    Integrable (fun t : ℝ => 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
      * (1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹) := by
  have hFwc : Continuous (𝓕 w) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hw
  have h1r : (0 : ℝ) < 1 - r := by linarith
  have hne : ∀ t : ℝ, (1 : ℂ) - (r : ℂ) * charFun μ (-(2 * Real.pi * t)) ≠ 0 := by
    intro t h
    have hb := le_norm_one_sub_smul_charFun μ hr0 (-(2 * Real.pi * t))
    rw [h, norm_zero] at hb
    linarith
  have hexp : ∀ t : ℝ, ‖Complex.exp ((2 : ℂ) * Real.pi * t * y * Complex.I)‖ = 1 := by
    intro t
    have hcast : ((2 : ℂ) * Real.pi * t * y * Complex.I)
        = ((2 * Real.pi * t * y : ℝ) : ℂ) * Complex.I := by push_cast <;> ring
    rw [hcast, Complex.norm_exp_ofReal_mul_I]
  refine (hFw.norm.const_mul ((1 - r)⁻¹)).mono' ?_ (Filter.Eventually.of_forall fun t => ?_)
  · refine ((hFwc.mul (Complex.continuous_exp.comp (by fun_prop))).mul ?_).aestronglyMeasurable
    exact (continuous_const.sub (continuous_const.mul
      (continuous_charFun.comp (by fun_prop)))).inv₀ hne
  · rw [norm_mul, norm_mul, hexp t, mul_one, norm_inv]
    have hb : (‖(1 : ℂ) - (r : ℂ) * charFun μ (-(2 * Real.pi * t))‖)⁻¹ ≤ (1 - r)⁻¹ :=
      inv_anti₀ h1r (le_norm_one_sub_smul_charFun μ hr0 _)
    calc ‖𝓕 w t‖ * (‖(1 : ℂ) - (r : ℂ) * charFun μ (-(2 * Real.pi * t))‖)⁻¹
        ≤ ‖𝓕 w t‖ * (1 - r)⁻¹ := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ = (1 - r)⁻¹ * ‖𝓕 w t‖ := by ring

/-- The model-pole integrand is `L¹` at fixed `r < 1`, by the same domination.
No hypothesis on `μ` — indeed `μ` does not appear. -/
theorem integrable_fourier_mul_model_pole {w : ℝ → ℂ} (hw : Integrable w)
    (hFw : Integrable (𝓕 w)) {r : ℝ} (hr1 : r < 1) (m y : ℝ) :
    Integrable (fun t : ℝ => 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
      * (((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ) * (t : ℂ) * Complex.I)⁻¹) := by
  have hFwc : Continuous (𝓕 w) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hw
  have h1r : (0 : ℝ) < 1 - r := by linarith
  have hne : ∀ t : ℝ, ((1 - r : ℝ) : ℂ)
      + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ) * (t : ℂ) * Complex.I ≠ 0 := by
    intro t h
    have hb := le_norm_model_denominator_re (m := m) r t
    rw [h, norm_zero] at hb
    linarith
  have hexp : ∀ t : ℝ, ‖Complex.exp ((2 : ℂ) * Real.pi * t * y * Complex.I)‖ = 1 := by
    intro t
    have hcast : ((2 : ℂ) * Real.pi * t * y * Complex.I)
        = ((2 * Real.pi * t * y : ℝ) : ℂ) * Complex.I := by push_cast <;> ring
    rw [hcast, Complex.norm_exp_ofReal_mul_I]
  refine (hFw.norm.const_mul ((1 - r)⁻¹)).mono' ?_ (Filter.Eventually.of_forall fun t => ?_)
  · refine ((hFwc.mul (Complex.continuous_exp.comp (by fun_prop))).mul ?_).aestronglyMeasurable
    exact (by fun_prop : Continuous fun t : ℝ => ((1 - r : ℝ) : ℂ)
      + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ) * (t : ℂ) * Complex.I).inv₀ hne
  · rw [norm_mul, norm_mul, hexp t, mul_one, norm_inv]
    have hb : (‖((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ)
        * (t : ℂ) * Complex.I‖)⁻¹ ≤ (1 - r)⁻¹ :=
      inv_anti₀ h1r (le_norm_model_denominator_re r t)
    calc ‖𝓕 w t‖ * (‖((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ)
          * (t : ℂ) * Complex.I‖)⁻¹
        ≤ ‖𝓕 w t‖ * (1 - r)⁻¹ := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ = (1 - r)⁻¹ * ‖𝓕 w t‖ := by ring

/-- **The discounted resolvent integral splits** as corrected part plus model
pole: for `0 ≤ r < 1`,

`∫ 𝓕w e^{2πiyt}(1 - rχ(-2πt))⁻¹ = ∫ 𝓕w e^{2πiyt}D_r + ∫ 𝓕w e^{2πiyt}((1-r)+2πi r m̂ t)⁻¹`.

Pointwise this is `sub_add_cancel`; the content is the two integrability side
conditions above, which `integral_sub` consumes. The second term is evaluated in
closed form by `integral_fourier_model_pole_Iio`, and its `r ↑ 1` limit is
`tendsto_integral_fourier_model_pole`; the first term is what
`exists_bound_pole_correction_uniform` and `tendsto_pole_correction` control. -/
theorem integral_fourier_discounted_resolvent_eq_add {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {w : ℝ → ℂ} (hw : Integrable w) (hFw : Integrable (𝓕 w)) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (m y : ℝ) :
    ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
        * (1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹
      = (∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
          * ((1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹
            - (((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ)
                * (t : ℂ) * Complex.I)⁻¹))
        + ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
            * (((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ)
                * (t : ℂ) * Complex.I)⁻¹ := by
  have hA := integrable_fourier_mul_discounted_resolvent (μ := μ) hw hFw hr0 hr1 y
  have hB := integrable_fourier_mul_model_pole hw hFw hr1 m y
  have hpt : ∀ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
      * ((1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹
        - (((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ) * (t : ℂ) * Complex.I)⁻¹)
      = 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
          * (1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹
        - 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
          * (((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ)
              * (t : ℂ) * Complex.I)⁻¹ := by
    intro t; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_sub hA hB]
  ring

/-- The corrected integrand is `L¹` at fixed `r < 1`: the difference of the two
integrable pieces, re-associated. -/
theorem integrable_fourier_mul_pole_correction {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {w : ℝ → ℂ} (hw : Integrable w) (hFw : Integrable (𝓕 w)) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (m y : ℝ) :
    Integrable (fun t : ℝ => 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
      * ((1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹
        - (((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ)
            * (t : ℂ) * Complex.I)⁻¹)) := by
  have hA := integrable_fourier_mul_discounted_resolvent (μ := μ) hw hFw hr0 hr1 y
  have hB := integrable_fourier_mul_model_pole hw hFw hr1 m y
  refine (hA.sub hB).congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [Pi.sub_apply]
  ring

/-- **The corrected term passes to the limit `r ↑ 1`** for a bandlimited kernel:

`∫ 𝓕w e^{2πiyt}D_r(t) dt ⟶ ∫ 𝓕w e^{2πiyt}D₁(t) dt`.

Dominated convergence along `𝓝[<] 1`, with the two A-4g-4b/4d2 ingredients in
their intended roles: the **constant** dominator `|C|‖𝓕w‖` comes from the uniform
bound on the band `|t| ≤ T` (and the integrand vanishes off the band, where the
uniform bound says nothing), and the pointwise limit comes from
`tendsto_pole_correction`, valid off the single point `t = 0` — a null set, which
is all dominated convergence needs.

This is where bandlimitedness of `w` is genuinely used: without compact support of
`𝓕w` there is no band on which to apply the uniform bound. -/
theorem tendsto_integral_fourier_pole_correction {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ)
    {w : ℝ → ℂ} {T : ℝ} (hw : Integrable w) (hFw : Integrable (𝓕 w))
    (hT : ∀ t : ℝ, T < |t| → 𝓕 w t = 0) (y : ℝ) :
    Filter.Tendsto (fun r : ℝ => ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
        * ((1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹
          - (((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * (((r * (∫ x, x ∂μ)) : ℝ) : ℂ)
              * (t : ℂ) * Complex.I)⁻¹))
      (nhdsWithin 1 (Set.Iio 1))
      (nhds (∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
        * ((1 - charFun μ (-(2 * Real.pi * t)))⁻¹
          - (2 * (Real.pi : ℂ) * ((∫ x, x ∂μ : ℝ) : ℂ) * (t : ℂ) * Complex.I)⁻¹))) := by
  obtain ⟨r₀, hr₀half, hr₀one, C, hC⟩ := exists_bound_pole_correction_uniform hμ hint hm T
  have hev0 : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio (1 : ℝ)), r₀ ≤ r :=
    ((eventually_gt_nhds hr₀one).filter_mono nhdsWithin_le_nhds).mono fun r hr => hr.le
  have hev1 : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio (1 : ℝ)), r < 1 := eventually_mem_nhdsWithin
  have hevpos : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio (1 : ℝ)), 0 ≤ r :=
    ((eventually_gt_nhds (by linarith : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds).mono
      fun r hr => hr.le
  refine tendsto_integral_filter_of_dominated_convergence (fun t => |C| * ‖𝓕 w t‖) ?_ ?_
    (hFw.norm.const_mul _) ?_
  · filter_upwards [hevpos, hev1] with r hr0 hr1
    exact (integrable_fourier_mul_pole_correction (μ := μ) hw hFw hr0 hr1 _ y).1
  · filter_upwards [hev0, hev1] with r hr hr1
    refine Filter.Eventually.of_forall fun t => ?_
    by_cases hband : |t| ≤ T
    · have hb := hC r hr hr1 t hband
      have hexp : ‖Complex.exp ((2 : ℂ) * Real.pi * t * y * Complex.I)‖ = 1 := by
        have hcast : ((2 : ℂ) * Real.pi * t * y * Complex.I)
            = ((2 * Real.pi * t * y : ℝ) : ℂ) * Complex.I := by push_cast <;> ring
        rw [hcast, Complex.norm_exp_ofReal_mul_I]
      rw [norm_mul, norm_mul, hexp, mul_one]
      calc ‖𝓕 w t‖ * ‖(1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹
            - (((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * (((r * (∫ x, x ∂μ)) : ℝ) : ℂ)
                * (t : ℂ) * Complex.I)⁻¹‖
          ≤ ‖𝓕 w t‖ * |C| :=
            mul_le_mul_of_nonneg_left (hb.trans (le_abs_self C)) (norm_nonneg _)
        _ = |C| * ‖𝓕 w t‖ := by ring
    · rw [not_le] at hband
      rw [hT t hband]
      simp
  · have h0 : ∀ᵐ t : ℝ, t ≠ 0 := by simp [ae_iff]
    filter_upwards [h0] with t ht
    exact (tendsto_pole_correction hμ hm ht).const_mul _

/-!
### Abel's limit theorem for nonnegative series

The last step of the reference-kernel argument reads the *undiscounted* renewal
series off the discounted ones. For a **nonnegative** sequence this is elementary
and needs no Tauberian input: if `∑ₙ rⁿaₙ → L` as `r ↑ 1` then `a` is summable
with `∑ₙ aₙ = L`. One inequality compares each *finite* partial sum
`∑_{n<N} rⁿaₙ ≤ ∑ₙ rⁿaₙ` and lets `r ↑ 1` (the left side is a polynomial in `r`,
so continuous), giving `∑_{n<N} aₙ ≤ L` for every `N` and hence summability; the
other compares termwise `rⁿaₙ ≤ aₙ`.

Nonnegativity is exactly what the sinc-squared reference kernel supplies, and it
is why the plan insists on a nonnegative kernel here. Nothing in this subsection
is measure-theoretic; it is stated for a bare sequence.
-/

/-- **Abel's limit theorem for a nonnegative series.** If the discounted sums
`∑ₙ rⁿaₙ` converge to `L` as `r ↑ 1`, then `a` is summable and `∑ₙ aₙ = L`.

The summability hypothesis on each discounted series is genuinely needed: `a` may
grow, and summability of `∑ rⁿaₙ` for `r < 1` is what the renewal application
supplies (via the Chernoff bound / discounted Parseval), not something automatic. -/
theorem summable_and_tsum_eq_of_tendsto_tsum_pow_mul {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hsum : ∀ r : ℝ, 0 ≤ r → r < 1 → Summable fun n => r ^ n * a n)
    {L : ℝ} (hL : Filter.Tendsto (fun r : ℝ => ∑' n, r ^ n * a n)
      (nhdsWithin 1 (Set.Iio 1)) (nhds L)) :
    Summable a ∧ ∑' n, a n = L := by
  have hpos : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio (1 : ℝ)), 0 ≤ r :=
    ((eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds).mono
      fun r hr => hr.le
  have hlt : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio (1 : ℝ)), r < 1 := eventually_mem_nhdsWithin
  have hpartial : ∀ N : ℕ, ∑ n ∈ Finset.range N, a n ≤ L := by
    intro N
    have h1 : Filter.Tendsto (fun r : ℝ => ∑ n ∈ Finset.range N, r ^ n * a n)
        (nhdsWithin 1 (Set.Iio (1 : ℝ))) (nhds (∑ n ∈ Finset.range N, a n)) := by
      have hc : Continuous fun r : ℝ => ∑ n ∈ Finset.range N, r ^ n * a n := by fun_prop
      have h2 := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))
      simpa using h2
    refine le_of_tendsto_of_tendsto h1 hL ?_
    filter_upwards [hpos, hlt] with r hr0 hr1
    exact (hsum r hr0 hr1).sum_le_tsum _ (fun i _ => mul_nonneg (pow_nonneg hr0 i) (ha i))
  have hsa : Summable a := summable_of_sum_range_le ha hpartial
  refine ⟨hsa, le_antisymm (hsa.tsum_le_of_sum_range_le hpartial) ?_⟩
  refine le_of_tendsto hL ?_
  filter_upwards [hpos, hlt] with r hr0 hr1
  refine (hsum r hr0 hr1).tsum_le_tsum (fun n => ?_) hsa
  calc r ^ n * a n ≤ 1 * a n :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ hr0 hr1.le) (ha n)
    _ = a n := one_mul _

/-!
### The real bridge for a nonnegative kernel

Discounted Parseval is stated for `ℂ`-valued kernels, but Abel's limit theorem
above needs a *real nonnegative* sequence. For a real kernel `v ≥ 0` the two
descriptions differ only by `integral_ofReal` (which is unconditional, being the
`ℝ`-linear isometry `ofReal` commuted past a Bochner integral), so the discounted
smoothed renewal series is literally `ofReal` of a nonnegative real series.

Boundedness `v ≤ B` is assumed rather than derived. It gives both integrability of
`z ↦ v(y-z)` against each convolution power (a probability measure) and the
geometric domination `rⁿ∫v(y−z)dμ^{*n} ≤ B rⁿ` that makes each discounted series
summable — the hypothesis Abel's theorem needs and which is *not* automatic. For
the sinc-squared reference kernel it comes free from `sincSq_le`.
-/

/-- Each discounted smoothed renewal series is summable, for a bounded nonnegative
kernel: the terms are squeezed between `0` and `B rⁿ`. -/
theorem summable_pow_mul_integral_comp_sub {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {v : ℝ → ℝ} {B : ℝ} (hv0 : ∀ x, 0 ≤ v x) (hB : ∀ x, v x ≤ B) (hvc : Continuous v)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (y : ℝ) :
    Summable fun n => r ^ n * ∫ z, v (y - z) ∂(convPow μ n) := by
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (fun z : ℝ => v (y - z)) (convPow μ n) := fun n =>
    (hvc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hint : ∀ n : ℕ, Integrable (fun z : ℝ => v (y - z)) (convPow μ n) := by
    intro n
    refine (integrable_const B).mono' (hmeas n) (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_of_nonneg (hv0 _)]
    exact hB _
  have hle : ∀ n : ℕ, ∫ z, v (y - z) ∂(convPow μ n) ≤ B := by
    intro n
    have h1 := integral_mono (hint n) (integrable_const B) (fun z => hB (y - z))
    simpa using h1
  have hnn : ∀ n : ℕ, 0 ≤ ∫ z, v (y - z) ∂(convPow μ n) := fun n =>
    integral_nonneg fun z => hv0 _
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (pow_nonneg hr0 n) (hnn n)) (fun n => ?_)
    ((summable_geometric_of_lt_one hr0 hr1).mul_left B)
  calc r ^ n * ∫ z, v (y - z) ∂(convPow μ n) ≤ r ^ n * B :=
        mul_le_mul_of_nonneg_left (hle n) (pow_nonneg hr0 n)
    _ = B * r ^ n := by ring

/-- **Discounted Parseval for a real nonnegative kernel**: the discounted smoothed
renewal series is `ofReal` of a real series, and equals the resolvent integral.

This is the interface Abel's limit theorem consumes: the left-hand side is
`ofReal` of `∑ₙ rⁿaₙ` with `aₙ = ∫v(y−z)dμ^{*n} ≥ 0`, and the right-hand side is
what `integral_fourier_discounted_resolvent_eq_add`, A-4g-4d3 and
`tendsto_integral_fourier_model_pole` evaluate in the limit `r ↑ 1`. -/
theorem ofReal_tsum_pow_mul_integral_comp_sub_eq {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {v : ℝ → ℝ} {B : ℝ} (hv0 : ∀ x, 0 ≤ v x) (hB : ∀ x, v x ≤ B) (hvc : Continuous v)
    (hvi : Integrable v) (hFv : Integrable (𝓕 fun x => ((v x : ℝ) : ℂ)))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (y : ℝ) :
    ((∑' n, r ^ n * ∫ z, v (y - z) ∂(convPow μ n) : ℝ) : ℂ)
      = ∫ t : ℝ, 𝓕 (fun x => ((v x : ℝ) : ℂ)) t
          * Complex.exp (2 * Real.pi * t * y * Complex.I)
          * (1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹ := by
  have hwc : Continuous (fun x => ((v x : ℝ) : ℂ)) := Complex.continuous_ofReal.comp hvc
  have hwi : Integrable (fun x => ((v x : ℝ) : ℂ)) := hvi.ofReal
  have hsummable := summable_pow_mul_integral_comp_sub (μ := μ) hv0 hB hvc hr0 hr1 y
  have hpartial : ∀ N : ℕ,
      ∑ n ∈ Finset.range N, (r : ℂ) ^ n * ∫ z, ((v (y - z) : ℝ) : ℂ) ∂(convPow μ n)
      = ((∑ n ∈ Finset.range N, r ^ n * ∫ z, v (y - z) ∂(convPow μ n) : ℝ) : ℂ) := by
    intro N
    push_cast
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
    exact integral_ofReal
  have h1 := tendsto_sum_pow_integral_comp_sub (μ := μ) hwc hwi hFv hr0 hr1 y
  rw [funext hpartial] at h1
  have h2 : Filter.Tendsto
      (fun N : ℕ => ((∑ n ∈ Finset.range N, r ^ n * ∫ z, v (y - z) ∂(convPow μ n) : ℝ) : ℂ))
      Filter.atTop
      (nhds ((∑' n, r ^ n * ∫ z, v (y - z) ∂(convPow μ n) : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp hsummable.hasSum.tendsto_sum_nat
  exact tendsto_nhds_unique h2 h1

/-- **The undiscounted smoothed renewal series, evaluated** (the `r ↑ 1` half of
`prop:reference-kernel`). For a bounded nonnegative continuous bandlimited kernel
`v`, the series `∑ₙ ∫v(y−z)dμ^{*n}` converges, with

`∑ₙ ∫v(y−z)dμ^{*n} = Re ∫ 𝓕v(t)e^{2πiyt}D₁(t) dt + (∫_{-∞}^y v)/m̂`.

All the Abel machinery meets here: the discounted series is `ofReal` of a
nonnegative real series (A-4g-4d4b), it splits as corrected part plus model pole
(A-4g-4d1), the two pieces converge as `r ↑ 1` (A-4g-4d3 and
`tendsto_integral_fourier_model_pole`), and Abel's theorem (A-4g-4d4a) transfers
the limit to the undiscounted series. Real parts are taken at the very end, which
is legitimate without knowing a priori that the complex limit is real: `Re` is
continuous and `Re ∘ ofReal = id`.

`y` is still fixed. Letting `y → ∞` — where Riemann–Lebesgue kills the first term
and `∫_{-∞}^y v → ∫v`, leaving `(∫v)/m̂` — is the next unit and must not be
interchanged with the `r ↑ 1` limit taken here. -/
theorem summable_integral_comp_sub_and_tsum_eq {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ)
    {v : ℝ → ℝ} {B T : ℝ} (hv0 : ∀ x, 0 ≤ v x) (hB : ∀ x, v x ≤ B) (hvc : Continuous v)
    (hvi : Integrable v) (hFv : Integrable (𝓕 fun x => ((v x : ℝ) : ℂ)))
    (hT : ∀ t : ℝ, T < |t| → 𝓕 (fun x => ((v x : ℝ) : ℂ)) t = 0) (y : ℝ) :
    Summable (fun n => ∫ z, v (y - z) ∂(convPow μ n)) ∧
      ∑' n, ∫ z, v (y - z) ∂(convPow μ n)
        = (∫ t : ℝ, 𝓕 (fun x => ((v x : ℝ) : ℂ)) t
            * Complex.exp (2 * Real.pi * t * y * Complex.I)
            * ((1 - charFun μ (-(2 * Real.pi * t)))⁻¹
              - (2 * (Real.pi : ℂ) * ((∫ x, x ∂μ : ℝ) : ℂ) * (t : ℂ) * Complex.I)⁻¹)).re
          + (∫ x in Set.Iio y, v x) / (∫ x, x ∂μ) := by
  set m : ℝ := ∫ x, x ∂μ with hmdef
  set w : ℝ → ℂ := fun x => ((v x : ℝ) : ℂ) with hwdef
  have hwc : Continuous w := Complex.continuous_ofReal.comp hvc
  have hwi : Integrable w := hvi.ofReal
  have hpos : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio (1 : ℝ)), 0 ≤ r :=
    ((eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds).mono
      fun r hr => hr.le
  have hlt : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio (1 : ℝ)), r < 1 := eventually_mem_nhdsWithin
  have hlimC := (tendsto_integral_fourier_pole_correction hμ hint hm hwi hFv hT y).add
    (tendsto_integral_fourier_model_pole hwc hwi hFv hm y)
  have heq : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio (1 : ℝ)),
      ((∑' n, r ^ n * ∫ z, v (y - z) ∂(convPow μ n) : ℝ) : ℂ)
        = (∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
            * ((1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹
              - (((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ)
                  * (t : ℂ) * Complex.I)⁻¹))
          + ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
              * (((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ)
                  * (t : ℂ) * Complex.I)⁻¹ := by
    filter_upwards [hpos, hlt] with r hr0 hr1
    rw [ofReal_tsum_pow_mul_integral_comp_sub_eq hv0 hB hvc hvi hFv hr0 hr1 y,
      integral_fourier_discounted_resolvent_eq_add hwi hFv hr0 hr1 m y]
  have hlim : Filter.Tendsto
      (fun r : ℝ => ((∑' n, r ^ n * ∫ z, v (y - z) ∂(convPow μ n) : ℝ) : ℂ))
      (nhdsWithin 1 (Set.Iio (1 : ℝ))) (nhds _) := (Filter.tendsto_congr' heq).mpr hlimC
  have hlimR : Filter.Tendsto (fun r : ℝ => ∑' n, r ^ n * ∫ z, v (y - z) ∂(convPow μ n))
      (nhdsWithin 1 (Set.Iio (1 : ℝ))) (nhds _) :=
    ((Complex.continuous_re.tendsto _).comp hlim).congr fun r => by simp
  obtain ⟨hs, hval⟩ := summable_and_tsum_eq_of_tendsto_tsum_pow_mul
    (fun n => integral_nonneg fun z => hv0 _)
    (fun r hr0 hr1 => summable_pow_mul_integral_comp_sub (μ := μ) hv0 hB hvc hr0 hr1 y)
    hlimR
  refine ⟨hs, ?_⟩
  rw [hval]
  have hIio : (∫ x in Set.Iio y, w x) = ((∫ x in Set.Iio y, v x : ℝ) : ℂ) := integral_ofReal
  rw [Complex.add_re, hIio]
  congr 1
  simp
  ring

/-!
### The reference-kernel limit: the constant `1/m̂`

Letting `y → ∞` in `summable_integral_comp_sub_and_tsum_eq` finishes A-4g-4. The
corrected term is the Fourier transform of `t ↦ 𝓕v(t)D₁(t)` evaluated at `−y`, so
Riemann–Lebesgue sends it to `0`; the mass term `∫_{-∞}^y v` increases to `∫v`.
What is left is exactly `(∫v)/m̂`.
-/

/-- **Riemann–Lebesgue in this file's exponential convention**: for *any* `g`,

`∫ g(t)e^{2πity} dt ⟶ 0`  as `|y| → ∞`.

Generalizes `tendsto_integral_fourier_resolvent` away from the specific resolvent
integrand. Unconditional, because `Real.zero_at_infty_fourier` is: a
non-integrable integrand gives the junk value `0` at every frequency. -/
theorem tendsto_integral_mul_exp_cocompact (g : ℝ → ℂ) :
    Filter.Tendsto (fun y : ℝ => ∫ t : ℝ, g t * Complex.exp (2 * Real.pi * t * y * Complex.I))
      (Filter.cocompact ℝ) (nhds 0) := by
  have hrw : ∀ y : ℝ, (∫ t : ℝ, g t * Complex.exp (2 * Real.pi * t * y * Complex.I))
      = 𝓕 g (-y) := by
    intro y
    rw [Real.fourier_eq']
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [Real.inner_apply, smul_eq_mul]
    have hce : Complex.exp (((-2 * Real.pi * (t * -y) : ℝ) : ℂ) * Complex.I)
        = Complex.exp (2 * Real.pi * t * y * Complex.I) := by
      congr 1; push_cast <;> ring
    rw [hce]; ring
  have hneg : Filter.Tendsto (fun y : ℝ => -y) (Filter.cocompact ℝ) (Filter.cocompact ℝ) := by
    rw [cocompact_eq_atBot_atTop]
    exact Filter.tendsto_sup.2 ⟨Filter.tendsto_neg_atBot_atTop.mono_right le_sup_right,
      Filter.tendsto_neg_atTop_atBot.mono_right le_sup_left⟩
  simp only [hrw]
  exact (Real.zero_at_infty_fourier _).comp hneg

/-- **The reference-kernel renewal limit** (`prop:reference-kernel`; the
replacement for the old A-4g-4, and the step at which Blackwell's constant is
finally identified):

`∑ₙ ∫ v(y−z) μ^{*n}(dz) ⟶ (∫v)/m̂`  as `y → ∞`,

for every bounded nonnegative continuous bandlimited kernel `v`. Note this is
already more general than the note's proposition, which is stated for the
sinc-squared kernel: nothing beyond `v ≥ 0`, `v ≤ B`, continuity, `v, 𝓕v ∈ L¹` and
compact support of `𝓕v` is used.

The limit order is the one fixed in the proof note: `r ↑ 1` at fixed `y` happens
inside `summable_integral_comp_sub_and_tsum_eq`, and only here is `y → ∞` taken.
Interchanging them would produce `1/(2m̂)`. -/
theorem tendsto_tsum_integral_comp_sub {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ)
    {v : ℝ → ℝ} {B T : ℝ} (hv0 : ∀ x, 0 ≤ v x) (hB : ∀ x, v x ≤ B) (hvc : Continuous v)
    (hvi : Integrable v) (hFv : Integrable (𝓕 fun x => ((v x : ℝ) : ℂ)))
    (hT : ∀ t : ℝ, T < |t| → 𝓕 (fun x => ((v x : ℝ) : ℂ)) t = 0) :
    Filter.Tendsto (fun y : ℝ => ∑' n, ∫ z, v (y - z) ∂(convPow μ n)) Filter.atTop
      (nhds ((∫ x, v x) / (∫ x, x ∂μ))) := by
  set m : ℝ := ∫ x, x ∂μ with hmdef
  set w : ℝ → ℂ := fun x => ((v x : ℝ) : ℂ) with hwdef
  set D : ℝ → ℂ := fun t => (1 - charFun μ (-(2 * Real.pi * t)))⁻¹
    - (2 * (Real.pi : ℂ) * (m : ℂ) * (t : ℂ) * Complex.I)⁻¹ with hD
  have hRL : Filter.Tendsto (fun y : ℝ => (∫ t : ℝ, 𝓕 w t
      * Complex.exp (2 * Real.pi * t * y * Complex.I) * D t).re) Filter.atTop (nhds 0) := by
    have hshape : ∀ y : ℝ, (∫ t : ℝ, 𝓕 w t
        * Complex.exp (2 * Real.pi * t * y * Complex.I) * D t)
        = ∫ t : ℝ, (𝓕 w t * D t) * Complex.exp (2 * Real.pi * t * y * Complex.I) := by
      intro y
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      ring
    have h1 : Filter.Tendsto (fun y : ℝ => ∫ t : ℝ, 𝓕 w t
        * Complex.exp (2 * Real.pi * t * y * Complex.I) * D t) Filter.atTop (nhds 0) := by
      simp only [hshape]
      exact (tendsto_integral_mul_exp_cocompact (fun t => 𝓕 w t * D t)).mono_left
        (by rw [cocompact_eq_atBot_atTop]; exact le_sup_right)
    have h2 := (Complex.continuous_re.tendsto _).comp h1
    simp only [Complex.zero_re] at h2
    exact h2
  have hmass : Filter.Tendsto (fun y : ℝ => (∫ x in Set.Iio y, v x) / m) Filter.atTop
      (nhds ((∫ x, v x) / m)) := by
    have h := (aecover_Iio (l := Filter.atTop) (b := id)
      Filter.tendsto_id).integral_tendsto_of_countably_generated hvi
    exact h.div_const m
  have hsum := hRL.add hmass
  rw [zero_add] at hsum
  refine hsum.congr fun y => ?_
  exact ((summable_integral_comp_sub_and_tsum_eq hμ hint hm hv0 hB hvc hvi hFv hT y).2).symm

/-!
### Boundedness from an integrable transform

The signed case (A-4g-4e) subtracts a multiple of the reference kernel from the
target kernel, and to split the renewal series along that subtraction one needs
each smoothed integral to exist separately. Both kernels are bounded, so both are
integrable against every convolution power — and boundedness is not an extra
hypothesis: a continuous `w` with `w, 𝓕w ∈ L¹` is automatically bounded by
`‖𝓕w‖_{L¹}`, being the inverse transform of an `L¹` function.
-/

/-!
### Fourier linearity for kernel corrections

A-4g-4e replaces a signed kernel `w` by the difference `w − cκ` with
`c = (∫w)/(∫κ)`, so that the corrected kernel has total mass zero. Verifying that
its transform vanishes at the origin needs two elementary facts about `𝓕` that
Mathlib states only in the general `VectorFourier` form.

**API note.** `𝓕` is notation for `Real.fourierIntegral`, which is *definitionally*
but not *syntactically* `VectorFourier.fourierIntegral 𝐞 volume (innerₛₗ ℝ)`. So
`rw [VectorFourier.fourierIntegral_add …]` fails against a goal written with `𝓕`;
the lemma has to be instantiated into a `have` with an explicit `𝓕`-typed
statement (which elaborates up to defeq) and rewritten from there.
-/

/-- `𝓕 f 0 = ∫ f`: the transform at the origin is the total mass. This is what
turns the normalization `c = (∫w)/(∫κ)` into the vanishing `𝓕(w − cκ)(0) = 0`. -/
theorem fourier_zero_eq_integral (f : ℝ → ℂ) : 𝓕 f 0 = ∫ x : ℝ, f x := by
  rw [Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp

end Renewal

end AbsorptionCutoff
end

section
-- module Solutions.OAIQ247_JB.Supercritical_RenewalKernel
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

/-!
# The smoothing kernel of the renewal mini-library

Split out of `AbsorptionCutoff.Supercritical.Renewal` purely for build time: these are
finished, computation-heavy proofs (`sincSq_le` and `triangle_eq` carry the
expensive `nlinarith`/interval work) that the in-progress Blackwell argument only
consumes, never edits. This module depends on nothing else in `AbsorptionCutoff`.

Blackwell's theorem is proved by testing the renewal measure against a kernel `w`
whose Fourier transform has **compact support** — that is what makes the
Riemann-Lebesgue step legitimate without any decay assumption on `charFun` at
infinity, which nonlatticeness alone does not provide.

The kernel is built from the unit box `1_{[-1,1]}`: its Fourier transform is the
sinc function, so the *square* of that transform is nonnegative and is itself the
Fourier transform of the triangle `1_{[-1,1]} * 1_{[-1,1]}`, supported in
`[-2,2]`. Mathlib has the convolution theorem (`fourier_mul_convolution_eq`) but
no Fourier transform of an indicator, so the closed forms are computed here.
-/

open MeasureTheory
open scoped Convolution FourierTransform

namespace AbsorptionCutoff

namespace Renewal

/-! ### Dilation

Mathlib has no dilation rule for `𝓕`, and the d.R.i. approximation argument needs
one: the approximate identity is a *rescaled* smoothing kernel, and the whole
point of rescaling is that the band `supp 𝓕` scales the other way. -/

lemma integrable_unitBox : Integrable unitBox := by
  rw [unitBox]
  refine (integrable_indicator_iff measurableSet_Icc).2 ?_
  exact integrableOn_const (by simp) |>.mono_set (le_refl _)

/-- **The Fourier transform of the unit box is the sinc function**,
`𝓕 1_{[-1,1]}(t) = sin (2πt) / (πt)`.

In particular it is real-valued, so its square — the kernel used below — is
nonnegative. -/
theorem fourier_unitBox {t : ℝ} (ht : t ≠ 0) :
    𝓕 unitBox t = ((Real.sin (2 * Real.pi * t) / (Real.pi * t) : ℝ) : ℂ) := by
  have hstep : 𝓕 unitBox t
      = ∫ x in (-1 : ℝ)..1,
          Complex.exp ((((-2 * Real.pi * t : ℝ)) : ℂ) * Complex.I * x) := by
    rw [Real.fourier_eq']
    simp only [Real.inner_apply, unitBox]
    have hpt : ∀ v : ℝ,
        Complex.exp ((-2 * Real.pi * (v * t) : ℝ) * Complex.I) •
            Set.indicator (Set.Icc (-1 : ℝ) 1) (fun _ => (1 : ℂ)) v
          = Set.indicator (Set.Icc (-1 : ℝ) 1)
              (fun x : ℝ =>
                Complex.exp ((((-2 * Real.pi * t : ℝ)) : ℂ) * Complex.I * x)) v := by
      intro v
      by_cases hv : v ∈ Set.Icc (-1 : ℝ) 1
      · simp only [Set.indicator_of_mem hv, smul_eq_mul, mul_one]
        congr 1
        push_cast
        ring
      · simp [Set.indicator_of_notMem hv]
    simp only [hpt]
    rw [MeasureTheory.integral_indicator measurableSet_Icc,
      intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hc : (((-2 * Real.pi * t : ℝ)) : ℂ) * Complex.I ≠ 0 := by
    refine mul_ne_zero ?_ Complex.I_ne_zero
    simpa using ht
  rw [hstep, integral_exp_mul_complex hc]
  set z : ℂ := ((2 * Real.pi * t : ℝ) : ℂ) with hz
  have h2 : ((-2 * Real.pi * t : ℝ) : ℂ) * Complex.I * ((1 : ℝ) : ℂ) = -z * Complex.I := by
    rw [hz]; push_cast <;> ring
  have h3 : ((-2 * Real.pi * t : ℝ) : ℂ) * Complex.I * ((-1 : ℝ) : ℂ) = z * Complex.I := by
    rw [hz]; push_cast <;> ring
  rw [h2, h3]
  -- `e^{-izθ} - e^{izθ} = -2i sin θ`
  have hA : Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)
      = 2 * Complex.sin z * (-Complex.I) := by
    have h := Complex.two_sin z
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination Complex.I * h
      + (Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)) * hI
  rw [hA, hz, ← Complex.ofReal_sin]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  push_cast
  field_simp

/-- The removable singularity of `fourier_unitBox` at the origin: the transform
takes the value `|[-1,1]| = 2` there. -/
theorem fourier_unitBox_zero : 𝓕 unitBox 0 = 2 := by
  rw [Real.fourier_eq', unitBox]
  simp only [Real.inner_apply, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    one_smul, mul_zero]
  rw [MeasureTheory.integral_indicator measurableSet_Icc]
  simp
  norm_num

open scoped Convolution

lemma integrable_triangle : Integrable triangle :=
  integrable_unitBox.integrable_convolution _ integrable_unitBox

/-- The convolution theorem for the triangle: `𝓕(1_{[-1,1]} ⋆ 1_{[-1,1]}) = (𝓕 1_{[-1,1]})²`. -/
lemma fourier_triangle (t : ℝ) : 𝓕 triangle t = (𝓕 unitBox t) ^ 2 := by
  rw [triangle, Real.fourier_mul_convolution_eq integrable_unitBox integrable_unitBox, sq]

lemma sincSq_nonneg (t : ℝ) : 0 ≤ sincSq t := by
  unfold sincSq; split <;> positivity

/-- The kernel is exactly the Fourier transform of the triangle. -/
lemma ofReal_sincSq (t : ℝ) : ((sincSq t : ℝ) : ℂ) = 𝓕 triangle t := by
  rw [fourier_triangle]
  unfold sincSq
  split
  · subst ‹t = 0›
    rw [fourier_unitBox_zero]
    norm_num
  · rw [fourier_unitBox ‹t ≠ 0›]
    push_cast
    ring

lemma continuous_fourier_triangle : Continuous (𝓕 triangle) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ integrable_triangle

lemma continuous_sincSq : Continuous sincSq := by
  have h : sincSq = fun t => (𝓕 triangle t).re := by
    funext t; rw [← ofReal_sincSq]; simp
  rw [h]
  exact Complex.continuous_re.comp continuous_fourier_triangle

lemma support_unitBox : Function.support unitBox = Set.Icc (-1 : ℝ) 1 := by
  rw [unitBox]
  ext x
  by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1 <;> simp [Function.mem_support, hx]

lemma support_triangle_subset : Function.support triangle ⊆ Set.Icc (-2 : ℝ) 2 := by
  refine (support_convolution_subset (ContinuousLinearMap.mul ℂ ℂ) (f := unitBox)
    (g := unitBox) (μ := volume)).trans ?_
  rw [support_unitBox, Set.Icc_add_Icc (by norm_num) (by norm_num)]
  norm_num

/-- The kernel is dominated by a multiple of the Cauchy density: `|sin| ≤ |·|`
near the origin gives the bound `4`, and `|sin| ≤ 1` gives `(πt)^{-2}` away from
it. This is what makes it integrable. -/
lemma sincSq_le (t : ℝ) : sincSq t ≤ 8 * (1 + t ^ 2)⁻¹ := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi2 : (2 : ℝ) ≤ Real.pi := Real.two_le_pi
  have hden : (0 : ℝ) < 1 + t ^ 2 := by positivity
  unfold sincSq
  split
  · subst ‹t = 0›
    norm_num
  · rename_i ht
    have ht2 : (0 : ℝ) < (Real.pi * t) ^ 2 := by positivity
    by_cases h : t ^ 2 ≤ 1
    · have h1 : (Real.sin (2 * Real.pi * t)) ^ 2 ≤ (2 * Real.pi * t) ^ 2 := by
        have := Real.abs_sin_le_abs (x := 2 * Real.pi * t)
        nlinarith [abs_nonneg (Real.sin (2 * Real.pi * t)), abs_nonneg (2 * Real.pi * t),
          sq_abs (Real.sin (2 * Real.pi * t)), sq_abs (2 * Real.pi * t)]
      have h2 : (Real.sin (2 * Real.pi * t) / (Real.pi * t)) ^ 2 ≤ 4 := by
        rw [div_pow, div_le_iff₀ ht2]
        nlinarith
      have h3 : (4 : ℝ) ≤ 8 * (1 + t ^ 2)⁻¹ := by
        rw [le_mul_inv_iff₀ hden]
        nlinarith
      linarith
    · have h' : 1 < t ^ 2 := by simpa using lt_of_not_ge h
      have h1 : (Real.sin (2 * Real.pi * t)) ^ 2 ≤ 1 := by
        have := Real.abs_sin_le_one (2 * Real.pi * t)
        nlinarith [sq_abs (Real.sin (2 * Real.pi * t)), abs_nonneg (Real.sin (2 * Real.pi * t))]
      have h2 : (Real.sin (2 * Real.pi * t) / (Real.pi * t)) ^ 2 ≤ ((Real.pi * t) ^ 2)⁻¹ := by
        rw [div_pow, div_eq_mul_inv]
        exact mul_le_of_le_one_left (by positivity) h1
      have h3 : ((Real.pi * t) ^ 2)⁻¹ ≤ 8 * (1 + t ^ 2)⁻¹ := by
        rw [inv_le_iff_one_le_mul₀ ht2]
        have hinv : (0 : ℝ) < (1 + t ^ 2)⁻¹ := inv_pos.mpr hden
        have hkey : (1 + t ^ 2) ≤ 8 * (Real.pi * t) ^ 2 := by
          have hpisq : (4 : ℝ) ≤ Real.pi ^ 2 := by nlinarith
          have hexp : (Real.pi * t) ^ 2 = Real.pi ^ 2 * t ^ 2 := by ring
          rw [hexp]
          nlinarith [sq_nonneg t]
        calc (1 : ℝ) = (1 + t ^ 2) * (1 + t ^ 2)⁻¹ := by field_simp
          _ ≤ (8 * (Real.pi * t) ^ 2) * (1 + t ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right hkey hinv.le
          _ = 8 * (1 + t ^ 2)⁻¹ * (Real.pi * t) ^ 2 := by ring
      linarith

lemma integrable_sincSq : Integrable sincSq := by
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul 8)
    continuous_sincSq.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_of_nonneg (sincSq_nonneg t)]
  exact sincSq_le t

/-- Integrability of `𝓕 triangle`, the hypothesis Fourier inversion needs. -/
lemma integrable_fourier_triangle : Integrable (𝓕 triangle) := by
  have h : (𝓕 triangle) = fun t => ((sincSq t : ℝ) : ℂ) := by
    funext t; rw [ofReal_sincSq]
  rw [h]
  exact integrable_sincSq.ofReal

/-- **The triangle in closed form**: `(1_{[-1,1]} ⋆ 1_{[-1,1]})(x) = (2 - |x|)⁺`.

Needed because Fourier inversion is applied *at* the triangle, and its hypothesis
is continuity there. Mathlib's continuity lemmas for convolutions
(`HasCompactSupport.continuous_convolution_left/right`,
`BddAbove.continuous_convolution_right_of_integrable`) all require one factor to
be *continuous*, which the box is not — so the closed form is computed instead.
The integrand is the indicator of `[-1,1] ∩ [x-1,x+1] = [max(-1,x-1), min(1,x+1)]`,
whose length is `2 - |x|` when positive. -/
theorem triangle_eq (x : ℝ) : triangle x = ((max (2 - |x|) 0 : ℝ) : ℂ) := by
  have hpt : ∀ t : ℝ, (ContinuousLinearMap.mul ℂ ℂ) (unitBox t) (unitBox (x - t))
      = Set.indicator (Set.Icc (max (-1) (x - 1)) (min 1 (x + 1))) (fun _ => (1 : ℂ)) t := by
    intro t
    by_cases h : t ∈ Set.Icc (max (-1 : ℝ) (x - 1)) (min 1 (x + 1))
    · have hmem := h
      simp only [Set.mem_Icc, max_le_iff, le_min_iff] at h
      have h1 : t ∈ Set.Icc (-1 : ℝ) 1 := ⟨h.1.1, h.2.1⟩
      have h2 : x - t ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [h.2.2], by linarith [h.1.2]⟩
      rw [Set.indicator_of_mem hmem]
      simp [unitBox, Set.indicator_of_mem h1, Set.indicator_of_mem h2]
    · rw [Set.indicator_of_notMem h]
      by_cases h1 : t ∈ Set.Icc (-1 : ℝ) 1
      · by_cases h2 : x - t ∈ Set.Icc (-1 : ℝ) 1
        · simp only [Set.mem_Icc] at h1 h2
          exact absurd (⟨by simp only [max_le_iff]; constructor <;> linarith [h1.1, h2.2],
            by simp only [le_min_iff]; constructor <;> linarith [h1.2, h2.1]⟩ :
              t ∈ Set.Icc (max (-1 : ℝ) (x - 1)) (min 1 (x + 1))) h
        · simp [unitBox, Set.indicator_of_notMem h2]
      · simp [unitBox, Set.indicator_of_notMem h1]
  rw [triangle, convolution]
  simp only [hpt]
  rw [MeasureTheory.integral_indicator measurableSet_Icc, MeasureTheory.setIntegral_const,
    Real.volume_real_Icc, Complex.real_smul, mul_one]
  congr 2
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx, min_eq_left (by linarith), max_eq_right (by linarith)]
    ring
  · rw [abs_of_nonpos hx, min_eq_right (by linarith), max_eq_left (by linarith)]
    ring

lemma continuous_triangle : Continuous triangle := by
  have h : triangle = fun x => ((max (2 - |x|) 0 : ℝ) : ℂ) := funext triangle_eq
  rw [h]
  fun_prop

/-- **The Fourier transform of the kernel is the reflected triangle**, hence
compactly supported (`support_triangle_subset`). This is the property that makes
the Riemann–Lebesgue step of Blackwell's theorem work: the `t`-integral in the
Parseval atom `integral_comp_sub_eq_integral_charFun` runs over a compact set,
where `1 - charFun μ` is bounded away from `0` off the origin
(`charFun_ne_one_of_nonlattice` plus continuity). -/
theorem fourier_fourier_triangle (x : ℝ) : 𝓕 (𝓕 triangle) x = triangle (-x) := by
  have h : 𝓕⁻ (𝓕 triangle) (-x) = triangle (-x) :=
    integrable_triangle.fourierInv_fourier_eq integrable_fourier_triangle
      continuous_triangle.continuousAt
  rw [Real.fourierInv_eq_fourier_neg] at h
  simpa using h

/-- The same statement with the kernel written as the real-valued `sincSq`, the
form `integral_comp_sub_eq_integral_charFun` consumes. -/
theorem fourier_ofReal_sincSq (x : ℝ) :
    𝓕 (fun t : ℝ => ((sincSq t : ℝ) : ℂ)) x = triangle (-x) := by
  have h : (fun t : ℝ => ((sincSq t : ℝ) : ℂ)) = 𝓕 triangle := by
    funext t; rw [ofReal_sincSq]
  rw [h, fourier_fourier_triangle]

/-- The kernel is bounded below on a neighbourhood of the origin — all that the
domination step `A-4e` needs, and cheaper than any explicit sinc inequality:
it follows from continuity and `sincSq 0 = 4`. -/
lemma exists_pos_le_sincSq : ∃ δ > 0, ∀ t ∈ Set.Icc (-δ) δ, 2 ≤ sincSq t := by
  have h : ∀ᶠ t in nhds (0 : ℝ), 2 < sincSq t := by
    refine continuous_sincSq.continuousAt.eventually_const_lt ?_
    rw [sincSq_zero]; norm_num
  rw [Metric.eventually_nhds_iff] at h
  obtain ⟨ε, hε, hball⟩ := h
  refine ⟨ε / 2, by linarith, fun t ht => ?_⟩
  have hd : dist t 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_lt]
    constructor <;> [linarith [ht.1]; linarith [ht.2]]
  exact (hball hd).le

end Renewal

end AbsorptionCutoff
end

section
-- module Solutions.OAIQ247_JB.Supercritical_RenewalSinc
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

/-!
# The renewal limit at the sinc-squared kernel

`AbsorptionCutoff.Supercritical.RenewalAbel` proves the renewal limit for an *abstract*
reference kernel, because it is a pure-Mathlib leaf and cannot name a concrete
witness. This module is the meeting point: it imports the kernel constructions of
`AbsorptionCutoff.Supercritical.RenewalKernel` and discharges every abstract hypothesis at
`Renewal.sincSq`.

## Main results

* `Renewal.integral_sincSq`: `∫ sincSq = 2`, read off `𝓕(sincSq) = triangle(−·)`
  at the origin.
* `Renewal.tendsto_tsum_integral_comp_sub_sincSq`: `∑ₙ ∫ sincSq(y−z) μ^{*n}(dz) ⟶ 2/m̂`.
* `Renewal.tendsto_of_tendsto_sum_integral_comp_sub_sincSq`: the same limit for a
  general bandlimited kernel, with `sincSq` supplying the reference kernel.
* `Renewal.exists_bound_renewalMeasure_Icc_of_expTransform`: the two-sided uniform
  cell bound `U([y, y+ℓ]) ≤ C` for *all* `y`, combining the `atTop` bound above
  with the Chernoff left-tail bound of `AbsorptionCutoff.Supercritical.Renewal`.

The bandlimited-approximation machinery built on top of these — the rescaled
approximate identity and the smoothing `w ⋆ K_a` — lives in the continuation
module `AbsorptionCutoff.Supercritical.RenewalApprox`.
-/

open MeasureTheory
open scoped Convolution ENNReal NNReal FourierTransform

namespace AbsorptionCutoff

namespace Renewal

/-! ### Discharging the abstract reference-kernel hypotheses at `sincSq` -/

/-- The kernel is bounded by `8`. Coarser than `sincSq_le`, and all the renewal
argument needs: boundedness is used only to dominate `rⁿ∫sincSq(y−z)dμ^{*n}` by
`8rⁿ`. -/
lemma sincSq_le_eight (t : ℝ) : sincSq t ≤ 8 := by
  have h1 : sincSq t ≤ 8 * (1 + t ^ 2)⁻¹ := sincSq_le t
  have h2 : (1 + t ^ 2)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity)]
    nlinarith [sq_nonneg t]
  calc sincSq t ≤ 8 * (1 + t ^ 2)⁻¹ := h1
    _ ≤ 8 * 1 := by gcongr
    _ = 8 := by ring

/-- `𝓕(sincSq)` is integrable: it *is* the reflected triangle, which is
integrable. -/
lemma integrable_fourier_ofReal_sincSq :
    Integrable (𝓕 fun t : ℝ => ((sincSq t : ℝ) : ℂ)) := by
  have h : (𝓕 fun t : ℝ => ((sincSq t : ℝ) : ℂ)) = fun x : ℝ => triangle (-x) :=
    funext fourier_ofReal_sincSq
  rw [h]
  exact integrable_triangle.comp_neg

/-- `𝓕(sincSq)` is supported in `[-2,2]`: bandlimitedness of the reference
kernel, from `support_triangle_subset`. -/
lemma fourier_ofReal_sincSq_eq_zero {t : ℝ} (ht : 2 < |t|) :
    𝓕 (fun x : ℝ => ((sincSq x : ℝ) : ℂ)) t = 0 := by
  rw [fourier_ofReal_sincSq]
  by_contra h
  have hmem : (-t) ∈ Function.support triangle := h
  have h2 := support_triangle_subset hmem
  rw [Set.mem_Icc] at h2
  have habs : |t| ≤ 2 := abs_le.2 ⟨by linarith [h2.2], by linarith [h2.1]⟩
  linarith

/-- **`∫ sincSq = 2`.** The transform at the origin is the total mass
(`fourier_zero_eq_integral`), and `𝓕(sincSq)(0) = triangle 0 = 2`. In particular
the reference kernel has *positive* mass, which is what makes the normalization
`c = (∫w)/(∫κ)` legitimate. -/
theorem integral_sincSq : ∫ x : ℝ, sincSq x = 2 := by
  have h1 : (∫ x : ℝ, ((sincSq x : ℝ) : ℂ)) = triangle 0 := by
    rw [← fourier_zero_eq_integral, fourier_ofReal_sincSq]
    norm_num
  rw [triangle_eq] at h1
  norm_num at h1
  have h2 : ((∫ x : ℝ, sincSq x : ℝ) : ℂ) = (2 : ℂ) := by
    rw [← h1]
    exact integral_ofReal.symm
  exact_mod_cast h2

/-! ### The concrete renewal limits -/

/-- **The reference-kernel renewal limit at `sincSq`**:
`∑ₙ ∫ sincSq(y−z) μ^{*n}(dz) ⟶ 2/m̂` as `y → ∞`. -/
theorem tendsto_tsum_integral_comp_sub_sincSq {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ) :
    Filter.Tendsto (fun y : ℝ => ∑' n, ∫ z, sincSq (y - z) ∂(convPow μ n)) Filter.atTop
      (nhds (2 / (∫ x, x ∂μ))) := by
  have h := tendsto_tsum_integral_comp_sub (B := 8) (T := 2) hμ hint hm sincSq_nonneg
    sincSq_le_eight continuous_sincSq integrable_sincSq integrable_fourier_ofReal_sincSq
    (fun _ ht => fourier_ofReal_sincSq_eq_zero ht)
  rwa [integral_sincSq] at h

/-- The smoothed renewal series at `sincSq` is summable at every `y`. -/
lemma summable_integral_comp_sub_sincSq {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ) (y : ℝ) :
    Summable fun n => ∫ z, sincSq (y - z) ∂(convPow μ n) :=
  (summable_integral_comp_sub_and_tsum_eq (B := 8) (T := 2) hμ hint hm sincSq_nonneg
    sincSq_le_eight continuous_sincSq integrable_sincSq integrable_fourier_ofReal_sincSq
    (fun _ ht => fourier_ofReal_sincSq_eq_zero ht) y).1

/-- **The uniform local renewal bound, on a fixed short interval** (A-4e): there
are `δ > 0` and `C < ∞` with

`U([y−δ, y+δ]) ≤ C`  for all large `y`.

Two ingredients meet: `renewalMeasure_le_ofReal_tsum_integral` turns the lower
bound `2 ≤ sincSq` on `[-δ,δ]` into `U([y−δ,y+δ]) ≤ (smoothed series)/2`, and
`tendsto_tsum_integral_comp_sub_sincSq` says the smoothed series converges, hence
is eventually bounded.

**The bound is stated on `atTop`, not for all `y ∈ ℝ`, and that is not an
artefact.** A limit at `+∞` says nothing about the left tail, and under these
hypotheses — nonlattice, `MemLp id 2 μ`, positive drift — nothing bounds `U` near
`−∞`. Getting a genuinely global bound would need a finite exponential moment
(A-2's Chernoff estimate `renewalMeasure_lt_top_of_expTransform_lt_one`), which the
chapter's *tilted* law has but a general nonlattice law does not; it would
therefore have to be added to the hypotheses. The `atTop` form is what a directly
Riemann integrable tail estimate needs. -/
theorem exists_bound_renewalMeasure_Icc_atTop {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ) :
    ∃ δ > 0, ∃ C : ℝ, ∀ᶠ y : ℝ in Filter.atTop,
      renewalMeasure μ (Set.Icc (y - δ) (y + δ)) ≤ ENNReal.ofReal C := by
  obtain ⟨δ, hδ, hδle⟩ := exists_pos_le_sincSq
  refine ⟨δ, hδ, (2 / (∫ x, x ∂μ) + 1) / 2, ?_⟩
  have hev : ∀ᶠ y : ℝ in Filter.atTop,
      (∑' n, ∫ z, sincSq (y - z) ∂(convPow μ n)) ≤ 2 / (∫ x, x ∂μ) + 1 :=
    (tendsto_tsum_integral_comp_sub_sincSq hμ hint hm).eventually_le_const (by linarith)
  filter_upwards [hev] with y hy
  calc renewalMeasure μ (Set.Icc (y - δ) (y + δ))
      ≤ ENNReal.ofReal ((∑' n, ∫ z, sincSq (y - z) ∂(convPow μ n)) / 2) := by
        refine renewalMeasure_le_ofReal_tsum_integral sincSq_nonneg continuous_sincSq
          sincSq_le_eight measurableSet_Icc two_pos (fun z hz => ?_)
          (summable_integral_comp_sub_sincSq hμ hint hm y)
        refine hδle _ ?_
        rw [Set.mem_Icc] at hz ⊢
        constructor <;> linarith [hz.1, hz.2]
    _ ≤ ENNReal.ofReal ((2 / (∫ x, x ∂μ) + 1) / 2) := by
        refine ENNReal.ofReal_le_ofReal ?_
        linarith

/-- **The uniform local renewal bound at any fixed length** (A-4e): for every
`ℓ`, there is `C < ∞` with `U([y, y+ℓ]) ≤ C` for all large `y`.

The short interval of `exists_bound_renewalMeasure_Icc_atTop` has a length `2δ`
fixed by the kernel, so intervals of a prescribed length are covered by finitely
many translates and the bounds added. The cover is built by induction on the number
of cells using `Set.Icc_union_Icc_eq_Icc`, which is cheaper than a floor-function
argument; each cell's bound is the short-interval bound translated along
`y ↦ y + (2kδ + δ)`, a map tending to `atTop`, so all the cells' bounds hold
eventually together.

Rescaling the kernel to cover `[y, y+ℓ]` in one step would instead require a
scaling lemma for the whole package — band, mass and boundedness all change — so
the finite cover is the cheaper route. As in the short-interval version, the bound
is on `atTop` only. -/
theorem exists_bound_renewalMeasure_Icc_atTop_of_length {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ)
    (ℓ : ℝ) :
    ∃ C : ℝ, ∀ᶠ y : ℝ in Filter.atTop,
      renewalMeasure μ (Set.Icc y (y + ℓ)) ≤ ENNReal.ofReal C := by
  obtain ⟨δ, hδ, C₀, hC₀⟩ := exists_bound_renewalMeasure_Icc_atTop hμ hint hm
  set D : ℝ := max C₀ 0 with hDdef
  have hD0 : 0 ≤ D := le_max_right _ _
  have hCD : ∀ᶠ y : ℝ in Filter.atTop,
      renewalMeasure μ (Set.Icc (y - δ) (y + δ)) ≤ ENNReal.ofReal D := by
    filter_upwards [hC₀] with y hy
    exact hy.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  -- the bound on a union of `K` cells, by induction on `K`
  have key : ∀ K : ℕ, ∀ᶠ y : ℝ in Filter.atTop,
      renewalMeasure μ (Set.Icc y (y + 2 * (K : ℝ) * δ))
        ≤ ENNReal.ofReal (((K : ℝ) + 1) * D) := by
    intro K
    induction K with
    | zero =>
        filter_upwards [hCD] with y hy
        have hsub : Set.Icc y (y + 2 * ((0 : ℕ) : ℝ) * δ) ⊆ Set.Icc (y - δ) (y + δ) := by
          intro x hx
          rw [Set.mem_Icc] at hx ⊢
          norm_num at hx
          constructor <;> [linarith [hx.1]; linarith [hx.2]]
        refine (measure_mono hsub).trans (hy.trans (ENNReal.ofReal_le_ofReal ?_))
        push_cast
        linarith
    | succ K ih =>
        have hshift : ∀ᶠ y : ℝ in Filter.atTop,
            renewalMeasure μ (Set.Icc (y + 2 * (K : ℝ) * δ) (y + 2 * ((K : ℝ) + 1) * δ))
              ≤ ENNReal.ofReal D := by
          have h := (Filter.tendsto_atTop_add_const_right Filter.atTop
            (2 * (K : ℝ) * δ + δ) Filter.tendsto_id).eventually hCD
          filter_upwards [h] with y hy
          simp only [id_eq] at hy
          have he1 : y + (2 * (K : ℝ) * δ + δ) - δ = y + 2 * (K : ℝ) * δ := by ring
          have he2 : y + (2 * (K : ℝ) * δ + δ) + δ = y + 2 * ((K : ℝ) + 1) * δ := by ring
          rwa [he1, he2] at hy
        filter_upwards [ih, hshift] with y h1 h2
        have hsplit : Set.Icc y (y + 2 * ((K : ℕ) + 1 : ℝ) * δ)
            = Set.Icc y (y + 2 * (K : ℝ) * δ)
              ∪ Set.Icc (y + 2 * (K : ℝ) * δ) (y + 2 * ((K : ℝ) + 1) * δ) := by
          rw [Set.Icc_union_Icc_eq_Icc] <;> nlinarith [Nat.cast_nonneg (α := ℝ) K]
        have hcast : ((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1 := by push_cast <;> ring
        rw [hcast, hsplit]
        calc renewalMeasure μ (Set.Icc y (y + 2 * (K : ℝ) * δ)
              ∪ Set.Icc (y + 2 * (K : ℝ) * δ) (y + 2 * ((K : ℝ) + 1) * δ))
            ≤ renewalMeasure μ (Set.Icc y (y + 2 * (K : ℝ) * δ))
              + renewalMeasure μ (Set.Icc (y + 2 * (K : ℝ) * δ)
                  (y + 2 * ((K : ℝ) + 1) * δ)) := measure_union_le _ _
          _ ≤ ENNReal.ofReal (((K : ℝ) + 1) * D) + ENNReal.ofReal D := add_le_add h1 h2
          _ = ENNReal.ofReal (((K : ℝ) + 1) * D + D) :=
              (ENNReal.ofReal_add (by positivity) hD0).symm
          _ = ENNReal.ofReal ((((K : ℝ) + 1) + 1) * D) := by ring_nf
  -- choose enough cells to cover an interval of length `ℓ`
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ℓ ≤ 2 * (K : ℝ) * δ := by
    refine ⟨⌈ℓ / (2 * δ)⌉₊, ?_⟩
    have h1 : ℓ / (2 * δ) ≤ (⌈ℓ / (2 * δ)⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (0 : ℝ) < 2 * δ := by linarith
    rw [div_le_iff₀ h2] at h1
    linarith
  refine ⟨((K : ℝ) + 1) * D, ?_⟩
  filter_upwards [key K] with y hy
  refine le_trans (measure_mono ?_) hy
  exact Set.Icc_subset_Icc le_rfl (by linarith)

/-- **The two-sided uniform cell bound** (A-4e′): under a finite exponential
moment, `U([y, y+ℓ]) ≤ C` for **every** `y ∈ ℝ`, not just for large `y`.

The two tails are bounded by completely different arguments, and this is the point
of the statement: on the right, `exists_bound_renewalMeasure_Icc_atTop_of_length`
— an Abel/Fourier renewal estimate, which needs `μ` nonlattice with a second
moment and positive drift; on the left, the Chernoff bound
`renewalMeasure_le_of_expTransform`, which needs `∫e^{-θz}dμ < 1` at some `θ > 0`
and gives the *monotone* bound `e^{θb}(1-λ)⁻¹` on all of `(-∞, b]` at once. Since
the eventual bound holds past some `y₀`, the whole left part `y ≤ y₀` is a single
half-line and one Chernoff constant covers it.

The exponential-moment hypothesis is essential and cannot be dropped: with only
nonlattice + `MemLp id 2 μ` there is nothing to bound `U` near `−∞`. The chapter
supplies it, since the increment law is the Cramér tilt. -/
theorem exists_bound_renewalMeasure_Icc_of_expTransform {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ)
    {θ : ℝ} (hθ : 0 < θ) (hlt : expTransform θ μ < 1) (ℓ : ℝ) :
    ∃ C : ℝ, ∀ y : ℝ, renewalMeasure μ (Set.Icc y (y + ℓ)) ≤ ENNReal.ofReal C := by
  obtain ⟨C₁, hC₁⟩ := exists_bound_renewalMeasure_Icc_atTop_of_length hμ hint hm ℓ
  obtain ⟨y₀, hy₀⟩ := Filter.eventually_atTop.1 hC₁
  -- the left half-line `(-∞, b]`, covered in one shot by the Chernoff bound
  set b : ℝ := y₀ + max ℓ 0 with hbdef
  set E : ℝ≥0∞ := ENNReal.ofReal (Real.exp (θ * b)) * (1 - expTransform θ μ)⁻¹ with hEdef
  have hEfin : E ≠ ∞ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.inv_lt_top.2 (tsub_pos_of_lt hlt))).ne
  refine ⟨max C₁ E.toReal, fun y => ?_⟩
  rcases le_or_gt y₀ y with hy | hy
  · exact (hy₀ y hy).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  · have hsub : Set.Icc y (y + ℓ) ⊆ Set.Iic b := by
      intro x hx
      have := hx.2
      simp only [Set.mem_Iic, hbdef]
      have hℓ : ℓ ≤ max ℓ 0 := le_max_left _ _
      linarith [hy.le]
    calc renewalMeasure μ (Set.Icc y (y + ℓ)) ≤ E :=
          renewalMeasure_le_of_expTransform hθ measurableSet_Icc hsub
      _ = ENNReal.ofReal E.toReal := (ENNReal.ofReal_toReal hEfin).symm
      _ ≤ ENNReal.ofReal (max C₁ E.toReal) := ENNReal.ofReal_le_ofReal (le_max_right _ _)

end Renewal

end AbsorptionCutoff
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

namespace NumberTheoryLean.CycleCostAtomless

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures KernelDensityBridge
open PairedCostProcess CostReturnLaw MinorizingCostRegularity

theorem positive_second_cost_level_null (T y : ℝ) :
    ((volume : Measure ℝ).prod volume) {x : ℝ × ℝ | 0 < x.2 ∧ T + cost x.1 + cost x.2 = y} = 0 := by
  have hA : MeasurableSet {x : ℝ × ℝ | 0 < x.2 ∧ T + cost x.1 + cost x.2 = y} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_eq_fun ((measurable_const.add (cost_measurable.comp measurable_fst)).add
        (cost_measurable.comp measurable_snd)) measurable_const)
  rw [Measure.prod_apply hA]
  apply lintegral_eq_zero_of_ae_eq_zero
  apply Eventually.of_forall
  intro t
  apply Set.Subsingleton.measure_zero
  intro u hu v hv
  have hu0 : 0 < u := hu.1
  have hv0 : 0 < v := hv.1
  have huEq : T + cost t + cost u = y := hu.2
  have hvEq : T + cost t + cost v = y := hv.2
  exact cost_strictAntiOn.injOn hu0 hv0 (by linarith)

theorem oddTwoStep_second_positive (s : OddState) : ∀ᵐ x ∂oddTwoStep s, 0 < x.2 := by
  have hm : Measurable (fun x : EvenState × OddState => (x.1.1, x.2.1)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk (measurable_subtype_coe.comp measurable_snd)
  rw [oddTwoStep, Kernel.map_apply _ hm]
  apply (ae_map_iff hm.aemeasurable (measurableSet_lt measurable_const measurable_snd)).mpr
  exact Eventually.of_forall (fun x => by change 0 < x.2.1; linarith [x.2.2])

theorem oddTwoStep_cost_level (s : OddState) (T y : ℝ) :
    oddTwoStep s {x : ℝ × ℝ | T + cost x.1 + cost x.2 = y} = 0 := by
  have heq : {x : ℝ × ℝ | T + cost x.1 + cost x.2 = y} =ᵐ[oddTwoStep s]
      {x : ℝ × ℝ | 0 < x.2 ∧ T + cost x.1 + cost x.2 = y} := by
    filter_upwards [oddTwoStep_second_positive s] with x hx
    exact propext ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩
  rw [measure_congr heq, oddTwoStep_eq_withDensity]
  exact withDensity_absolutelyContinuous _ _ (positive_second_cost_level_null T y)

theorem pairedCost_cost_level (z : OddCost) (y : ℝ) :
    pairedCostKernel z {w : OddCost | w.2 = y} = 0 := by
  have hm : Measurable (fun x : EvenState × OddState => (x.1.1, x.2.1)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk (measurable_subtype_coe.comp measurable_snd)
  have hB : MeasurableSet {x : ℝ × ℝ | z.2 + cost x.1 + cost x.2 = y} :=
    measurableSet_eq_fun ((measurable_const.add (cost_measurable.comp measurable_fst)).add
      (cost_measurable.comp measurable_snd)) measurable_const
  have h := oddTwoStep_cost_level z.1 z.2 y
  rw [oddTwoStep, Kernel.map_apply _ hm, Measure.map_apply hm hB] at h
  rw [pairedCostKernel_apply z (measurableSet_eq_fun measurable_snd measurable_const)]
  exact h

theorem captured_cost_level (z : OddCost) (y : ℝ) : costCaptured z {w : OddCost | w.2 = y} = 0 := by
  rw [costCaptured, Kernel.restrict_apply' _ _ _ (measurableSet_eq_fun measurable_snd measurable_const)]
  exact measure_mono_null inter_subset_left (pairedCost_cost_level z y)

theorem firstReturn_cost_level (n : ℕ) (z : OddCost) (y : ℝ) :
    firstReturn n z {w : OddCost | w.2 = y} = 0 := by
  rw [firstReturn, Kernel.comp_apply' _ _ _ (measurableSet_eq_fun measurable_snd measurable_const)]
  simp only [captured_cost_level, lintegral_zero]

theorem returnLaw_cost_level (z : OddCost) (y : ℝ) : returnLaw z {w : OddCost | w.2 = y} = 0 := by
  rw [returnLaw, Kernel.sum_apply' _ _ (measurableSet_eq_fun measurable_snd measurable_const)]
  simp only [firstReturn_cost_level, tsum_zero]

instance cycleCostLaw_nullSingletonClass : NullSingletonClass cycleCostLaw := by
  constructor
  intro y
  rw [cycleCostLaw, Measure.map_apply measurable_snd (measurableSet_singleton y)]
  exact returnLaw_cost_level (RegenerationTails.regenerationState, 0) y

theorem cycleCostLaw_countable_null {C : Set ℝ} (hC : C.Countable) : cycleCostLaw C = 0 :=
  hC.measure_zero _

theorem cycleCostLaw_lattice_null (a r : ℝ) :
    cycleCostLaw {x : ℝ | ∃ k : ℤ, x = a + k * r} = 0 := by
  apply cycleCostLaw_countable_null
  apply (countable_range (fun k : ℤ => a + k * r)).mono
  intro x hx
  obtain ⟨k, hk⟩ := hx
  exact ⟨k, hk.symm⟩

end NumberTheoryLean.CycleCostAtomless

end

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

namespace NumberTheoryLean.CycleRegeneration

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels PairedCostProcess CostReturnLaw RegenerationTails

theorem costKilled_regeneration (s : OddState) (hs : s.1 ≤ 3) (T : ℝ) :
    costKilled (s, T) = costKilled (regenerationState, T) := by
  rw [costKilled, Kernel.restrict_apply, Kernel.restrict_apply, pairedCost_regeneration s hs T]

theorem costCaptured_regeneration (s : OddState) (hs : s.1 ≤ 3) (T : ℝ) :
    costCaptured (s, T) = costCaptured (regenerationState, T) := by
  rw [costCaptured, Kernel.restrict_apply, Kernel.restrict_apply, pairedCost_regeneration s hs T]

theorem firstReturn_regeneration (n : ℕ) (s : OddState) (hs : s.1 ≤ 3) (T : ℝ) :
    firstReturn n (s, T) = firstReturn n (regenerationState, T) := by
  cases n with
  | zero =>
    change (costCaptured ∘ₖ (Kernel.id : Kernel OddCost OddCost)) (s, T) =
      (costCaptured ∘ₖ (Kernel.id : Kernel OddCost OddCost)) (regenerationState, T)
    rw [Kernel.comp_id]
    exact costCaptured_regeneration s hs T
  | succ n =>
    have hp : costKilled ^ (n + 1) = (costKilled ^ n) ∘ₖ costKilled := pow_succ costKilled n
    have hq : (costKilled ^ (n + 1)) (s, T) = (costKilled ^ (n + 1)) (regenerationState, T) := by
      rw [hp, Kernel.comp_apply, Kernel.comp_apply, costKilled_regeneration s hs T]
    rw [firstReturn, Kernel.comp_apply, Kernel.comp_apply, hq]

theorem returnLaw_regeneration (s : OddState) (hs : s.1 ≤ 3) (T : ℝ) :
    returnLaw (s, T) = returnLaw (regenerationState, T) := by
  ext B hB
  rw [returnLaw, Kernel.sum_apply' _ _ hB, Kernel.sum_apply' _ _ hB]
  apply tsum_congr
  intro n
  rw [firstReturn_regeneration n s hs T]

theorem costKilled_translation (z : OddCost) (a : ℝ) :
    (costKilled z).map (shiftCost a) = costKilled (shiftCost a z) := by
  rw [costKilled, Kernel.restrict_apply, Kernel.restrict_apply]
  calc
    _ = ((pairedCostKernel z).map (shiftCost a)).restrict returnSetᶜ :=
      (Measure.restrict_map (shiftCost_measurable a) returnSet_measurable.compl).symm
    _ = _ := by rw [pairedCost_translation]; rfl

theorem costCaptured_translation (z : OddCost) (a : ℝ) :
    (costCaptured z).map (shiftCost a) = costCaptured (shiftCost a z) := by
  rw [costCaptured, Kernel.restrict_apply, Kernel.restrict_apply]
  calc
    _ = ((pairedCostKernel z).map (shiftCost a)).restrict returnSet :=
      (Measure.restrict_map (shiftCost_measurable a) returnSet_measurable).symm
    _ = _ := by rw [pairedCost_translation]; rfl

theorem shift_commutes_killed (a : ℝ) : Commute (shiftKernel a) costKilled := by
  change shiftKernel a ∘ₖ costKilled = costKilled ∘ₖ shiftKernel a
  rw [shiftKernel, Kernel.deterministic_comp_eq_map, Kernel.comp_deterministic_eq_comap]
  ext z : 1
  rw [Kernel.map_apply _ (shiftCost_measurable a), Kernel.comap_apply]
  exact costKilled_translation z a

theorem shift_commutes_captured (a : ℝ) : Commute (shiftKernel a) costCaptured := by
  change shiftKernel a ∘ₖ costCaptured = costCaptured ∘ₖ shiftKernel a
  rw [shiftKernel, Kernel.deterministic_comp_eq_map, Kernel.comp_deterministic_eq_comap]
  ext z : 1
  rw [Kernel.map_apply _ (shiftCost_measurable a), Kernel.comap_apply]
  exact costCaptured_translation z a

theorem shift_commutes_firstReturn (a : ℝ) (n : ℕ) : Commute (shiftKernel a) (firstReturn n) :=
  (shift_commutes_captured a).mul_right ((shift_commutes_killed a).pow_right n)

theorem shift_commutes_returnLaw (a : ℝ) : Commute (shiftKernel a) returnLaw := by
  change shiftKernel a ∘ₖ returnLaw = returnLaw ∘ₖ shiftKernel a
  rw [returnLaw, Kernel.comp_sum_right, Kernel.comp_sum_left]
  apply congrArg Kernel.sum
  funext n
  exact (shift_commutes_firstReturn a n).eq

theorem returnLaw_translation (z : OddCost) (a : ℝ) :
    (returnLaw z).map (shiftCost a) = returnLaw (shiftCost a z) := by
  have h := (shift_commutes_returnLaw a).eq
  change shiftKernel a ∘ₖ returnLaw = returnLaw ∘ₖ shiftKernel a at h
  rw [shiftKernel, Kernel.deterministic_comp_eq_map, Kernel.comp_deterministic_eq_comap] at h
  have hz := congrArg (fun K : Kernel OddCost OddCost => K z) h
  rwa [Kernel.map_apply _ (shiftCost_measurable a), Kernel.comap_apply] at hz

theorem return_increment_law (s : OddState) (hs : s.1 ≤ 3) (T : ℝ) :
    (returnLaw (s, T)).map (shiftCost (-T)) = cycleJointLaw := by
  rw [returnLaw_regeneration s hs T]
  have ht := returnLaw_translation (regenerationState, 0) T
  have hz : shiftCost T (regenerationState, 0) = (regenerationState, T) := by simp [shiftCost]
  rw [hz] at ht
  rw [← ht, Measure.map_map (shiftCost_measurable (-T)) (shiftCost_measurable T)]
  have heq : shiftCost (-T) ∘ shiftCost T = id := by
    funext z
    ext <;> simp [shiftCost, Function.comp_apply, add_assoc]
  rw [heq, Measure.map_id]
  rfl

theorem returnLaw_ae_regeneration (z : OddCost) : ∀ᵐ y ∂returnLaw z, y ∈ returnSet := by
  apply ae_iff.mpr
  exact returnLaw_off_returnSet z

theorem cycle_increment_integral (z : OddCost) (hz : z ∈ returnSet)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y, F (y.2 - z.2) ∂returnLaw z) = ∫⁻ G, F G ∂cycleCostLaw := by
  have h := congrArg (fun μ : Measure OddCost => ∫⁻ y, F y.2 ∂μ) (return_increment_law z.1 hz z.2)
  rw [lintegral_map (f := fun y : OddCost => F y.2) (hF.comp measurable_snd) (shiftCost_measurable (-z.2))] at h
  rw [cycleCostLaw, lintegral_map hF measurable_snd]
  simpa only [shiftCost, sub_eq_add_neg, cycleJointLaw] using h

end NumberTheoryLean.CycleRegeneration

end

section

namespace NumberTheoryLean.MarkedCycleLaw

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open PairedCostProcess CostReturnLaw CycleRegeneration

theorem markReturn_measurable (n : ℕ) : Measurable (markReturn n) :=
  measurable_const.prodMk measurable_id

instance firstMarkedReturn_isFiniteKernel (n : ℕ) : IsFiniteKernel (firstMarkedReturn n) := by
  unfold firstMarkedReturn
  first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply markReturn_measurable <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance markedReturnLaw_isMarkovKernel : IsMarkovKernel markedReturnLaw := by
  constructor
  intro z
  constructor
  rw [markedReturnLaw, Kernel.sum_apply' _ _ MeasurableSet.univ]
  have heq : ∀ n, firstMarkedReturn n z univ = firstReturn n z univ := by
    intro n
    rw [firstMarkedReturn, Kernel.map_apply' _ (markReturn_measurable n) _ MeasurableSet.univ, preimage_univ]
  simp_rw [heq]
  rw [← Kernel.sum_apply' firstReturn z MeasurableSet.univ]
  change returnLaw z univ = 1
  exact measure_univ

theorem markedReturnLaw_forget (z : OddCost) : (markedReturnLaw z).map Prod.snd = returnLaw z := by
  ext B hB
  rw [Measure.map_apply measurable_snd hB, markedReturnLaw,
    Kernel.sum_apply' _ _ (measurable_snd hB), returnLaw, Kernel.sum_apply' _ _ hB]
  apply tsum_congr
  intro n
  rw [firstMarkedReturn, Kernel.map_apply' _ (markReturn_measurable n) _ (measurable_snd hB)]
  rfl

instance markedCycleLaw_isProbabilityMeasure : IsProbabilityMeasure markedCycleLaw := by
  unfold markedCycleLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem markedCycleLaw_cost_projection :
    markedCycleLaw.map (fun x => x.2.2) = cycleCostLaw := by
  have h := markedReturnLaw_forget (RegenerationTails.regenerationState, 0)
  change markedCycleLaw.map Prod.snd = returnLaw (RegenerationTails.regenerationState, 0) at h
  rw [cycleCostLaw, ← h, Measure.map_map measurable_snd measurable_snd]
  rfl

end NumberTheoryLean.MarkedCycleLaw

end

section

namespace NumberTheoryLean.CycleDurationMoments

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open TransitionKernels PairedHitting PairedDrift PairedBlockContraction PairedCostProcess
open CostReturnLaw MarkedCycleLaw

instance durationFrom_isProbabilityMeasure (z : OddCost) : IsProbabilityMeasure (durationFrom z) :=
  (Measure.isProbabilityMeasure_map_iff (μ := markedReturnLaw z)
    measurable_fst.aemeasurable).mpr inferInstance

theorem durationFrom_lintegral (z : OddCost) (H : ℕ → ℝ≥0∞) :
    (∫⁻ n, H n ∂durationFrom z) = ∑' n : ℕ, H (2 * (n + 1)) * firstReturn n z univ := by
  have hH : Measurable H := measurable_of_countable H
  rw [durationFrom, lintegral_map hH measurable_fst, markedReturnLaw, Kernel.sum_apply, lintegral_sum_measure]
  apply tsum_congr
  intro n
  rw [firstMarkedReturn, Kernel.map_apply _ (markReturn_measurable n),
    lintegral_map (f := fun x : MarkedReturn => H x.1) (hH.comp measurable_fst) (markReturn_measurable n)]
  change (∫⁻ _y, H (2 * (n + 1)) ∂firstReturn n z) = _
  rw [lintegral_const]

theorem firstReturn_geometric : ∃ m : ℕ, 0 < m ∧ ∃ ρ D : ℝ, 0 < ρ ∧ ρ < 1 ∧ 0 < D ∧
    ∀ n : ℕ, ∀ z : OddCost, firstReturn n z univ ≤ ENNReal.ofReal (ρ ^ (n / m) * (V z.1 + D)) := by
  obtain ⟨m, hm, ρ, D, hρ, hρ1, hD, hb⟩ := paired_survival_geometric
  refine ⟨m, hm, ρ, D, hρ, hρ1, hD, ?_⟩
  intro n z
  calc
    _ ≤ firstReturn n z univ + (costKilled ^ (n + 1)) z univ := le_add_of_nonneg_right zero_le
    _ = (costKilled ^ n) z univ := return_mass_step n z
    _ = (pairedKilled ^ n) z.1 univ := costKilled_mass n z
    _ ≤ (pairedKilled ^ (m * (n / m))) z.1 univ := paired_survival_antitone z.1 (Nat.mul_div_le n m)
    _ ≤ _ := hb (n / m) z.1

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

theorem return_duration_exponential_moment : ∃ θ : ℝ, 0 < θ ∧ ∀ z : OddCost,
    (∫⁻ n, ENNReal.ofReal (Real.exp (θ * (n : ℝ))) ∂durationFrom z) < ∞ := by
  obtain ⟨m, hm, ρ, D, hρ, hρ1, hD, hb⟩ := firstReturn_geometric
  let θ := -Real.log ρ / (4 * (m : ℝ))
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hθ : 0 < θ := div_pos (neg_pos.mpr (Real.log_neg hρ hρ1)) (by positivity)
  have hrel : 4 * (m : ℝ) * θ = -Real.log ρ := by dsimp [θ]; field_simp
  refine ⟨θ, hθ, ?_⟩
  intro z
  let A := Real.exp (-Real.log ρ + 2 * θ) * (V z.1 + D)
  let r := Real.exp (-2 * θ)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hsum : Summable (fun n : ℕ => A * r ^ n) := (summable_geometric_of_lt_one hr0 hr1).mul_left A
  rw [durationFrom_lintegral]
  apply lt_of_le_of_lt (ENNReal.tsum_le_tsum ?_) hsum.tsum_ofReal_lt_top
  intro n
  have hW : 0 < V z.1 + D := add_pos (V_pos z.1) hD
  have hn := weighted_geometric_bound hm hρ hθ hrel n
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  calc
    _ ≤ ENNReal.ofReal (Real.exp (θ * (2 * ((n : ℝ) + 1)))) *
        ENNReal.ofReal (ρ ^ (n / m) * (V z.1 + D)) := mul_le_mul le_rfl (hb n z) zero_le zero_le
    _ = ENNReal.ofReal ((Real.exp (θ * (2 * ((n : ℝ) + 1)))) * ρ ^ (n / m) * (V z.1 + D)) := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (A * r ^ n) := ENNReal.ofReal_le_ofReal (by
      dsimp [A, r]
      nlinarith [mul_le_mul_of_nonneg_right hn hW.le])

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

theorem captured_cost_upper (z : OddCost) :
    ∀ᵐ y ∂costCaptured z, y.2 ≤ z.2 + 2 * Real.log 3 := ae_restrict_of_ae (pairedCost_cost_upper z)

theorem firstReturn_cost_upper (n : ℕ) (z : OddCost) :
    ∀ᵐ y ∂firstReturn n z, y.2 ≤ z.2 + 2 * ((n + 1 : ℕ) : ℝ) * Real.log 3 := by
  rw [firstReturn]
  apply Kernel.ae_comp_of_ae_ae (measurableSet_le measurable_snd measurable_const)
  filter_upwards [costKilled_pow_cost_upper n z] with y hy
  filter_upwards [captured_cost_upper y] with w hw
  push_cast
  nlinarith

theorem markedReturn_cost_upper (z : OddCost) :
    ∀ᵐ x ∂markedReturnLaw z, x.2.2 ≤ z.2 + (x.1 : ℝ) * Real.log 3 := by
  rw [markedReturnLaw, Kernel.sum_apply, Measure.ae_sum_iff]
  intro n
  rw [firstMarkedReturn, Kernel.map_apply _ (markReturn_measurable n)]
  have hm : Measurable (fun x : MarkedReturn => z.2 + (x.1 : ℝ) * Real.log 3) :=
    measurable_const.add (((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp measurable_fst).mul measurable_const)
  apply (ae_map_iff (markReturn_measurable n).aemeasurable
    (measurableSet_le (measurable_snd.comp measurable_snd) hm)).mpr
  filter_upwards [firstReturn_cost_upper n z] with x hx
  change x.2 ≤ z.2 + ((2 * (n + 1) : ℕ) : ℝ) * Real.log 3
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hx

theorem markedCycle_cost_upper : ∀ᵐ x ∂markedCycleLaw, x.2.2 ≤ (x.1 : ℝ) * Real.log 3 := by
  have h := markedReturn_cost_upper (RegenerationTails.regenerationState, 0)
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  simp

theorem cycle_cost_exponential_moment : ∃ η : ℝ, 0 < η ∧
    (∫⁻ G, ENNReal.ofReal (Real.exp (η * G)) ∂cycleCostLaw) < ∞ := by
  obtain ⟨θ, hθ, hb⟩ := return_duration_exponential_moment
  have hL : 0 < Real.log 3 := Real.log_pos (by norm_num)
  let η := θ / Real.log 3
  have hη : 0 < η := div_pos hθ hL
  refine ⟨η, hη, ?_⟩
  rw [← markedCycleLaw_cost_projection,
    lintegral_map (g := fun x : MarkedReturn => x.2.2) (f := fun G : ℝ => ENNReal.ofReal (Real.exp (η * G)))
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul measurable_id)))
      (measurable_snd.comp measurable_snd)]
  have hbound : (∫⁻ x : MarkedReturn, ENNReal.ofReal (Real.exp (η * x.2.2)) ∂markedCycleLaw) ≤
      ∫⁻ x : MarkedReturn, ENNReal.ofReal (Real.exp (θ * (x.1 : ℝ))) ∂markedCycleLaw := by
    apply lintegral_mono_ae
    filter_upwards [markedCycle_cost_upper] with x hx
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have heq : η * ((x.1 : ℝ) * Real.log 3) = θ * (x.1 : ℝ) := by dsimp [η]; field_simp [ne_of_gt hL]
    nlinarith [mul_le_mul_of_nonneg_left hx hη.le]
  apply lt_of_le_of_lt hbound
  have h := hb (RegenerationTails.regenerationState, 0)
  rw [durationFrom, lintegral_map (measurable_of_countable (fun n : ℕ => ENNReal.ofReal (Real.exp (θ * (n : ℝ))))) measurable_fst] at h
  exact h

theorem cycle_cost_exponential_integrable : ∃ η : ℝ, 0 < η ∧
    Integrable (fun G : ℝ => Real.exp (η * G)) cycleCostLaw := by
  obtain ⟨η, hη, hb⟩ := cycle_cost_exponential_moment
  refine ⟨η, hη, ⟨(Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable, ?_⟩⟩
  exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun G : ℝ => (Real.exp_pos (η * G)).le))).mpr hb

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

theorem pairVisits_full_steps (z : OddCost) :
    pairVisits z = costKernel (embedOdd z) + (costKernel ^ 2) (embedOdd z) := by
  rw [pairVisits, add_apply, evenVisit_eq_full_step, oddVisit_eq_paired, pairedCost_full_grouping]

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

end NumberTheoryLean.CycleOccupation

end

section

namespace NumberTheoryLean.CycleRenewalInputs

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
open CostReturnLaw CycleCostLower CycleCostMoments CycleCostAtomless
open AbsorptionCutoff.Renewal

theorem cycle_negative_exponential_integrable {η : ℝ} (hη : 0 ≤ η) :
    Integrable (fun G : ℝ => Real.exp (-η * G)) cycleCostLaw := by
  refine (integrable_const (1 : ℝ)).mono'
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable) ?_
  filter_upwards [cycleCostLaw_positive] with G hG
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (by nlinarith)

theorem cycle_all_moments (n : ℕ) : Integrable (fun G : ℝ => G ^ n) cycleCostLaw := by
  obtain ⟨η, hη, hp⟩ := cycle_cost_exponential_integrable
  have hn := cycle_negative_exponential_integrable hη.le
  simpa only [id_eq] using integrable_pow_of_integrable_exp_mul (μ := cycleCostLaw)
    (X := id) (ne_of_gt hη) hp hn n

theorem cycle_integrable_id : Integrable id cycleCostLaw := by
  convert! cycle_all_moments 1 using 1
  all_goals try with_reducible_and_instances rfl
  simp
  rfl

theorem cycle_memLp_two : MemLp id 2 cycleCostLaw := by
  apply (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr
  exact cycle_all_moments 2

theorem cycle_mean_lower : Real.log (4 / 3) ≤ ∫ G : ℝ, G ∂cycleCostLaw := by
  have h := integral_mono_ae (integrable_const (Real.log (4 / 3))) cycle_integrable_id cycleCostLaw_lower
  simpa using h

theorem cycle_mean_pos : 0 < ∫ G : ℝ, G ∂cycleCostLaw :=
  lt_of_lt_of_le (Real.log_pos (by norm_num)) cycle_mean_lower

theorem cycle_nonlattice : Nonlattice cycleCostLaw := by
  intro a r
  rw [cycleCostLaw_lattice_null]
  norm_num

theorem cycle_expTransform_le : expTransform 1 cycleCostLaw ≤ ENNReal.ofReal (3 / 4 : ℝ) := by
  unfold expTransform
  simp only [one_mul]
  have heq : Real.exp (-Real.log (4 / 3)) = (3 : ℝ) / 4 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4 / 3)]
    norm_num
  calc
    _ ≤ ∫⁻ _G : ℝ, ENNReal.ofReal (Real.exp (-Real.log (4 / 3))) ∂cycleCostLaw := by
      apply lintegral_mono_ae
      filter_upwards [cycleCostLaw_lower] with G hG
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith))
    _ = _ := by rw [lintegral_const, measure_univ, mul_one, heq]

theorem cycle_expTransform_lt_one : expTransform 1 cycleCostLaw < 1 :=
  lt_of_le_of_lt cycle_expTransform_le (by norm_num)

theorem cycle_renewal_cell_bound (ell : ℝ) : ∃ C : ℝ, ∀ y : ℝ,
    renewalMeasure cycleCostLaw (Icc y (y + ell)) ≤ ENNReal.ofReal C :=
  exists_bound_renewalMeasure_Icc_of_expTransform cycle_nonlattice cycle_memLp_two cycle_mean_pos
    (θ := 1) (by norm_num) cycle_expTransform_lt_one ell

end NumberTheoryLean.CycleRenewalInputs

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

theorem lintegral_state_occupation {Q : State → ℝ≥0∞} (hQ : Measurable Q) :
    (∫⁻ y : CostState, Q y.1 ∂occupationMeasure) =
      (ENNReal.ofReal beta)⁻¹ * ∫⁻ s : State, Q s ∂stateMeasure := by
  rw [← lintegral_map hQ measurable_fst, occupation_map_stateMeasure, lintegral_smul_measure, smul_eq_mul]

end Erdos970Dependency.ActualCycleOccupation

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



namespace NumberTheoryLean.CycleConvolutionLaw

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Topology
open PairedCostProcess CostReturnLaw CycleRegeneration CycleRenewalInputs
open AbsorptionCutoff.Renewal

theorem cumulative_cost_lintegral (n : ℕ) (z : OddCost) (hz : z ∈ returnSet)
    {H : ℝ → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ y, H y.2 ∂(returnLaw ^ n) z) = ∫⁻ G, H (z.2 + G) ∂convPow cycleCostLaw n := by
  induction n generalizing z with
  | zero =>
    change (∫⁻ y, H y.2 ∂Measure.dirac z) = _
    rw [lintegral_dirac' z (f := fun y : OddCost => H y.2) (hH.comp measurable_snd), convPow_zero,
      lintegral_dirac' 0 (f := fun G : ℝ => H (z.2 + G)) (hH.comp (measurable_const.add measurable_id)), add_zero]
  | succ n ih =>
    have hp : returnLaw ^ (n + 1) = (returnLaw ^ n) ∘ₖ returnLaw := pow_succ returnLaw n
    rw [hp, Kernel.lintegral_comp _ _ _ (g := fun y : OddCost => H y.2) (hH.comp measurable_snd)]
    let F : ℝ → ℝ≥0∞ := fun t => ∫⁻ G, H (z.2 + t + G) ∂convPow cycleCostLaw n
    have hF : Measurable F := (hH.comp ((measurable_const.add measurable_fst).add measurable_snd)).lintegral_prod_right'
    calc
      _ = ∫⁻ y, F (y.2 - z.2) ∂returnLaw z := by
        apply lintegral_congr_ae
        filter_upwards [returnLaw_ae_regeneration z] with y hy
        rw [ih y hy]
        apply lintegral_congr
        intro G
        congr 1
        ring
      _ = ∫⁻ t, F t ∂cycleCostLaw := cycle_increment_integral z hz hF
      _ = _ := by
        rw [convPow_succ', Measure.lintegral_conv (f := fun G : ℝ => H (z.2 + G))
          (hH.comp (measurable_const.add measurable_id))]
        apply lintegral_congr
        intro t
        apply lintegral_congr
        intro G
        congr 1
        ring

theorem cumulative_cost_law (n : ℕ) (z : OddCost) (hz : z ∈ returnSet) :
    ((returnLaw ^ n) z).map (fun y => y.2 - z.2) = convPow cycleCostLaw n := by
  apply Measure.ext_of_lintegral
  intro H hH
  rw [lintegral_map (g := fun y : OddCost => y.2 - z.2) hH (measurable_snd.sub measurable_const),
    cumulative_cost_lintegral n z hz (H := fun G : ℝ => H (G - z.2))
      (hH.comp (measurable_id.sub measurable_const))]
  apply lintegral_congr
  intro G
  rw [add_sub_cancel_left]

theorem actualArrivalLaw_eq_convPow (n : ℕ) : actualArrivalLaw n = convPow cycleCostLaw n := by
  have hz : (RegenerationTails.regenerationState, (0 : ℝ)) ∈ returnSet := by
    change (1 : ℝ) ≤ 3
    norm_num
  have h := cumulative_cost_law n (RegenerationTails.regenerationState, 0) hz
  simp only [sub_zero] at h
  convert! h using 1
  all_goals try with_reducible_and_instances rfl

theorem actualArrival_sum_eq_renewal : Measure.sum actualArrivalLaw = renewalMeasure cycleCostLaw := by
  unfold renewalMeasure
  apply congrArg Measure.sum
  funext n
  exact actualArrivalLaw_eq_convPow n

end NumberTheoryLean.CycleConvolutionLaw



namespace NumberTheoryLean.OccupationDecomposition

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathMeasures PairedCostProcess PairedCostGrouping
open CostReturnLaw CycleOccupation KernelPotential

instance pairedOccupation_isSFiniteKernel : IsSFiniteKernel pairedOccupation := by
  unfold pairedOccupation
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem returnLaw_eq_potential : returnLaw = potential costCaptured costKilled := rfl

theorem occupationKernel_eq_potential : occupationKernel = potential pairVisits costKilled := rfl

theorem pairedOccupation_cycle_decomposition :
    pairedOccupation = Kernel.sum (fun n : ℕ => occupationKernel ∘ₖ (returnLaw ^ n)) := by
  have hsplit : pairedCostKernel = costKilled + costCaptured := by
    rw [add_comm, costCaptured_add_costKilled]
  rw [pairedOccupation, hsplit, first_capture_decomposition,
    ← occupationKernel_eq_potential, ← returnLaw_eq_potential]
  rfl

theorem oddEmbedding_intertwines :
    oddEmbeddingKernel ∘ₖ pairedCostKernel = (costKernel ^ 2) ∘ₖ oddEmbeddingKernel := by
  rw [oddEmbeddingKernel, Kernel.deterministic_comp_eq_map, Kernel.comp_deterministic_eq_comap]
  ext z : 1
  rw [Kernel.map_apply _ embedOdd_measurable, Kernel.comap_apply]
  exact pairedCost_full_grouping z

theorem oddEmbedding_intertwines_pow (n : ℕ) :
    oddEmbeddingKernel ∘ₖ (pairedCostKernel ^ n) = (costKernel ^ (2 * n)) ∘ₖ oddEmbeddingKernel := by
  induction n with
  | zero =>
    have h0 : pairedCostKernel ^ 0 = (Kernel.id : Kernel OddCost OddCost) := rfl
    have h1 : costKernel ^ (2 * 0) = (Kernel.id : Kernel CostState CostState) := rfl
    rw [h0, h1, Kernel.comp_id, Kernel.id_comp]
  | succ n ih =>
    have hp : pairedCostKernel ^ (n + 1) = (pairedCostKernel ^ n) ∘ₖ pairedCostKernel := pow_succ _ _
    rw [hp, ← Kernel.comp_assoc, ih, Kernel.comp_assoc, oddEmbedding_intertwines,
      ← Kernel.comp_assoc, ← Kernel.pow_add]
    congr 2

theorem pairVisits_as_full_kernel :
    pairVisits = (costKernel + costKernel ^ 2) ∘ₖ oddEmbeddingKernel := by
  rw [oddEmbeddingKernel, Kernel.comp_deterministic_eq_comap]
  ext z : 1
  rw [Kernel.comap_apply, add_apply]
  exact pairVisits_full_steps z

theorem pairedVisits_full_grouping (n : ℕ) (z : OddCost) :
    (pairVisits ∘ₖ (pairedCostKernel ^ n)) z =
      (costKernel ^ (2 * n + 1)) (embedOdd z) + (costKernel ^ (2 * n + 2)) (embedOdd z) := by
  have heq : pairVisits ∘ₖ (pairedCostKernel ^ n) =
      (costKernel ^ (2 * n + 1) + costKernel ^ (2 * n + 2)) ∘ₖ oddEmbeddingKernel := by
    rw [pairVisits_as_full_kernel, Kernel.comp_assoc, oddEmbedding_intertwines_pow,
      ← Kernel.comp_assoc, Kernel.comp_add_left]
    have h1 : costKernel ∘ₖ (costKernel ^ (2 * n)) = costKernel ^ (2 * n + 1) := by
      exact (pow_succ' costKernel (2 * n)).symm
    have h2 : (costKernel ^ 2) ∘ₖ (costKernel ^ (2 * n)) = costKernel ^ (2 * n + 2) := by
      rw [← Kernel.pow_add]
      congr 1
      omega
    rw [h1, h2]
  rw [heq, oddEmbeddingKernel, Kernel.comp_deterministic_eq_comap, Kernel.comap_apply, add_apply]

theorem pairedOccupation_eq_full (z : OddCost) : pairedOccupation z = fullOccupation (embedOdd z) := by
  ext B hB
  rw [pairedOccupation, potential, Kernel.sum_apply' _ _ hB, fullOccupation, Kernel.sum_apply' _ _ hB]
  simp_rw [pairedVisits_full_grouping, Measure.add_apply]
  rw [ENNReal.tsum_add]
  simpa only [Nat.add_assoc, show (1 : ℕ) + 1 = 2 by rfl] using
    (tsum_even_add_odd (f := fun n : ℕ => (costKernel ^ (n + 1)) (embedOdd z) B)
      ENNReal.summable ENNReal.summable)

theorem fullOccupation_cycle_decomposition (z : OddCost) :
    fullOccupation (embedOdd z) =
      Measure.sum (fun n : ℕ => (occupationKernel ∘ₖ (returnLaw ^ n)) z) := by
  rw [← pairedOccupation_eq_full, pairedOccupation_cycle_decomposition, Kernel.sum_apply]

theorem fullOccupation_cycle_lintegral (z : OddCost) {F : CostState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y, F y ∂fullOccupation (embedOdd z)) =
      ∑' n : ℕ, ∫⁻ w, ∫⁻ y, F y ∂occupationKernel w ∂(returnLaw ^ n) z := by
  rw [fullOccupation_cycle_decomposition, lintegral_sum_measure]
  apply tsum_congr
  intro n
  exact Kernel.lintegral_comp _ _ _ hF

end NumberTheoryLean.OccupationDecomposition



namespace NumberTheoryLean.OccupationRegeneration

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostProcess PairedCostGrouping
open RegenerationTails CostReturnLaw CycleRegeneration CycleOccupation
open OccupationDecomposition CycleResponse CycleConvolutionLaw

theorem costKernel_translation (z : CostState) (a : ℝ) :
    (costKernel z).map (shiftFullCost a) = costKernel (shiftFullCost a z) := by
  ext B hB
  rw [Measure.map_apply (shiftFullCost_measurable a) hB,
    costKernel_apply _ ((shiftFullCost_measurable a) hB), costKernel_apply _ hB]
  congr 1
  ext s
  change (s, (z.2 + cost (stateRatio s)) + a) ∈ B ↔
    (s, (z.2 + a) + cost (stateRatio s)) ∈ B
  rw [show z.2 + cost (stateRatio s) + a = z.2 + a + cost (stateRatio s) by ring]

theorem shiftFull_commutes (a : ℝ) : Commute (shiftFullKernel a) costKernel := by
  change shiftFullKernel a ∘ₖ costKernel = costKernel ∘ₖ shiftFullKernel a
  rw [shiftFullKernel, Kernel.deterministic_comp_eq_map, Kernel.comp_deterministic_eq_comap]
  ext z : 1
  rw [Kernel.map_apply _ (shiftFullCost_measurable a), Kernel.comap_apply]
  exact costKernel_translation z a

theorem costKernel_pow_translation (n : ℕ) (z : CostState) (a : ℝ) :
    ((costKernel ^ n) z).map (shiftFullCost a) = (costKernel ^ n) (shiftFullCost a z) := by
  have h := ((shiftFull_commutes a).pow_right n).eq
  change shiftFullKernel a ∘ₖ (costKernel ^ n) = (costKernel ^ n) ∘ₖ shiftFullKernel a at h
  rw [shiftFullKernel, Kernel.deterministic_comp_eq_map, Kernel.comp_deterministic_eq_comap] at h
  have hz := congrArg (fun K : Kernel CostState CostState => K z) h
  rwa [Kernel.map_apply _ (shiftFullCost_measurable a), Kernel.comap_apply] at hz

theorem pairVisits_translation (z : OddCost) (a : ℝ) :
    (pairVisits z).map (shiftFullCost a) = pairVisits (shiftCost a z) := by
  rw [pairVisits_full_steps, Measure.map_add _ _ (shiftFullCost_measurable a),
    costKernel_translation, costKernel_pow_translation, pairVisits_full_steps]
  rfl

theorem shifts_intertwine_pairVisits (a : ℝ) :
    shiftFullKernel a ∘ₖ pairVisits = pairVisits ∘ₖ shiftKernel a := by
  rw [shiftFullKernel, shiftKernel, Kernel.deterministic_comp_eq_map, Kernel.comp_deterministic_eq_comap]
  ext z : 1
  rw [Kernel.map_apply _ (shiftFullCost_measurable a), Kernel.comap_apply]
  exact pairVisits_translation z a

theorem shifts_intertwine_occupation (a : ℝ) :
    shiftFullKernel a ∘ₖ occupationKernel = occupationKernel ∘ₖ shiftKernel a := by
  rw [occupationKernel, Kernel.comp_sum_right, Kernel.comp_sum_left]
  apply congrArg Kernel.sum
  funext n
  have hQ := ((shift_commutes_killed a).pow_right n).eq
  change shiftKernel a ∘ₖ (costKilled ^ n) = (costKilled ^ n) ∘ₖ shiftKernel a at hQ
  change shiftFullKernel a ∘ₖ (pairVisits ∘ₖ (costKilled ^ n)) =
    (pairVisits ∘ₖ (costKilled ^ n)) ∘ₖ shiftKernel a
  rw [← Kernel.comp_assoc, shifts_intertwine_pairVisits, Kernel.comp_assoc, hQ, ← Kernel.comp_assoc]

theorem occupation_translation (z : OddCost) (a : ℝ) :
    (occupationKernel z).map (shiftFullCost a) = occupationKernel (shiftCost a z) := by
  have h := shifts_intertwine_occupation a
  rw [shiftFullKernel, shiftKernel, Kernel.deterministic_comp_eq_map, Kernel.comp_deterministic_eq_comap] at h
  have hz := congrArg (fun K : Kernel OddCost CostState => K z) h
  rwa [Kernel.map_apply _ (shiftFullCost_measurable a), Kernel.comap_apply] at hz

theorem pairVisits_regeneration (s : OddState) (hs : s.1 ≤ 3) (T : ℝ) :
    pairVisits (s, T) = pairVisits (regenerationState, T) := by
  rw [pairVisits_full_steps, pairVisits_full_steps]
  have hfirst : costKernel (embedOdd (s, T)) = costKernel (embedOdd (regenerationState, T)) :=
    costKernel_regeneration s hs T
  have hpow : costKernel ^ 2 = costKernel ∘ₖ costKernel := by rw [pow_two]; rfl
  rw [hfirst, hpow, Kernel.comp_apply, Kernel.comp_apply, hfirst]

theorem visitBlock_regeneration (n : ℕ) (s : OddState) (hs : s.1 ≤ 3) (T : ℝ) :
    visitBlock n (s, T) = visitBlock n (regenerationState, T) := by
  cases n with
  | zero =>
    change (pairVisits ∘ₖ (Kernel.id : Kernel OddCost OddCost)) (s, T) =
      (pairVisits ∘ₖ (Kernel.id : Kernel OddCost OddCost)) (regenerationState, T)
    rw [Kernel.comp_id]
    exact pairVisits_regeneration s hs T
  | succ n =>
    have hp : costKilled ^ (n + 1) = (costKilled ^ n) ∘ₖ costKilled := pow_succ _ _
    have hq : (costKilled ^ (n + 1)) (s, T) = (costKilled ^ (n + 1)) (regenerationState, T) := by
      rw [hp, Kernel.comp_apply, Kernel.comp_apply, costKilled_regeneration s hs T]
    rw [visitBlock, Kernel.comp_apply, Kernel.comp_apply, hq]

theorem occupation_regeneration (s : OddState) (hs : s.1 ≤ 3) (T : ℝ) :
    occupationKernel (s, T) = occupationKernel (regenerationState, T) := by
  ext B hB
  rw [occupationKernel, Kernel.sum_apply' _ _ hB, Kernel.sum_apply' _ _ hB]
  apply tsum_congr
  intro n
  rw [visitBlock_regeneration n s hs T]

theorem occupation_regeneration_law (z : OddCost) (hz : z ∈ returnSet) :
    occupationKernel z = occupationMeasure.map (shiftFullCost z.2) := by
  rw [occupation_regeneration z.1 hz z.2, occupationMeasure, occupation_translation]
  have heq : shiftCost z.2 (regenerationState, 0) = (regenerationState, z.2) := by simp [shiftCost]
  rw [heq]

theorem positiveResponse_measurable {F : ℝ × State → ℝ≥0∞} (hF : Measurable F) :
    Measurable (positiveResponse F) := by
  exact (hF.comp ((measurable_fst.sub (measurable_snd.comp measurable_snd)).prodMk
    (measurable_fst.comp measurable_snd))).lintegral_prod_right'

theorem occupation_response_lintegral (z : OddCost) (hz : z ∈ returnSet)
    {F : ℝ × State → ℝ≥0∞} (hF : Measurable F) (v : ℝ) :
    (∫⁻ y : CostState, F (v - y.2, y.1) ∂occupationKernel z) = positiveResponse F (v - z.2) := by
  rw [occupation_regeneration_law z hz, lintegral_map
    (f := fun y : CostState => F (v - y.2, y.1))
    (hF.comp ((measurable_const.sub measurable_snd).prodMk measurable_fst)) (shiftFullCost_measurable z.2)]
  apply lintegral_congr
  intro y
  congr 1
  dsimp [shiftFullCost]
  ext <;> simp only
  ring

theorem returnLaw_pow_ae_regeneration (n : ℕ) (z : OddCost) (hz : z ∈ returnSet) :
    ∀ᵐ w ∂(returnLaw ^ n) z, w ∈ returnSet := by
  cases n with
  | zero =>
    change ∀ᵐ w ∂Measure.dirac z, w ∈ returnSet
    exact (ae_dirac_iff returnSet_measurable).mpr hz
  | succ n =>
    have hp : returnLaw ^ (n + 1) = returnLaw ∘ₖ (returnLaw ^ n) := pow_succ' _ _
    rw [hp]
    exact Kernel.ae_comp_of_ae_ae returnSet_measurable
      (Eventually.of_forall fun w => returnLaw_ae_regeneration w)

theorem fullOccupation_positive_convolution {F : ℝ × State → ℝ≥0∞}
    (hF : Measurable F) (v : ℝ) :
    (∫⁻ y : CostState, F (v - y.2, y.1) ∂fullOccupation (embedOdd (regenerationState, 0))) =
      ∑' n : ℕ, ∫⁻ s, positiveResponse F (v - s) ∂actualArrivalLaw n := by
  have hz : (regenerationState, (0 : ℝ)) ∈ returnSet := by change (1 : ℝ) ≤ 3; norm_num
  rw [fullOccupation_cycle_lintegral _ (F := fun y : CostState => F (v - y.2, y.1)) (hF.comp ((measurable_const.sub measurable_snd).prodMk measurable_fst))]
  apply tsum_congr
  intro n
  rw [actualArrivalLaw, lintegral_map (f := fun s : ℝ => positiveResponse F (v - s))
    ((positiveResponse_measurable hF).comp (measurable_const.sub measurable_id)) measurable_snd]
  apply lintegral_congr_ae
  filter_upwards [returnLaw_pow_ae_regeneration n (regenerationState, 0) hz] with w hw
  exact occupation_response_lintegral w hw hF v

end NumberTheoryLean.OccupationRegeneration



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

namespace NumberTheoryLean.RegenerationBandBounds

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathMeasures PairedCostGrouping RegenerationTails CostReturnLaw
open CycleOccupation CycleConvolutionLaw OccupationDecomposition OccupationRegeneration
open AbsorptionCutoff.Renewal
open Erdos970Dependency.InvariantDensities Erdos970Dependency.StateKernelInvariance
open Erdos970Dependency.ActualCycleOccupation

instance cycleRenewal_sFinite : SFinite (renewalMeasure cycleCostLaw) := by
  unfold renewalMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem sub_mem_band_iff (v T h : ℝ) : v - T ∈ Icc (-h) 0 ↔ T ∈ Icc v (v + h) := by
  simp only [mem_Icc]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

theorem regeneration_band_identity {Q : State → ℝ≥0∞} (hQ : Measurable Q) (v h : ℝ) :
    (∫⁻ y, stateBandReward Q v h y ∂fullOccupation (embedOdd (regenerationState, 0))) =
      ∫⁻ y : CostState, Q y.1 * renewalMeasure cycleCostLaw (Icc (v - y.2) (v + h - y.2)) ∂occupationMeasure := by
  classical
  let F : ℝ × State → ℝ≥0∞ := (Prod.fst ⁻¹' Icc (-h) 0).indicator (fun x => Q x.2)
  have hF : Measurable F := (hQ.comp measurable_snd).indicator (measurable_fst measurableSet_Icc)
  have heq : stateBandReward Q v h = fun y : CostState => F (v - y.2, y.1) := by
    funext y
    simp only [stateBandReward, F, indicator_apply, mem_preimage, sub_mem_band_iff]
  rw [heq, fullOccupation_positive_convolution hF, ← lintegral_sum_measure, actualArrival_sum_eq_renewal]
  change (∫⁻ T : ℝ, ∫⁻ y : CostState, F (v - T - y.2, y.1) ∂occupationMeasure ∂renewalMeasure cycleCostLaw) = _
  have hjoint : Measurable (Function.uncurry (fun T : ℝ => fun y : CostState => F (v - T - y.2, y.1))) :=
    hF.comp (((measurable_const.sub measurable_fst).sub (measurable_snd.comp measurable_snd)).prodMk
      (measurable_fst.comp measurable_snd))
  rw [lintegral_lintegral_swap hjoint.aemeasurable]
  apply lintegral_congr
  intro y
  have hinner : (fun T : ℝ => F (v - T - y.2, y.1)) =
      (Icc (v - y.2) (v + h - y.2)).indicator (fun _ : ℝ => Q y.1) := by
    funext T
    have hiff : v - T - y.2 ∈ Icc (-h) 0 ↔ T ∈ Icc (v - y.2) (v + h - y.2) := by
      simp only [mem_Icc]
      constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
    simp only [F, indicator_apply, mem_preimage]
    simp only [hiff]
  rw [hinner, lintegral_indicator measurableSet_Icc, lintegral_const]
  simp

theorem regeneration_uniform_band_jb247_oai (h : ℝ) : ∃ C : ℝ≥0∞, C < ∞ ∧
    ∀ Q : State → ℝ≥0∞, Measurable Q → ∀ v : ℝ,
      (∫⁻ y, stateBandReward Q v h y ∂fullOccupation (embedOdd (regenerationState, 0))) ≤
        C * ∫⁻ s : State, Q s ∂stateMeasure := by
  obtain ⟨B, hB⟩ := CycleRenewalInputs.cycle_renewal_cell_bound h
  let C := ENNReal.ofReal B * (ENNReal.ofReal beta)⁻¹
  have hβ : ENNReal.ofReal beta ≠ 0 := (ENNReal.ofReal_pos.mpr beta_pos).ne'
  have hC : C < ∞ := lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.mpr hβ))
  refine ⟨C, hC, ?_⟩
  intro Q hQ v
  rw [regeneration_band_identity hQ v h]
  calc
    _ ≤ ∫⁻ y : CostState, Q y.1 * ENNReal.ofReal B ∂occupationMeasure := by
      apply lintegral_mono
      intro y
      apply mul_le_mul le_rfl _ zero_le zero_le
      have hb := hB (v - y.2)
      rwa [show (v - y.2) + h = v + h - y.2 by ring] at hb
    _ = (∫⁻ y : CostState, Q y.1 ∂occupationMeasure) * ENNReal.ofReal B :=
      lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    _ = C * ∫⁻ s : State, Q s ∂stateMeasure := by
      rw [lintegral_state_occupation hQ]
      dsimp [C]
      ring

end NumberTheoryLean.RegenerationBandBounds

end

end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.NumberTheoryLean.RegenerationBandBounds.regeneration_uniform_band_jb247_oai := @OAI.Erdos970.NumberTheoryLean.RegenerationBandBounds.regeneration_uniform_band_jb247_oai
