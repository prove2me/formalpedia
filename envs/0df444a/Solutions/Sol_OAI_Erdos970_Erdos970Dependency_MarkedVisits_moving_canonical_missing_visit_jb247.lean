-- Prove2me | solution 1 for OAI.Erdos970.Erdos970Dependency.MarkedVisits.moving_canonical_missing_visit_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:02:39.293869+00:00
-- url     : https://prove2.me/submissions/806e95bd-f0a2-4482-89e7-a13179332af0

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
import Mathlib.Data.List.OfFn
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
import Theorems.Thm_OAI_Erdos970_Erdos970Dependency_MarkedVisits_beginningWindow_exponential_jb247

section
-- module Solutions.OAIQ247_JB.Compat
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434

end OAI
end

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

theorem exponent_le_cutoff {i : Side} {s t r : ℝ}
    (hs : Valid i s) (ht : minRatio i s ≤ t) (hr : 0 < r) : nextExponent r t ≤ r / s := by
  have hs0 := valid_pos hs
  have ht0 := valid_pos (valid_next hs ht)
  have hst : s ≤ t + 1 := by linarith [minRatio_ge_sub_one i s]
  exact div_le_div_of_nonneg_left hr.le hs0 hst

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
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
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

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.TransitionKernels NumberTheoryLean.FinitePathGeometry
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.RegenerationTails

lemma markedPairKernel_apply (z : OddCost) {B : Set MarkedOddCost} (hB : MeasurableSet B) :
    markedPairKernel z B = pairedDraws z.1
      {x | (sourceMark x.1,(x.2,z.2+cost x.1.1+cost x.2.1)) ∈ B} := by
  rw [markedPairKernel,Kernel.map_apply' _ markedPairUpdate_measurable _ hB,
    Kernel.prod_apply' _ _ _ (markedPairUpdate_measurable hB),Kernel.id_apply,lintegral_dirac']
  · rfl
  · exact measurable_measure_prodMk_left (markedPairUpdate_measurable hB)

lemma markedPair_forget (z : OddCost) : (markedPairKernel z).map Prod.snd = pairedCostKernel z := by
  ext B hB
  rw [Measure.map_apply measurable_snd hB,markedPairKernel_apply _ (measurable_snd hB),
    pairedCostKernel_apply _ hB]
  rfl

lemma markedPair_regeneration (s : OddState) (hs : s.1 ≤ 3) (T : ℝ) :
    markedPairKernel (s,T) = markedPairKernel (regenerationState,T) := by
  ext B hB
  rw [markedPairKernel_apply _ hB,markedPairKernel_apply _ hB,pairedDraws_regeneration s hs]

lemma markedShift_measurable (a : ℝ) : Measurable (markedShift a) :=
  measurable_fst.prodMk ((shiftCost_measurable a).comp measurable_snd)

lemma markedPair_translation (s : OddState) (T a : ℝ) :
    (markedPairKernel (s,T)).map (markedShift a) = markedPairKernel (s,T+a) := by
  ext B hB
  rw [Measure.map_apply (markedShift_measurable a) hB,
    markedPairKernel_apply _ ((markedShift_measurable a) hB),markedPairKernel_apply _ hB]
  congr 1
  ext x
  change (sourceMark x.1,(x.2,(T+cost x.1.1+cost x.2.1)+a)) ∈ B ↔
    (sourceMark x.1,(x.2,(T+a)+cost x.1.1+cost x.2.1)) ∈ B
  rw [show (T+cost x.1.1+cost x.2.1)+a=(T+a)+cost x.1.1+cost x.2.1 by ring]

end Erdos970Dependency.MarkedVisits

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

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.TransitionKernels NumberTheoryLean.RegenerationTails
open NumberTheoryLean.DerivativeWeights NumberTheoryLean.WeightFutureIntegrals
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.KernelDensityBridge

lemma regeneration_density_eq {t : ℝ} (ht : 2 ≤ t) :
    oddDensity regenerationState t = W t*phiEven t/phiOdd 1 := by
  simp [oddDensity,tailDensity,regenerationState,ht]

lemma regeneration_interval_positive {a b : ℝ} (ha : 2 ≤ a) (hab : a < b) :
    0 < oddKernel regenerationState (Icc a b) := by
  have hp : ∀ t ∈ Icc a b, 0 < oddDensity regenerationState t := by
    intro t ht
    rw [regeneration_density_eq (ha.trans ht.1)]
    exact div_pos (mul_pos (W_pos (by linarith [ht.1])) (phiEven_pos (by linarith [ht.1]))) (phiOdd_pos 1)
  have hf : ContinuousOn (fun t => W t*phiEven t/phiOdd 1) (Icc a b) := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have ht2 : t^2 ≠ 0 := pow_ne_zero 2 ht0
    have hW : ContinuousAt W t := by unfold W; fun_prop
    exact ((hW.mul (phiEven_continuousAt (by linarith [ht.1]))).div_const _).continuousWithinAt
  have hc : ContinuousOn (oddDensity regenerationState) (Icc a b) := hf.congr
    (fun t ht => regeneration_density_eq (ha.trans ht.1))
  have hi := intervalIntegral.integral_pos hab hc (fun t ht => (hp t ⟨ht.1.le,ht.2⟩).le)
    ⟨a,⟨le_rfl,hab.le⟩,hp a ⟨le_rfl,hab.le⟩⟩
  rw [oddKernel_apply,← ofReal_integral_eq_lintegral_ofReal
    (oddDensity_integrable regenerationState).integrableOn
    (Filter.Eventually.of_forall (oddDensity_nonneg regenerationState))]
  apply ENNReal.ofReal_pos.mpr
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hab.le]
  exact hi

lemma markProbability_pos : 0 < markProbability :=
  regeneration_interval_positive (by norm_num) (by norm_num)

lemma markProbability_lt_one : markProbability < 1 := by
  let J := Icc (5/2:ℝ) (13/5)
  have hJ : 0 < oddKernel regenerationState J := regeneration_interval_positive (by norm_num) (by norm_num)
  have hdisj : Disjoint (Icc (209/100:ℝ) (213/100)) J := by
    apply Set.disjoint_left.mpr
    intro t ht hj
    dsimp [J] at hj
    linarith [ht.2,hj.1]
  have hsum : markProbability+oddKernel regenerationState J ≤ 1 := by
    rw [markProbability,← measure_union hdisj measurableSet_Icc]
    exact prob_le_one
  exact (ENNReal.lt_add_right (measure_ne_top _ _) hJ.ne').trans_le hsum

lemma sourceMark_true (t : EvenState) : sourceMark t = true ↔ t.1 ∈ Icc (209/100:ℝ) (213/100) := by
  simp [sourceMark]

lemma markedPair_mark_mass (s : OddState) (hs : s.1 ≤ 3) (T : ℝ) :
    markedPairKernel (s,T) {z | z.1=true} = markProbability := by
  have hm : MeasurableSet {z : MarkedOddCost | z.1=true} := measurable_fst (measurableSet_singleton true)
  rw [markedPair_regeneration s hs T,markedPairKernel_apply _ hm]
  have he : {x : EvenState × OddState | sourceMark x.1=true} =
      Prod.fst ⁻¹' {t : EvenState | t.1 ∈ Icc (209/100:ℝ) (213/100)} := by
    ext x
    exact sourceMark_true x.1
  change pairedDraws regenerationState {x : EvenState × OddState | sourceMark x.1=true} = _
  rw [he]
  let E : Set EvenState := {t | t.1 ∈ Icc (209/100:ℝ) (213/100)}
  have hE : MeasurableSet E := measurable_subtype_coe measurableSet_Icc
  have hfst : pairedDraws.fst regenerationState E =
      pairedDraws regenerationState {p | p.1 ∈ E} := Kernel.fst_apply' _ _ hE
  change pairedDraws regenerationState {p | p.1 ∈ E} = _
  rw [← hfst,pairedDraws,Kernel.fst_compProd]
  have hmap := oddToEven_map_ratio regenerationState
  have hmeasure := congrArg (fun μ : Measure ℝ => μ (Icc (209/100:ℝ) (213/100))) hmap
  rw [Measure.map_apply measurable_subtype_coe measurableSet_Icc] at hmeasure
  exact hmeasure

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set
open scoped Topology
open NumberTheoryLean.TransitionKernels NumberTheoryLean.FinitePathGeometry

lemma gapAt_le_iff {r B : ℝ} (hr : 0 < r) (hB : 0 < B) (T : ℝ) :
    gapAt r T ≤ B ↔ Real.log (r/B) ≤ T := by
  rw [gapAt,Real.exp_neg,← div_eq_mul_inv,div_le_iff₀ (Real.exp_pos T),
    Real.log_le_iff_le_exp (div_pos hr hB),div_le_iff₀ hB]
  simp only [mul_comm]

lemma le_gapAt_iff {r A : ℝ} (hr : 0 < r) (hA : 0 < A) (T : ℝ) :
    A ≤ gapAt r T ↔ T ≤ Real.log (r/A) := by
  rw [gapAt,Real.exp_neg,← div_eq_mul_inv,le_div_iff₀ (Real.exp_pos T),
    Real.le_log_iff_exp_le (div_pos hr hA),le_div_iff₀ hA]
  simp only [mul_comm]

lemma marked_cost_window {r b0 b1 : ℝ} (hr : 0 < r) (hb0 : 0 < b0) (hb1 : 0 < b1) (T : ℝ) :
    10*b0 ≤ gapAt r T ∧ gapAt r T ≤ b1 ↔
      Real.log (r/b1) ≤ T ∧ T ≤ Real.log (r/b1)+Real.log (b1/(10*b0)) := by
  have he : Real.log (r/(10*b0)) = Real.log (r/b1)+Real.log (b1/(10*b0)) := by
    rw [Real.log_div hr.ne' (by positivity),Real.log_div hr.ne' hb1.ne',
      Real.log_div hb1.ne' (by positivity)]
    ring
  rw [le_gapAt_iff hr (by positivity),gapAt_le_iff hr hb1,he,and_comm]

lemma proportional_window_width {rho b0 : ℝ} (hrho : 0 < rho) (hb0 : 0 < b0) :
    Real.log ((rho*b0)/(10*b0)) = Real.log (rho/10) := by
  congr 1
  field_simp

lemma moving_window_cost_threshold {K rho : ℝ} (hK : 0 < K) (hrho : 0 < rho) (M : ℝ) :
    ∀ᶠ w : ℝ in atTop, 3 ≤ w ∧ ∀ r : ℝ, w ≤ r →
      M ≤ Real.log (r/(rho*K*(Real.log w)^2)) := by
  have ht : Tendsto (fun w:ℝ => (Real.log w)^2/w) atTop (𝓝 0) := by
    simpa only [one_mul,add_zero] using Real.tendsto_pow_log_div_mul_add_atTop (1:ℝ) 0 2 one_ne_zero
  have hl : Tendsto (fun w:ℝ => (Real.exp M*rho*K)*((Real.log w)^2/w)) atTop (𝓝 0) := by
    simpa only [mul_zero] using ht.const_mul (Real.exp M*rho*K)
  filter_upwards [eventually_ge_atTop (3:ℝ),hl.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num))]
    with w hw hs
  refine ⟨hw,?_⟩
  intro r hr
  have hw0 : 0 < w := by linarith
  have hr0 : 0 < r := hw0.trans_le hr
  have hlog : 0 < Real.log w := Real.log_pos (by linarith)
  have hden : 0 < rho*K*(Real.log w)^2 := by positivity
  apply (Real.le_log_iff_exp_le (div_pos hr0 hden)).mpr
  apply (le_div_iff₀ hden).mpr
  have he := (div_le_iff₀ hw0).mp (show (Real.exp M*rho*K*(Real.log w)^2)/w ≤ 1 by simpa only [mul_div_assoc] using hs.le)
  nlinarith

end Erdos970Dependency.MarkedVisits

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
-- module Solutions.OAIQ247_JB.Supercritical_Renewal
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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

/-!
### The pole at the origin

`(1 - charFun μ t)⁻¹` blows up at `t = 0`; that pole is precisely what carries
the `1/m̂` of Blackwell's theorem. The three lemmas below quantify it. They are
the only place where the **deliberate hypothesis strengthening** `MemLp id 2 μ`
(a finite second moment, where sharp Feller needs only a finite mean) is used;
`μ̂_{A,N}` has exponential moments, so it costs nothing at the instantiation.
-/

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

end NumberTheoryLean.CycleCostLower

end

section

namespace NumberTheoryLean.CycleRegeneration

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels PairedCostProcess CostReturnLaw RegenerationTails

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

theorem returnLaw_ae_regeneration (z : OddCost) : ∀ᵐ y ∂returnLaw z, y ∈ returnSet := by
  apply ae_iff.mpr
  exact returnLaw_off_returnSet z

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

end NumberTheoryLean.CycleCostMoments

end

section

namespace NumberTheoryLean.CycleOccupation

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostProcess PairedCostGrouping
open CostReturnLaw CycleCostLower CycleCostMoments

theorem sampling_map_measure {α : Type*} [MeasurableSpace α]
    (f : OddCost × (EvenState × OddState) → α) (hf : Measurable f) (z : OddCost) :
    (pairSampling.map f) z = (pairedDraws z.1).map (fun x => f (z, x)) := by
  ext B hB
  rw [Kernel.map_apply' _ hf _ hB, pairSampling,
    Kernel.prod_apply' _ _ _ (hf hB), Kernel.id_apply, lintegral_dirac']
  · rw [Measure.map_apply (f := fun x : EvenState × OddState => f (z, x)) (hf.comp measurable_prodMk_left) hB]
    rfl
  · exact measurable_measure_prodMk_left (hf hB)

end NumberTheoryLean.CycleOccupation

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



namespace NumberTheoryLean.UniformCycleMoments

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open PairedCostProcess CostReturnLaw CycleCostMoments CycleDurationMoments
open PairedDrift PairedHitting PairedBlockContraction CycleOccupation

theorem geometric_exponential_budget {m : ℕ} (hm : 0 < m) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) : ∃ θ C : ℝ, 0 < θ ∧ 0 ≤ C ∧ ∀ W : ℝ, 0 ≤ W →
      (∑' n : ℕ, ENNReal.ofReal (Real.exp (θ * (2 * ((n : ℝ) + 1)))) *
        ENNReal.ofReal (ρ ^ (n / m) * W)) ≤ ENNReal.ofReal (C * W) := by
  let θ := -Real.log ρ / (4 * (m : ℝ))
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hθ : 0 < θ := div_pos (neg_pos.mpr (Real.log_neg hρ hρ1)) (by positivity)
  have hrel : 4 * (m : ℝ) * θ = -Real.log ρ := by dsimp [θ]; field_simp
  let A := Real.exp (-Real.log ρ + 2 * θ)
  let r := Real.exp (-2 * θ)
  have hA : 0 ≤ A := (Real.exp_pos _).le
  have hr : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hsum : Summable (fun n : ℕ => A * r ^ n) := (summable_geometric_of_lt_one hr hr1).mul_left A
  let C := ∑' n : ℕ, A * r ^ n
  have hC : 0 ≤ C := tsum_nonneg (fun n => mul_nonneg hA (pow_nonneg hr n))
  refine ⟨θ, C, hθ, hC, ?_⟩
  intro W hW
  calc
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (A * r ^ n) * ENNReal.ofReal W := by
      apply ENNReal.tsum_le_tsum
      intro n
      have h := weighted_geometric_bound hm hρ hθ hrel n
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (mul_nonneg hA (pow_nonneg hr n))]
      apply ENNReal.ofReal_le_ofReal
      dsimp [A, r]
      nlinarith [mul_le_mul_of_nonneg_right h hW]
    _ = (∑' n : ℕ, ENNReal.ofReal (A * r ^ n)) * ENNReal.ofReal W := ENNReal.tsum_mul_right
    _ = ENNReal.ofReal C * ENNReal.ofReal W := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg hA (pow_nonneg hr n)) hsum]
    _ = _ := (ENNReal.ofReal_mul hC).symm

theorem return_increment_uniform_exponential : ∃ η C D : ℝ,
    0 < η ∧ 0 ≤ C ∧ 0 < D ∧ ∀ z : OddCost,
      (∫⁻ y, ENNReal.ofReal (Real.exp (η * (y.2 - z.2))) ∂returnLaw z) ≤
        ENNReal.ofReal (C * (V z.1 + D)) := by
  obtain ⟨m, hm, ρ, D, hρ, hρ1, hD, hb⟩ := firstReturn_geometric
  obtain ⟨θ, C, hθ, hC, hbudget⟩ := geometric_exponential_budget hm hρ hρ1
  let η := θ / Real.log 3
  have hL : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hη : 0 < η := div_pos hθ hL
  refine ⟨η, C, D, hη, hC, hD, ?_⟩
  intro z
  rw [returnLaw, Kernel.sum_apply, lintegral_sum_measure]
  apply le_trans (ENNReal.tsum_le_tsum ?_) (hbudget (V z.1 + D) (add_nonneg (V_pos z.1).le hD.le))
  intro n
  calc
    _ ≤ ∫⁻ _y, ENNReal.ofReal (Real.exp (θ * (2 * ((n : ℝ) + 1)))) ∂firstReturn n z := by
      apply lintegral_mono_ae
      filter_upwards [firstReturn_cost_upper n z] with y hy
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      calc
        η * (y.2 - z.2) ≤ η * (2 * ((n + 1 : ℕ) : ℝ) * Real.log 3) :=
          mul_le_mul_of_nonneg_left (by linarith) hη.le
        _ = _ := by dsimp [η]; push_cast; field_simp
    _ = ENNReal.ofReal (Real.exp (θ * (2 * ((n : ℝ) + 1)))) * firstReturn n z univ := lintegral_const _
    _ ≤ _ := mul_le_mul le_rfl (hb n z) zero_le zero_le

end NumberTheoryLean.UniformCycleMoments


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_InitialOddDraw
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.InitialRegeneration.hitOrReturn_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.InitialOddDraw

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostProcess PairedCostGrouping
open KernelDensityBridge CycleCostMoments PairedDrift CompactExponentialMoments

theorem firstOddUpdate_measurable : Measurable firstOddUpdate :=
  measurable_id.prodMk (cost_measurable.comp measurable_subtype_coe)

instance firstOdd_isMarkovKernel : IsMarkovKernel firstOdd :=
  Kernel.IsMarkovKernel.map _ firstOddUpdate_measurable

theorem firstOdd_full_draw (s : EvenState) :
    (firstOdd s).map embedOdd = costKernel (.inl s, 0) := by
  apply Measure.ext_of_lintegral
  intro H hH
  rw [lintegral_map hH embedOdd_measurable, firstOdd, Kernel.map_apply _ firstOddUpdate_measurable,
    lintegral_map (f := fun z : OddCost => H (embedOdd z)) (hH.comp embedOdd_measurable) firstOddUpdate_measurable]
  simpa only [embedOdd, firstOddUpdate, zero_add] using (costKernel_even_lintegral s 0 hH).symm

theorem firstOdd_cost_bounds (s : EvenState) : ∀ᵐ z ∂firstOdd s,
    0 ≤ z.2 ∧ z.2 ≤ Real.log 3 := by
  rw [firstOdd, Kernel.map_apply _ firstOddUpdate_measurable]
  apply (ae_map_iff firstOddUpdate_measurable.aemeasurable
    ((measurableSet_le measurable_const measurable_snd).inter (measurableSet_le measurable_snd measurable_const))).mpr
  exact Eventually.of_forall fun t =>
    ⟨(cost_pos (by linarith [t.2])).le, draw_cost_le_log_three (by linarith [t.2])⟩

theorem firstOdd_drift_lintegral (s : EvenState) {D : ℝ} (hD : 0 ≤ D) :
    (∫⁻ z, ENNReal.ofReal (V z.1 + D) ∂firstOdd s) =
      (∫⁻ t, ENNReal.ofReal (Real.exp t) ∂evenKernel s) + ENNReal.ofReal D := by
  rw [firstOdd, Kernel.map_apply _ firstOddUpdate_measurable,
    lintegral_map (f := fun z : OddCost => ENNReal.ofReal (V z.1 + D))
      (ENNReal.measurable_ofReal.comp ((V_measurable.comp measurable_fst).add measurable_const)) firstOddUpdate_measurable]
  change (∫⁻ t : OddState, ENNReal.ofReal (Real.exp t.1 + D) ∂evenToOdd s) = _
  rw [evenToOdd_lintegral_ratio s (H := fun t : ℝ => ENNReal.ofReal (Real.exp t + D))
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.add measurable_const))]
  simp_rw [ENNReal.ofReal_add (Real.exp_pos _).le hD]
  rw [lintegral_add_left (f := fun t : ℝ => ENNReal.ofReal (Real.exp t))
    (ENNReal.measurable_ofReal.comp Real.measurable_exp), lintegral_const, measure_univ, mul_one]

theorem firstOdd_weighted_exponential (S η D : ℝ) (hη : 0 ≤ η) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : EvenState, s.1 ≤ S →
      (∫⁻ z, ENNReal.ofReal (Real.exp (η * z.2) * (V z.1 + D)) ∂firstOdd s) ≤ ENNReal.ofReal C := by
  obtain ⟨B, hB, hb, _⟩ := kernel_compact_exponential_moments S
  let C := Real.exp (η * Real.log 3) * (B + D)
  have hC : 0 ≤ C := mul_nonneg (Real.exp_pos _).le (add_nonneg hB.le hD)
  refine ⟨C, hC, ?_⟩
  intro s hs
  calc
    _ ≤ ∫⁻ z, ENNReal.ofReal (Real.exp (η * Real.log 3)) * ENNReal.ofReal (V z.1 + D) ∂firstOdd s := by
      apply lintegral_mono_ae
      filter_upwards [firstOdd_cost_bounds s] with z hz
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hz.2 hη)) (add_nonneg (V_pos z.1).le hD))
    _ = ENNReal.ofReal (Real.exp (η * Real.log 3)) *
        ((∫⁻ t, ENNReal.ofReal (Real.exp t) ∂evenKernel s) + ENNReal.ofReal D) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, firstOdd_drift_lintegral s hD]
    _ ≤ ENNReal.ofReal (Real.exp (η * Real.log 3)) * (ENNReal.ofReal B + ENNReal.ofReal D) := by
      apply mul_le_mul le_rfl _ zero_le zero_le
      apply add_le_add _ le_rfl
      rw [← ofReal_integral_eq_lintegral_ofReal (hb s hs).1 (Eventually.of_forall fun t => (Real.exp_pos t).le)]
      exact ENNReal.ofReal_le_ofReal (hb s hs).2
    _ = _ := by rw [← ENNReal.ofReal_add hB.le hD, ← ENNReal.ofReal_mul (Real.exp_pos _).le]

end NumberTheoryLean.InitialOddDraw

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

namespace NumberTheoryLean.InitialRegeneration

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostProcess
open CostReturnLaw CycleRegeneration CycleCostLower PairedDrift
open UniformCycleMoments InitialOddDraw

theorem hitOrReturn_ae_regeneration (z : OddCost) : ∀ᵐ w ∂hitOrReturn z, w ∈ returnSet := by
  classical
  rw [hitOrReturn, Kernel.piecewise_apply]
  split_ifs with hz
  · rw [Kernel.id_apply]
    exact (ae_dirac_iff returnSet_measurable).mpr hz
  · exact returnLaw_ae_regeneration z

theorem hitOrReturn_cost_monotone (z : OddCost) : ∀ᵐ w ∂hitOrReturn z, z.2 ≤ w.2 := by
  classical
  rw [hitOrReturn, Kernel.piecewise_apply]
  split_ifs
  · rw [Kernel.id_apply]
    exact (ae_dirac_iff (measurableSet_le measurable_const measurable_snd)).mpr le_rfl
  · filter_upwards [returnLaw_cost_lower z] with w hw
    have hc : 0 < cost (3 : ℝ) := cost_pos (by norm_num)
    linarith

instance delayedRegeneration_isMarkovKernel : IsMarkovKernel delayedRegeneration := by
  unfold delayedRegeneration
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem delayedRegeneration_ae_regeneration (s : EvenState) :
    ∀ᵐ z ∂delayedRegeneration s, z ∈ returnSet := by
  rw [delayedRegeneration]
  exact Kernel.ae_comp_of_ae_ae returnSet_measurable (Eventually.of_forall hitOrReturn_ae_regeneration)

theorem delayedRegeneration_cost_nonneg (s : EvenState) :
    ∀ᵐ z ∂delayedRegeneration s, 0 ≤ z.2 := by
  rw [delayedRegeneration]
  apply Kernel.ae_comp_of_ae_ae (measurableSet_le measurable_const measurable_snd)
  filter_upwards [firstOdd_cost_bounds s] with z hz
  filter_upwards [hitOrReturn_cost_monotone z] with w hw
  exact le_trans hz.1 hw

theorem exponential_total_eq {α : Type*} [MeasurableSpace α]
    (μ : Measure (α × ℝ)) (η T : ℝ) :
    (∫⁻ y, ENNReal.ofReal (Real.exp (η * y.2)) ∂μ) =
      ENNReal.ofReal (Real.exp (η * T)) *
        (∫⁻ y, ENNReal.ofReal (Real.exp (η * (y.2 - T))) ∂μ) := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro y
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

theorem delayedRegeneration_uniform_exponential (S : ℝ) :
    ∃ η B : ℝ, 0 < η ∧ 0 ≤ B ∧ ∀ s : EvenState, s.1 ≤ S →
      (∫⁻ z, ENNReal.ofReal (Real.exp (η * z.2)) ∂delayedRegeneration s) ≤ ENNReal.ofReal B := by
  classical
  obtain ⟨η, C, D, hη, hC, hD, hb⟩ := return_increment_uniform_exponential
  have hpoint : ∀ z : OddCost,
      (∫⁻ w, ENNReal.ofReal (Real.exp (η * w.2)) ∂hitOrReturn z) ≤
        ENNReal.ofReal (C + 1) * ENNReal.ofReal (Real.exp (η * z.2) * (V z.1 + (D + 1))) := by
    intro z
    rw [hitOrReturn, Kernel.piecewise_apply]
    split_ifs
    · rw [Kernel.id_apply, lintegral_dirac' z (f := fun w : OddCost => ENNReal.ofReal (Real.exp (η * w.2)))
        (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul measurable_snd))),
        ← ENNReal.ofReal_mul (by linarith : 0 ≤ C + 1)]
      apply ENNReal.ofReal_le_ofReal
      have hV : 1 ≤ V z.1 := V_one_le z.1
      have hw : 1 ≤ (C + 1) * (V z.1 + (D + 1)) := by nlinarith [mul_nonneg hC (by linarith : 0 ≤ V z.1 + (D + 1))]
      nlinarith [mul_le_mul_of_nonneg_left hw (Real.exp_pos (η * z.2)).le]
    · rw [exponential_total_eq _ η z.2]
      calc
        _ ≤ ENNReal.ofReal (Real.exp (η * z.2)) * ENNReal.ofReal (C * (V z.1 + D)) :=
          mul_le_mul le_rfl (hb z) zero_le zero_le
        _ ≤ _ := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
            ← ENNReal.ofReal_mul (by linarith : 0 ≤ C + 1)]
          apply ENNReal.ofReal_le_ofReal
          have hV : 0 ≤ V z.1 := (V_pos z.1).le
          have hw : C * (V z.1 + D) ≤ (C + 1) * (V z.1 + (D + 1)) := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_left hw (Real.exp_pos (η * z.2)).le]
  obtain ⟨B, hB, hfirst⟩ := firstOdd_weighted_exponential S η (D + 1) hη.le (by linarith)
  refine ⟨η, (C + 1) * B, hη, mul_nonneg (by linarith) hB, ?_⟩
  intro s hs
  rw [delayedRegeneration, Kernel.lintegral_comp _ _ _
    (g := fun z : OddCost => ENNReal.ofReal (Real.exp (η * z.2)))
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul measurable_snd)))]
  calc
    _ ≤ ∫⁻ z, ENNReal.ofReal (C + 1) * ENNReal.ofReal (Real.exp (η * z.2) * (V z.1 + (D + 1))) ∂firstOdd s :=
      lintegral_mono hpoint
    _ = ENNReal.ofReal (C + 1) *
        (∫⁻ z, ENNReal.ofReal (Real.exp (η * z.2) * (V z.1 + (D + 1))) ∂firstOdd s) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (C + 1) * ENNReal.ofReal B := mul_le_mul le_rfl (hfirst s hs) zero_le zero_le
    _ = _ := (ENNReal.ofReal_mul (by linarith : 0 ≤ C + 1)).symm

instance delayedCostLaw_isProbabilityMeasure (s : EvenState) : IsProbabilityMeasure (delayedCostLaw s) :=
  (Measure.isProbabilityMeasure_map_iff (μ := delayedRegeneration s)
    measurable_snd.aemeasurable).mpr inferInstance

theorem delayedCostLaw_uniform_exponential (S : ℝ) : ∃ η B : ℝ, 0 < η ∧ 0 ≤ B ∧
    ∀ s : EvenState, s.1 ≤ S →
      (∫⁻ T, ENNReal.ofReal (Real.exp (η * T)) ∂delayedCostLaw s) ≤ ENNReal.ofReal B := by
  obtain ⟨η, B, hη, hB, hb⟩ := delayedRegeneration_uniform_exponential S
  refine ⟨η, B, hη, hB, ?_⟩
  intro s hs
  rw [delayedCostLaw, lintegral_map (f := fun T : ℝ => ENNReal.ofReal (Real.exp (η * T))) (ENNReal.measurable_ofReal.comp
    (Real.measurable_exp.comp (measurable_const.mul measurable_id))) measurable_snd]
  exact hb s hs

end NumberTheoryLean.InitialRegeneration

end

section

namespace NumberTheoryLean.RegenerationBandBounds

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathMeasures PairedCostGrouping RegenerationTails CostReturnLaw
open CycleOccupation CycleConvolutionLaw OccupationDecomposition OccupationRegeneration
open AbsorptionCutoff.Renewal
open Erdos970Dependency.InvariantDensities Erdos970Dependency.StateKernelInvariance

instance cycleRenewal_sFinite : SFinite (renewalMeasure cycleCostLaw) := by
  unfold renewalMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end NumberTheoryLean.RegenerationBandBounds

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ReturnCompletionAlgebra
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.TransitionKernels NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.CostReturnLaw NumberTheoryLean.CycleRegeneration
open NumberTheoryLean.InitialRegeneration

lemma firstReturn_succ_comp (n : ℕ) : firstReturn (n+1) = firstReturn n ∘ₖ costKilled := by
  unfold firstReturn
  rw [pow_succ]
  exact (Kernel.comp_assoc _ _ _).symm

lemma returnLaw_first_step : returnLaw = costCaptured + returnLaw ∘ₖ costKilled := by
  have hsplit : returnLaw = firstReturn 0+Kernel.sum (fun n => firstReturn (n+1)) := by
    ext z B hB
    rw [returnLaw,Kernel.sum_apply' _ _ hB,add_apply,Measure.add_apply,Kernel.sum_apply' _ _ hB]
    exact tsum_eq_zero_add' ENNReal.summable
  calc
    _ = firstReturn 0+Kernel.sum (fun n => firstReturn (n+1)) := hsplit
    _ = costCaptured+(Kernel.sum firstReturn) ∘ₖ costKilled := by
      congr 1
      · change costCaptured ∘ₖ (Kernel.id : Kernel OddCost OddCost) = costCaptured
        exact Kernel.comp_id _
      · rw [Kernel.comp_sum_left]
        apply congrArg Kernel.sum
        funext n
        exact firstReturn_succ_comp n
    _ = _ := rfl

lemma hitOrReturn_comp_captured : hitOrReturn ∘ₖ costCaptured = costCaptured := by
  classical
  have he : hitOrReturn ∘ₖ costCaptured = Kernel.id ∘ₖ costCaptured := by
    ext z B hB
    rw [Kernel.comp_apply' _ _ _ hB,Kernel.comp_apply' _ _ _ hB]
    apply lintegral_congr_ae
    have hae : ∀ᵐ y ∂costCaptured z, y ∈ returnSet := by
      rw [costCaptured,Kernel.restrict_apply]
      exact ae_restrict_mem returnSet_measurable
    filter_upwards [hae] with y hy
    rw [hitOrReturn,Kernel.piecewise_apply,ite_eq_left hy]
  simpa only [Kernel.id_comp] using he

lemma hitOrReturn_comp_killed : hitOrReturn ∘ₖ costKilled = returnLaw ∘ₖ costKilled := by
  classical
  ext z B hB
  rw [Kernel.comp_apply' _ _ _ hB,Kernel.comp_apply' _ _ _ hB]
  apply lintegral_congr_ae
  have hae : ∀ᵐ y ∂costKilled z, y ∉ returnSet := by
    rw [costKilled,Kernel.restrict_apply]
    exact ae_restrict_mem returnSet_measurable.compl
  filter_upwards [hae] with y hy
  rw [hitOrReturn,Kernel.piecewise_apply,ite_eq_right hy]

lemma complete_first_pair : hitOrReturn ∘ₖ pairedCostKernel = returnLaw := by
  rw [← costCaptured_add_costKilled,Kernel.comp_add_right,hitOrReturn_comp_captured,hitOrReturn_comp_killed]
  exact returnLaw_first_step.symm

lemma hitOrReturn_translation (z : OddCost) (a : ℝ) :
    (hitOrReturn z).map (shiftCost a) = hitOrReturn (shiftCost a z) := by
  classical
  have he : shiftCost a z ∈ returnSet ↔ z ∈ returnSet := Iff.rfl
  by_cases hz : z ∈ returnSet
  · rw [hitOrReturn,Kernel.piecewise_apply,ite_eq_left hz,Kernel.piecewise_apply,ite_eq_left (he.mpr hz),
      Kernel.id_apply,Kernel.id_apply]
    exact Measure.map_dirac' (shiftCost_measurable a) z
  · rw [hitOrReturn,Kernel.piecewise_apply,ite_eq_right hz,Kernel.piecewise_apply,
      ite_eq_right (fun h => hz (he.mp h))]
    exact returnLaw_translation z a

end Erdos970Dependency.MarkedVisits


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_MarkedCycleCompletion
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.TransitionKernels NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.CostReturnLaw NumberTheoryLean.CycleRegeneration
open NumberTheoryLean.InitialRegeneration NumberTheoryLean.RegenerationTails
open NumberTheoryLean.CycleCostLower NumberTheoryLean.FinitePathGeometry

lemma markContinuation_apply (z : MarkedOddCost) {B : Set MarkedOddCost} (hB : MeasurableSet B) :
    markContinuation z B = hitOrReturn z.2 {y | (z.1,y) ∈ B} := by
  rw [markContinuation,Kernel.map_apply' _ continueMarkUpdate_measurable _ hB,
    Kernel.prod_apply' _ _ _ (continueMarkUpdate_measurable hB),Kernel.id_apply,lintegral_dirac']
  · rfl
  · exact measurable_measure_prodMk_left (continueMarkUpdate_measurable hB)

lemma markContinuation_forget (z : MarkedOddCost) :
    (markContinuation z).map Prod.snd = hitOrReturn z.2 := by
  ext B hB
  rw [Measure.map_apply measurable_snd hB,markContinuation_apply _ (measurable_snd hB)]
  rfl

lemma completedMarked_forget (z : OddCost) :
    (completedMarkedKernel z).map Prod.snd = returnLaw z := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF measurable_snd,completedMarkedKernel,
    Kernel.lintegral_comp _ _ _ (g := fun y : MarkedOddCost => F y.2) (hF.comp measurable_snd)]
  have he (y : MarkedOddCost) : (∫⁻ t, F t.2 ∂markContinuation y) = ∫⁻ t, F t ∂hitOrReturn y.2 := by
    rw [← markContinuation_forget y,lintegral_map hF measurable_snd]
  simp_rw [he]
  have hJ : Measurable (fun y : OddCost => ∫⁻ t, F t ∂hitOrReturn y) := hF.lintegral_kernel
  calc
    _ = ∫⁻ y : OddCost, ∫⁻ t, F t ∂hitOrReturn y ∂pairedCostKernel z := by
      rw [← markedPair_forget z,lintegral_map hJ measurable_snd]
    _ = _ := by rw [← complete_first_pair,Kernel.lintegral_comp _ _ _ hF]

lemma completedMarked_regeneration (s : OddState) (hs : s.1 ≤ 3) (T : ℝ) :
    completedMarkedKernel (s,T) = completedMarkedKernel (regenerationState,T) := by
  ext B hB
  rw [completedMarkedKernel,Kernel.comp_apply' _ _ _ hB,Kernel.comp_apply' _ _ _ hB,
    markedPair_regeneration s hs T]

lemma markContinuation_preserves_mark (z : MarkedOddCost) :
    markContinuation z {y | y.1=true} = if z.1=true then 1 else 0 := by
  have hB : MeasurableSet {y : MarkedOddCost | y.1=true} := measurable_fst (measurableSet_singleton true)
  rw [markContinuation_apply _ hB]
  by_cases hz : z.1=true <;> simp [hz]

lemma completedMarked_mark_eq (z : OddCost) :
    completedMarkedKernel z {y | y.1=true} = markedPairKernel z {y | y.1=true} := by
  let B : Set MarkedOddCost := {y | y.1=true}
  have hB : MeasurableSet B := measurable_fst (measurableSet_singleton true)
  rw [completedMarkedKernel,Kernel.comp_apply' _ _ _ hB]
  calc
    _ = ∫⁻ y, B.indicator (fun _ => (1:ℝ≥0∞)) y ∂markedPairKernel z := by
      apply lintegral_congr
      intro y
      rw [markContinuation_preserves_mark]
      simp [B,Set.indicator_apply]
    _ = ∫⁻ _y in B, (1:ℝ≥0∞) ∂markedPairKernel z := lintegral_indicator hB _
    _ = _ := by simp [B]

lemma completedMarked_mark_mass (s : OddState) (hs : s.1 ≤ 3) (T : ℝ) :
    completedMarkedKernel (s,T) {y | y.1=true} = markProbability := by
  rw [completedMarked_mark_eq,markedPair_mark_mass s hs T]

lemma markContinuation_translation (z : MarkedOddCost) (a : ℝ) :
    (markContinuation z).map (markedShift a) = markContinuation (markedShift a z) := by
  ext B hB
  rw [Measure.map_apply (markedShift_measurable a) hB,
    markContinuation_apply _ ((markedShift_measurable a) hB),markContinuation_apply _ hB]
  change hitOrReturn z.2 {y | (z.1,shiftCost a y) ∈ B} =
    hitOrReturn (shiftCost a z.2) {y | (z.1,y) ∈ B}
  have hD : MeasurableSet {y : OddCost | (z.1,y) ∈ B} :=
    (measurable_const.prodMk measurable_id) hB
  rw [← hitOrReturn_translation z.2 a,Measure.map_apply (shiftCost_measurable a) hD]
  rfl

lemma completedMarked_translation (s : OddState) (T a : ℝ) :
    (completedMarkedKernel (s,T)).map (markedShift a) = completedMarkedKernel (s,T+a) := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (markedShift_measurable a),completedMarkedKernel,
    Kernel.lintegral_comp _ _ _ (g := fun y : MarkedOddCost => F (markedShift a y)) (hF.comp (markedShift_measurable a)),Kernel.lintegral_comp _ _ _ hF]
  have he (z : MarkedOddCost) : (∫⁻ y, F (markedShift a y) ∂markContinuation z) =
      ∫⁻ y, F y ∂markContinuation (markedShift a z) := by
    rw [← markContinuation_translation z a,lintegral_map hF (markedShift_measurable a)]
  simp_rw [he]
  have hJ : Measurable (fun z : MarkedOddCost => ∫⁻ y, F y ∂markContinuation z) := hF.lintegral_kernel
  rw [← markedPair_translation s T a,lintegral_map hJ (markedShift_measurable a)]

end Erdos970Dependency.MarkedVisits


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_MarkedCostSublaws
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.CostReturnLaw
open NumberTheoryLean.RegenerationTails NumberTheoryLean.CycleCostLower
open NumberTheoryLean.CycleCostMoments

lemma sourceMarkSet_measurable : MeasurableSet sourceMarkSet :=
  measurable_fst (measurableSet_singleton true)

lemma sourceCostProjection_measurable : Measurable sourceCostProjection :=
  measurable_snd.comp measurable_snd

lemma sourceCycle_cost_projection : sourceCycleLaw.map sourceCostProjection = cycleCostLaw := by
  rw [cycleCostLaw,← completedMarked_forget (regenerationState,0),
    Measure.map_map measurable_snd measurable_snd]
  rfl

lemma sourceCycle_mark_mass : sourceCycleLaw sourceMarkSet = markProbability :=
  completedMarked_mark_mass regenerationState (by norm_num [regenerationState]) 0

instance markedCostLaw_isFiniteMeasure : IsFiniteMeasure markedCostLaw := by
  unfold markedCostLaw
  first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply sourceCostProjection_measurable <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance unmarkedCostLaw_isFiniteMeasure : IsFiniteMeasure unmarkedCostLaw := by
  unfold unmarkedCostLaw
  first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply sourceCostProjection_measurable <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma markedCostLaw_add_unmarked : markedCostLaw+unmarkedCostLaw = cycleCostLaw := by
  calc
    _ = (sourceCycleLaw.restrict sourceMarkSet+sourceCycleLaw.restrict sourceMarkSetᶜ).map sourceCostProjection :=
      (Measure.map_add _ _ sourceCostProjection_measurable).symm
    _ = sourceCycleLaw.map sourceCostProjection := by rw [Measure.restrict_add_restrict_compl sourceMarkSet_measurable]
    _ = _ := sourceCycle_cost_projection

lemma markedCostLaw_mass : markedCostLaw univ = markProbability := by
  rw [markedCostLaw,Measure.map_apply sourceCostProjection_measurable MeasurableSet.univ,
    preimage_univ,Measure.restrict_apply MeasurableSet.univ,univ_inter]
  exact sourceCycle_mark_mass

lemma unmarkedCostLaw_mass : unmarkedCostLaw univ = 1-markProbability := by
  rw [unmarkedCostLaw,Measure.map_apply sourceCostProjection_measurable MeasurableSet.univ,
    preimage_univ,Measure.restrict_apply MeasurableSet.univ,univ_inter,
    measure_compl sourceMarkSet_measurable (measure_ne_top _ _),measure_univ,sourceCycle_mark_mass]

lemma markedCostLaw_le : markedCostLaw ≤ cycleCostLaw := by
  rw [← markedCostLaw_add_unmarked]
  exact Measure.le_add_right le_rfl

lemma unmarkedCostLaw_le : unmarkedCostLaw ≤ cycleCostLaw := by
  rw [← markedCostLaw_add_unmarked]
  exact Measure.le_add_left le_rfl

lemma source_marked_cost_lower : ∀ᵐ G ∂markedCostLaw, Real.log (4/3) ≤ G :=
  (ae_mono markedCostLaw_le) cycleCostLaw_lower

lemma source_unmarked_cost_lower : ∀ᵐ G ∂unmarkedCostLaw, Real.log (4/3) ≤ G :=
  (ae_mono unmarkedCostLaw_le) cycleCostLaw_lower

lemma source_marked_exponential_moments : ∃ eta : ℝ, 0 < eta ∧
    (∫⁻ G, ENNReal.ofReal (Real.exp (eta*G)) ∂markedCostLaw) < ∞ ∧
    (∫⁻ G, ENNReal.ofReal (Real.exp (eta*G)) ∂unmarkedCostLaw) < ∞ := by
  obtain ⟨eta,heta,hfin⟩ := cycle_cost_exponential_moment
  exact ⟨eta,heta,(lintegral_mono' markedCostLaw_le le_rfl).trans_lt hfin,
    (lintegral_mono' unmarkedCostLaw_le le_rfl).trans_lt hfin⟩

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_MarkedCycleFactorization
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.TransitionKernels NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.CostReturnLaw NumberTheoryLean.CycleRegeneration
open NumberTheoryLean.RegenerationTails

lemma completedMarked_ae_regeneration (z : OddCost) :
    ∀ᵐ y ∂completedMarkedKernel z, y.2 ∈ returnSet := by
  have he := returnLaw_ae_regeneration z
  rw [← completedMarked_forget z] at he
  exact (ae_map_iff measurable_snd.aemeasurable returnSet_measurable).mp he

lemma completedMarked_increment_law (s : OddState) (hs : s.1 ≤ 3) (T : ℝ) :
    (completedMarkedKernel (s,T)).map (markedShift (-T)) = sourceCycleLaw := by
  rw [completedMarked_regeneration s hs T]
  have ht := completedMarked_translation regenerationState 0 T
  simp only [zero_add] at ht
  rw [← ht,Measure.map_map (markedShift_measurable (-T)) (markedShift_measurable T)]
  have he : markedShift (-T) ∘ markedShift T = id := by
    funext z
    ext <;> simp [markedShift,shiftCost,Function.comp_apply,add_assoc]
  rw [he,Measure.map_id]
  rfl

lemma markCostProjection_measurable : Measurable markCostProjection :=
  measurable_fst.prodMk (measurable_snd.comp measurable_snd)

instance jointMarkCostLaw_isProbabilityMeasure : IsProbabilityMeasure jointMarkCostLaw := by
  unfold jointMarkCostLaw
  exact (Measure.isProbabilityMeasure_map_iff markCostProjection_measurable.aemeasurable).mpr inferInstance

lemma marked_cycle_increment_integral (z : OddCost) (hz : z ∈ returnSet)
    {F : Bool × ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y, F (y.1,y.2.2-z.2) ∂completedMarkedKernel z) = ∫⁻ u, F u ∂jointMarkCostLaw := by
  have he := congrArg (fun μ : Measure MarkedOddCost => ∫⁻ y, F (markCostProjection y) ∂μ)
    (completedMarked_increment_law z.1 hz z.2)
  rw [lintegral_map (f := fun y : MarkedOddCost => F (markCostProjection y))
    (hF.comp markCostProjection_measurable) (markedShift_measurable (-z.2))] at he
  rw [jointMarkCostLaw,lintegral_map hF markCostProjection_measurable]
  simpa only [markCostProjection,markedShift,shiftCost,sub_eq_add_neg] using he

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_UnmarkedTransform
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
open NumberTheoryLean.CostReturnLaw

lemma unmarked_mass_lt_one : unmarkedCostLaw univ < 1 := by
  have he := congrArg (fun μ : Measure ℝ => μ univ) markedCostLaw_add_unmarked
  have hsum : unmarkedCostLaw univ+markProbability=1 := by
    simpa only [Measure.add_apply,markedCostLaw_mass,measure_univ,add_comm] using he
  exact (ENNReal.lt_add_right (measure_ne_top _ _) markProbability_pos.ne').trans_eq hsum

lemma positive_cost_of_lower {G : ℝ} (hG : Real.log (4/3) ≤ G) : 0 ≤ G := by
  have h : 0 < Real.log (4/3:ℝ) := Real.log_pos (by norm_num)
  linarith

theorem exists_subcritical_unmarked_transform : ∃ eta : ℝ, 0 < eta ∧
    (∫⁻ G, ENNReal.ofReal (Real.exp (eta*G)) ∂unmarkedCostLaw) < 1 ∧
    (∫⁻ G, ENNReal.ofReal (Real.exp (eta*G)) ∂markedCostLaw) < ∞ := by
  obtain ⟨eta0,heta0,hMarked,hUnmarked⟩ := source_marked_exponential_moments
  let eta : ℕ → ℝ := fun n => eta0/((n:ℝ)+1)
  have heta (n : ℕ) : 0 < eta n := by dsimp [eta] <;> positivity
  have hle (n : ℕ) : eta n ≤ eta0 := by
    exact div_le_self heta0.le (by have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  have hseq : Tendsto eta atTop (𝓝 0) := by
    simpa only [eta,mul_one_div,mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul eta0
  let F : ℕ → ℝ → ℝ≥0∞ := fun n G => ENNReal.ofReal (Real.exp (eta n*G))
  let bound : ℝ → ℝ≥0∞ := fun G => ENNReal.ofReal (Real.exp (eta0*G))
  have hF (n : ℕ) : Measurable (F n) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul measurable_id))
  have hBound (n : ℕ) : F n ≤ᵐ[unmarkedCostLaw] bound := by
    filter_upwards [source_unmarked_cost_lower] with G hG
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (hle n) (positive_cost_of_lower hG)))
  have hLim : ∀ᵐ G ∂unmarkedCostLaw, Tendsto (fun n => F n G) atTop (𝓝 1) := by
    apply Eventually.of_forall
    intro G
    have he := (ENNReal.continuous_ofReal.tendsto _).comp
      ((Real.continuous_exp.tendsto _).comp (hseq.mul_const G))
    simpa only [F,Function.comp_def,zero_mul,Real.exp_zero,ENNReal.ofReal_one] using! he
  have hInt := tendsto_lintegral_of_dominated_convergence bound hF hBound hUnmarked.ne hLim
  have hInt' : Tendsto (fun n => ∫⁻ G, F n G ∂unmarkedCostLaw) atTop
      (𝓝 (unmarkedCostLaw univ)) := by simpa only [lintegral_one] using hInt
  obtain ⟨n,hn⟩ := (hInt'.eventually (gt_mem_nhds unmarked_mass_lt_one)).exists
  refine ⟨eta n,heta n,hn,?_⟩
  have hm : (∫⁻ G, ENNReal.ofReal (Real.exp (eta n*G)) ∂markedCostLaw) ≤
      ∫⁻ G, ENNReal.ofReal (Real.exp (eta0*G)) ∂markedCostLaw := by
    apply lintegral_mono_ae
    filter_upwards [source_marked_cost_lower] with G hG
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (hle n) (positive_cost_of_lower hG)))
  exact hm.trans_lt hMarked

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_GeometricCostLaws
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
open AbsorptionCutoff.Renewal

lemma costTransform_zero (μ : Measure ℝ) : costTransform μ 0 = μ univ := by simp [costTransform]

lemma costTransform_conv (μ ν : Measure ℝ) [SFinite ν] (eta : ℝ) :
    costTransform (μ ∗ ν) eta = costTransform μ eta*costTransform ν eta := by
  have hm : Measurable (fun G : ℝ => ENNReal.ofReal (Real.exp (eta*G))) := by fun_prop
  rw [costTransform,Measure.lintegral_conv hm]
  have hi (x : ℝ) : (∫⁻ y, ENNReal.ofReal (Real.exp (eta*(x+y))) ∂ν) =
      ENNReal.ofReal (Real.exp (eta*x))*costTransform ν eta := by
    simp_rw [mul_add,Real.exp_add,ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  simp_rw [hi]
  exact lintegral_mul_const _ hm

lemma conv_mass (μ ν : Measure ℝ) [SFinite ν] : (μ ∗ ν) univ = μ univ*ν univ := by
  simpa only [costTransform_zero] using costTransform_conv μ ν 0

lemma convPow_costTransform (μ : Measure ℝ) [SFinite μ] (eta : ℝ) (n : ℕ) :
    costTransform (convPow μ n) eta = (costTransform μ eta)^n := by
  induction n with
  | zero => simp [convPow_zero,costTransform]
  | succ n ih => rw [convPow_succ,costTransform_conv,ih,pow_succ]

lemma renewal_costTransform (μ : Measure ℝ) [SFinite μ] (eta : ℝ) :
    costTransform (renewalMeasure μ) eta = (1-costTransform μ eta)⁻¹ := by
  rw [costTransform,renewalMeasure,lintegral_sum_measure]
  change (∑' n, costTransform (convPow μ n) eta) = _
  simp_rw [convPow_costTransform]
  exact ENNReal.tsum_geometric _

lemma unmarkedPotential_mass : unmarkedPotential univ = markProbability⁻¹ := by
  have he := renewal_costTransform unmarkedCostLaw 0
  rw [costTransform_zero,costTransform_zero,unmarkedCostLaw_mass,
    ENNReal.sub_sub_cancel (by simp : (1:ℝ≥0∞) ≠ ∞) markProbability_lt_one.le] at he
  exact he

instance unmarkedPotential_isFiniteMeasure : IsFiniteMeasure unmarkedPotential := by
  constructor
  rw [unmarkedPotential_mass]
  exact lt_top_iff_ne_top.mpr (ENNReal.inv_ne_top.mpr markProbability_pos.ne')

instance geometricMarkedCostLaw_isProbabilityMeasure : IsProbabilityMeasure geometricMarkedCostLaw := by
  constructor
  rw [geometricMarkedCostLaw,conv_mass,markedCostLaw_mass,unmarkedPotential_mass]
  exact ENNReal.mul_inv_cancel markProbability_pos.ne' (lt_trans markProbability_lt_one (by simp)).ne

lemma geometricMarked_costTransform (eta : ℝ) :
    costTransform geometricMarkedCostLaw eta =
      costTransform markedCostLaw eta*(1-costTransform unmarkedCostLaw eta)⁻¹ := by
  rw [geometricMarkedCostLaw,costTransform_conv,unmarkedPotential,renewal_costTransform]

lemma conv_ae_lower {μ ν : Measure ℝ} [SFinite μ] [SFinite ν] {a b : ℝ}
    (hμ : ∀ᵐ x ∂μ, a ≤ x) (hν : ∀ᵐ y ∂ν, b ≤ y) :
    ∀ᵐ z ∂(μ ∗ ν), a+b ≤ z := by
  rw [Measure.conv]
  apply (ae_map_iff measurable_add.aemeasurable measurableSet_Ici).mpr
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le measurable_const measurable_add)).mpr
  filter_upwards [hμ] with x hx
  filter_upwards [hν] with y hy
  linarith

lemma convPow_ae_nonneg (μ : Measure ℝ) [SFinite μ] (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (n : ℕ) :
    ∀ᵐ x ∂convPow μ n, 0 ≤ x := by
  induction n with
  | zero => simp [convPow_zero]
  | succ n ih =>
    rw [convPow_succ]
    simpa only [zero_add] using conv_ae_lower ih hμ

lemma unmarkedPotential_ae_nonneg : ∀ᵐ G ∂unmarkedPotential, 0 ≤ G := by
  rw [unmarkedPotential,renewalMeasure,Measure.ae_sum_iff]
  intro n
  apply convPow_ae_nonneg
  filter_upwards [source_unmarked_cost_lower] with G hG
  exact positive_cost_of_lower hG

lemma geometricMarked_cost_lower : ∀ᵐ G ∂geometricMarkedCostLaw, Real.log (4/3) ≤ G := by
  rw [geometricMarkedCostLaw]
  simpa only [add_zero] using conv_ae_lower source_marked_cost_lower unmarkedPotential_ae_nonneg

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_MarkedCycleWords
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory ENNReal
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.CostReturnLaw

lemma branchCostLaw_true : branchCostLaw true = markedCostLaw := rfl

lemma false_mark_set : {z : MarkedOddCost | z.1=false} = sourceMarkSetᶜ := by
  ext z
  cases z.1 <;> simp [sourceMarkSet]

lemma branchCostLaw_false : branchCostLaw false = unmarkedCostLaw := by
  rw [branchCostLaw,false_mark_set]
  rfl

instance branchCostLaw_isFiniteMeasure (b : Bool) : IsFiniteMeasure (branchCostLaw b) := by
  unfold branchCostLaw
  first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply sourceCostProjection_measurable <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma cycleBranch_sum : cycleBranchKernel true+cycleBranchKernel false = returnLaw := by
  ext z : 1
  rw [add_apply]
  unfold cycleBranchKernel
  rw [Kernel.map_apply _ measurable_snd,Kernel.map_apply _ measurable_snd,
    Kernel.restrict_apply,Kernel.restrict_apply]
  change ((completedMarkedKernel z).restrict {y | y.1=true}).map Prod.snd +
    ((completedMarkedKernel z).restrict {y | y.1=false}).map Prod.snd = returnLaw z
  rw [false_mark_set]
  change ((completedMarkedKernel z).restrict sourceMarkSet).map Prod.snd +
    ((completedMarkedKernel z).restrict sourceMarkSetᶜ).map Prod.snd = returnLaw z
  rw [← Measure.map_add _ _ measurable_snd,Measure.restrict_add_restrict_compl sourceMarkSet_measurable,
    completedMarked_forget]

lemma cycleBranch_ae_regeneration (b : Bool) (z : OddCost) :
    ∀ᵐ y ∂cycleBranchKernel b z, y ∈ returnSet := by
  rw [cycleBranchKernel,Kernel.map_apply _ measurable_snd,Kernel.restrict_apply]
  apply (ae_map_iff measurable_snd.aemeasurable returnSet_measurable).mpr
  exact ae_restrict_of_ae (completedMarked_ae_regeneration z)

lemma cycleBranch_increment_integral (b : Bool) (z : OddCost) (hz : z ∈ returnSet)
    {H : ℝ → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ y, H (y.2-z.2) ∂cycleBranchKernel b z) = ∫⁻ G, H G ∂branchCostLaw b := by
  let F : Bool × ℝ → ℝ≥0∞ := fun x => if x.1=b then H x.2 else 0
  have hF : Measurable F := Measurable.ite (measurable_fst (measurableSet_singleton b))
    (hH.comp measurable_snd) measurable_const
  have hB : MeasurableSet {y : MarkedOddCost | y.1=b} := measurable_fst (measurableSet_singleton b)
  have hleft : (∫⁻ y, H (y.2-z.2) ∂cycleBranchKernel b z) =
      ∫⁻ y, F (y.1,y.2.2-z.2) ∂completedMarkedKernel z := by
    rw [cycleBranchKernel,Kernel.map_apply _ measurable_snd,Kernel.restrict_apply,
      lintegral_map (f := fun y : OddCost => H (y.2-z.2)) (hH.comp (measurable_snd.sub measurable_const)) measurable_snd]
    change (∫⁻ y in {a : MarkedOddCost | a.1=b}, H (y.2.2-z.2) ∂completedMarkedKernel z) = _
    rw [← lintegral_indicator hB]
    apply lintegral_congr
    intro y
    simp [F,Set.indicator_apply]
  have hright : (∫⁻ G, H G ∂branchCostLaw b) = ∫⁻ u, F u ∂jointMarkCostLaw := by
    rw [branchCostLaw,lintegral_map hH sourceCostProjection_measurable,
      ← lintegral_indicator hB,jointMarkCostLaw,lintegral_map hF markCostProjection_measurable]
    apply lintegral_congr
    intro y
    simp [F,sourceCostProjection,markCostProjection,Set.indicator_apply]
  rw [hleft,hright,marked_cycle_increment_integral z hz hF]

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory ENNReal
open AbsorptionCutoff.Renewal
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.CostReturnLaw

lemma cycleBranch_mass (b : Bool) (z : OddCost) (hz : z ∈ returnSet) :
    cycleBranchKernel b z univ = branchCostLaw b univ := by
  simpa only [lintegral_one] using cycleBranch_increment_integral b z hz (H := fun _ => 1) measurable_const

lemma cycleBranch_true_mass (z : OddCost) (hz : z ∈ returnSet) :
    cycleBranchKernel true z univ = markProbability := by
  rw [cycleBranch_mass true z hz,branchCostLaw_true,markedCostLaw_mass]

lemma cycleBranch_pow_ae_regeneration (b : Bool) (n : ℕ) (z : OddCost) (hz : z ∈ returnSet) :
    ∀ᵐ y ∂(cycleBranchKernel b ^ n) z, y ∈ returnSet := by
  cases n with
  | zero =>
    change ∀ᵐ y ∂Measure.dirac z, y ∈ returnSet
    exact (ae_dirac_iff returnSet_measurable).mpr hz
  | succ n =>
    rw [pow_succ']
    change ∀ᵐ y ∂(cycleBranchKernel b ∘ₖ (cycleBranchKernel b ^ n)) z, y ∈ returnSet
    exact Kernel.ae_comp_of_ae_ae returnSet_measurable (Eventually.of_forall (cycleBranch_ae_regeneration b))

lemma branch_cumulative_cost_lintegral (b : Bool) (n : ℕ) (z : OddCost) (hz : z ∈ returnSet)
    {H : ℝ → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ y, H y.2 ∂(cycleBranchKernel b ^ n) z) =
      ∫⁻ G, H (z.2+G) ∂convPow (branchCostLaw b) n := by
  induction n generalizing z with
  | zero =>
    change (∫⁻ y, H y.2 ∂Measure.dirac z) = _
    rw [lintegral_dirac' z (f := fun y : OddCost => H y.2) (hH.comp measurable_snd),convPow_zero,
      lintegral_dirac' 0 (f := fun G : ℝ => H (z.2+G)) (hH.comp (measurable_const.add measurable_id)),add_zero]
  | succ n ih =>
    have hp : cycleBranchKernel b ^ (n+1) = (cycleBranchKernel b ^ n) ∘ₖ cycleBranchKernel b := pow_succ _ _
    rw [hp,Kernel.lintegral_comp _ _ _ (g := fun y : OddCost => H y.2) (hH.comp measurable_snd)]
    let F : ℝ → ℝ≥0∞ := fun t => ∫⁻ G, H (z.2+t+G) ∂convPow (branchCostLaw b) n
    have hF : Measurable F := (hH.comp ((measurable_const.add measurable_fst).add measurable_snd)).lintegral_prod_right'
    calc
      _ = ∫⁻ y, F (y.2-z.2) ∂cycleBranchKernel b z := by
        apply lintegral_congr_ae
        filter_upwards [cycleBranch_ae_regeneration b z] with y hy
        rw [ih y hy]
        apply lintegral_congr
        intro G
        congr 1
        ring
      _ = ∫⁻ t, F t ∂branchCostLaw b := cycleBranch_increment_integral b z hz hF
      _ = _ := by
        rw [convPow_succ',Measure.lintegral_conv (f := fun G : ℝ => H (z.2+G))
          (hH.comp (measurable_const.add measurable_id))]
        apply lintegral_congr
        intro t
        apply lintegral_congr
        intro G
        congr 1
        ring

lemma branch_cumulative_cost_law (b : Bool) (n : ℕ) (z : OddCost) (hz : z ∈ returnSet) :
    ((cycleBranchKernel b ^ n) z).map (fun y => y.2-z.2) = convPow (branchCostLaw b) n := by
  apply Measure.ext_of_lintegral
  intro H hH
  rw [lintegral_map (g := fun y : OddCost => y.2-z.2) hH (measurable_snd.sub measurable_const),
    branch_cumulative_cost_lintegral b n z hz (H := fun G => H (G-z.2))
      (hH.comp (measurable_id.sub measurable_const))]
  simp only [add_sub_cancel_left]

lemma branch_word_ae_regeneration (first rest : Bool) (n : ℕ) (z : OddCost) :
    ∀ᵐ y ∂((cycleBranchKernel rest ^ n) ∘ₖ cycleBranchKernel first) z, y ∈ returnSet := by
  apply Kernel.ae_comp_of_ae_ae returnSet_measurable
  filter_upwards [cycleBranch_ae_regeneration first z] with y hy
  exact cycleBranch_pow_ae_regeneration rest n y hy

lemma branch_word_cost_lintegral (first rest : Bool) (n : ℕ) (z : OddCost) (hz : z ∈ returnSet)
    {H : ℝ → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ y, H y.2 ∂((cycleBranchKernel rest ^ n) ∘ₖ cycleBranchKernel first) z) =
      ∫⁻ G, H (z.2+G) ∂(branchCostLaw first ∗ convPow (branchCostLaw rest) n) := by
  rw [Kernel.lintegral_comp _ _ _ (g := fun y : OddCost => H y.2) (hH.comp measurable_snd)]
  let F : ℝ → ℝ≥0∞ := fun t => ∫⁻ G, H (z.2+t+G) ∂convPow (branchCostLaw rest) n
  have hF : Measurable F := (hH.comp ((measurable_const.add measurable_fst).add measurable_snd)).lintegral_prod_right'
  calc
    _ = ∫⁻ y, F (y.2-z.2) ∂cycleBranchKernel first z := by
      apply lintegral_congr_ae
      filter_upwards [cycleBranch_ae_regeneration first z] with y hy
      rw [branch_cumulative_cost_lintegral rest n y hy hH]
      apply lintegral_congr
      intro G
      congr 1
      ring
    _ = ∫⁻ t, F t ∂branchCostLaw first := cycleBranch_increment_integral first z hz hF
    _ = _ := by
      rw [Measure.lintegral_conv (f := fun G : ℝ => H (z.2+G)) (hH.comp (measurable_const.add measurable_id))]
      apply lintegral_congr
      intro t
      apply lintegral_congr
      intro G
      congr 1
      ring

lemma branch_word_cost_law (first rest : Bool) (n : ℕ) (z : OddCost) (hz : z ∈ returnSet) :
    (((cycleBranchKernel rest ^ n) ∘ₖ cycleBranchKernel first) z).map (fun y => y.2-z.2) =
      branchCostLaw first ∗ convPow (branchCostLaw rest) n := by
  apply Measure.ext_of_lintegral
  intro H hH
  rw [lintegral_map (g := fun y : OddCost => y.2-z.2) hH (measurable_snd.sub measurable_const),
    branch_word_cost_lintegral first rest n z hz (H := fun G => H (G-z.2))
      (hH.comp (measurable_id.sub measurable_const))]
  simp only [add_sub_cancel_left]

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_MarkedReturnKernel
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory ENNReal
open AbsorptionCutoff.Renewal
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.CostReturnLaw
open NumberTheoryLean.RegenerationTails

lemma nextMarkWeight_measurable : Measurable nextMarkWeight :=
  (cycleBranchKernel true).measurable_coe MeasurableSet.univ

lemma markProbability_ne_top : markProbability ≠ ∞ :=
  (lt_trans markProbability_lt_one (by simp)).ne

lemma actualWaitingTerm_eq (n : ℕ) (z : OddCost) (hz : z ∈ returnSet) :
    actualWaitingTerm n z = markProbability • convPow unmarkedCostLaw n := by
  have hw : nextMarkWeight =ᵐ[(cycleBranchKernel false ^ n) z] fun _ => markProbability := by
    filter_upwards [cycleBranch_pow_ae_regeneration false n z hz] with y hy
    exact cycleBranch_true_mass y hy
  have hmap : Measurable (fun y : OddCost => y.2-z.2) := measurable_snd.sub measurable_const
  rw [actualWaitingTerm,withDensity_congr_ae hw,withDensity_const,Measure.map_smul,
    branch_cumulative_cost_law false n z hz,branchCostLaw_false]

lemma actualSpacingTerm_eq (n : ℕ) (z : OddCost) (hz : z ∈ returnSet) :
    actualSpacingTerm n z = markedCostLaw ∗ convPow unmarkedCostLaw n := by
  have hw : nextMarkWeight =ᵐ[((cycleBranchKernel false ^ n) ∘ₖ cycleBranchKernel true) z]
      fun _ => markProbability := by
    filter_upwards [branch_word_ae_regeneration true false n z] with y hy
    exact cycleBranch_true_mass y hy
  have hmap : Measurable (fun y : OddCost => y.2-z.2) := measurable_snd.sub measurable_const
  rw [actualSpacingTerm,withDensity_congr_ae hw,withDensity_const,Measure.map_smul,smul_smul,
    ENNReal.inv_mul_cancel markProbability_pos.ne' markProbability_ne_top,one_smul,
    branch_word_cost_law true false n z hz,branchCostLaw_true,branchCostLaw_false]

lemma conv_sum_right (μ : Measure ℝ) (ν : ℕ → Measure ℝ) [∀ n, SFinite (ν n)] :
    μ ∗ Measure.sum ν = Measure.sum (fun n => μ ∗ ν n) := by
  unfold Measure.conv
  rw [Measure.prod_sum_right,Measure.map_sum measurable_add.aemeasurable]

lemma actualWaitingLaw_eq (z : OddCost) (hz : z ∈ returnSet) :
    actualWaitingLaw z = markProbability • unmarkedPotential := by
  ext B hB
  rw [actualWaitingLaw,Measure.sum_apply _ hB]
  simp_rw [actualWaitingTerm_eq _ z hz,Measure.smul_apply,smul_eq_mul]
  rw [unmarkedPotential,renewalMeasure,Measure.sum_apply _ hB,ENNReal.tsum_mul_left]

lemma actualSpacingLaw_eq (z : OddCost) (hz : z ∈ returnSet) :
    actualSpacingLaw z = geometricMarkedCostLaw := by
  rw [actualSpacingLaw,geometricMarkedCostLaw,unmarkedPotential,renewalMeasure,conv_sum_right]
  apply congrArg Measure.sum
  funext n
  exact actualSpacingTerm_eq n z hz

lemma actualWaitingLaw_mass (z : OddCost) (hz : z ∈ returnSet) : actualWaitingLaw z univ = 1 := by
  rw [actualWaitingLaw_eq z hz,Measure.smul_apply,smul_eq_mul,unmarkedPotential_mass]
  exact ENNReal.mul_inv_cancel markProbability_pos.ne' markProbability_ne_top

lemma actualSpacingLaw_mass (z : OddCost) (hz : z ∈ returnSet) : actualSpacingLaw z univ = 1 := by
  rw [actualSpacingLaw_eq z hz]
  exact measure_univ

instance firstMarkWaitingLaw_isProbabilityMeasure : IsProbabilityMeasure firstMarkWaitingLaw :=
  ⟨actualWaitingLaw_mass _ (by norm_num [returnSet,NumberTheoryLean.PairedHitting.pairedRegeneration,regenerationState])⟩

instance markedSpacingLaw_isProbabilityMeasure : IsProbabilityMeasure markedSpacingLaw :=
  ⟨actualSpacingLaw_mass _ (by norm_num [returnSet,NumberTheoryLean.PairedHitting.pairedRegeneration,regenerationState])⟩

lemma markedSpacingLaw_eq : markedSpacingLaw = geometricMarkedCostLaw :=
  actualSpacingLaw_eq _ (by norm_num [returnSet,NumberTheoryLean.PairedHitting.pairedRegeneration,regenerationState])

lemma markedSpacing_cost_lower : ∀ᵐ G ∂markedSpacingLaw, Real.log (4/3) ≤ G := by
  rw [markedSpacingLaw_eq]
  exact geometricMarked_cost_lower

lemma firstMarkWaiting_costTransform (eta : ℝ) : costTransform firstMarkWaitingLaw eta =
    markProbability*(1-costTransform unmarkedCostLaw eta)⁻¹ := by
  rw [firstMarkWaitingLaw,actualWaitingLaw_eq _ (by norm_num [returnSet,NumberTheoryLean.PairedHitting.pairedRegeneration,regenerationState])]
  unfold costTransform
  rw [lintegral_smul_measure]
  change markProbability*costTransform unmarkedPotential eta = _
  rw [unmarkedPotential,renewal_costTransform]
  rfl

lemma marked_waiting_common_exponential_moment : ∃ eta : ℝ, 0 < eta ∧
    costTransform firstMarkWaitingLaw eta < ∞ ∧ costTransform markedSpacingLaw eta < ∞ := by
  obtain ⟨eta,heta,hU,hM⟩ := exists_subcritical_unmarked_transform
  have hi : (1-costTransform unmarkedCostLaw eta)⁻¹ < ∞ :=
    lt_top_iff_ne_top.mpr (ENNReal.inv_ne_top.mpr (tsub_pos_iff_lt.mpr hU).ne')
  refine ⟨eta,heta,?_,?_⟩
  · rw [firstMarkWaiting_costTransform]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr markProbability_ne_top) hi
  · rw [markedSpacingLaw_eq,geometricMarked_costTransform]
    exact ENNReal.mul_lt_top hM hi

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_MarkedBeginningKernel
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory ENNReal
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.CostReturnLaw

lemma rawBeginning_ae_regeneration (z : OddCost) : ∀ᵐ y ∂rawBeginningKernel z, y ∈ returnSet := by
  rw [rawBeginningKernel,Kernel.sum_apply,Measure.ae_sum_iff]
  intro n
  exact branch_word_ae_regeneration true false n z

lemma rawBeginning_project_actual (z : OddCost) (hz : z ∈ returnSet) :
    (rawBeginningKernel z).map (fun y => y.2-z.2) = actualSpacingLaw z := by
  rw [rawBeginningKernel,Kernel.sum_apply,
    Measure.map_sum (f := fun y : OddCost => y.2-z.2) (measurable_snd.sub measurable_const).aemeasurable,actualSpacingLaw]
  apply congrArg Measure.sum
  funext n
  rw [actualSpacingTerm_eq n z hz,branch_word_cost_law true false n z hz,
    branchCostLaw_true,branchCostLaw_false]

lemma rawBeginning_cost_law (z : OddCost) (hz : z ∈ returnSet) :
    (rawBeginningKernel z).map (fun y => y.2-z.2) = markedSpacingLaw := by
  rw [rawBeginning_project_actual z hz,actualSpacingLaw_eq z hz,markedSpacingLaw_eq]

lemma markedBeginning_map_state (z : RegCost) :
    (markedBeginningKernel z).map (Subtype.val : RegCost → OddCost) = rawBeginningKernel z.1 := by
  calc
    _ = (rawBeginningKernel z.1).restrict returnSet := by
      change (((rawBeginningKernel z.1).comap (Subtype.val : RegCost → OddCost)).map Subtype.val) = _
      exact map_comap_subtype_coe (μ := rawBeginningKernel z.1) returnSet_measurable
    _ = _ := Measure.restrict_eq_self_of_ae_mem (rawBeginning_ae_regeneration z.1)

lemma markedBeginning_increment_law (z : RegCost) :
    (markedBeginningKernel z).map (fun y => beginningCost y-beginningCost z) = markedSpacingLaw := by
  calc
    _ = ((markedBeginningKernel z).map (Subtype.val : RegCost → OddCost)).map (fun y => y.2-z.1.2) :=
      (Measure.map_map (measurable_snd.sub measurable_const) measurable_subtype_coe).symm
    _ = (rawBeginningKernel z.1).map (fun y => y.2-z.1.2) := by rw [markedBeginning_map_state]
    _ = _ := rawBeginning_cost_law z.1 z.2

instance markedClockKernel_isMarkovKernel : IsMarkovKernel markedClockKernel :=
  Kernel.IsMarkovKernel.map _ measurable_add

lemma markedClockKernel_apply (x : ℝ) : markedClockKernel x = markedSpacingLaw.map (fun G => x+G) := by
  ext B hB
  rw [markedClockKernel,Kernel.map_apply' _ measurable_add _ hB,
    Kernel.prod_apply' _ _ _ (measurable_add hB),Kernel.id_apply,lintegral_dirac']
  · rw [Measure.map_apply (f := fun G : ℝ => x+G) (measurable_const.add measurable_id) hB]
    rfl
  · exact measurable_measure_prodMk_left (measurable_add hB)

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_ClockTailReward
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory ENNReal
open AbsorptionCutoff.Renewal
open NumberTheoryLean.KernelPotential

instance markedClock_pow_isMarkovKernel (n : ℕ) : IsMarkovKernel (markedClockKernel ^ n) := by
  induction n with
  | zero => change IsMarkovKernel (Kernel.id : Kernel ℝ ℝ); infer_instance
  | succ n ih =>
    rw [pow_succ']
    change IsMarkovKernel (markedClockKernel ∘ₖ (markedClockKernel ^ n))
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma markedClock_increment_lower (x : ℝ) :
    ∀ᵐ y ∂markedClockKernel x, x+Real.log (4/3) ≤ y := by
  rw [markedClockKernel_apply]
  apply (ae_map_iff (measurable_const.add measurable_id).aemeasurable measurableSet_Ici).mpr
  filter_upwards [markedSpacing_cost_lower] with G hG
  change x+Real.log (4/3) ≤ x+G
  linarith

lemma markedClock_minimum_pos : (0:ℝ) < Real.log (4/3) := Real.log_pos (by norm_num)

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory ENNReal
open AbsorptionCutoff.Renewal
open NumberTheoryLean.KernelPotential

instance clockBelow_isFiniteKernel (v : ℝ) : IsFiniteKernel (clockBelow v) := by unfold clockBelow; infer_instance
instance clockOver_isFiniteKernel (v H : ℝ) : IsFiniteKernel (clockOver v H) := by unfold clockOver; infer_instance

instance clockBelow_pow_isFiniteKernel (v : ℝ) (n : ℕ) : IsFiniteKernel (clockBelow v ^ n) := by
  induction n with
  | zero => change IsFiniteKernel (Kernel.id : Kernel ℝ ℝ); infer_instance
  | succ n ih => rw [pow_succ']; change IsFiniteKernel (clockBelow v ∘ₖ (clockBelow v ^ n)); infer_instance

instance clockOverReward_isFiniteKernel (v H : ℝ) : IsFiniteKernel (clockOverReward v H) := by
  classical
  unfold clockOverReward
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma clockBelow_ae_lt (v x : ℝ) : ∀ᵐ y ∂clockBelow v x, y < v := by
  rw [clockBelow,Kernel.restrict_apply]
  exact ae_restrict_mem measurableSet_Iio

lemma clockBelow_pow_ae_lt {v : ℝ} (hv : 0 < v) (n : ℕ) : ∀ᵐ y ∂(clockBelow v ^ n) 0, y < v := by
  cases n with
  | zero => change ∀ᵐ y ∂Measure.dirac (0:ℝ), y < v; exact (ae_dirac_iff measurableSet_Iio).mpr hv
  | succ n =>
    rw [pow_succ']
    change ∀ᵐ y ∂(clockBelow v ∘ₖ (clockBelow v ^ n)) 0, y < v
    exact Kernel.ae_comp_of_ae_ae measurableSet_Iio (Eventually.of_forall (clockBelow_ae_lt v))

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_ClockWindowPassage
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory ENNReal
open NumberTheoryLean.KernelPotential

instance clockAtOrAbove_isFiniteKernel (v : ℝ) : IsFiniteKernel (clockAtOrAbove v) := by
  unfold clockAtOrAbove; infer_instance

lemma clockAtOrAbove_add_below (v : ℝ) : clockAtOrAbove v + clockBelow v = markedClockKernel := by
  ext x : 1
  change (markedClockKernel x).restrict (Ici v) + (markedClockKernel x).restrict (Iio v) = _
  simpa only [compl_Ici] using Measure.restrict_add_restrict_compl (μ := markedClockKernel x) measurableSet_Ici

lemma clockBelow_increment_lower (v x : ℝ) :
    ∀ᵐ y ∂clockBelow v x, x+Real.log (4/3) ≤ y := by
  rw [clockBelow,Kernel.restrict_apply]
  exact ae_restrict_of_ae (markedClock_increment_lower x)

lemma clockBelow_pow_lower (v x : ℝ) (n : ℕ) :
    ∀ᵐ y ∂(clockBelow v ^ n) x, x+(n:ℝ)*Real.log (4/3) ≤ y := by
  induction n with
  | zero =>
    simp only [pow_zero,Nat.cast_zero,zero_mul,add_zero]
    exact (ae_dirac_iff measurableSet_Ici).mpr le_rfl
  | succ n ih =>
    rw [pow_succ']
    change ∀ᵐ y ∂(clockBelow v ∘ₖ (clockBelow v ^ n)) x, _ ≤ y
    apply Kernel.ae_comp_of_ae_ae measurableSet_Ici
    filter_upwards [ih] with y hy
    filter_upwards [clockBelow_increment_lower v y] with z hz
    push_cast
    nlinarith

lemma clockBelow_mass_eq_zero {v : ℝ} (hv : 0 < v) {n : ℕ}
    (hn : v ≤ (n:ℝ)*Real.log (4/3)) : (clockBelow v ^ n) 0 univ = 0 := by
  have hfalse : ∀ᵐ y ∂(clockBelow v ^ n) 0, False := by
    filter_upwards [clockBelow_pow_lower v 0 n,clockBelow_pow_ae_lt hv n] with y hy hvy
    linarith
  simpa only [ae_iff,not_false_eq_true,ofPred_true] using hfalse

lemma clockBelow_survival_tendsto_zero {v : ℝ} (hv : 0 < v) :
    Tendsto (fun n : ℕ => (clockBelow v ^ n) 0 univ) atTop (𝓝 0) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (v/Real.log (4/3))
  have hNc : v ≤ (N:ℝ)*Real.log (4/3) :=
    (div_lt_iff₀ markedClock_minimum_pos).mp hN |>.le
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  exact (clockBelow_mass_eq_zero hv (hNc.trans (mul_le_mul_of_nonneg_right
    (by exact_mod_cast hn) markedClock_minimum_pos.le))).symm

lemma clockExit_mass_step (v : ℝ) (n : ℕ) :
    (clockAtOrAbove v ∘ₖ (clockBelow v ^ n)) 0 univ +
      (clockBelow v ^ (n+1)) 0 univ = (clockBelow v ^ n) 0 univ := by
  have hp : clockBelow v ^ (n+1) = clockBelow v ∘ₖ (clockBelow v ^ n) := pow_succ' _ _
  calc
    _ = ((clockAtOrAbove v+clockBelow v) ∘ₖ (clockBelow v ^ n)) 0 univ := by
      rw [Kernel.comp_add_left,_root_.add_apply,Measure.add_apply,hp]
    _ = (markedClockKernel ∘ₖ (clockBelow v ^ n)) 0 univ := by rw [clockAtOrAbove_add_below]
    _ = _ := by rw [Kernel.comp_apply' _ _ _ MeasurableSet.univ]; simp

lemma clockExit_finite_mass (v : ℝ) (n : ℕ) :
    (clockBelow v ^ n) 0 univ +
      ∑ k ∈ Finset.range n, (clockAtOrAbove v ∘ₖ (clockBelow v ^ k)) 0 univ = 1 := by
  induction n with
  | zero => change (Measure.dirac (0:ℝ)) univ + 0 = 1; simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    calc
      _ = (∑ k ∈ Finset.range n, (clockAtOrAbove v ∘ₖ (clockBelow v ^ k)) 0 univ)+
        ((clockAtOrAbove v ∘ₖ (clockBelow v ^ n)) 0 univ+(clockBelow v ^ (n+1)) 0 univ) := by ac_rfl
      _ = _ := by rw [clockExit_mass_step]; simpa only [add_comm] using ih

lemma clockExit_mass_one {v : ℝ} (hv : 0 < v) :
    (potential (clockAtOrAbove v) (clockBelow v)) 0 univ = 1 := by
  rw [potential,Kernel.sum_apply' _ _ MeasurableSet.univ]
  have h := (clockBelow_survival_tendsto_zero hv).add (ENNReal.tendsto_nat_tsum
    (fun n => (clockAtOrAbove v ∘ₖ (clockBelow v ^ n)) 0 univ))
  simp only [zero_add,clockExit_finite_mass] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

instance clockWindow_isFiniteKernel (v H : ℝ) : IsFiniteKernel (clockWindow v H) := by
  unfold clockWindow; infer_instance

lemma clockWindow_add_over {v H : ℝ} (hH : 0 ≤ H) :
    clockWindow v H+clockOver v H = clockAtOrAbove v := by
  ext x : 1
  change (markedClockKernel x).restrict (Icc v (v+H))+
    (markedClockKernel x).restrict (Ioi (v+H)) = (markedClockKernel x).restrict (Ici v)
  have hd : Disjoint (Icc v (v+H)) (Ioi (v+H)) := by
    rw [disjoint_left]
    intro y hy hz
    exact (not_lt_of_ge hy.2) hz
  rw [← Measure.restrict_union hd measurableSet_Ioi]
  congr 1
  ext y
  simp only [mem_union,mem_Icc,mem_Ioi,mem_Ici]
  constructor
  · rintro (h|h) <;> linarith
  · intro h
    by_cases hy : y ≤ v+H
    · exact Or.inl ⟨h,hy⟩
    · exact Or.inr (lt_of_not_ge hy)

theorem clockWindowHit_add_overshoot {v H : ℝ} (hv : 0 < v) (hH : 0 ≤ H) :
    clockWindowHit v H+clockOvershoot v H = 1 := by
  rw [clockWindowHit,clockOvershoot,← Measure.add_apply,← _root_.add_apply,
    ← potential_add,clockWindow_add_over hH]
  exact clockExit_mass_one hv

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_BeginningWindowTransport
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory ENNReal
open NumberTheoryLean.KernelPotential

section Projection
variable {α : Type*} [MeasurableSpace α] {f : α → ℝ} (hf : Measurable f)
include hf

lemma costProjection_comp {K B : Kernel α α} {L C : Kernel ℝ ℝ}
    (hK : ∀ z, (K z).map f = L (f z)) (hB : ∀ z, (B z).map f = C (f z)) (z : α) :
    ((B ∘ₖ K) z).map f = (C ∘ₖ L) (f z) := by
  ext S hS
  rw [Measure.map_apply hf hS,Kernel.comp_apply' _ _ _ (hf hS),Kernel.comp_apply' _ _ _ hS]
  have hi (y : α) : B y (f ⁻¹' S) = C (f y) S := by
    rw [← Measure.map_apply hf hS,hB y]
  simp_rw [hi]
  rw [← lintegral_map (g := f) (C.measurable_coe hS) hf,hK z]

lemma costProjection_power {K : Kernel α α} {L : Kernel ℝ ℝ}
    (hK : ∀ z, (K z).map f = L (f z)) (n : ℕ) (z : α) :
    ((K ^ n) z).map f = (L ^ n) (f z) := by
  induction n generalizing z with
  | zero =>
    change (Measure.dirac z).map f = Measure.dirac (f z)
    exact Measure.map_dirac' hf z
  | succ n ih =>
    rw [pow_succ',pow_succ']
    exact costProjection_comp hf (fun z => ih z) hK z

lemma costProjection_potential {K B : Kernel α α} {L C : Kernel ℝ ℝ}
    (hK : ∀ z, (K z).map f = L (f z)) (hB : ∀ z, (B z).map f = C (f z)) (z : α) :
    ((potential B K) z).map f = (potential C L) (f z) := by
  rw [potential,Kernel.sum_apply,Measure.map_sum (f := f) hf.aemeasurable,
    potential,Kernel.sum_apply]
  apply congrArg Measure.sum
  funext n
  exact costProjection_comp hf (costProjection_power hf hK n) hB z

lemma costProjection_restrict {K : Kernel α α} {L : Kernel ℝ ℝ}
    (hK : ∀ z, (K z).map f = L (f z)) {S : Set ℝ} (hS : MeasurableSet S) (z : α) :
    ((K.restrict (s := f ⁻¹' S) (hf hS)) z).map f = (L.restrict hS) (f z) := by
  rw [Kernel.restrict_apply,Kernel.restrict_apply,← Measure.restrict_map hf hS,hK z]
end Projection

lemma beginning_relative_cost_projection (t : ℝ) (z : RegCost) :
    (markedBeginningKernel z).map (relativeBeginningCost t) =
      markedClockKernel (relativeBeginningCost t z) := by
  rw [markedClockKernel_apply]
  calc
    _ = ((markedBeginningKernel z).map (fun y => beginningCost y-beginningCost z)).map
        (fun G => relativeBeginningCost t z+G) := by
      rw [Measure.map_map (f := fun y : RegCost => beginningCost y-beginningCost z)
        (g := fun G : ℝ => relativeBeginningCost t z+G) (measurable_const.add measurable_id)
        (beginningCost_measurable.sub measurable_const)]
      congr 1
      funext y
      dsimp [Function.comp_def,relativeBeginningCost]
      ring
    _ = _ := by rw [markedBeginning_increment_law]

lemma beginningBelow_projection (t v : ℝ) (z : RegCost) :
    (beginningBelow t v z).map (relativeBeginningCost t) =
      clockBelow v (relativeBeginningCost t z) :=
  costProjection_restrict (relativeBeginningCost_measurable t)
    (beginning_relative_cost_projection t) measurableSet_Iio z

lemma beginningWindow_projection (t v H : ℝ) (z : RegCost) :
    (beginningWindow t v H z).map (relativeBeginningCost t) =
      clockWindow v H (relativeBeginningCost t z) :=
  costProjection_restrict (relativeBeginningCost_measurable t)
    (beginning_relative_cost_projection t) measurableSet_Icc z

lemma beginningOver_projection (t v H : ℝ) (z : RegCost) :
    (beginningOver t v H z).map (relativeBeginningCost t) =
      clockOver v H (relativeBeginningCost t z) :=
  costProjection_restrict (relativeBeginningCost_measurable t)
    (beginning_relative_cost_projection t) measurableSet_Ioi z

lemma beginningWindowHit_eq_clock (z : RegCost) (v H : ℝ) :
    beginningWindowHit z v H = clockWindowHit v H := by
  have he := costProjection_potential (relativeBeginningCost_measurable (beginningCost z))
    (beginningBelow_projection (beginningCost z) v) (beginningWindow_projection (beginningCost z) v H) z
  apply_fun (fun μ : Measure ℝ => μ univ) at he
  rw [Measure.map_apply (relativeBeginningCost_measurable _) MeasurableSet.univ,preimage_univ] at he
  simpa only [relativeBeginningCost,sub_self,beginningWindowHit,clockWindowHit] using he

lemma beginningOvershoot_eq_clock (z : RegCost) (v H : ℝ) :
    beginningOvershoot z v H = clockOvershoot v H := by
  have he := costProjection_potential (relativeBeginningCost_measurable (beginningCost z))
    (beginningBelow_projection (beginningCost z) v) (beginningOver_projection (beginningCost z) v H) z
  apply_fun (fun μ : Measure ℝ => μ univ) at he
  rw [Measure.map_apply (relativeBeginningCost_measurable _) MeasurableSet.univ,preimage_univ] at he
  simpa only [relativeBeginningCost,sub_self,beginningOvershoot,clockOvershoot] using he

theorem beginningWindow_partition (z : RegCost) {v H : ℝ} (hv : 0 < v) (hH : 0 ≤ H) :
    beginningWindowHit z v H+beginningOvershoot z v H = 1 := by
  rw [beginningWindowHit_eq_clock,beginningOvershoot_eq_clock]
  exact clockWindowHit_add_overshoot hv hH

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_MovingMarkedWindow
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory ENNReal
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.CostReturnLaw
open NumberTheoryLean.InitialRegeneration NumberTheoryLean.TransitionKernels
open NumberTheoryLean.KernelPotential
open AbsorptionCutoff.Renewal

lemma rawFirstMarkedBeginning_apply (z : OddCost) :
    rawFirstMarkedBeginning z =
      Measure.sum (fun n : ℕ => ((cycleBranchKernel false ^ n) z).withDensity nextMarkWeight) := by
  rw [rawFirstMarkedBeginning,Kernel.withDensity_apply _ (f := fun _ y : OddCost => nextMarkWeight y) (nextMarkWeight_measurable.comp measurable_snd),
    potential,Kernel.sum_apply]
  simp only [Kernel.id_comp]
  exact withDensity_sum _ _

lemma rawFirstMarkedBeginning_increment (z : OddCost) (hz : z ∈ returnSet) :
    (rawFirstMarkedBeginning z).map (fun y => y.2-z.2) = firstMarkWaitingLaw := by
  rw [rawFirstMarkedBeginning_apply,
    Measure.map_sum (f := fun y : OddCost => y.2-z.2) (measurable_snd.sub measurable_const).aemeasurable]
  change actualWaitingLaw z = firstMarkWaitingLaw
  rw [actualWaitingLaw_eq z hz,firstMarkWaitingLaw,actualWaitingLaw_eq]
  norm_num [returnSet,NumberTheoryLean.PairedHitting.pairedRegeneration,NumberTheoryLean.RegenerationTails.regenerationState]

lemma rawFirstMarkedBeginning_mass (z : OddCost) (hz : z ∈ returnSet) :
    rawFirstMarkedBeginning z univ = 1 := by
  have he := congrArg (fun μ : Measure ℝ => μ univ) (rawFirstMarkedBeginning_increment z hz)
  rw [Measure.map_apply (f := fun y : OddCost => y.2-z.2) (measurable_snd.sub measurable_const) MeasurableSet.univ,preimage_univ] at he
  exact he.trans measure_univ

lemma rawFirstMarkedBeginning_ae_regeneration (z : OddCost) (hz : z ∈ returnSet) :
    ∀ᵐ y ∂rawFirstMarkedBeginning z, y ∈ returnSet := by
  rw [rawFirstMarkedBeginning_apply,Measure.ae_sum_iff]
  intro n
  exact (withDensity_absolutelyContinuous _ _).ae_le (cycleBranch_pow_ae_regeneration false n z hz)

lemma rawFirstMarkedBeginning_cost_integral (z : OddCost) (hz : z ∈ returnSet)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y, F y.2 ∂rawFirstMarkedBeginning z) = ∫⁻ G, F (z.2+G) ∂firstMarkWaitingLaw := by
  rw [← rawFirstMarkedBeginning_increment z hz,
    lintegral_map (g := fun y : OddCost => y.2-z.2) (f := fun G : ℝ => F (z.2+G))
      (hF.comp (measurable_const.add measurable_id)) (measurable_snd.sub measurable_const)]
  apply lintegral_congr
  intro y
  congr 1
  ring

instance initialMarkedBeginning_isMarkovKernel : IsMarkovKernel initialMarkedBeginning := by
  constructor
  intro s
  constructor
  rw [initialMarkedBeginning,Kernel.comp_apply' _ _ _ MeasurableSet.univ]
  have he : (fun z => rawFirstMarkedBeginning z univ) =ᵐ[delayedRegeneration s] fun _ => 1 := by
    filter_upwards [delayedRegeneration_ae_regeneration s] with z hz
    exact rawFirstMarkedBeginning_mass z hz
  rw [lintegral_congr_ae he]
  simp

lemma initialMarkedBeginning_ae_regeneration (s : EvenState) :
    ∀ᵐ z ∂initialMarkedBeginning s, z ∈ returnSet := by
  rw [initialMarkedBeginning]
  apply Kernel.ae_comp_of_ae_ae returnSet_measurable
  filter_upwards [delayedRegeneration_ae_regeneration s] with z hz
  exact rawFirstMarkedBeginning_ae_regeneration z hz

instance initialMarkedCostLaw_isProbabilityMeasure (s : EvenState) : IsProbabilityMeasure (initialMarkedCostLaw s) :=
  (Measure.isProbabilityMeasure_map_iff measurable_snd.aemeasurable).mpr inferInstance

lemma initialMarkedCostLaw_eq (s : EvenState) :
    initialMarkedCostLaw s = delayedCostLaw s ∗ firstMarkWaitingLaw := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [initialMarkedCostLaw,lintegral_map hF measurable_snd,initialMarkedBeginning,
    Kernel.lintegral_comp _ _ _ (g := fun z : OddCost => F z.2) (hF.comp measurable_snd),
    Measure.lintegral_conv hF,delayedCostLaw,
    lintegral_map (g := Prod.snd) (f := fun x : ℝ => ∫⁻ y, F (x+y) ∂firstMarkWaitingLaw)
      ((hF.comp measurable_add).lintegral_prod_right') measurable_snd]
  apply lintegral_congr_ae
  filter_upwards [delayedRegeneration_ae_regeneration s] with z hz
  exact rawFirstMarkedBeginning_cost_integral z hz hF

lemma firstMarkWaiting_nonneg : ∀ᵐ G ∂firstMarkWaitingLaw, 0 ≤ G := by
  rw [firstMarkWaitingLaw,actualWaitingLaw_eq _ (by norm_num [returnSet,
    NumberTheoryLean.PairedHitting.pairedRegeneration,NumberTheoryLean.RegenerationTails.regenerationState])]
  exact Measure.ae_smul_measure unmarkedPotential_ae_nonneg _

lemma costTransform_mono {μ : Measure ℝ} (hμ : ∀ᵐ G ∂μ, 0 ≤ G) {a b : ℝ} (hab : a ≤ b) :
    costTransform μ a ≤ costTransform μ b := by
  apply lintegral_mono_ae
  filter_upwards [hμ] with G hG
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hab hG))

theorem initialMarkedCost_uniform_exponential (S : ℝ) : ∃ eta B : ℝ, 0 < eta ∧ 0 ≤ B ∧
    ∀ s : EvenState, s.1 ≤ S → costTransform (initialMarkedCostLaw s) eta ≤ ENNReal.ofReal B := by
  obtain ⟨a,A,ha,hA,hDelay⟩ := delayedCostLaw_uniform_exponential S
  obtain ⟨b,hb,hWait,_⟩ := marked_waiting_common_exponential_moment
  let eta := min a b
  have heta : 0 < eta := lt_min ha hb
  have hW : costTransform firstMarkWaitingLaw eta < ∞ :=
    (costTransform_mono firstMarkWaiting_nonneg (min_le_right a b)).trans_lt hWait
  let W : ℝ := (costTransform firstMarkWaitingLaw eta).toReal
  have hWreal : costTransform firstMarkWaitingLaw eta = ENNReal.ofReal W :=
    (ENNReal.ofReal_toReal hW.ne).symm
  refine ⟨eta,A*W,heta,mul_nonneg hA ENNReal.toReal_nonneg,?_⟩
  intro s hs
  have hd : ∀ᵐ T ∂delayedCostLaw s, 0 ≤ T := by
    rw [delayedCostLaw]
    exact (ae_map_iff measurable_snd.aemeasurable measurableSet_Ici).mpr (delayedRegeneration_cost_nonneg s)
  rw [initialMarkedCostLaw_eq,costTransform_conv,hWreal,ENNReal.ofReal_mul hA]
  exact mul_le_mul_left ((costTransform_mono hd (min_le_left a b)).trans (hDelay s hs)) _

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory ENNReal
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.CostReturnLaw
open NumberTheoryLean.TransitionKernels NumberTheoryLean.KernelPotential

instance initialBeginningReg_isMarkovKernel : IsMarkovKernel initialBeginningReg := by
  apply Kernel.IsMarkovKernel.comapRight
  intro s
  have he := (ae_mem_iff_measure_eq (μ := initialMarkedBeginning s)
    returnSet_measurable.nullMeasurableSet).mp (initialMarkedBeginning_ae_regeneration s)
  rw [measure_univ] at he
  convert! he using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ext y
  simp

lemma initialBeginningReg_map_state (s : EvenState) :
    (initialBeginningReg s).map (Subtype.val : RegCost → OddCost) = initialMarkedBeginning s := by
  calc
    _ = (initialMarkedBeginning s).restrict returnSet := by
      change (((initialMarkedBeginning s).comap (Subtype.val : RegCost → OddCost)).map Subtype.val) = _
      exact map_comap_subtype_coe (μ := initialMarkedBeginning s) returnSet_measurable
    _ = _ := Measure.restrict_eq_self_of_ae_mem (initialMarkedBeginning_ae_regeneration s)

lemma initialBeginningReg_cost_law (s : EvenState) :
    (initialBeginningReg s).map beginningCost = initialMarkedCostLaw s := by
  rw [initialMarkedCostLaw,← initialBeginningReg_map_state s,
    Measure.map_map measurable_snd measurable_subtype_coe]
  rfl

lemma beginningBelow_shift (t v : ℝ) : beginningBelow t (v-t) = beginningBelow 0 v := by
  unfold beginningBelow
  congr 1
  ext z
  simp only [mem_preimage,mem_Iio,relativeBeginningCost,sub_zero]
  constructor <;> intro h <;> linarith

lemma beginningOver_shift (t v H : ℝ) : beginningOver t (v-t) H = beginningOver 0 v H := by
  unfold beginningOver
  congr 1
  ext z
  simp only [mem_preimage,mem_Ioi,relativeBeginningCost,sub_zero]
  constructor <;> intro h <;> linarith

lemma beginningWindow_shift (t v H : ℝ) : beginningWindow t (v-t) H = beginningWindow 0 v H := by
  unfold beginningWindow
  congr 1
  ext z
  simp only [mem_preimage,mem_Icc,relativeBeginningCost,sub_zero]
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith

lemma absoluteBeginningOvershoot_eq (z : RegCost) (v H : ℝ) :
    (potential (beginningOver 0 v H) (beginningBelow 0 v)) z univ =
      beginningOvershoot z (v-beginningCost z) H := by
  rw [beginningOvershoot,beginningOver_shift,beginningBelow_shift]

lemma absoluteBeginningWindowHit_eq (z : RegCost) (v H : ℝ) :
    (potential (beginningWindow 0 v H) (beginningBelow 0 v)) z univ =
      beginningWindowHit z (v-beginningCost z) H := by
  rw [beginningWindowHit,beginningWindow_shift,beginningBelow_shift]

lemma markedWindowSuccess_measurable (v H : ℝ) : Measurable (markedWindowSuccess v H) := by
  unfold markedWindowSuccess
  exact Measurable.ite (measurableSet_lt beginningCost_measurable measurable_const)
    ((potential _ _).measurable_coe MeasurableSet.univ)
    (Measurable.ite (measurableSet_le beginningCost_measurable measurable_const) measurable_const measurable_const)

lemma markedWindow_partition (z : RegCost) (v H : ℝ) (hH : 0 ≤ H) :
    markedWindowSuccess v H z+markedWindowFailure v H z = 1 := by
  unfold markedWindowSuccess markedWindowFailure
  by_cases hz : beginningCost z < v
  · rw [ite_eq_left hz,ite_eq_left hz,absoluteBeginningOvershoot_eq,absoluteBeginningWindowHit_eq]
    exact beginningWindow_partition z (by linarith) hH
  · rw [ite_eq_right hz,ite_eq_right hz]
    split_ifs <;> simp

lemma initialMarkedWindow_partition (s : EvenState) (v H : ℝ) (hH : 0 ≤ H) :
    initialMarkedWindowSuccess s v H+initialMarkedWindowFailure s v H = 1 := by
  rw [initialMarkedWindowSuccess,initialMarkedWindowFailure,
    ← lintegral_add_left (markedWindowSuccess_measurable v H)]
  simp only [markedWindow_partition _ v H hH,lintegral_const,measure_univ,mul_one]

lemma cost_tail_le_transform (μ : Measure ℝ) {eta : ℝ} (heta : 0 ≤ eta) (v : ℝ) :
    μ (Ici v) ≤ ENNReal.ofReal (Real.exp (-eta*v))*costTransform μ eta := by
  calc
    _ = ∫⁻ G, (Ici v).indicator (fun _ => (1:ℝ≥0∞)) G ∂μ := by
      rw [lintegral_indicator measurableSet_Ici]; simp
    _ ≤ ∫⁻ G, ENNReal.ofReal (Real.exp (-eta*v))*ENNReal.ofReal (Real.exp (eta*G)) ∂μ := by
      apply lintegral_mono
      intro G
      by_cases hG : G ∈ Ici v
      · rw [indicator_of_mem hG]
        change (1:ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (-eta*v))*ENNReal.ofReal (Real.exp (eta*G))
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
        have he : (1:ℝ) ≤ Real.exp (-eta*v+eta*G) := Real.one_le_exp_iff.mpr (by change v≤G at hG; nlinarith)
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal he
      · rw [indicator_of_notMem hG]; exact zero_le
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

lemma initialMarkedWindowFailure_le (s : EvenState) (v H R : ℝ)
    (hTail : ∀ z : RegCost, ∀ u : ℝ, 0 < u → beginningOvershoot z u H ≤ ENNReal.ofReal R) :
    initialMarkedWindowFailure s v H ≤ ENNReal.ofReal R+initialMarkedCostLaw s (Ici v) := by
  have hp (z : RegCost) : markedWindowFailure v H z ≤ ENNReal.ofReal R+
      (beginningCost ⁻¹' Ici v).indicator (fun _ => (1:ℝ≥0∞)) z := by
    by_cases hz : beginningCost z < v
    · rw [markedWindowFailure,ite_eq_left hz,absoluteBeginningOvershoot_eq,
        indicator_of_notMem (show z ∉ beginningCost ⁻¹' Ici v from not_le_of_gt hz),add_zero]
      exact hTail z _ (by linarith)
    · rw [indicator_of_mem (show z ∈ beginningCost ⁻¹' Ici v from le_of_not_gt hz),
        markedWindowFailure,ite_eq_right hz]
      split_ifs
      · exact zero_le
      · exact le_add_left le_rfl
  calc
    _ ≤ ∫⁻ z, ENNReal.ofReal R+(beginningCost ⁻¹' Ici v).indicator (fun _ => (1:ℝ≥0∞)) z ∂initialBeginningReg s :=
      lintegral_mono hp
    _ = ENNReal.ofReal R+initialBeginningReg s (beginningCost ⁻¹' Ici v) := by
      rw [lintegral_add_left measurable_const,lintegral_const,measure_univ,mul_one,
        lintegral_indicator (beginningCost_measurable measurableSet_Ici)]
      simp
    _ = _ := by
      rw [← initialBeginningReg_cost_law s,Measure.map_apply beginningCost_measurable measurableSet_Ici]

theorem initialMarkedWindow_exponential (S : ℝ) : ∃ eta C eta0 B : ℝ,
    0 < eta ∧ 0 < C ∧ 0 < eta0 ∧ 0 ≤ B ∧ ∀ s : EvenState, s.1 ≤ S → ∀ v H : ℝ,
      0 ≤ H → initialMarkedWindowFailure s v H ≤
        ENNReal.ofReal (C*Real.exp (-eta*H)+B*Real.exp (-eta0*v)) := by
  obtain ⟨eta,C,heta,hC,hTail⟩ := beginningWindow_exponential_jb247
  obtain ⟨eta0,B,heta0,hB,hDelay⟩ := initialMarkedCost_uniform_exponential S
  refine ⟨eta,C,eta0,B,heta,hC,heta0,hB,?_⟩
  intro s hs v H hH
  calc
    _ ≤ ENNReal.ofReal (C*Real.exp (-eta*H))+initialMarkedCostLaw s (Ici v) :=
      initialMarkedWindowFailure_le s v H _ (fun z u hu => (hTail z u H hu hH).1)
    _ ≤ ENNReal.ofReal (C*Real.exp (-eta*H))+
      ENNReal.ofReal (Real.exp (-eta0*v))*costTransform (initialMarkedCostLaw s) eta0 :=
      add_le_add le_rfl (cost_tail_le_transform _ heta0.le v)
    _ ≤ ENNReal.ofReal (C*Real.exp (-eta*H))+ENNReal.ofReal (Real.exp (-eta0*v))*ENNReal.ofReal B :=
      add_le_add le_rfl (mul_le_mul_right (hDelay s hs) _)
    _ = _ := by rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,mul_comm (Real.exp (-eta0*v)),
      ← ENNReal.ofReal_add (mul_nonneg hC.le (Real.exp_pos _).le) (mul_nonneg hB (Real.exp_pos _).le)]

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory ENNReal
open NumberTheoryLean.TransitionKernels

lemma exponential_decay_tendsto {eta : ℝ} (heta : 0 < eta) (C : ℝ) :
    Tendsto (fun H : ℝ => C*Real.exp (-eta*H)) atTop (𝓝 0) := by
  have he : Tendsto (fun H : ℝ => Real.exp (-eta*H)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,id_eq,neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (Tendsto.const_mul_atTop heta tendsto_id)
  simpa only [mul_zero] using he.const_mul C

theorem moving_marked_window_capture {eps : ℝ} (heps : 0 < eps) :
    ∃ rho : ℝ, 10 < rho ∧ ∀ K : ℝ, 0 < K →
      ∀ᶠ w : ℝ in atTop, 3 ≤ w ∧ ∀ r : ℝ, w ≤ r → ∀ s : EvenState,
        199/100 ≤ s.1 → s.1 ≤ 23/10 →
        initialMarkedWindowFailure s (Real.log (r/(rho*K*(Real.log w)^2))) (Real.log (rho/10)) ≤
          ENNReal.ofReal eps ∧
        1-ENNReal.ofReal eps ≤
          initialMarkedWindowSuccess s (Real.log (r/(rho*K*(Real.log w)^2))) (Real.log (rho/10)) := by
  obtain ⟨eta,C,eta0,B,heta,_hC,heta0,_hB,hBound⟩ := initialMarkedWindow_exponential (23/10)
  have hHalf : 0 < eps/2 := by positivity
  obtain ⟨H,hH,hSmall⟩ := ((eventually_gt_atTop (0:ℝ)).and
    ((tendsto_order.mp (exponential_decay_tendsto heta C)).2 (eps/2) hHalf)).exists
  obtain ⟨V,hV⟩ := eventually_atTop.mp
    ((tendsto_order.mp (exponential_decay_tendsto heta0 B)).2 (eps/2) hHalf)
  let rho : ℝ := 10*Real.exp H
  have hrho : 10 < rho := by
    have he := Real.one_lt_exp_iff.mpr hH
    dsimp [rho]
    linarith
  have hWidth : Real.log (rho/10) = H := by
    dsimp [rho]
    rw [mul_div_cancel_left₀ _ (by norm_num : (10:ℝ) ≠ 0),Real.log_exp]
  refine ⟨rho,hrho,?_⟩
  intro K hK
  filter_upwards [moving_window_cost_threshold hK (by linarith : 0 < rho) V] with w hw
  refine ⟨hw.1,?_⟩
  intro r hr s _hs0 hs1
  have hFailure : initialMarkedWindowFailure s
      (Real.log (r/(rho*K*(Real.log w)^2))) (Real.log (rho/10)) ≤ ENNReal.ofReal eps := by
    rw [hWidth]
    apply (hBound s hs1 _ H hH.le).trans
    apply ENNReal.ofReal_le_ofReal
    have htail := hV _ (hw.2 r hr)
    linarith
  refine ⟨hFailure,?_⟩
  apply tsub_le_iff_right.mpr
  have hp := initialMarkedWindow_partition s (Real.log (r/(rho*K*(Real.log w)^2)))
    (Real.log (rho/10)) (by rw [hWidth]; exact hH.le)
  calc
    1 = initialMarkedWindowSuccess s (Real.log (r/(rho*K*(Real.log w)^2))) (Real.log (rho/10))+
        initialMarkedWindowFailure s (Real.log (r/(rho*K*(Real.log w)^2))) (Real.log (rho/10)) := hp.symm
    _ ≤ _ := add_le_add le_rfl hFailure

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_SourceCycleDuration
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory ENNReal
open NumberTheoryLean.TransitionKernels NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.CostReturnLaw NumberTheoryLean.InitialRegeneration
open NumberTheoryLean.MarkedCycleLaw

lemma pairWitnessUpdate_measurable : Measurable pairWitnessUpdate :=
  (measurable_fst.comp measurable_snd).prodMk pairUpdate_measurable

instance pairWitnessKernel_isMarkovKernel : IsMarkovKernel pairWitnessKernel :=
  Kernel.IsMarkovKernel.map _ pairWitnessUpdate_measurable

lemma firstPairProjection_measurable : Measurable firstPairProjection :=
  (sourceMark_measurable.comp measurable_fst).prodMk measurable_snd

lemma pairWitness_projection (z : OddCost) :
    (pairWitnessKernel z).map firstPairProjection = markedPairKernel z := by
  rw [pairWitnessKernel,Kernel.map_apply _ pairWitnessUpdate_measurable,
    Measure.map_map firstPairProjection_measurable pairWitnessUpdate_measurable,
    markedPairKernel,Kernel.map_apply _ markedPairUpdate_measurable]
  rfl

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_PairTraceBridge
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.TransitionKernels NumberTheoryLean.FinitePathGeometry
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping NumberTheoryLean.CycleOccupation

lemma pairWitness_lintegral (z : OddCost) {F : FirstPairWitness → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y, F y ∂pairWitnessKernel z) =
      ∫⁻ t : EvenState, ∫⁻ u : OddState, F (t,(u,z.2+cost t.1+cost u.1)) ∂evenToOdd t ∂oddToEven z.1 := by
  have hm : Measurable (fun x : EvenState × OddState => pairWitnessUpdate (z,x)) :=
    pairWitnessUpdate_measurable.comp measurable_prodMk_left
  have he : pairWitnessKernel z = (pairedDraws z.1).map (fun x => pairWitnessUpdate (z,x)) :=
    sampling_map_measure pairWitnessUpdate pairWitnessUpdate_measurable z
  rw [he,lintegral_map hF hm,pairedDraws,
    Kernel.lintegral_compProd _ _ _ (f := fun x : EvenState × OddState => F (pairWitnessUpdate (z,x))) (hF.comp hm)]
  rfl

lemma pairTraceOfWitness_measurable (z : OddCost) : Measurable (pairTraceOfWitness z) :=
  ((measurable_inl.comp measurable_fst).prodMk
    (measurable_const.add (cost_measurable.comp (measurable_subtype_coe.comp measurable_fst)))).prodMk
    (embedOdd_measurable.comp measurable_snd)

theorem pairWitness_joint_full_trace (z : OddCost) :
    (pairWitnessKernel z).map (pairTraceOfWitness z) = fullPairTraceKernel (embedOdd z) := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (pairTraceOfWitness_measurable z),
    pairWitness_lintegral z (F := fun x : FirstPairWitness => F (pairTraceOfWitness z x)) (hF.comp (pairTraceOfWitness_measurable z)),fullPairTraceKernel,
    Kernel.lintegral_compProd _ _ _ hF]
  change (∫⁻ t : EvenState, ∫⁻ u : OddState,
      F ((Sum.inl t,z.2+cost t.1),(Sum.inr u,z.2+cost t.1+cost u.1)) ∂evenToOdd t ∂oddToEven z.1) =
    ∫⁻ x : CostState, ∫⁻ y : CostState, F (x,y) ∂costKernel x ∂costKernel (embedOdd z)
  have hJ : Measurable (fun x : CostState => ∫⁻ y : CostState, F (x,y) ∂costKernel x) :=
    hF.lintegral_kernel_prod_right'
  simp only [embedOdd]
  rw [costKernel_odd_lintegral z.1 z.2 hJ]
  apply lintegral_congr
  intro t
  exact (costKernel_even_lintegral t (z.2+cost t.1)
    (H := fun y : CostState => F ((Sum.inl t,z.2+cost t.1),y))
    (hF.comp measurable_prodMk_left)).symm

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_HistoryRestrictionAlgebra
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory Function Preorder
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures

lemma restriction_comp_of_retained_prefix {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (K : Kernel α β) (L : Kernel β γ) {r : γ → β} (hr : Measurable r)
    (hPast : ∀ y, ∀ᵐ z ∂L y, r z=y) {B : Set β} {C : Set γ}
    (hB : MeasurableSet B) (hC : MeasurableSet C) :
    (L ∘ₖ K).restrict ((hr hB).inter hC) = (L.restrict hC) ∘ₖ (K.restrict hB) := by
  ext x S hS
  rw [Kernel.restrict_apply' _ _ _ hS,Kernel.comp_apply' _ _ _ (hS.inter ((hr hB).inter hC)),
    Kernel.comp_apply' _ _ _ hS,Kernel.restrict_apply]
  simp_rw [Kernel.restrict_apply' _ _ _ hS]
  rw [← lintegral_indicator hB]
  apply lintegral_congr
  intro y
  by_cases hy : y ∈ B
  · rw [indicator_of_mem hy]
    apply measure_congr
    filter_upwards [hPast y] with z hz
    apply propext
    change (z ∈ S ∧ (r z ∈ B ∧ z ∈ C)) ↔ (z ∈ S ∧ z ∈ C)
    simp only [hz,hy,true_and]
  · rw [indicator_of_notMem hy]
    calc
      _ = L y ∅ := by
        apply measure_congr
        filter_upwards [hPast y] with z hz
        apply propext
        change (z ∈ S ∧ (r z ∈ B ∧ z ∈ C)) ↔ False
        simp only [hz,hy,false_and,and_false]
      _ = 0 := measure_empty

local instance instMeasurableSingletonClassState : MeasurableSingletonClass State := by
  constructor
  intro x
  cases x with
  | inl e =>
    simpa only [image_singleton] using ((measurableSet_singleton e).inl_image :
      MeasurableSet (Sum.inl '' {e} : Set State))
  | inr o =>
    simpa only [image_singleton] using ((measurableSet_singleton o).inr_image :
      MeasurableSet (Sum.inr '' {o} : Set State))

lemma rawExtension_retains_prefix {b c : ℕ} (hbc : b ≤ c) (h : RawHistory b) :
    ∀ᵐ z ∂rawExtension b c h, rawPrefix hbc z = h := by
  have he : (rawExtension b c h).map (rawPrefix hbc) = Measure.dirac h := by
    rw [rawExtension,rawPrefix,Kernel.partialTraj_map_frestrictLe₂_apply (X := fun _ => CostState) (κ := historyKernel) h hbc,Kernel.partialTraj_self,Kernel.id_apply]
  have hd : ∀ᵐ y ∂(rawExtension b c h).map (rawPrefix hbc), y=h := by
    rw [he]
    exact ae_eq_dirac' measurable_id
  exact (ae_map_iff (rawPrefix_measurable hbc).aemeasurable (measurableSet_singleton h)).mp hd

theorem rawExtension_restrict_comp {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    {B : Set (RawHistory b)} {C : Set (RawHistory c)}
    (hB : MeasurableSet B) (hC : MeasurableSet C) :
    (rawExtension a c).restrict (((rawPrefix_measurable hbc) hB).inter hC) =
      ((rawExtension b c).restrict hC) ∘ₖ ((rawExtension a b).restrict hB) := by
  rw [← restriction_comp_of_retained_prefix _ _ (rawPrefix_measurable hbc)
    (rawExtension_retains_prefix hbc) hB hC]
  have he : rawExtension b c ∘ₖ rawExtension a b = rawExtension a c :=
    Kernel.partialTraj_comp_partialTraj hab hbc
  rw [he]

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_RawReturnBound
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping NumberTheoryLean.FirstHitKernels

lemma measurableSigmaMk {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)] (i : ι) :
    Measurable (@Sigma.mk ι X i) := Measurable.of_le_map (iInf_le _ i)

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_RawInitialEven
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping NumberTheoryLean.TransitionKernels
open NumberTheoryLean.InitialOddDraw NumberTheoryLean.InitialRegeneration

lemma rawExtension_last_step (a : ℕ) (h : RawHistory a) :
    (rawExtension a (a+1) h).map (rawLast (a+1))=costKernel (rawLast a h) := by
  have he := congrArg (fun K : Kernel (RawHistory a) CostState => K h)
    (Kernel.map_partialTraj_succ_self (X := fun _ => CostState) (κ := historyKernel) a)
  change ((rawExtension a (a+1)).map (rawLast (a+1))) h=costKernel (rawLast a h) at he
  rw [Kernel.map_apply _ (rawLast_measurable (a+1))] at he
  exact he

lemma rawFirstOdd_draw_law (a : ℕ) (h : RawHistory a) (s : EvenState)
    (hs : rawLast a h=(Sum.inl s,0)) :
    (rawExtension a (a+1) h).map (rawLast (a+1))=(firstOdd s).map embedOdd := by
  rw [rawExtension_last_step,hs,firstOdd_full_draw]

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_OrdinaryMarkedWindow
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.KernelPotential

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

lemma potential_factor_right (B : Kernel α β) (U : Kernel α α) :
    potential B U = B ∘ₖ potential Kernel.id U := by
  simpa only [Kernel.comp_id] using potential_comp_left (Kernel.id : Kernel α α) B U

lemma kernel_middle_power (S H : Kernel α α) (n : ℕ) :
    S ∘ₖ ((H ∘ₖ S)^n) = ((S ∘ₖ H)^n) ∘ₖ S := (mul_pow_mul S H n).symm

lemma potential_exchange (B : Kernel α β) (S H : Kernel α α) :
    potential (B ∘ₖ S) (H ∘ₖ S) = (potential B (S ∘ₖ H)) ∘ₖ S := by
  rw [potential,potential,Kernel.comp_sum_left]
  apply congrArg Kernel.sum
  funext n
  rw [Kernel.comp_assoc,kernel_middle_power,← Kernel.comp_assoc]

theorem potential_denesting (B : Kernel α β) (U H : Kernel α α) :
    potential B (U+H) =
      (potential B ((potential Kernel.id U) ∘ₖ H)) ∘ₖ potential Kernel.id U := by
  rw [first_capture_decomposition,potential_factor_right B U,potential_factor_right H U,potential_exchange]

lemma compose_mono_right_general {K L : Kernel α α} (hKL : K ≤ L) (B : Kernel α β) :
    B ∘ₖ K ≤ B ∘ₖ L := by
  intro x
  apply Measure.le_iff.mpr
  intro S hS
  rw [Kernel.comp_apply' _ _ _ hS,Kernel.comp_apply' _ _ _ hS]
  exact lintegral_mono' (hKL x) le_rfl

lemma potential_mono_step_general {K L : Kernel α α} (hKL : K ≤ L) (B : Kernel α β) :
    potential B K ≤ potential B L := by
  apply potential_le_of_super B K (potential B L)
  calc
    _ ≤ B+(potential B L) ∘ₖ L := fun x => add_le_add le_rfl ((compose_mono_right_general hKL _) x)
    _ = _ := (potential_unfold B L).symm

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical
open NumberTheoryLean.KernelPotential

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

lemma stateFilter_apply {S : Set α} (hS : MeasurableSet S) (x : α) :
    stateFilter hS x = if x ∈ S then Measure.dirac x else 0 := by
  classical
  rw [stateFilter,Kernel.restrict_apply,Kernel.id_apply,restrict_dirac' hS]

lemma stateFilter_mass {S : Set α} (hS : MeasurableSet S) (x : α) :
    stateFilter hS x univ = if x ∈ S then 1 else 0 := by
  classical
  rw [stateFilter_apply]
  split_ifs <;> simp

lemma stateFilter_output (K : Kernel α β) {S : Set β} (hS : MeasurableSet S) :
    stateFilter hS ∘ₖ K = K.restrict hS := by
  rw [stateFilter,Kernel.comp_restrict,Kernel.id_comp]

lemma stateFilter_input (K : Kernel α β) {S : Set α} (hS : MeasurableSet S) (x : α) :
    (K ∘ₖ stateFilter hS) x = if x ∈ S then K x else 0 := by
  classical
  by_cases hx : x ∈ S
  · rw [ite_eq_left hx]
    ext B hB
    rw [Kernel.comp_apply' _ _ _ hB,stateFilter_apply,ite_eq_left hx,lintegral_dirac' x (K.measurable_coe hB)]
  · rw [ite_eq_right hx]
    ext B hB
    rw [Kernel.comp_apply' _ _ _ hB,stateFilter_apply,ite_eq_right hx,lintegral_zero_measure]
    rfl

lemma stateFilter_mono {S T : Set α} (hS : MeasurableSet S) (hT : MeasurableSet T) (hST : S ⊆ T) :
    stateFilter hS ≤ stateFilter hT := by
  classical
  intro x
  by_cases hx : x ∈ S
  · rw [stateFilter_apply,stateFilter_apply,ite_eq_left hx,ite_eq_left (hST hx)]
  · rw [stateFilter_apply,ite_eq_right hx]
    exact Measure.zero_le _

instance stateFilter_stopping_isMarkov (R : Kernel α α) [IsMarkovKernel R]
    {S : Set α} (hS : MeasurableSet S) : IsMarkovKernel (stateFilter hS+R ∘ₖ stateFilter hS.compl) := by
  classical
  constructor
  intro x
  constructor
  rw [_root_.add_apply,Measure.add_apply,stateFilter_mass,stateFilter_input]
  by_cases hx : x ∈ S <;> simp [hx]

lemma capturePotential_mass_le_one (B H : Kernel α α) [IsFiniteKernel B] [IsFiniteKernel H]
    [IsMarkovKernel (B+H)] (x : α) : potential B H x univ ≤ 1 := by
  have (n : ℕ) : IsFiniteKernel (H^n) := by
    induction n with
    | zero => change IsFiniteKernel (Kernel.id : Kernel α α); infer_instance
    | succ n ih => rw [pow_succ']; change IsFiniteKernel (H ∘ₖ (H^n)); infer_instance
  have hs (n : ℕ) : (B ∘ₖ (H^n)) x univ+(H^(n+1)) x univ=(H^n) x univ := by
    have hp : H^(n+1)=H ∘ₖ (H^n) := pow_succ' _ _
    calc
      _ = ((B+H) ∘ₖ (H^n)) x univ := by rw [Kernel.comp_add_left,_root_.add_apply,Measure.add_apply,hp]
      _ = _ := by
        rw [Kernel.comp_apply' _ _ _ MeasurableSet.univ]
        simp only [measure_univ,lintegral_const,one_mul]
  have hf (n : ℕ) : (H^n) x univ+∑ k ∈ Finset.range n, (B ∘ₖ (H^k)) x univ=1 := by
    induction n with
    | zero => change (Measure.dirac x) univ+0=1; simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      calc
        _ = (∑ k ∈ Finset.range n, (B ∘ₖ (H^k)) x univ)+
            ((B ∘ₖ (H^n)) x univ+(H^(n+1)) x univ) := by ac_rfl
        _ = _ := by rw [hs]; simpa only [add_comm] using ih
  rw [potential,Kernel.sum_apply' _ _ MeasurableSet.univ,ENNReal.tsum_eq_iSup_nat]
  apply iSup_le
  intro n
  calc
    _ ≤ (H^n) x univ+∑ k ∈ Finset.range n, (B ∘ₖ (H^k)) x univ := le_add_left le_rfl
    _ = 1 := hf n

lemma currentHit_outside (R : Kernel α α) {S : Set α} (hS : MeasurableSet S) (x : α) (hx : x ∉ S) :
    potential (stateFilter hS) (R ∘ₖ stateFilter hS.compl) x =
      (potential (stateFilter hS) (R ∘ₖ stateFilter hS.compl) ∘ₖ R) x := by
  classical
  conv_lhs =>
    rw [potential_unfold,_root_.add_apply,stateFilter_apply,ite_eq_right hx,
      ← Kernel.comp_assoc,stateFilter_input,ite_eq_left (show x ∈ Sᶜ from hx),zero_add]

lemma currentHit_inside (R : Kernel α α) {S : Set α} (hS : MeasurableSet S) (x : α) (hx : x ∈ S) :
    1 ≤ potential (stateFilter hS) (R ∘ₖ stateFilter hS.compl) x univ := by
  rw [potential_unfold,_root_.add_apply,Measure.add_apply,stateFilter_mass,ite_eq_left hx]
  exact le_add_right le_rfl

theorem restricted_crossing_le_current_hit (R : Kernel α α) {S T : Set α}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hTS : T ⊆ Sᶜ) (x : α) (hx : x ∈ T) :
    potential (R.restrict hS) (R.restrict hT) x univ ≤
      potential (stateFilter hS) (R ∘ₖ stateFilter hS.compl) x univ := by
  rw [← stateFilter_output R hS,← stateFilter_output R hT,potential_exchange]
  have hK : R ∘ₖ stateFilter hT ≤ R ∘ₖ stateFilter hS.compl :=
    compose_mono_right_general (stateFilter_mono hT hS.compl hTS) R
  have hP := potential_mono_step_general hK (stateFilter hS)
  have he := currentHit_outside R hS x (hTS hx)
  exact ((compose_mono_left hP R) x univ).trans_eq (congrArg (fun μ : Measure α => μ univ) he.symm)

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.CostReturnLaw
open NumberTheoryLean.KernelPotential

lemma cycleBranch_mass_partition (z : OddCost) :
    cycleBranchKernel true z univ+cycleBranchKernel false z univ=1 := by
  rw [← Measure.add_apply,← _root_.add_apply,cycleBranch_sum]
  exact measure_univ

lemma nextMarkWeight_le_one (z : OddCost) : nextMarkWeight z ≤ 1 := by
  change cycleBranchKernel true z univ ≤ 1
  calc
    _ ≤ cycleBranchKernel true z univ+cycleBranchKernel false z univ := le_add_right le_rfl
    _ = 1 := cycleBranch_mass_partition z

instance markInputWeightKernel_isFiniteKernel : IsFiniteKernel markInputWeightKernel := by
  apply Kernel.isFiniteKernel_withDensity_of_bounded _ (B := 1) (by simp)
  exact fun _ z => nextMarkWeight_le_one z

lemma markInputWeightKernel_apply (z : OddCost) :
    markInputWeightKernel z=nextMarkWeight z • Measure.dirac z := by
  rw [markInputWeightKernel,Kernel.withDensity_apply _ (f := fun _ z : OddCost => nextMarkWeight z)
    (nextMarkWeight_measurable.comp measurable_snd),Kernel.id_apply,dirac_withDensity' nextMarkWeight_measurable]

instance ordinaryWindowCapture_isFiniteKernel (v H : ℝ) : IsFiniteKernel (ordinaryWindowCapture v H) := by
  unfold ordinaryWindowCapture
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma ordinaryWindowCapture_mass (v H : ℝ) (z : OddCost) :
    ordinaryWindowCapture v H z univ = if z ∈ ordinaryCostWindow v H then nextMarkWeight z else 0 := by
  rw [ordinaryWindowCapture,Kernel.restrict_apply' _ _ _ MeasurableSet.univ,univ_inter,
    markInputWeightKernel_apply,Measure.smul_apply,smul_eq_mul,
    Measure.dirac_apply' z (ordinaryCostWindow_measurable v H)]
  split_ifs <;> simp_all

instance ordinaryWindow_stop_isMarkov (v H : ℝ) :
    IsMarkovKernel (ordinaryWindowCapture v H+ordinaryWindowContinue v H) := by
  constructor
  intro z
  constructor
  rw [_root_.add_apply,Measure.add_apply,ordinaryWindowCapture_mass,ordinaryWindowContinue,
    _root_.add_apply,Measure.add_apply,stateFilter_input]
  by_cases hz : z ∈ ordinaryCostWindow v H
  · simp only [hz,ite_true, if_true,mem_compl_iff,not_true_eq_false,ite_false, if_false,Measure.coe_zero,Pi.zero_apply,add_zero]
    exact cycleBranch_mass_partition z
  · simp only [hz,ite_false, if_false,mem_compl_iff,not_false_eq_true,ite_true, if_true,zero_add]
    simpa only [nextMarkWeight,add_comm] using cycleBranch_mass_partition z

lemma ordinaryMarkedHit_mass_le_one (v H : ℝ) (z : OddCost) : ordinaryMarkedHit v H z univ ≤ 1 :=
  capturePotential_mass_le_one _ _ z

lemma rawBeginning_unmarkedStar : rawBeginningKernel = unmarkedStar ∘ₖ cycleBranchKernel true := by
  rw [unmarkedStar,potential,Kernel.comp_sum_left,rawBeginningKernel]
  apply congrArg Kernel.sum
  funext n
  rw [Kernel.id_comp]

theorem ordinaryMarkedHit_denested (v H : ℝ) :
    ordinaryMarkedHit v H =
      (potential (ordinaryWindowCapture v H)
        (rawBeginningKernel ∘ₖ stateFilter (ordinaryCostWindow_measurable v H).compl)) ∘ₖ unmarkedStar := by
  rw [ordinaryMarkedHit,ordinaryWindowContinue,rawBeginning_unmarkedStar,Kernel.comp_assoc]
  exact potential_denesting _ _ _

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_MarkedCostHitReduction
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.KernelPotential

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

lemma kernel_power_sfinite (K : Kernel α α) [IsSFiniteKernel K] (n : ℕ) : IsSFiniteKernel (K^n) := by
  induction n with
  | zero => change IsSFiniteKernel (Kernel.id : Kernel α α); infer_instance
  | succ n ih => rw [pow_succ']; change IsSFiniteKernel (K ∘ₖ (K^n)); infer_instance

lemma kernel_power_support (K : Kernel α α) [IsSFiniteKernel K] {S : Set α} (hS : MeasurableSet S)
    (hK : ∀ x, ∀ᵐ y ∂K x, y ∈ S) (n : ℕ) (x : α) (hx : x ∈ S) :
    ∀ᵐ y ∂(K^n) x, y ∈ S := by
  have (m : ℕ) : IsSFiniteKernel (K^m) := kernel_power_sfinite K m
  cases n with
  | zero => change ∀ᵐ y ∂Measure.dirac x, y ∈ S; exact (ae_dirac_iff hS).mpr hx
  | succ n =>
    rw [pow_succ']
    change ∀ᵐ y ∂(K ∘ₖ (K^n)) x, y ∈ S
    exact Kernel.ae_comp_of_ae_ae hS (Eventually.of_forall hK)

lemma supported_projection_power (K : Kernel α α) (L : Kernel β β) [IsSFiniteKernel K] [IsSFiniteKernel L]
    {S : Set α} (_hS : MeasurableSet S) (hSupp : ∀ x, ∀ᵐ y ∂K x, y ∈ S)
    {f : α → β} (hf : Measurable f) (hKL : ∀ x ∈ S, (K x).map f=L (f x))
    (n : ℕ) (x : α) (hx : x ∈ S) : ((K^n) x).map f=(L^n) (f x) := by
  have (m : ℕ) : IsSFiniteKernel (K^m) := kernel_power_sfinite K m
  have (m : ℕ) : IsSFiniteKernel (L^m) := kernel_power_sfinite L m
  induction n generalizing x with
  | zero => change (Measure.dirac x).map f=Measure.dirac (f x); exact Measure.map_dirac' hf x
  | succ n ih =>
    apply Measure.ext_of_lintegral
    intro F hF
    have hp : K^(n+1)=(K^n) ∘ₖ K := pow_succ _ _
    have hq : L^(n+1)=(L^n) ∘ₖ L := pow_succ _ _
    rw [lintegral_map hF hf,hp,hq,Kernel.lintegral_comp _ _ _ (g := fun z => F (f z)) (hF.comp hf),
      Kernel.lintegral_comp _ _ _ hF]
    have he : (fun y => ∫⁻ z, F (f z) ∂(K^n) y) =ᵐ[K x] fun y => ∫⁻ z, F z ∂(L^n) (f y) := by
      filter_upwards [hSupp x] with y hy
      rw [← lintegral_map (g := f) hF hf,ih y hy]
    rw [lintegral_congr_ae he]
    have hJ : Measurable (fun y : β => ∫⁻ z, F z ∂(L^n) y) := hF.lintegral_kernel
    rw [← lintegral_map (g := f) hJ hf,hKL x hx]

lemma supported_projection_potential (K B : Kernel α α) (L C : Kernel β β)
    [IsSFiniteKernel K] [IsSFiniteKernel B] [IsSFiniteKernel L] [IsSFiniteKernel C]
    {S : Set α} (hS : MeasurableSet S) (hSupp : ∀ x, ∀ᵐ y ∂K x, y ∈ S)
    {f : α → β} (hf : Measurable f) (hKL : ∀ x ∈ S, (K x).map f=L (f x))
    (hBC : ∀ x ∈ S, (B x).map f=C (f x)) (x : α) (hx : x ∈ S) :
    (potential B K x).map f=potential C L (f x) := by
  have (m : ℕ) : IsSFiniteKernel (K^m) := kernel_power_sfinite K m
  have (m : ℕ) : IsSFiniteKernel (L^m) := kernel_power_sfinite L m
  rw [potential,Kernel.sum_apply,Measure.map_sum (f := f) hf.aemeasurable,potential,Kernel.sum_apply]
  apply congrArg Measure.sum
  funext n
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF hf,Kernel.lintegral_comp _ _ _ (g := fun z => F (f z)) (hF.comp hf),
    Kernel.lintegral_comp _ _ _ hF]
  have he : (fun y => ∫⁻ z, F (f z) ∂B y) =ᵐ[(K^n) x] fun y => ∫⁻ z, F z ∂C (f y) := by
    filter_upwards [kernel_power_support K hS hSupp n x hx] with y hy
    rw [← lintegral_map (g := f) hF hf,hBC y hy]
  rw [lintegral_congr_ae he]
  have hJ : Measurable (fun y : β => ∫⁻ z, F z ∂C y) := hF.lintegral_kernel
  rw [← lintegral_map (g := f) hJ hf,supported_projection_power K L hS hSupp hf hKL n x hx]

lemma kernelScale_apply (p : ℝ≥0∞) (B : Kernel α β) [IsSFiniteKernel B] (x : α) :
    kernelScale p B x=p • B x := by
  rw [kernelScale,Kernel.withDensity_apply _ (f := fun _ _ => p) measurable_const,withDensity_const]

lemma kernelScale_isSFinite (p : ℝ≥0∞) (hp : p ≠ ∞) (B : Kernel α β) [IsSFiniteKernel B] :
    IsSFiniteKernel (kernelScale p B) := Kernel.IsSFiniteKernel.withDensity B (fun _ _ => hp)

lemma potential_scale_base (p : ℝ≥0∞) (hp : p ≠ ∞) (B : Kernel α β) (K : Kernel α α)
    [IsSFiniteKernel B] [IsSFiniteKernel K] (x : α) :
    potential (kernelScale p B) K x=p • potential B K x := by
  have : IsSFiniteKernel (kernelScale p B) := kernelScale_isSFinite p hp B
  have (n : ℕ) : IsSFiniteKernel (K^n) := kernel_power_sfinite K n
  ext S hS
  rw [potential,Kernel.sum_apply' _ _ hS,Measure.smul_apply,smul_eq_mul,
    potential,Kernel.sum_apply' _ _ hS,← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro n
  rw [Kernel.comp_apply' _ _ _ hS,Kernel.comp_apply' _ _ _ hS]
  simp_rw [kernelScale_apply,Measure.smul_apply,smul_eq_mul]
  exact lintegral_const_mul' _ _ hp

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.CostReturnLaw
open NumberTheoryLean.KernelPotential

instance costMarkedLoop_isFiniteKernel (v H : ℝ) : IsFiniteKernel (costMarkedLoop v H) := by
  unfold costMarkedLoop
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance costCurrentHit_isSFiniteKernel (v H : ℝ) : IsSFiniteKernel (costCurrentHit v H) := by
  unfold costCurrentHit
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance costWindow_stopping_isMarkov (v H : ℝ) : IsMarkovKernel (costWindowFilter v H+costMarkedLoop v H) := by
  unfold costWindowFilter costMarkedLoop costOutsideFilter
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma rawBeginning_total_cost (z : OddCost) (hz : z ∈ returnSet) :
    (rawBeginningKernel z).map Prod.snd=markedClockKernel z.2 := by
  rw [markedClockKernel_apply]
  calc
    _ = ((rawBeginningKernel z).map (fun y => y.2-z.2)).map (fun G : ℝ => z.2+G) := by
      rw [Measure.map_map (g := fun G : ℝ => z.2+G) (f := fun y : OddCost => y.2-z.2)
        (measurable_const.add measurable_id) (measurable_snd.sub measurable_const)]
      congr 1
      funext y
      simp only [Function.comp_def,add_sub_cancel]
    _ = _ := by rw [rawBeginning_cost_law z hz]

lemma ordinaryMarkedLoop_support (v H : ℝ) (z : OddCost) :
    ∀ᵐ y ∂ordinaryMarkedLoop v H z, y ∈ returnSet := by
  rw [ordinaryMarkedLoop,stateFilter_input]
  split_ifs
  · exact rawBeginning_ae_regeneration z
  · simp

lemma ordinaryMarkedLoop_cost (v H : ℝ) (z : OddCost) (hz : z ∈ returnSet) :
    (ordinaryMarkedLoop v H z).map Prod.snd=costMarkedLoop v H z.2 := by
  rw [ordinaryMarkedLoop,costMarkedLoop,costOutsideFilter,stateFilter_input,stateFilter_input]
  by_cases h : z.2 ∈ Icc v (v+H)
  · rw [ite_eq_right (show z ∉ (ordinaryCostWindow v H)ᶜ from fun hn => hn h),
      ite_eq_right (show z.2 ∉ (Icc v (v+H))ᶜ from fun hn => hn h),Measure.map_zero]
  · rw [ite_eq_left (show z ∈ (ordinaryCostWindow v H)ᶜ from h),
      ite_eq_left (show z.2 ∈ (Icc v (v+H))ᶜ from h)]
    exact rawBeginning_total_cost z hz

lemma cost_filter_projection (v H : ℝ) (z : OddCost) :
    (stateFilter (ordinaryCostWindow_measurable v H) z).map Prod.snd=costWindowFilter v H z.2 := by
  rw [stateFilter,costWindowFilter,stateFilter,Kernel.restrict_apply,Kernel.restrict_apply,Kernel.id_apply,Kernel.id_apply]
  change ((Measure.dirac z).restrict (Prod.snd ⁻¹' Icc v (v+H))).map Prod.snd =
    (Measure.dirac z.2).restrict (Icc v (v+H))
  rw [← Measure.restrict_map measurable_snd measurableSet_Icc,Measure.map_dirac' measurable_snd]

lemma ordinaryWindowCapture_on_regeneration (v H : ℝ) (z : OddCost) (hz : z ∈ returnSet) :
    ordinaryWindowCapture v H z=markProbability • stateFilter (ordinaryCostWindow_measurable v H) z := by
  have hp : nextMarkWeight z=markProbability := cycleBranch_true_mass z hz
  rw [ordinaryWindowCapture,Kernel.restrict_apply,markInputWeightKernel_apply,hp,Measure.restrict_smul]
  rfl

lemma ordinaryWindowCapture_cost (v H : ℝ) (z : OddCost) (hz : z ∈ returnSet) :
    (ordinaryWindowCapture v H z).map Prod.snd=kernelScale markProbability (costWindowFilter v H) z.2 := by
  rw [ordinaryWindowCapture_on_regeneration v H z hz,Measure.map_smul,cost_filter_projection,kernelScale_apply]

theorem ordinaryMarkedPotential_cost (v H : ℝ) (z : OddCost) (hz : z ∈ returnSet) :
    (potential (ordinaryWindowCapture v H) (ordinaryMarkedLoop v H) z).map Prod.snd =
      markProbability • costCurrentHit v H z.2 := by
  have : IsSFiniteKernel (kernelScale markProbability (costWindowFilter v H)) :=
    kernelScale_isSFinite markProbability markProbability_ne_top _
  rw [supported_projection_potential (ordinaryMarkedLoop v H) (ordinaryWindowCapture v H)
    (costMarkedLoop v H) (kernelScale markProbability (costWindowFilter v H))
    returnSet_measurable (ordinaryMarkedLoop_support v H) measurable_snd
    (ordinaryMarkedLoop_cost v H) (ordinaryWindowCapture_cost v H) z hz,
    potential_scale_base markProbability markProbability_ne_top]
  rfl

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.CostReturnLaw
open NumberTheoryLean.InitialRegeneration NumberTheoryLean.TransitionKernels
open NumberTheoryLean.KernelPotential

lemma unmarkedStar_support (z : OddCost) (hz : z ∈ returnSet) :
    ∀ᵐ y ∂unmarkedStar z, y ∈ returnSet := by
  rw [unmarkedStar,potential,Kernel.sum_apply,Measure.ae_sum_iff]
  intro n
  rw [Kernel.id_comp]
  exact cycleBranch_pow_ae_regeneration false n z hz

lemma ordinaryMarkedPotential_mass (v H : ℝ) (z : OddCost) (hz : z ∈ returnSet) :
    potential (ordinaryWindowCapture v H) (ordinaryMarkedLoop v H) z univ =
      markProbability*costCurrentHit v H z.2 univ := by
  have he := congrArg (fun μ : Measure ℝ => μ univ) (ordinaryMarkedPotential_cost v H z hz)
  rw [Measure.map_apply measurable_snd MeasurableSet.univ,preimage_univ,Measure.smul_apply,smul_eq_mul] at he
  exact he

theorem ordinaryMarkedHit_first_mark_reduction (v H : ℝ) (z : OddCost) (hz : z ∈ returnSet) :
    ordinaryMarkedHit v H z univ =
      ∫⁻ y, costCurrentHit v H y.2 univ ∂rawFirstMarkedBeginning z := by
  have hQ : Measurable (fun y : OddCost => costCurrentHit v H y.2 univ) :=
    ((costCurrentHit v H).measurable_coe MeasurableSet.univ).comp measurable_snd
  rw [ordinaryMarkedHit_denested,Kernel.comp_apply' _ _ _ MeasurableSet.univ,
    rawFirstMarkedBeginning,Kernel.withDensity_apply _ (f := fun _ y : OddCost => nextMarkWeight y)
      (nextMarkWeight_measurable.comp measurable_snd),
    lintegral_withDensity_eq_lintegral_mul _ nextMarkWeight_measurable hQ]
  change (∫⁻ y, potential (ordinaryWindowCapture v H) (ordinaryMarkedLoop v H) y univ ∂unmarkedStar z) =
    ∫⁻ y, nextMarkWeight y*costCurrentHit v H y.2 univ ∂unmarkedStar z
  apply lintegral_congr_ae
  filter_upwards [unmarkedStar_support z hz] with y hy
  rw [ordinaryMarkedPotential_mass v H y hy]
  have hp : nextMarkWeight y=markProbability := cycleBranch_true_mass y hy
  rw [hp]

lemma ordinaryInitialHitMass_le_one (s : EvenState) (v H : ℝ) : ordinaryInitialHitMass s v H ≤ 1 := by
  calc
    _ ≤ ∫⁻ _z, (1:ℝ≥0∞) ∂delayedRegeneration s := lintegral_mono (ordinaryMarkedHit_mass_le_one v H)
    _ = 1 := by simp

theorem ordinaryInitialHit_cost_law (s : EvenState) (v H : ℝ) :
    ordinaryInitialHitMass s v H = ∫⁻ T, costCurrentHit v H T univ ∂initialMarkedCostLaw s := by
  have hQ : Measurable (fun y : OddCost => costCurrentHit v H y.2 univ) :=
    ((costCurrentHit v H).measurable_coe MeasurableSet.univ).comp measurable_snd
  rw [ordinaryInitialHitMass,initialMarkedCostLaw,
    lintegral_map ((costCurrentHit v H).measurable_coe MeasurableSet.univ) measurable_snd,
    initialMarkedBeginning,Kernel.lintegral_comp _ _ _ hQ]
  apply lintegral_congr_ae
  filter_upwards [delayedRegeneration_ae_regeneration s] with z hz
  exact ordinaryMarkedHit_first_mark_reduction v H z hz

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_QuantitativeOrdinaryHit
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical
open NumberTheoryLean.TransitionKernels NumberTheoryLean.KernelPotential

lemma absoluteBeginningWindow_mass_cost (z : RegCost) (v H : ℝ) :
    potential (beginningWindow 0 v H) (beginningBelow 0 v) z univ =
      potential (clockWindow v H) (clockBelow v) (beginningCost z) univ := by
  have he := costProjection_potential (relativeBeginningCost_measurable 0)
    (beginningBelow_projection 0 v) (beginningWindow_projection 0 v H) z
  apply_fun (fun μ : Measure ℝ => μ univ) at he
  rw [Measure.map_apply (relativeBeginningCost_measurable 0) MeasurableSet.univ,preimage_univ] at he
  simpa only [relativeBeginningCost,sub_zero] using he

lemma markedWindowSuccess_le_cost_hit (z : RegCost) (v H : ℝ) :
    markedWindowSuccess v H z ≤ costCurrentHit v H (beginningCost z) univ := by
  rw [markedWindowSuccess]
  by_cases hz : beginningCost z < v
  · rw [ite_eq_left hz,absoluteBeginningWindow_mass_cost]
    have hsub : Iio v ⊆ (Icc v (v+H))ᶜ := by
      intro x hx hs
      exact (not_lt_of_ge hs.1) hx
    exact restricted_crossing_le_current_hit markedClockKernel
      (S := Icc v (v+H)) (T := Iio v) measurableSet_Icc measurableSet_Iio hsub _ hz
  · rw [ite_eq_right hz]
    split_ifs with hin
    · exact currentHit_inside markedClockKernel (S := Icc v (v+H)) measurableSet_Icc
        (beginningCost z) ⟨le_of_not_gt hz,hin⟩
    · exact zero_le

theorem initialMarkedWindowSuccess_le_ordinaryHit (s : EvenState) (v H : ℝ) :
    initialMarkedWindowSuccess s v H ≤ ordinaryInitialHitMass s v H := by
  rw [ordinaryInitialHit_cost_law,initialMarkedWindowSuccess]
  calc
    _ ≤ ∫⁻ z, costCurrentHit v H (beginningCost z) univ ∂initialBeginningReg s :=
      lintegral_mono (fun z => markedWindowSuccess_le_cost_hit z v H)
    _ = ∫⁻ T, costCurrentHit v H T univ ∂(initialBeginningReg s).map beginningCost := by
      rw [lintegral_map ((costCurrentHit v H).measurable_coe MeasurableSet.univ) beginningCost_measurable]
    _ = _ := by rw [initialBeginningReg_cost_law]

theorem moving_ordinary_marked_hit {eps : ℝ} (heps : 0 < eps) :
    ∃ rho : ℝ, 10 < rho ∧ ∀ K : ℝ, 0 < K →
      ∀ᶠ w : ℝ in atTop, 3 ≤ w ∧ ∀ r : ℝ, w ≤ r → ∀ s : EvenState,
        199/100 ≤ s.1 → s.1 ≤ 23/10 →
        1-ordinaryInitialHitMass s (Real.log (r/(rho*K*(Real.log w)^2))) (Real.log (rho/10)) ≤ ENNReal.ofReal eps := by
  obtain ⟨rho,hrho,hMoving⟩ := moving_marked_window_capture heps
  refine ⟨rho,hrho,?_⟩
  intro K hK
  filter_upwards [hMoving K hK] with w hw
  refine ⟨hw.1,?_⟩
  intro r hr s hs0 hs1
  have hOld := hw.2 r hr s hs0 hs1
  have hWidth : 0 ≤ Real.log (rho/10) := Real.log_nonneg (by linarith)
  apply tsub_le_iff_right.mpr
  have he : 1 ≤ ordinaryInitialHitMass s (Real.log (r/(rho*K*(Real.log w)^2))) (Real.log (rho/10))+
      ENNReal.ofReal eps := by
    calc
      1 = initialMarkedWindowSuccess s (Real.log (r/(rho*K*(Real.log w)^2))) (Real.log (rho/10))+
          initialMarkedWindowFailure s (Real.log (r/(rho*K*(Real.log w)^2))) (Real.log (rho/10)) :=
        (initialMarkedWindow_partition _ _ _ hWidth).symm
      _ ≤ _ := add_le_add (initialMarkedWindowSuccess_le_ordinaryHit _ _ _) hOld.1
  simpa only [add_comm] using he

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_RawIncreasingPrefix
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.FinitePathGeometry
open NumberTheoryLean.TransitionKernels

lemma actualCostKernel_strict (z : CostState) : ∀ᵐ y ∂costKernel z, z.2 < y.2 := by
  have hm : MeasurableSet {y : CostState | z.2 < y.2} := measurableSet_lt measurable_const measurable_snd
  apply (ae_mem_iff_measure_eq hm.nullMeasurableSet).mpr
  rw [costKernel_apply z hm]
  have he : {s : State | z.2 < (s,z.2+cost (stateRatio s)).2}=univ := by
    apply eq_univ_of_forall
    intro s
    have hp := cost_pos (valid_pos (stateRatio_valid s))
    exact lt_add_of_pos_right z.2 hp
  simp only [mem_ofPred_eq]
  rw [he]
  simp

lemma rawExtension_strict_step (k : ℕ) (h : RawHistory k) :
    ∀ᵐ y ∂rawExtension k (k+1) h,
      (y ⟨k,Finset.mem_Iic.mpr (by omega)⟩).2 < (rawLast (k+1) y).2 := by
  have hs : ∀ᵐ y ∂rawExtension k (k+1) h, (rawLast k h).2 < (rawLast (k+1) y).2 := by
    apply (ae_map_iff (rawLast_measurable (k+1)).aemeasurable
      (measurableSet_lt measurable_const measurable_snd)).mp
    rw [rawExtension_last_step]
    exact actualCostKernel_strict _
  filter_upwards [hs,rawExtension_retains_prefix (show k ≤ k+1 by omega) h] with y hy hp
  have he := congrFun hp (⟨k,by simp⟩ : Finset.Iic k)
  change y ⟨k,_⟩=rawLast k h at he
  rw [he]
  exact hy

lemma rawExtension_strict_coordinate {a b k : ℕ} (hak : a ≤ k) (hkb : k < b) (h : RawHistory a) :
    ∀ᵐ y ∂rawExtension a b h,
      (y ⟨k,Finset.mem_Iic.mpr (by omega)⟩).2 <
        (y ⟨k+1,Finset.mem_Iic.mpr (by omega)⟩).2 := by
  have hm : MeasurableSet {y : RawHistory (k+1) |
      (y ⟨k,Finset.mem_Iic.mpr (by omega)⟩).2 < (rawLast (k+1) y).2} :=
    measurableSet_lt (measurable_snd.comp (measurable_pi_apply _))
      (measurable_snd.comp (rawLast_measurable _))
  have he : (rawExtension a b h).map (rawPrefix (show k+1 ≤ b by omega))=rawExtension a (k+1) h :=
    Kernel.partialTraj_map_frestrictLe₂_apply (X := fun _ => CostState) (κ := historyKernel) h (show k+1 ≤ b by omega)
  have ht : ∀ᵐ y ∂rawExtension a (k+1) h,
      (y ⟨k,Finset.mem_Iic.mpr (by omega)⟩).2 < (rawLast (k+1) y).2 := by
    have hc : rawExtension a (k+1)=rawExtension k (k+1) ∘ₖ rawExtension a k :=
      (Kernel.partialTraj_comp_partialTraj hak (by omega)).symm
    rw [hc]
    exact Kernel.ae_comp_of_ae_ae hm (Eventually.of_forall (rawExtension_strict_step k))
  rw [← he] at ht
  exact (ae_map_iff (rawPrefix_measurable (show k+1 ≤ b by omega)).aemeasurable hm).mp ht

lemma increasingCosts_of_steps {a b : ℕ} (h : RawHistory b)
    (hs : ∀ k : Fin b, a ≤ k.1 →
      (h ⟨k.1,Finset.mem_Iic.mpr (by have hk:=k.2; omega)⟩).2 ≤
        (h ⟨k.1+1,Finset.mem_Iic.mpr (by have hk:=k.2; omega)⟩).2) :
    h ∈ increasingCosts a b := by
  intro i j hai hij
  have aux : ∀ m, i.1 ≤ m → ∀ hm : m ≤ b, (h i).2 ≤ (h ⟨m,Finset.mem_Iic.mpr hm⟩).2 := by
    intro m him
    induction m,him using Nat.le_induction with
    | base => intro hm; exact le_rfl
    | succ m him ih =>
      intro hmb
      have hmb' : m < b := by omega
      exact (ih (by omega)).trans (hs ⟨m,hmb'⟩ (hai.trans him))
  exact aux j.1 hij (Finset.mem_Iic.mp j.2)

theorem rawExtension_increasingCosts (a b : ℕ) (h : RawHistory a) :
    ∀ᵐ y ∂rawExtension a b h, y ∈ increasingCosts a b := by
  have hs : ∀ᵐ y ∂rawExtension a b h, ∀ k : Fin b, a ≤ k.1 →
      (y ⟨k.1,Finset.mem_Iic.mpr (by have hk:=k.2; omega)⟩).2 <
        (y ⟨k.1+1,Finset.mem_Iic.mpr (by have hk:=k.2; omega)⟩).2 := by
    rw [ae_all_iff]
    intro k
    by_cases hak : a ≤ k.1
    · filter_upwards [rawExtension_strict_coordinate hak k.2 h] with y hy
      exact fun _ => hy
    · exact Eventually.of_forall (fun _ hy => (hak hy).elim)
  filter_upwards [hs] with y hy
  exact increasingCosts_of_steps y (fun k hk => (hy k hk).le)

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_RawCompactPlacement
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.FinitePathGeometry
open NumberTheoryLean.FirstHitKernels

lemma gapAt_antitone_cost {r T U : ℝ} (hr : 0 ≤ r) (hTU : T ≤ U) : gapAt r U ≤ gapAt r T :=
  mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hTU)) hr

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_ArrivalKernelGeometry
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.initialBeginningReg_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.initialMarkedBeginning_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.initialMarkedCostLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markInputWeightKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindow_stop_isMarkov _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWitnessKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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

theorem costKernel_exponent_nonincreasing (v : ℝ) (z : CostState) :
    ∀ᵐ y ∂costKernel z, currentExponent v y ≤ currentExponent v z := by
  have hm : Measurable (fun s : State => (s, z.2 + cost (stateRatio s))) :=
    measurable_id.prodMk (measurable_const.add (cost_measurable.comp stateRatio_measurable))
  have hp : MeasurableSet {y : CostState | currentExponent v y ≤ currentExponent v z} :=
    measurableSet_le (currentExponent_measurable v) measurable_const
  rw [costKernel_eq_map]
  apply (ae_map_iff hm.aemeasurable hp).mpr
  filter_upwards [stateKernel_ae_minRatio z.1] with s hs
  rw [currentExponent_update]
  exact exponent_le_cutoff (stateRatio_valid z.1) hs (Real.exp_pos _)

end NumberTheoryLean.ArrivalKernelGeometry

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_RawSuppliedPast
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures

variable (F : CostState → ℝ) (hF : Measurable F)
variable (hStep : ∀ z, ∀ᵐ y ∂costKernel z, F z ≤ F y)

include hF hStep in
lemma rawExtension_scalar_step (k : ℕ) (h : RawHistory k) :
    ∀ᵐ y ∂rawExtension k (k+1) h,
      F (y ⟨k,Finset.mem_Iic.mpr (by omega)⟩) ≤ F (rawLast (k+1) y) := by
  have hs : ∀ᵐ y ∂rawExtension k (k+1) h, F (rawLast k h) ≤ F (rawLast (k+1) y) := by
    apply (ae_map_iff (rawLast_measurable (k+1)).aemeasurable
      (measurableSet_le measurable_const hF)).mp
    rw [rawExtension_last_step]
    exact hStep _
  filter_upwards [hs,rawExtension_retains_prefix (show k ≤ k+1 by omega) h] with y hy hp
  have he := congrFun hp (⟨k,by simp⟩ : Finset.Iic k)
  change y ⟨k,_⟩=rawLast k h at he
  rw [he]
  exact hy

include hF hStep in
lemma rawExtension_scalar_coordinate {a b k : ℕ} (hak : a ≤ k) (hkb : k < b) (h : RawHistory a) :
    ∀ᵐ y ∂rawExtension a b h,
      F (y ⟨k,Finset.mem_Iic.mpr (by omega)⟩) ≤ F (y ⟨k+1,Finset.mem_Iic.mpr (by omega)⟩) := by
  have hm : MeasurableSet {y : RawHistory (k+1) |
      F (y ⟨k,Finset.mem_Iic.mpr (by omega)⟩) ≤ F (rawLast (k+1) y)} :=
    measurableSet_le (hF.comp (measurable_pi_apply _)) (hF.comp (rawLast_measurable _))
  have he : (rawExtension a b h).map (rawPrefix (show k+1 ≤ b by omega))=rawExtension a (k+1) h :=
    Kernel.partialTraj_map_frestrictLe₂_apply (X := fun _ => CostState) (κ := historyKernel) h (show k+1 ≤ b by omega)
  have ht : ∀ᵐ y ∂rawExtension a (k+1) h,
      F (y ⟨k,Finset.mem_Iic.mpr (by omega)⟩) ≤ F (rawLast (k+1) y) := by
    have hc : rawExtension a (k+1)=rawExtension k (k+1) ∘ₖ rawExtension a k :=
      (Kernel.partialTraj_comp_partialTraj hak (by omega)).symm
    rw [hc]
    exact Kernel.ae_comp_of_ae_ae hm (Eventually.of_forall (rawExtension_scalar_step F hF hStep k))
  rw [← he] at ht
  exact (ae_map_iff (rawPrefix_measurable (show k+1 ≤ b by omega)).aemeasurable hm).mp ht

include hF hStep in
lemma rawExtension_scalarIncreasing (a b : ℕ) (h : RawHistory a) :
    ∀ᵐ y ∂rawExtension a b h, y ∈ scalarIncreasing F a b := by
  have hs : ∀ᵐ y ∂rawExtension a b h, ∀ k : Fin b, a ≤ k.1 →
      F (y ⟨k.1,Finset.mem_Iic.mpr (by have hk:=k.2; omega)⟩) ≤
        F (y ⟨k.1+1,Finset.mem_Iic.mpr (by have hk:=k.2; omega)⟩) := by
    rw [ae_all_iff]
    intro k
    by_cases hak : a ≤ k.1
    · filter_upwards [rawExtension_scalar_coordinate F hF hStep hak k.2 h] with y hy
      exact fun _ => hy
    · exact Eventually.of_forall (fun _ hy => (hak hy).elim)
  filter_upwards [hs] with y hy
  exact increasingCosts_of_steps (scalarHistory F b y) hy

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.FinitePathGeometry
open NumberTheoryLean.TransitionKernels NumberTheoryLean.RegeneratingInverseBands
open NumberTheoryLean.ArrivalKernelGeometry

lemma gapValue_log_eq_gapAt {r : ℝ} (hr : 0 < r) (z : CostState) :
    gapValue (Real.log r) z=gapAt r z.2 := by
  unfold gapValue gapAt
  rw [Real.exp_sub,Real.exp_log hr,Real.exp_neg,div_eq_mul_inv]

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FiniteVisitMass
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.TransitionKernels

lemma finiteRawLast_measurable : Measurable finiteRawLast := by
  apply measurable_sigma_family
  intro n
  exact rawLast_measurable n

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.FirstHitKernels
open NumberTheoryLean.FinitePathGeometry

lemma finiteRawLength_measurable : Measurable (fun q : FiniteRawHistory => q.1) := by
  apply measurable_sigma_family
  intro n
  exact measurable_const

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_CanonicalPairHitEvents
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.FirstHitKernels

lemma pairHitTest_prefix {a k b c : ℕ} (hab : a+2*k+1 ≤ b) (hbc : b ≤ c) (v H : ℝ) :
    rawPrefix hbc ⁻¹' pairHitTest a k b hab v H=pairHitTest a k c (hab.trans hbc) v H := rfl

lemma noPairHits_prefix {a m b c : ℕ} (hab : a+2*m ≤ b) (hbc : b ≤ c) (v H : ℝ) :
    rawPrefix hbc ⁻¹' noPairHits a m b hab v H=noPairHits a m c (hab.trans hbc) v H := rfl

lemma noPairHits_zero (a b : ℕ) (hab : a+2*0 ≤ b) (v H : ℝ) :
    noPairHits a 0 b hab v H=univ := by
  ext h
  simp [noPairHits]

lemma noPairHits_succ (a n b : ℕ) (hab : a+2*(n+1) ≤ b) (v H : ℝ) :
    noPairHits a (n+1) b hab v H =
      noPairHits a n b (by omega) v H ∩ (pairHitTest a n b (by omega) v H)ᶜ := by
  ext h
  change (∀ k : Fin (n+1), h ∉ pairHitTest a k.1 b _ v H) ↔
    (∀ k : Fin n, h ∉ pairHitTest a k.1 b _ v H) ∧ h ∉ pairHitTest a n b _ v H
  constructor
  · intro hh
    exact ⟨fun k => hh k.castSucc,hh (Fin.last n)⟩
  · rintro ⟨hh,hn⟩ k
    by_cases hk : k.1 < n
    · exact hh ⟨k.1,hk⟩
    · have he : k.1=n := by have := k.2; omega
      have hkLast : k=Fin.last n := Fin.ext he
      subst k
      exact hn

lemma firstPairHitEvent_prefix {a n b c : ℕ} (hab : a+2*n+1 ≤ b) (hbc : b ≤ c) (v H : ℝ) :
    rawPrefix hbc ⁻¹' firstPairHitEvent a n b hab v H=firstPairHitEvent a n c (hab.trans hbc) v H := rfl

lemma firstPairHitEvent_disjoint {a n m b : ℕ} (hn : a+2*n+1 ≤ b) (hm : a+2*m+1 ≤ b)
    (hnm : n ≠ m) (v H : ℝ) : Disjoint (firstPairHitEvent a n b hn v H) (firstPairHitEvent a m b hm v H) := by
  apply disjoint_left.mpr
  intro h hN hM
  obtain hlt | hgt := lt_or_gt_of_ne hnm
  · exact (hM.1 ⟨n,hlt⟩) hN.2
  · exact (hN.1 ⟨m,hgt⟩) hM.2

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_CanonicalPairCylinders
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

lemma pairSurvivingHistory_zero (a : ℕ) (v H : ℝ) : pairSurvivingHistory a 0 v H=Kernel.id := by
  ext h S hS
  rw [pairSurvivingHistory,Kernel.restrict_apply' _ _ _ hS,noPairHits_zero,inter_univ]
  simp only [Nat.mul_zero,Nat.add_zero,rawExtension,Kernel.partialTraj_self]

lemma pairStoppedHistory_zero (a : ℕ) (v H : ℝ) :
    pairStoppedHistory a 0 v H=(rawExtension a (a+1)).restrict
      (pairHitTest_measurable a 0 (a+1) (by omega) v H) := by
  ext h S hS
  rw [pairStoppedHistory,Kernel.restrict_apply' _ _ _ hS,Kernel.restrict_apply' _ _ _ hS,
    firstPairHitEvent,noPairHits_zero,univ_inter]

theorem pairSurvivingHistory_succ (a n : ℕ) (v H : ℝ) :
    pairSurvivingHistory a (n+1) v H=
      ((rawExtension (a+2*n) (a+2*(n+1))).restrict
        (pairHitTest_measurable a n (a+2*(n+1)) (by omega) v H).compl) ∘ₖ
      pairSurvivingHistory a n v H := by
  unfold pairSurvivingHistory
  rw [← rawExtension_restrict_comp (show a ≤ a+2*n by omega) (show a+2*n ≤ a+2*(n+1) by omega)
    (noPairHits_measurable a n (a+2*n) le_rfl v H)
    (pairHitTest_measurable a n (a+2*(n+1)) (by omega) v H).compl]
  congr 1
  rw [noPairHits_prefix,noPairHits_succ]

theorem pairStoppedHistory_factor (a n : ℕ) (v H : ℝ) :
    pairStoppedHistory a n v H=
      ((rawExtension (a+2*n) (a+2*n+1)).restrict
        (pairHitTest_measurable a n (a+2*n+1) le_rfl v H)) ∘ₖ pairSurvivingHistory a n v H := by
  unfold pairStoppedHistory pairSurvivingHistory
  rw [← rawExtension_restrict_comp (show a ≤ a+2*n by omega) (show a+2*n ≤ a+2*n+1 by omega)
    (noPairHits_measurable a n (a+2*n) le_rfl v H)
    (pairHitTest_measurable a n (a+2*n+1) le_rfl v H)]
  congr 1

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_ConsecutivePairStop
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical

lemma boundedPairCylinder_disjoint (a N : ℕ) (v H : ℝ) :
    Pairwise (fun n m : ℕ => Disjoint (boundedPairCylinder a N n v H) (boundedPairCylinder a N m v H)) := by
  intro n m hnm
  unfold boundedPairCylinder
  split_ifs with hn hm
  · exact firstPairHitEvent_disjoint hn hm hnm v H
  all_goals simp

theorem firstPairHit_union_eq_any (a N : ℕ) (v H : ℝ) :
    (⋃ n ∈ Finset.range (N+1), boundedPairCylinder a N n v H)=anyPairHit a N v H := by
  ext h
  constructor
  · intro hh
    obtain ⟨n,hh⟩ := mem_iUnion.mp hh
    obtain ⟨_hn,hh⟩ := mem_iUnion.mp hh
    by_cases hn : a+2*n+1 ≤ N
    · rw [boundedPairCylinder,dite_eq_left hn] at hh
      exact ⟨n,hn,hh.2⟩
    · simp [boundedPairCylinder,hn] at hh
  · intro hh
    have hex : ∃ n : ℕ, ∃ hn : a+2*n+1 ≤ N, h ∈ pairHitTest a n N hn v H := hh
    obtain ⟨hn,hHit⟩ := Nat.find_spec hex
    have hNo : h ∈ noPairHits a (Nat.find hex) N (by omega) v H := by
      intro k hk
      exact (Nat.find_min hex k.2) ⟨(by have h:=k.2; omega),hk⟩
    refine mem_iUnion.mpr ⟨Nat.find hex,mem_iUnion.mpr ⟨?_,?_⟩⟩
    · exact Finset.mem_range.mpr (by omega)
    · rw [boundedPairCylinder,dite_eq_left hn]
      exact ⟨hNo,hHit⟩

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical

theorem completedPairHit_eq_extension {a N n : ℕ} (hn : a+2*n+1 ≤ N) (v H : ℝ) :
    completedPairHit a N n v H=rawExtension (a+2*n+1) N ∘ₖ pairStoppedHistory a n v H := by
  unfold completedPairHit pairStoppedHistory
  have hB := firstPairHitEvent_measurable a n (a+2*n+1) le_rfl v H
  have he := rawExtension_restrict_comp (show a ≤ a+2*n+1 by omega) hn hB MeasurableSet.univ
  rw [Kernel.restrict_univ] at he
  have hc : boundedPairCylinder a N n v H=
      rawPrefix hn ⁻¹' firstPairHitEvent a n (a+2*n+1) le_rfl v H ∩ univ := by
    rw [boundedPairCylinder,dite_eq_left hn,inter_univ,firstPairHitEvent_prefix]
  ext past S hS
  have heS := congrArg (fun K : Kernel (RawHistory a) (RawHistory N) => K past S) he
  rw [Kernel.restrict_apply' _ _ _ hS] at heS
  rw [Kernel.restrict_apply' _ _ _ hS,hc]
  exact heS

lemma firstPairHit_iUnion_eq_any (a N : ℕ) (v H : ℝ) :
    (⋃ n : ℕ, boundedPairCylinder a N n v H)=anyPairHit a N v H := by
  rw [← firstPairHit_union_eq_any]
  apply Subset.antisymm
  · intro h hh
    obtain ⟨n,hC⟩ := mem_iUnion.mp hh
    have hn : a+2*n+1 ≤ N := by
      by_contra hn
      simp [boundedPairCylinder,hn] at hC
    exact mem_iUnion.mpr ⟨n,mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega),hC⟩⟩
  · intro h hh
    obtain ⟨n,hh⟩ := mem_iUnion.mp hh
    obtain ⟨_hn,hC⟩ := mem_iUnion.mp hh
    exact mem_iUnion.mpr ⟨n,hC⟩

theorem completedPairHit_sum (a N : ℕ) (v H : ℝ) :
    Kernel.sum (fun n : ℕ => completedPairHit a N n v H)=
      (rawExtension a N).restrict (anyPairHit_measurable a N v H) := by
  ext past S hS
  rw [Kernel.sum_apply' _ _ hS,Kernel.restrict_apply]
  have he := Measure.restrict_iUnion (μ := rawExtension a N past)
    (boundedPairCylinder_disjoint a N v H) (fun n => boundedPairCylinder_measurable a N n v H)
  rw [firstPairHit_iUnion_eq_any] at he
  rw [he,Measure.sum_apply _ hS]
  apply tsum_congr
  intro n
  rw [completedPairHit,Kernel.restrict_apply]

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.FirstHitKernels
open NumberTheoryLean.KernelPotential

theorem consecutive_first_partition (v H : ℝ) :
    consecutiveCapture v H+consecutiveFirstContinue v H=costKernel := by
  ext z S hS
  rw [_root_.add_apply,Measure.add_apply,consecutiveCapture,stateFilter_input,
    consecutiveFirstContinue,Kernel.piecewise_apply]
  by_cases hz : z ∈ regenerativeCostWindow v H
  · rw [ite_eq_left hz,ite_eq_left hz,Kernel.restrict_apply,Kernel.restrict_apply,
      ← Measure.add_apply,Measure.restrict_add_restrict_compl markedArrival_measurable]
  · rw [ite_eq_right hz,ite_eq_right hz]
    simp

instance consecutive_stop_isMarkov (v H : ℝ) : IsMarkovKernel (consecutiveCapture v H+consecutiveContinue v H) := by
  constructor
  intro z
  constructor
  rw [_root_.add_apply,Measure.add_apply,consecutiveContinue,Kernel.comp_apply' _ _ _ MeasurableSet.univ]
  have hm : (∫⁻ y, costKernel y univ ∂consecutiveFirstContinue v H z)=consecutiveFirstContinue v H z univ := by
    simp
  rw [hm,← Measure.add_apply,← _root_.add_apply,consecutive_first_partition]
  exact measure_univ

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ConsecutivePowerProjection
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical
open NumberTheoryLean.FinitePathMeasures

lemma pairHitTest_first_eq (a : ℕ) (v H : ℝ) :
    pairHitTest a 0 (a+1) (by omega) v H =
      (rawPrefix (show a ≤ a+1 by omega) ⁻¹' historyGoodInput a v H) ∩ firstPrefixMarkEvent a true := by
  ext h
  change (_ ∧ _ ∧ _) ↔ ((_ ∧ _) ∧ _)
  constructor
  · rintro ⟨hR,hM,hW⟩
    exact ⟨⟨hR,hW⟩,hM⟩
  · rintro ⟨⟨hR,hW⟩,hM⟩
    exact ⟨hR,hM,hW⟩

theorem pairStoppedHistory_zero_input_filter (a : ℕ) (v H : ℝ) :
    pairStoppedHistory a 0 v H=
      ((rawExtension a (a+1)).restrict (firstPrefixMarkEvent_measurable a true)) ∘ₖ
        stateFilter (historyGoodInput_measurable a v H) := by
  rw [pairStoppedHistory_zero]
  have he := restriction_comp_of_retained_prefix (Kernel.id : Kernel (RawHistory a) (RawHistory a))
    (rawExtension a (a+1)) (rawPrefix_measurable (show a ≤ a+1 by omega))
    (rawExtension_retains_prefix (show a ≤ a+1 by omega))
    (historyGoodInput_measurable a v H) (firstPrefixMarkEvent_measurable a true)
  rw [Kernel.comp_id] at he
  ext past S hS
  have heS := congrArg (fun K : Kernel (RawHistory a) (RawHistory (a+1)) => K past S) he
  rw [Kernel.restrict_apply' _ _ _ hS] at heS
  rw [Kernel.restrict_apply' _ _ _ hS,pairHitTest_first_eq]
  exact heS

theorem canonical_capture_projection (a : ℕ) (v H : ℝ) (past : RawHistory a) :
    (pairStoppedHistory a 0 v H past).map (rawLast (a+1))=consecutiveCapture v H (rawLast a past) := by
  rw [pairStoppedHistory_zero_input_filter,stateFilter_input,consecutiveCapture,stateFilter_input]
  by_cases hp : rawLast a past ∈ regenerativeCostWindow v H
  · have hh : past ∈ historyGoodInput a v H := hp
    rw [ite_eq_left hh,ite_eq_left hp,Kernel.restrict_apply,Kernel.restrict_apply]
    change ((rawExtension a (a+1) past).restrict ((rawLast (a+1)) ⁻¹' markedArrival)).map (rawLast (a+1))=_
    rw [← Measure.restrict_map (rawLast_measurable (a+1)) markedArrival_measurable,rawExtension_last_step]
  · have hh : past ∉ historyGoodInput a v H := hp
    rw [ite_eq_right hh,ite_eq_right hp,Measure.map_zero]

lemma firstHistory_partition (a : ℕ) (v H : ℝ) :
    pairStoppedHistory a 0 v H+firstNoHitHistory a v H=rawExtension a (a+1) := by
  ext past S hS
  rw [_root_.add_apply,Measure.add_apply,pairStoppedHistory_zero,firstNoHitHistory,
    Kernel.restrict_apply,Kernel.restrict_apply,← Measure.add_apply,
    Measure.restrict_add_restrict_compl (pairHitTest_measurable a 0 (a+1) (by omega) v H)]

theorem canonical_first_continue_projection (a : ℕ) (v H : ℝ) (past : RawHistory a) :
    (firstNoHitHistory a v H past).map (rawLast (a+1))=consecutiveFirstContinue v H (rawLast a past) := by
  have hPart := congrArg (fun K : Kernel (RawHistory a) (RawHistory (a+1)) =>
    (K past).map (rawLast (a+1))) (firstHistory_partition a v H)
  rw [_root_.add_apply,Measure.map_add _ _ (rawLast_measurable (a+1)),
    canonical_capture_projection,rawExtension_last_step] at hPart
  have hOther := congrArg (fun K : Kernel CostState CostState => K (rawLast a past)) (consecutive_first_partition v H)
  rw [_root_.add_apply] at hOther
  ext S _hS
  have he := congrArg (fun μ : Measure CostState => μ S) (hPart.trans hOther.symm)
  simp only [Measure.add_apply] at he
  exact (ENNReal.add_right_inj (measure_ne_top (consecutiveCapture v H (rawLast a past)) S)).mp he

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures

theorem noHitPairHistory_factor (a : ℕ) (v H : ℝ) :
    noHitPairHistory a v H=rawExtension (a+1) (a+2) ∘ₖ firstNoHitHistory a v H := by
  unfold noHitPairHistory firstNoHitHistory
  have he := rawExtension_restrict_comp (show a ≤ a+1 by omega) (show a+1 ≤ a+2 by omega)
    (pairHitTest_measurable a 0 (a+1) (by omega) v H).compl MeasurableSet.univ
  rw [Kernel.restrict_univ] at he
  ext past S hS
  have heS := congrArg (fun K : Kernel (RawHistory a) (RawHistory (a+2)) => K past S) he
  rw [Kernel.restrict_apply' _ _ _ hS] at heS
  rw [Kernel.restrict_apply' _ _ _ hS]
  have hSet : (rawPrefix (show a+1 ≤ a+2 by omega) ⁻¹' (pairHitTest a 0 (a+1) (by omega) v H)ᶜ) ∩ univ=
      (pairHitTest a 0 (a+2) (by omega) v H)ᶜ := by
    rw [inter_univ,preimage_compl,pairHitTest_prefix]
  rw [hSet] at heS
  exact heS

theorem canonical_pair_continue_projection (a : ℕ) (v H : ℝ) (past : RawHistory a) :
    (noHitPairHistory a v H past).map (rawLast (a+2))=consecutiveContinue v H (rawLast a past) := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (rawLast_measurable (a+2)),noHitPairHistory_factor,
    Kernel.lintegral_comp _ _ _ (g := fun h => F (rawLast (a+2) h)) (hF.comp (rawLast_measurable (a+2)))]
  have he (h : RawHistory (a+1)) :
      (∫⁻ y, F (rawLast (a+2) y) ∂rawExtension (a+1) (a+2) h)=∫⁻ z, F z ∂costKernel (rawLast (a+1) h) := by
    rw [← lintegral_map (g := rawLast (a+2)) hF (rawLast_measurable (a+2)),rawExtension_last_step]
  simp_rw [he]
  have hG : Measurable (fun z : CostState => ∫⁻ y, F y ∂costKernel z) := hF.lintegral_kernel
  rw [← lintegral_map (g := rawLast (a+1)) hG (rawLast_measurable (a+1)),canonical_first_continue_projection,
    consecutiveContinue,Kernel.lintegral_comp _ _ _ hF]

lemma shifted_pair_continue_projection (a n b : ℕ) (hb : b=(a+2*n)+2) (v H : ℝ)
    (past : RawHistory (a+2*n)) :
    (((rawExtension (a+2*n) b).restrict
      (pairHitTest_measurable a n b (by omega) v H).compl) past).map (rawLast b)=
        consecutiveContinue v H (rawLast (a+2*n) past) := by
  subst b
  exact canonical_pair_continue_projection (a+2*n) v H past

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures

theorem pairSurvivingHistory_projection (a n : ℕ) (v H : ℝ) (past : RawHistory a) :
    (pairSurvivingHistory a n v H past).map (rawLast (a+2*n))=
      ((consecutiveContinue v H)^n) (rawLast a past) := by
  have (m : ℕ) : IsSFiniteKernel ((consecutiveContinue v H)^m) := kernel_power_sfinite _ m
  induction n with
  | zero =>
    rw [pairSurvivingHistory_zero]
    change (Measure.dirac past).map (rawLast a)=Measure.dirac (rawLast a past)
    exact Measure.map_dirac' (rawLast_measurable a) past
  | succ n ih =>
    apply Measure.ext_of_lintegral
    intro F hF
    rw [lintegral_map hF (rawLast_measurable _),pairSurvivingHistory_succ,
      Kernel.lintegral_comp _ _ _ (g := fun h => F (rawLast (a+2*(n+1)) h)) (hF.comp (rawLast_measurable _))]
    have he (h : RawHistory (a+2*n)) :
        (∫⁻ y, F (rawLast (a+2*(n+1)) y) ∂((rawExtension (a+2*n) (a+2*(n+1))).restrict
          (pairHitTest_measurable a n (a+2*(n+1)) (by omega) v H).compl) h)=
          ∫⁻ z, F z ∂consecutiveContinue v H (rawLast (a+2*n) h) := by
      rw [← lintegral_map (g := rawLast (a+2*(n+1))) hF (rawLast_measurable _),
        shifted_pair_continue_projection a n (a+2*(n+1)) (by omega) v H h]
    simp_rw [he]
    have hG : Measurable (fun z : CostState => ∫⁻ y, F y ∂consecutiveContinue v H z) := hF.lintegral_kernel
    rw [← lintegral_map (g := rawLast (a+2*n)) hG (rawLast_measurable _),ih,pow_succ']
    change (∫⁻ z, ∫⁻ y, F y ∂consecutiveContinue v H z ∂((consecutiveContinue v H)^n) (rawLast a past))=
      ∫⁻ y, F y ∂(consecutiveContinue v H ∘ₖ ((consecutiveContinue v H)^n)) (rawLast a past)
    exact (Kernel.lintegral_comp _ _ _ hF).symm

theorem pairStoppedHistory_projection (a n : ℕ) (v H : ℝ) (past : RawHistory a) :
    (pairStoppedHistory a n v H past).map (rawLast (a+2*n+1))=
      (consecutiveCapture v H ∘ₖ ((consecutiveContinue v H)^n)) (rawLast a past) := by
  have : IsSFiniteKernel ((consecutiveContinue v H)^n) := kernel_power_sfinite _ n
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (rawLast_measurable _),pairStoppedHistory_factor,
    Kernel.lintegral_comp _ _ _ (g := fun h => F (rawLast (a+2*n+1) h)) (hF.comp (rawLast_measurable _))]
  have he (h : RawHistory (a+2*n)) :
      (∫⁻ y, F (rawLast (a+2*n+1) y) ∂((rawExtension (a+2*n) (a+2*n+1)).restrict
        (pairHitTest_measurable a n (a+2*n+1) le_rfl v H)) h)=
        ∫⁻ z, F z ∂consecutiveCapture v H (rawLast (a+2*n) h) := by
    have hP := canonical_capture_projection (a+2*n) v H h
    rw [pairStoppedHistory_zero] at hP
    rw [← lintegral_map (g := rawLast (a+2*n+1)) hF (rawLast_measurable _)]
    exact congrArg (fun μ : Measure CostState => ∫⁻ z, F z ∂μ) hP
  simp_rw [he]
  have hG : Measurable (fun z : CostState => ∫⁻ y, F y ∂consecutiveCapture v H z) := hF.lintegral_kernel
  rw [← lintegral_map (g := rawLast (a+2*n)) hG (rawLast_measurable _),
    pairSurvivingHistory_projection,Kernel.lintegral_comp _ _ _ hF]

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_CanonicalPairVisitLaw
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.KernelPotential

theorem canonicalPairVisit_endpoint (a : ℕ) (v H : ℝ) (past : RawHistory a) :
    (canonicalPairVisitKernel a v H past).map finiteRawLast=consecutiveMarkedHit v H (rawLast a past) := by
  rw [canonicalPairVisitKernel,Kernel.sum_apply,Measure.map_sum finiteRawLast_measurable.aemeasurable,
    consecutiveMarkedHit,potential,Kernel.sum_apply]
  apply congrArg Measure.sum
  funext n
  rw [Kernel.map_apply _ (measurableSigmaMk (a+2*n+1)),
    Measure.map_map finiteRawLast_measurable (measurableSigmaMk (a+2*n+1))]
  exact pairStoppedHistory_projection a n v H past

lemma canonicalPairVisit_mass (a : ℕ) (v H : ℝ) (past : RawHistory a) :
    canonicalPairVisitKernel a v H past univ=consecutiveMarkedHit v H (rawLast a past) univ := by
  have he := congrArg (fun μ : Measure CostState => μ univ) (canonicalPairVisit_endpoint a v H past)
  rw [Measure.map_apply finiteRawLast_measurable MeasurableSet.univ,preimage_univ] at he
  exact he

lemma extendFinitePrefix_comp_map {α : Type*} [MeasurableSpace α] (N n : ℕ)
    (K : Kernel α (RawHistory n)) [IsSFiniteKernel K] :
    extendFinitePrefix N ∘ₖ K.map (@Sigma.mk ℕ RawHistory n)=
      if n ≤ N then rawExtension n N ∘ₖ K else 0 := by
  ext x S hS
  rw [Kernel.comp_apply' _ _ _ hS,Kernel.map_apply _ (measurableSigmaMk n),
    lintegral_map ((extendFinitePrefix N).measurable_coe hS) (measurableSigmaMk n)]
  by_cases hn : n ≤ N
  · rw [ite_eq_left hn,Kernel.comp_apply' _ _ _ hS]
    apply lintegral_congr
    intro h
    change (if n ≤ N then rawExtension n N h else 0) S=rawExtension n N h S
    rw [ite_eq_left hn]
  · rw [ite_eq_right hn]
    change (∫⁻ h, (if n ≤ N then rawExtension n N h else 0) S ∂K x)=0
    simp [hn]

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_CanonicalPairVisitCompletion
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical

theorem canonicalPairVisit_completion (a N : ℕ) (v H : ℝ) :
    extendFinitePrefix N ∘ₖ canonicalPairVisitKernel a v H=
      (rawExtension a N).restrict (anyPairHit_measurable a N v H) := by
  rw [canonicalPairVisitKernel,Kernel.comp_sum_right,← completedPairHit_sum]
  apply congrArg Kernel.sum
  funext n
  rw [extendFinitePrefix_comp_map]
  by_cases hn : a+2*n+1 ≤ N
  · rw [ite_eq_left hn,completedPairHit_eq_extension hn]
  · rw [ite_eq_right hn]
    ext past S hS
    rw [completedPairHit,Kernel.restrict_apply' _ _ _ hS,boundedPairCylinder,
      dite_eq_right hn,inter_empty]
    simp

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_RegenerationInputPotential
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.CostReturnLaw
open NumberTheoryLean.InitialRegeneration NumberTheoryLean.KernelPotential

lemma regenerationInput_after_pair : regenerationInput ∘ₖ pairedCostKernel=costCaptured := by
  rw [regenerationInput,stateFilter_output]
  rfl

lemma nonregenerationInput_after_pair : nonregenerationInput ∘ₖ pairedCostKernel=costKilled := by
  rw [nonregenerationInput,stateFilter_output]
  rfl

lemma returnLaw_potential : returnLaw=potential costCaptured costKilled := rfl

lemma hitOrReturn_input_split : hitOrReturn=regenerationInput+returnLaw ∘ₖ nonregenerationInput := by
  ext z S hS
  rw [hitOrReturn,Kernel.piecewise_apply,_root_.add_apply,Measure.add_apply,
    regenerationInput,stateFilter_apply,nonregenerationInput,stateFilter_input]
  by_cases hz : z ∈ returnSet
  · simp only [hz,ite_true, if_true,mem_compl_iff,not_true_eq_false,ite_false, if_false,Measure.coe_zero,Pi.zero_apply,add_zero]
    rfl
  · simp only [hz,ite_false, if_false,mem_compl_iff,not_false_eq_true,ite_true, if_true,Measure.coe_zero,Pi.zero_apply,zero_add]

theorem hitOrReturn_eq_input_potential :
    hitOrReturn=potential regenerationInput (pairedCostKernel ∘ₖ nonregenerationInput) := by
  have hR : returnLaw=
      (potential regenerationInput (pairedCostKernel ∘ₖ nonregenerationInput)) ∘ₖ pairedCostKernel := by
    rw [returnLaw_potential,← regenerationInput_after_pair,← nonregenerationInput_after_pair]
    exact potential_exchange regenerationInput pairedCostKernel nonregenerationInput
  rw [potential_unfold,← Kernel.comp_assoc,← hR]
  exact hitOrReturn_input_split

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_PairBranchFullProjection
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.InitialRegeneration

lemma markedKernel_branch_lintegral (K : Kernel OddCost MarkedOddCost) (b : Bool) (z : OddCost)
    {F : OddCost → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y, F y ∂((K.restrict (measurable_fst (measurableSet_singleton b))).map Prod.snd) z)=
      ∫⁻ y, (if y.1=b then F y.2 else 0) ∂K z := by
  rw [Kernel.map_apply _ measurable_snd,Kernel.restrict_apply,lintegral_map hF measurable_snd,
    ← lintegral_indicator (measurable_fst (measurableSet_singleton b))]
  apply lintegral_congr
  intro y
  simp only [Set.indicator_apply,mem_preimage,mem_singleton_iff]

lemma markContinuation_measure (z : MarkedOddCost) :
    markContinuation z=(hitOrReturn z.2).map (Prod.mk z.1) := by
  ext S hS
  rw [markContinuation_apply _ hS,Measure.map_apply measurable_prodMk_left hS]
  rfl

theorem cycleBranch_completion (b : Bool) : cycleBranchKernel b=hitOrReturn ∘ₖ pairBranchKernel b := by
  ext z : 1
  apply Measure.ext_of_lintegral
  intro F hF
  let G : MarkedOddCost → ℝ≥0∞ := fun y => if y.1=b then F y.2 else 0
  have hG : Measurable G := Measurable.ite (measurable_fst (measurableSet_singleton b))
    (hF.comp measurable_snd) measurable_const
  have hJ : Measurable (fun y : OddCost => ∫⁻ t, F t ∂hitOrReturn y) := hF.lintegral_kernel
  rw [cycleBranchKernel,markedKernel_branch_lintegral _ b z hF]
  change (∫⁻ y, G y ∂completedMarkedKernel z)=_
  rw [completedMarkedKernel,Kernel.lintegral_comp _ _ _ hG,Kernel.lintegral_comp _ _ _ hF,
    pairBranchKernel,markedKernel_branch_lintegral _ b z hJ]
  apply lintegral_congr
  intro y
  rw [markContinuation_measure,lintegral_map hG measurable_prodMk_left]
  by_cases hy : y.1=b <;> simp [G,hy]

lemma pairBranch_sum : pairBranchKernel true+pairBranchKernel false=NumberTheoryLean.PairedCostProcess.pairedCostKernel := by
  ext z : 1
  rw [_root_.add_apply]
  unfold pairBranchKernel
  rw [Kernel.map_apply _ measurable_snd,Kernel.map_apply _ measurable_snd,Kernel.restrict_apply,Kernel.restrict_apply]
  change ((markedPairKernel z).restrict {y | y.1=true}).map Prod.snd+
    ((markedPairKernel z).restrict {y | y.1=false}).map Prod.snd=_
  rw [false_mark_set]
  change ((markedPairKernel z).restrict sourceMarkSet).map Prod.snd+
    ((markedPairKernel z).restrict sourceMarkSetᶜ).map Prod.snd=_
  rw [← Measure.map_add _ _ measurable_snd,Measure.restrict_add_restrict_compl sourceMarkSet_measurable,markedPair_forget]

lemma nextMarkWeight_pair_mass (z : OddCost) : nextMarkWeight z=pairBranchKernel true z univ := by
  rw [nextMarkWeight,cycleBranch_completion,Kernel.comp_apply' _ _ _ MeasurableSet.univ]
  simp

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping

lemma pairBranch_full_lintegral (b : Bool) (z : OddCost) {F : CostState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y, F (embedOdd y) ∂pairBranchKernel b z)=
      ∫⁻ s, (if firstArrivalMark s=b then ∫⁻ t, F t ∂costKernel s else 0) ∂costKernel (embedOdd z) := by
  let G : MarkedOddCost → ℝ≥0∞ := fun y => if y.1=b then F (embedOdd y.2) else 0
  have hG : Measurable G := Measurable.ite (measurable_fst (measurableSet_singleton b))
    (hF.comp (embedOdd_measurable.comp measurable_snd)) measurable_const
  let J : CostState × CostState → ℝ≥0∞ := fun y => if firstArrivalMark y.1=b then F y.2 else 0
  have hJ : Measurable J := Measurable.ite ((firstArrivalMark_measurable.comp measurable_fst) (measurableSet_singleton b))
    (hF.comp measurable_snd) measurable_const
  rw [pairBranchKernel,markedKernel_branch_lintegral _ b z (F := fun y => F (embedOdd y)) (hF.comp embedOdd_measurable)]
  change (∫⁻ y, G y ∂markedPairKernel z)=_
  rw [← pairWitness_projection z,lintegral_map hG firstPairProjection_measurable]
  calc
    _ = ∫⁻ y, J y ∂fullPairTraceKernel (embedOdd z) := by
      rw [← pairWitness_joint_full_trace z,lintegral_map hJ (pairTraceOfWitness_measurable z)]
      rfl
    _ = _ := by
      rw [fullPairTraceKernel,Kernel.lintegral_compProd _ _ _ hJ]
      apply lintegral_congr
      intro s
      by_cases hs : firstArrivalMark s=b <;> simp [J,hs]

lemma pairBranch_full_projection (b : Bool) (z : OddCost) :
    (pairBranchKernel b z).map embedOdd=
      (costKernel ∘ₖ costKernel.restrict (firstArrivalMark_measurable (measurableSet_singleton b))) (embedOdd z) := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF embedOdd_measurable,pairBranch_full_lintegral b z hF,
    Kernel.lintegral_comp _ _ _ hF,Kernel.restrict_apply,
    ← lintegral_indicator (firstArrivalMark_measurable (measurableSet_singleton b))]
  apply lintegral_congr
  intro s
  simp only [Set.indicator_apply,mem_preimage,mem_singleton_iff]

lemma false_arrival_set : {s : CostState | firstArrivalMark s=false}=markedArrivalᶜ := by
  ext s
  cases he : firstArrivalMark s <;> simp [markedArrival,he]

lemma pairBranch_marked_first_mass (z : OddCost) :
    pairBranchKernel true z univ=(costKernel (embedOdd z)) markedArrival := by
  have he := congrArg (fun μ : Measure CostState => μ univ) (pairBranch_full_projection true z)
  rw [Measure.map_apply embedOdd_measurable MeasurableSet.univ,preimage_univ,
    Kernel.comp_apply' _ _ _ MeasurableSet.univ] at he
  simp only [measure_univ,lintegral_const,one_mul] at he
  rw [Kernel.restrict_apply' _ _ _ MeasurableSet.univ,univ_inter] at he
  exact he

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_OddPairCycleGrouping
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.InitialRegeneration
open NumberTheoryLean.KernelPotential

lemma pairWindowContinue_complete (v H : ℝ) :
    hitOrReturn ∘ₖ pairWindowContinue v H=ordinaryWindowContinue v H := by
  rw [pairWindowContinue,Kernel.comp_add_right,← Kernel.comp_assoc,
    ← cycleBranch_completion false,← cycleBranch_completion true]
  rfl

instance oddConsecutiveCapture_isFiniteKernel (v H : ℝ) : IsFiniteKernel (oddConsecutiveCapture v H) := by
  unfold oddConsecutiveCapture
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem oddConsecutiveHit_eq_cycles (v H : ℝ) :
    oddConsecutiveHit v H=ordinaryMarkedHit v H ∘ₖ hitOrReturn := by
  rw [oddConsecutiveHit,oddConsecutiveContinue,first_capture_decomposition,
    oddConsecutiveCapture,
    potential_comp_left regenerationInput (ordinaryWindowCapture v H) (pairedCostKernel ∘ₖ nonregenerationInput),
    potential_comp_left regenerationInput (pairWindowContinue v H) (pairedCostKernel ∘ₖ nonregenerationInput),
    ← hitOrReturn_eq_input_potential,potential_exchange,pairWindowContinue_complete]
  rfl

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ActualOddPairLink
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping NumberTheoryLean.CostReturnLaw

lemma oddGoodInput_embed (v H : ℝ) (z : OddCost) :
    embedOdd z ∈ regenerativeCostWindow v H ↔ z ∈ oddGoodInput v H := Iff.rfl

lemma pairWindowContinue_apply (v H : ℝ) (z : OddCost) :
    pairWindowContinue v H z=if z ∈ ordinaryCostWindow v H then pairBranchKernel false z else pairedCostKernel z := by
  rw [pairWindowContinue,_root_.add_apply,stateFilter_input]
  by_cases hz : z ∈ ordinaryCostWindow v H
  · simp [hz]
  · simp only [hz,ite_false, if_false,mem_compl_iff,not_false_eq_true,ite_true, if_true]
    have he := congrArg (fun K : Kernel OddCost OddCost => K z) pairBranch_sum
    rw [_root_.add_apply] at he
    simpa only [add_comm] using he

lemma oddConsecutiveContinue_apply (v H : ℝ) (z : OddCost) :
    oddConsecutiveContinue v H z=if z ∈ oddGoodInput v H then pairBranchKernel false z else pairedCostKernel z := by
  rw [oddConsecutiveContinue,_root_.add_apply,nonregenerationInput,stateFilter_input,regenerationInput,stateFilter_input]
  by_cases hr : z ∈ returnSet
  · simp only [hr,ite_true, if_true,mem_compl_iff,not_true_eq_false,ite_false, if_false,zero_add]
    rw [pairWindowContinue_apply]
    simp only [oddGoodInput,mem_inter_iff,hr,true_and]
  · simp only [hr,ite_false, if_false,mem_compl_iff,not_false_eq_true,ite_true, if_true,add_zero]
    simp only [oddGoodInput,mem_inter_iff,hr,false_and,ite_false, if_false]

lemma consecutiveContinue_apply (v H : ℝ) (s : CostState) :
    consecutiveContinue v H s=if s ∈ regenerativeCostWindow v H then
      (costKernel ∘ₖ costKernel.restrict markedArrival_measurable.compl) s else (costKernel^2) s := by
  ext S hS
  rw [consecutiveContinue,Kernel.comp_apply' _ _ _ hS,consecutiveFirstContinue,Kernel.piecewise_apply]
  by_cases hs : s ∈ regenerativeCostWindow v H
  · rw [ite_eq_left hs,ite_eq_left hs,Kernel.comp_apply' _ _ _ hS]
  · rw [ite_eq_right hs,ite_eq_right hs,pow_two]
    exact (Kernel.comp_apply' costKernel costKernel s hS).symm

lemma false_arrival_restriction :
    costKernel.restrict (firstArrivalMark_measurable (measurableSet_singleton false))=
      costKernel.restrict markedArrival_measurable.compl := by
  ext s S hS
  rw [Kernel.restrict_apply' _ _ _ hS,Kernel.restrict_apply' _ _ _ hS]
  change costKernel s (S ∩ {y | firstArrivalMark y=false})=costKernel s (S ∩ markedArrivalᶜ)
  rw [false_arrival_set]

theorem oddConsecutiveContinue_embed (v H : ℝ) (z : OddCost) :
    (oddConsecutiveContinue v H z).map embedOdd=consecutiveContinue v H (embedOdd z) := by
  rw [oddConsecutiveContinue_apply,consecutiveContinue_apply]
  by_cases hz : z ∈ oddGoodInput v H
  · rw [ite_eq_left hz,ite_eq_left ((oddGoodInput_embed v H z).mpr hz),pairBranch_full_projection,false_arrival_restriction]
  · rw [ite_eq_right hz,ite_eq_right (fun h => hz ((oddGoodInput_embed v H z).mp h))]
    exact pairedCost_full_grouping z

lemma oddConsecutiveCapture_mass (v H : ℝ) (z : OddCost) :
    oddConsecutiveCapture v H z univ=if z ∈ oddGoodInput v H then nextMarkWeight z else 0 := by
  rw [oddConsecutiveCapture,regenerationInput,stateFilter_input]
  by_cases hr : z ∈ returnSet
  · rw [ite_eq_left hr,ordinaryWindowCapture_mass]
    simp only [oddGoodInput,mem_inter_iff,hr,true_and]
  · rw [ite_eq_right hr]
    simp [oddGoodInput,hr]

lemma consecutiveCapture_mass (v H : ℝ) (s : CostState) :
    consecutiveCapture v H s univ=if s ∈ regenerativeCostWindow v H then costKernel s markedArrival else 0 := by
  rw [consecutiveCapture,stateFilter_input]
  split_ifs
  · rw [Kernel.restrict_apply' _ _ _ MeasurableSet.univ,univ_inter]
  · rfl

theorem oddConsecutiveCapture_mass_embed (v H : ℝ) (z : OddCost) :
    oddConsecutiveCapture v H z univ=consecutiveCapture v H (embedOdd z) univ := by
  rw [oddConsecutiveCapture_mass,consecutiveCapture_mass]
  by_cases hz : z ∈ oddGoodInput v H
  · rw [ite_eq_left hz,ite_eq_left ((oddGoodInput_embed v H z).mpr hz),nextMarkWeight_pair_mass,pairBranch_marked_first_mass]
  · rw [ite_eq_right hz,ite_eq_right (fun h => hz ((oddGoodInput_embed v H z).mp h))]

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_CanonicalUniformMissingVisit
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping NumberTheoryLean.InitialRegeneration
open NumberTheoryLean.KernelPotential

lemma oddConsecutiveContinue_power_embed (v H : ℝ) (n : ℕ) (z : OddCost) :
    (((oddConsecutiveContinue v H)^n) z).map embedOdd=
      ((consecutiveContinue v H)^n) (embedOdd z) := by
  exact supported_projection_power (oddConsecutiveContinue v H) (consecutiveContinue v H)
    (S := univ) MeasurableSet.univ (fun _ => Eventually.of_forall (fun _ => mem_univ _)) embedOdd_measurable
    (fun z _ => oddConsecutiveContinue_embed v H z) n z (mem_univ _)

theorem consecutiveMarkedHit_odd_mass (v H : ℝ) (z : OddCost) :
    consecutiveMarkedHit v H (embedOdd z) univ=oddConsecutiveHit v H z univ := by
  have (n : ℕ) : IsSFiniteKernel ((consecutiveContinue v H)^n) := kernel_power_sfinite _ n
  have (n : ℕ) : IsSFiniteKernel ((oddConsecutiveContinue v H)^n) := kernel_power_sfinite _ n
  rw [consecutiveMarkedHit,oddConsecutiveHit,potential,potential,Kernel.sum_apply' _ _ MeasurableSet.univ,
    Kernel.sum_apply' _ _ MeasurableSet.univ]
  apply tsum_congr
  intro n
  rw [Kernel.comp_apply' _ _ _ MeasurableSet.univ,Kernel.comp_apply' _ _ _ MeasurableSet.univ,
    ← oddConsecutiveContinue_power_embed v H n z,
    lintegral_map ((consecutiveCapture v H).measurable_coe MeasurableSet.univ) embedOdd_measurable]
  apply lintegral_congr
  intro y
  exact (oddConsecutiveCapture_mass_embed v H y).symm

theorem consecutiveMarkedHit_after_regeneration (v H : ℝ) (z : OddCost) :
    consecutiveMarkedHit v H (embedOdd z) univ=
      ∫⁻ y, ordinaryMarkedHit v H y univ ∂hitOrReturn z := by
  rw [consecutiveMarkedHit_odd_mass,oddConsecutiveHit_eq_cycles,Kernel.comp_apply' _ _ _ MeasurableSet.univ]

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping NumberTheoryLean.TransitionKernels
open NumberTheoryLean.InitialOddDraw NumberTheoryLean.InitialRegeneration

theorem canonicalEvenPairVisit_completion (a N : ℕ) (v H : ℝ) :
    extendFinitePrefix N ∘ₖ canonicalEvenPairVisitKernel a v H=
      (rawExtension a N).restrict (anyPairHit_measurable (a+1) N v H) := by
  rw [canonicalEvenPairVisitKernel,← Kernel.comp_assoc,canonicalPairVisit_completion,Kernel.comp_restrict]
  have he : rawExtension (a+1) N ∘ₖ rawExtension a (a+1)=rawExtension a N :=
    Kernel.partialTraj_comp_partialTraj' (X := fun _ => CostState) (κ := historyKernel) N (show a ≤ a+1 by omega)
  rw [he]

theorem canonicalEvenPairVisit_mass (a : ℕ) (v H : ℝ) (past : RawHistory a) (s : EvenState)
    (hs : rawLast a past=(Sum.inl s,0)) :
    canonicalEvenPairVisitKernel a v H past univ=ordinaryInitialHitMass s v H := by
  rw [canonicalEvenPairVisitKernel,Kernel.comp_apply' _ _ _ MeasurableSet.univ]
  simp_rw [canonicalPairVisit_mass]
  have hG : Measurable (fun z : CostState => consecutiveMarkedHit v H z univ) :=
    (consecutiveMarkedHit v H).measurable_coe MeasurableSet.univ
  rw [← lintegral_map (g := rawLast (a+1)) hG (rawLast_measurable (a+1)),
    rawFirstOdd_draw_law a past s hs,lintegral_map hG embedOdd_measurable]
  simp_rw [consecutiveMarkedHit_after_regeneration]
  rw [ordinaryInitialHitMass,delayedRegeneration,Kernel.lintegral_comp _ _ _
    ((ordinaryMarkedHit v H).measurable_coe MeasurableSet.univ)]

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Topology
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.TransitionKernels

lemma extendFinitePrefix_total {α : Type*} [MeasurableSpace α] (N : ℕ)
    (K : Kernel α FiniteRawHistory) (x : α) :
    (extendFinitePrefix N ∘ₖ K) x univ=K x {q | q.1 ≤ N} := by
  rw [Kernel.comp_apply' _ _ _ MeasurableSet.univ]
  have hi : (fun q : FiniteRawHistory => extendFinitePrefix N q univ)=
      {q : FiniteRawHistory | q.1 ≤ N}.indicator (fun _ => (1:ℝ≥0∞)) := by
    funext q
    by_cases hq : q.1 ≤ N <;> simp [extendFinitePrefix,hq]
  rw [hi,lintegral_indicator (measurableSet_le finiteRawLength_measurable measurable_const)]
  simp only [lintegral_const,one_mul,Measure.restrict_apply MeasurableSet.univ,univ_inter]

theorem canonicalEvenPairVisit_bounded_mass (a N : ℕ) (v H : ℝ) (past : RawHistory a) :
    canonicalEvenPairVisitKernel a v H past {q | q.1 ≤ N}=
      rawExtension a N past (anyPairHit (a+1) N v H) := by
  rw [← extendFinitePrefix_total N (canonicalEvenPairVisitKernel a v H) past,
    canonicalEvenPairVisit_completion,Kernel.restrict_apply' _ _ _ MeasurableSet.univ,univ_inter]

lemma finite_history_length_exhausts (μ : Measure FiniteRawHistory) :
    Tendsto (fun N : ℕ => μ {q | q.1 ≤ N}) atTop (𝓝 (μ univ)) := by
  have hm : Monotone (fun N : ℕ => {q : FiniteRawHistory | q.1 ≤ N}) := by
    intro N M hNM q hq
    exact hq.trans hNM
  have hu : (⋃ N : ℕ, {q : FiniteRawHistory | q.1 ≤ N})=univ := by
    apply eq_univ_of_forall
    intro q
    exact mem_iUnion.mpr ⟨q.1,(show q.1 ≤ q.1 from le_rfl)⟩
  have ht := tendsto_measure_iUnion_atTop (μ := μ) hm
  rwa [hu] at ht

theorem canonical_even_hit_probability_limit (a : ℕ) (v H : ℝ) (past : RawHistory a) (s : EvenState)
    (hs : rawLast a past=(Sum.inl s,0)) :
    Tendsto (fun N : ℕ => rawExtension a N past (anyPairHit (a+1) N v H)) atTop
      (𝓝 (ordinaryInitialHitMass s v H)) := by
  have ht := finite_history_length_exhausts (canonicalEvenPairVisitKernel a v H past)
  simp_rw [canonicalEvenPairVisit_bounded_mass,canonicalEvenPairVisit_mass a v H past s hs] at ht
  exact ht

theorem finitePathMeasure_marked_hit_limit (s : EvenState) (v H : ℝ) :
    Tendsto (fun N : ℕ => finitePathMeasure (Sum.inl s) N (anyPairHit 1 N v H)) atTop
      (𝓝 (ordinaryInitialHitMass s v H)) := by
  exact canonical_even_hit_probability_limit 0 v H (fun _ => (Sum.inl s,0)) s rfl

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.FirstHitKernels
open NumberTheoryLean.ArrivalKernelGeometry NumberTheoryLean.OccupationBoundaries

lemma pair_no_future_hit_of_bad_inputs (a N M : ℕ) (hNM : N ≤ M) (v H : ℝ)
    (past : RawHistory N) (hNo : past ∉ anyPairHit a N v H)
    (hBad : ∀ᵐ y ∂rawExtension N M past, ∀ i : Finset.Iic M, N ≤ i.1 →
      y i ∉ regenerativeCostWindow v H) :
    ∀ᵐ y ∂rawExtension N M past, y ∉ anyPairHit a M v H := by
  filter_upwards [hBad,rawExtension_retains_prefix hNM past] with y hy hp
  intro hHit
  obtain ⟨k,hk,hT⟩ := hHit
  by_cases hj : a+2*k+1 ≤ N
  · have hSmall : rawPrefix hNM y ∈ pairHitTest a k N hj v H := by
      change y ∈ rawPrefix hNM ⁻¹' pairHitTest a k N hj v H
      rw [pairHitTest_prefix]
      exact hT
    rw [hp] at hSmall
    exact hNo ⟨k,hj,hSmall⟩
  · exact hy ⟨a+2*k,Finset.mem_Iic.mpr (by omega)⟩ (show N ≤ a+2*k by omega) ⟨hT.1,hT.2.2⟩

lemma regeneration_ratio_le_three (z : CostState) (hz : z ∈ regenerationSet) : stateRatio z.1 ≤ 3 := by
  rcases z with ⟨s,T⟩
  cases s with
  | inl e => exact False.elim (regeneration_even e T hz)
  | inr o => exact hz

lemma eligible_input_large_exponent {r b0 b1 : ℝ} (hr : 0 < r) (hb0 : 0 < b0) (hb1 : 0 < b1)
    (z : CostState) (hz : z ∈ regenerativeCostWindow (Real.log (r/b1)) (Real.log (b1/(10*b0)))) :
    2*b0 < currentExponent (Real.log r) z := by
  have hGap := (marked_cost_window hr hb0 hb1 z.2).mpr hz.2
  have hRatio := regeneration_ratio_le_three z hz.1
  unfold currentExponent
  rw [gapValue_log_eq_gapAt hr]
  apply (lt_div_iff₀ (stateRatio_pos z.1)).mpr
  have hm := mul_le_mul_of_nonneg_left hRatio (show 0 ≤ 2*b0 by positivity)
  nlinarith [hGap.1]

theorem low_gap_no_future_pair_hit {r b0 b1 : ℝ} (hr : 0 < r) (hb0 : 0 < b0) (hb1 : 0 < b1)
    (a N M : ℕ) (hNM : N ≤ M) (past : RawHistory N)
    (hNo : past ∉ anyPairHit a N (Real.log (r/b1)) (Real.log (b1/(10*b0))))
    (hLow : gapAt r (rawLast N past).2 < 10*b0) :
    ∀ᵐ y ∂rawExtension N M past, y ∉ anyPairHit a M (Real.log (r/b1)) (Real.log (b1/(10*b0))) := by
  apply pair_no_future_hit_of_bad_inputs a N M hNM _ _ past hNo
  filter_upwards [rawExtension_increasingCosts N M past,rawExtension_retains_prefix hNM past] with y hI hp
  have he := congrFun hp (⟨N,by simp⟩ : Finset.Iic N)
  change y ⟨N,Finset.mem_Iic.mpr hNM⟩=rawLast N past at he
  intro i hNi hGood
  have hCost := hI ⟨N,Finset.mem_Iic.mpr hNM⟩ i le_rfl hNi
  have hGap := gapAt_antitone_cost hr.le hCost
  rw [he] at hGap
  have hWindow := (marked_cost_window hr hb0 hb1 (y i).2).mpr hGood.2
  exact (not_lt_of_ge (hWindow.1.trans hGap)) hLow

theorem cutoff_no_future_pair_hit {r b0 b1 ell : ℝ} (hr : 0 < r) (hb0 : 0 < b0) (hb1 : 0 < b1)
    (hell : ell < 2*b0) (a N M : ℕ) (hNM : N ≤ M) (past : RawHistory N)
    (hNo : past ∉ anyPairHit a N (Real.log (r/b1)) (Real.log (b1/(10*b0))))
    (hCut : currentExponent (Real.log r) (rawLast N past) ≤ ell) :
    ∀ᵐ y ∂rawExtension N M past, y ∉ anyPairHit a M (Real.log (r/b1)) (Real.log (b1/(10*b0))) := by
  apply pair_no_future_hit_of_bad_inputs a N M hNM _ _ past hNo
  have hF : Measurable (fun z => -currentExponent (Real.log r) z) := (currentExponent_measurable _).neg
  have hStep (z : CostState) : ∀ᵐ y ∂costKernel z, -currentExponent (Real.log r) z ≤ -currentExponent (Real.log r) y := by
    filter_upwards [costKernel_exponent_nonincreasing (Real.log r) z] with y hy
    exact neg_le_neg hy
  filter_upwards [rawExtension_scalarIncreasing (fun z => -currentExponent (Real.log r) z) hF hStep N M past,
    rawExtension_retains_prefix hNM past] with y hI hp
  change ∀ i j : Finset.Iic M, N ≤ i.1 → i.1 ≤ j.1 →
    -currentExponent (Real.log r) (y i) ≤ -currentExponent (Real.log r) (y j) at hI
  have he := congrFun hp (⟨N,by simp⟩ : Finset.Iic N)
  change y ⟨N,Finset.mem_Iic.mpr hNM⟩=rawLast N past at he
  intro i hNi hGood
  have hX := hI ⟨N,Finset.mem_Iic.mpr hNM⟩ i le_rfl hNi
  rw [he] at hX
  have hLarge := eligible_input_large_exponent hr hb0 hb1 (y i) hGood
  linarith

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Topology
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.TransitionKernels
open NumberTheoryLean.ArrivalKernelGeometry

lemma closedNoHitEvent_measurable (a N : ℕ) (r b0 b1 ell : ℝ) :
    MeasurableSet (closedNoHitEvent a N r b0 b1 ell) := by
  have hGap : Measurable (fun h : RawHistory N => gapAt r (rawLast N h).2) :=
    measurable_const.mul (Real.measurable_exp.comp ((measurable_snd.comp (rawLast_measurable N)).neg))
  exact (anyPairHit_measurable a N _ _).compl.inter
    ((measurableSet_lt hGap measurable_const).union
      (measurableSet_le ((currentExponent_measurable _).comp (rawLast_measurable N)) measurable_const))

lemma closedNoHitEvent_future {r b0 b1 ell : ℝ} (hr : 0 < r) (hb0 : 0 < b0) (hb1 : 0 < b1)
    (hell : ell < 2*b0) (a N M : ℕ) (hNM : N ≤ M) (past : RawHistory N)
    (hp : past ∈ closedNoHitEvent a N r b0 b1 ell) :
    ∀ᵐ y ∂rawExtension N M past,
      y ∉ anyPairHit a M (Real.log (r/b1)) (Real.log (b1/(10*b0))) := by
  rcases hp.2 with hLow | hCut
  · exact low_gap_no_future_pair_hit hr hb0 hb1 a N M hNM past hp.1 hLow
  · exact cutoff_no_future_pair_hit hr hb0 hb1 hell a N M hNM past hp.1 hCut

theorem closedNoHitEvent_mass_future {r b0 b1 ell : ℝ} (hr : 0 < r) (hb0 : 0 < b0) (hb1 : 0 < b1)
    (hell : ell < 2*b0) (s a N M : ℕ) (hsN : s ≤ N) (hNM : N ≤ M) (past : RawHistory s) :
    rawExtension s N past (closedNoHitEvent a N r b0 b1 ell) ≤
      rawExtension s M past (anyPairHit a M (Real.log (r/b1)) (Real.log (b1/(10*b0))))ᶜ := by
  let E := closedNoHitEvent a N r b0 b1 ell
  let C := (anyPairHit a M (Real.log (r/b1)) (Real.log (b1/(10*b0))))ᶜ
  have hE : MeasurableSet E := closedNoHitEvent_measurable a N r b0 b1 ell
  have hC : MeasurableSet C := (anyPairHit_measurable a M _ _).compl
  have he : rawExtension N M ∘ₖ rawExtension s N=rawExtension s M :=
    Kernel.partialTraj_comp_partialTraj hsN hNM
  change rawExtension s N past E ≤ rawExtension s M past C
  rw [← he,Kernel.comp_apply' _ _ _ hC]
  calc
    _ = ∫⁻ h, E.indicator (fun _ => (1:ℝ≥0∞)) h ∂rawExtension s N past := by
      rw [lintegral_indicator hE]
      simp
    _ ≤ _ := by
      apply lintegral_mono
      intro h
      by_cases hh : h ∈ E
      · have hStay := closedNoHitEvent_future hr hb0 hb1 hell a N M hNM h hh
        have hMass := (ae_mem_iff_measure_eq hC.nullMeasurableSet).mp hStay
        rw [measure_univ] at hMass
        rw [indicator_of_mem hh]
        change 1 ≤ rawExtension N M h C
        exact hMass.symm.le
      · rw [indicator_of_notMem hh]
        exact zero_le

theorem canonical_closed_nohit_le_failure {r b0 b1 ell : ℝ} (hr : 0 < r) (hb0 : 0 < b0) (hb1 : 0 < b1)
    (hell : ell < 2*b0) (s : EvenState) (N : ℕ) :
    finitePathMeasure (Sum.inl s) N (closedNoHitEvent 1 N r b0 b1 ell) ≤
      1-ordinaryInitialHitMass s (Real.log (r/b1)) (Real.log (b1/(10*b0))) := by
  let C := finitePathMeasure (Sum.inl s) N (closedNoHitEvent 1 N r b0 b1 ell)
  let I := ordinaryInitialHitMass s (Real.log (r/b1)) (Real.log (b1/(10*b0)))
  have hLimit := (finitePathMeasure_marked_hit_limit s (Real.log (r/b1)) (Real.log (b1/(10*b0)))).const_add C
  have hTail : ∀ᶠ M : ℕ in atTop,
      C+finitePathMeasure (Sum.inl s) M (anyPairHit 1 M (Real.log (r/b1)) (Real.log (b1/(10*b0)))) ≤ 1 := by
    filter_upwards [eventually_ge_atTop N] with M hNM
    have hle := closedNoHitEvent_mass_future hr hb0 hb1 hell 0 1 N M (Nat.zero_le _) hNM
      (fun _ => (Sum.inl s,0))
    calc
      _ ≤ finitePathMeasure (Sum.inl s) M (anyPairHit 1 M (Real.log (r/b1)) (Real.log (b1/(10*b0))))ᶜ+
          finitePathMeasure (Sum.inl s) M (anyPairHit 1 M (Real.log (r/b1)) (Real.log (b1/(10*b0)))) :=
        add_le_add hle le_rfl
      _ = 1 := by
        rw [add_comm,measure_add_measure_compl (anyPairHit_measurable 1 M _ _),measure_univ]
  have hAdd : C+I ≤ 1 := le_of_tendsto hLimit hTail
  have hI : I ≠ ∞ := ne_top_of_le_ne_top (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (1:ℝ≥0∞) ≠ ∞) (ordinaryInitialHitMass_le_one s _ _)
  exact ENNReal.le_sub_of_add_le_right hI hAdd

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Topology
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.TransitionKernels

lemma moving_cutoff_one {K : ℝ} (hK : 0 < K) :
    ∀ᶠ w : ℝ in atTop, 3 ≤ w ∧ 1 < 2*(K*(Real.log w)^2) := by
  filter_upwards [eventually_ge_atTop (max (3:ℝ) (Real.exp (1+1/K)))] with w hw
  have hw3 : 3 ≤ w := (le_max_left _ _).trans hw
  have hw0 : 0 < w := by linarith
  have hL : 1+1/K ≤ Real.log w := (Real.le_log_iff_exp_le hw0).mpr ((le_max_right _ _).trans hw)
  have hOne : 1 ≤ Real.log w := by have hi : 0 < 1/K := one_div_pos.mpr hK; linarith
  have hMul := mul_le_mul_of_nonneg_left hL hK.le
  have hEq : K*(1+1/K)=K+1 := by field_simp [hK.ne']
  rw [hEq] at hMul
  have hSq : Real.log w ≤ (Real.log w)^2 := by nlinarith
  have hMulSq := mul_le_mul_of_nonneg_left hSq hK.le
  refine ⟨hw3,?_⟩
  nlinarith

theorem moving_canonical_missing_visit_jb247_oai {eps : ℝ} (heps : 0 < eps) :
    ∃ rho : ℝ, 10 < rho ∧ ∀ K : ℝ, 0 < K →
      ∀ᶠ w : ℝ in atTop, 3 ≤ w ∧ ∀ r : ℝ, w ≤ r → ∀ s : EvenState,
        199/100 ≤ s.1 → s.1 ≤ 23/10 → ∀ N : ℕ,
        finitePathMeasure (Sum.inl s) N
          (closedNoHitEvent 1 N r (K*(Real.log w)^2) (rho*K*(Real.log w)^2) 1) ≤ ENNReal.ofReal eps := by
  obtain ⟨rho,hrho,hMoving⟩ := moving_ordinary_marked_hit heps
  refine ⟨rho,hrho,?_⟩
  intro K hK
  filter_upwards [hMoving K hK,moving_cutoff_one hK] with w hw hCut
  refine ⟨hw.1,?_⟩
  intro r hr s hs0 hs1 N
  have hw0 : 0 < w := by linarith [hw.1]
  have hr0 : 0 < r := hw0.trans_le hr
  have hlog : 0 < Real.log w := Real.log_pos (by linarith [hw.1])
  let b0 := K*(Real.log w)^2
  have hb0 : 0 < b0 := by dsimp [b0] <;> positivity
  have hrho0 : 0 < rho := by linarith
  have hb1 : 0 < rho*b0 := mul_pos hrho0 hb0
  have he : rho*b0=rho*K*(Real.log w)^2 := by dsimp [b0] <;> ring
  have hBound := canonical_closed_nohit_le_failure hr0 hb0 hb1 hCut.2 s N
  rw [proportional_window_width hrho0 hb0,he] at hBound
  exact hBound.trans (hw.2 r hr s hs0 hs1)

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.Erdos970Dependency.MarkedVisits.moving_canonical_missing_visit_jb247_oai := @OAI.Erdos970.Erdos970Dependency.MarkedVisits.moving_canonical_missing_visit_jb247_oai
