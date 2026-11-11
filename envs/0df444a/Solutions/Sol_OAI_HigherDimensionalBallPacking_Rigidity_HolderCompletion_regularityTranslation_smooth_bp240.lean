-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.regularityTranslation_smooth_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T02:20:51.45608+00:00
-- url     : https://prove2.me/submissions/aa8e68c0-0343-4833-83c3-544bfdb30fdd

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp022
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_actualFreeChart_contDiff_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_actualFreeChart_fderiv_fredholm_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_affineCurve_translation_CR_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_crSection_value_of_standard_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_jetObservations_translation_smooth_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_jetTest_separates_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_regularityTranslation_continuous_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_regularityTranslation_near_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_regularityTranslation_zero_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_supportedHolder_closed_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_finite_separating_family_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_fredholm_stabilized_leftInverse_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_nonlinear_stabilized_regularity_bp240

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_BanachSpace
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.FiniteMoment.Radial.instInhabitedQuadrant _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped BoundedContinuousFunction Topology ContDiff
open Set Filter
section

variable (X E : Type*) [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma graph_closed (α : ℝ) : IsClosed (graph X E α : Set (Ambient X E)) := by
  change IsClosed {u : Ambient X E | ∀ p : Pairs X, _}
  simp only [← Set.iInter_ofPred]
  apply isClosed_iInter
  intro p
  exact isClosed_eq
    ((BoundedContinuousFunction.evalCLM ℝ p).continuous.comp continuous_snd)
    ((((BoundedContinuousFunction.evalCLM ℝ p.val.1).continuous.comp continuous_fst).sub
      ((BoundedContinuousFunction.evalCLM ℝ p.val.2).continuous.comp continuous_fst)).const_smul _)

instance instCompleteSpaceSubtypeAmbientMemSubmoduleRealHolder (α : ℝ) [CompleteSpace E] : CompleteSpace (Holder X E α) :=
  (graph_closed X E α).completeSpace_coe

variable {X E}

variable {α : ℝ}

variable (D : Type*) [NormedAddCommGroup D] [NormedSpace ℝ D]

lemma jetGraph_closed (α : ℝ) : IsClosed (jetGraph (E := E) D α : Set (JetAmbient (E := E) D α)) := by
  apply isSeqClosed_iff_isClosed.mp
  intro u v hu huv x
  have hv0 : Tendsto (fun n => valueCLM α (u n).1) atTop (𝓝 (valueCLM α v.1)) :=
    ((valueCLM α).continuous.comp continuous_fst).tendsto v |>.comp huv
  have hv1 : Tendsto (fun n => valueCLM α (u n).2) atTop (𝓝 (valueCLM α v.2)) :=
    ((valueCLM α).continuous.comp continuous_snd).tendsto v |>.comp huv
  have huni := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hv1
  exact hasFDerivAt_of_tendstoUniformly huni (fun n => hu n)
    (fun y => (BoundedContinuousFunction.evalCLM ℝ y).continuous.tendsto _ |>.comp hv0) x

instance instCompleteSpaceSubtypeJetAmbientMemSubmoduleRealCOneHolder (α : ℝ) [CompleteSpace E] : CompleteSpace (COneHolder (E := E) D α) :=
  (jetGraph_closed (E := E) D α).completeSpace_coe

end

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_NonlinearCR
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
namespace HolderCompletion
variable {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedAddCommGroupSubtypeJetAmbientHDivRealOfNatMemSubmoduleCOne_1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedSpaceRealSubtypeJetAmbientHDivOfNatMemSubmoduleCOne_1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedAddCommGroupSubtypeJetAmbientHDivRealOfNatMemSubmoduleCOne_2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedSpaceRealSubtypeJetAmbientHDivOfNatMemSubmoduleCOne_2
local instance instNormedAddCommGroupContinuousLinearMapRealIdSubtypeJetAmbientHDivOfNatMemSubmoduleCOne_r928434_1 : NormedAddCommGroup (COne D E →L[ℝ] COne D F) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapIdSubtypeJetAmbientHDivOfNatMemSubmoduleCOne_r928434_1 : NormedSpace ℝ (COne D E →L[ℝ] COne D F) := ContinuousLinearMap.toNormedSpace
instance instCompleteSpaceSubtypeAmbientMemSubmoduleRealHMapSupportedHolder (K : Set D) [CompleteSpace E] : CompleteSpace (supportedHolder (E := E) K) :=
  (supportedHolder_closed_bp240 K).completeSpace_coe

end HolderCompletion

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_MarkedJets
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineJetDeriv_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineJetSuperpose_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineJetValue_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.bumpHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compactPerturbationJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedDX_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedQ_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedStructureJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.constHolderCLM_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficientHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrderHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.cutoffCoordinate_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.cutoffCurveJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.cutoffSlope_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frameCRCoefficient_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freePrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeSum_deriv _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeSum_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeZeroOrder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.holderCoefficientAction_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.holderTranslate_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetDirectional_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTest_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTranslate_deriv _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTranslate_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetZeroOrder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.localizedJetValue_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedCoefficientAction_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedDerivEval_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedDerivativeVariation_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedEval_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedFiniteCorrection_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedVariation_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedZeroOrder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ofBoundedLipschitz_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.principalCR_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.realConstantJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.restrictedValue_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothAlongJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothMarkedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.sourceCutoff_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedCoefficientAction_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedEval_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedFieldAction_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedSourceCutoff_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.translationVariation_deriv _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.translationVariation_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.truncateShift_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.truncatedCoefficient_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.geometricHolder_value _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.crSectInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.crSectInst4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.crSectInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.crSectInst6
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.crSectInst7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.crSectInst8
lemma affineCurve_fderiv (p : E) (a : ℂ →L[ℝ] E) (u : COne ℂ E) (z : ℂ) :
    fderiv ℝ (affineCurve p a u) z = a+cDeriv u z :=
  (affineCurve_hasFDerivAt p a u z).fderiv

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.crSectInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.crSectInst2
variable {J : E → E →L[ℝ] E} (hJ : BoundedCThree J)

@[simp] lemma crSection_value (p : E) (a : ℂ →L[ℝ] E) (u : COne ℂ E) (z : ℂ) :
    valueCLM _ (crSection hJ p a u) z =
      fderiv ℝ (affineCurve p a u) z Complex.I -
        J (affineCurve p a u z) (fderiv ℝ (affineCurve p a u) z 1) := by
  rw [affineCurve_fderiv]
  rfl

@[simp] lemma crSectionDeriv_value (p : E) (a : ℂ →L[ℝ] E)
    (u h : COne ℂ E) (z : ℂ) :
    valueCLM _ (crSectionDeriv hJ p a u h) z =
      fderiv ℝ (cValue h) z Complex.I - J (affineCurve p a u z) (fderiv ℝ (cValue h) z 1) -
      (fderiv ℝ J (affineCurve p a u z) (cValue h z))
        (fderiv ℝ (affineCurve p a u) z 1) := by
  rw [affineCurve_fderiv, c_fderiv]
  rfl

lemma crSection_eq_zero_iff (p : E) (a : ℂ →L[ℝ] E) (u : COne ℂ E) :
    crSection hJ p a u = 0 ↔ ∀ z,
      fderiv ℝ (affineCurve p a u) z Complex.I =
        J (affineCurve p a u z) (fderiv ℝ (affineCurve p a u) z 1) := by
  constructor
  · intro h z
    have he := congrArg (fun v : HMap ℂ E => valueCLM _ v z) h
    rw [crSection_value] at he
    change _ = 0 at he
    exact sub_eq_zero.mp he
  · intro h
    apply value_ext
    intro z
    rw [crSection_value, h z, sub_self]
    rfl


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_FiniteExtensions
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
namespace HolderCompletion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [completeSpaceE : CompleteSpace E]

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeInst1
local instance freeInst2_r928434_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance freeInst3_r928434_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance freeInst4_r928434_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
omit completeSpaceE in
lemma freeModel_closed [CompleteSpace E] (K : Set ℂ) :
    IsClosed (freeModel (E := E) K : Set (COne ℂ E)) :=
  (supportedHolder_closed_bp240 K).preimage standardJetCR.continuous

instance instCompleteSpaceSubtypeJetAmbientComplexHDivRealOfNatMemSubmoduleCOneFreeModel (K : Set ℂ) : CompleteSpace (freeModel (E := E) K) :=
  (freeModel_closed K).completeSpace_coe

end HolderCompletion

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_PointwiseMarkedCR
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion

open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeChartInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeChartInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeChartInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeChartInst4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeChartInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeChartInst6
variable {J : E → E →L[ℝ] E} (hJ : BoundedCThree J) (b : ContDiffBump (0:ℂ)) (p a : E)
variable (u : freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut))

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeChartInst7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeChartInst8
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeChartInst9
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeChartInst10
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeChartInst11
local instance freeChartInst12_r928434_1 : Module ℝ (freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := (freeChartInst8 (E := E) b).toModule
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeChartInst13
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeChartInst14
local instance freeChartInst15_r928434_1 : Module ℝ (COne ℂ E) := (freeChartInst4 (E := E)).toModule
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeChartInst16
omit [CompleteSpace E] in
lemma freeChart_value [CompleteSpace E] (v : freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) (z : ℂ) :
    valueCLM _ (freeChart hJ b p a u v).val z =
      valueCLM _ (standardJetCR (u.val+v.val)) z - b z •
        (valueCLM _ (standardJetCR (u.val+v.val)) z-
          valueCLM _ (crSection hJ p (complexSlope a) (u.val+v.val)) z) := rfl

omit [CompleteSpace E] in
lemma cutoff_residual_algebra [CompleteSpace E] (s t : E) (c : ℝ) (hc : c=1 ∨ s=t) :
    s-c • (s-t)=t := by
  rcases hc with rfl | rfl
  · rw [one_smul]; abel
  · rw [sub_self,smul_zero,sub_zero]

lemma freeChart_true_value {B : ℝ} (hstd : ∀ x, B < ‖x‖ → J x=complexI (E := E))
    (v : freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut))
    (he : ∀ z, b.rIn ≤ ‖z‖ → B < ‖affineCurve p (complexSlope a) (u.val+v.val) z‖) (z : ℂ) :
    valueCLM _ (freeChart hJ b p a u v).val z =
      valueCLM _ (crSection hJ p (complexSlope a) (u.val+v.val)) z := by
  apply (freeChart_value hJ b p a u v z).trans
  apply cutoff_residual_algebra
  by_cases hz : z ∈ Metric.closedBall (0:ℂ) b.rIn
  · exact Or.inl (b.one_of_mem_closedBall hz)
  · have hz' : b.rIn ≤ ‖z‖ := by
      simp only [Metric.mem_closedBall,dist_zero_right] at hz
      exact (lt_of_not_ge hz).le
    exact Or.inr (crSection_value_of_standard_bp240 hJ p a _ z (hstd _ (he z hz'))).symm



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_FreeLinearization
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.geometricHolder_value _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped Topology BoundedContinuousFunction ContDiff
open Set Function Filter
namespace HolderCompletion
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
section Generic
variable {X I : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
omit [CompleteSpace E] in
lemma observed_fredholm_leftInverse [CompleteSpace E] (P : X →L[ℝ] F) (hP : P.IsFredholm)
    (O : I → X →L[ℝ] E) (hO : ∀ x, (∀ i, O i x=0) → x=0) :
    ∃ (s : Finset I) (L : F × (s → E) →L[ℝ] X),
      LeftInverse L (P.prod (ContinuousLinearMap.pi (fun i : s => O i.val))) := by
  let := hP.finite_ker
  obtain ⟨s,hs⟩ := finite_separating_family_bp240 (fun i => (O i).comp P.ker.subtypeL)
    (by
      intro v hv
      apply Subtype.ext
      exact hO v.val hv)
  let Q : X →L[ℝ] (s → E) := ContinuousLinearMap.pi (fun i : s => O i.val)
  have hQ : Injective (Q.comp P.ker.subtypeL) := by
    intro u v huv
    apply sub_eq_zero.mp
    apply hs (u-v)
    intro i hi
    have hh := congrArg (fun f : s → E => f ⟨i,hi⟩) huv
    change O i u.val=O i v.val at hh
    change O i (u.val-v.val)=0
    rw [map_sub,hh,sub_self]
  obtain ⟨L,hL⟩ := fredholm_stabilized_leftInverse_bp240 P hP Q hQ
  exact ⟨s,L,hL⟩
end Generic

variable (S : Submodule ℝ (COne ℂ E))

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetObsInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetObsInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetObsInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetObsInst4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetObsInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetObsInst6
lemma exists_jet_fredholm_observations (P : S →L[ℝ] F) (hP : P.IsFredholm) :
    ∃ (s : Finset PlaneTest) (L : F × (s → E) →L[ℝ] S),
      LeftInverse L (P.prod (subspaceObservations S s)) := by
  let O : PlaneTest → S →L[ℝ] E := fun g => (jetTestCLM g).comp S.subtypeL
  have hO : ∀ u : S, (∀ g, O g u=0) → u=0 := by
    intro u hu
    apply Subtype.ext
    exact jetTest_separates_bp240 u.val hu
  have hh := observed_fredholm_leftInverse P hP O hO
  obtain ⟨s,L,hL⟩ := hh
  exact ⟨s,L,hL⟩

end HolderCompletion

end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
namespace HolderCompletion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

variable {R S : ℝ} (hRS : R+1 ≤ S) (a : E)
  (u : freeModel (E := E) (Metric.closedBall (0:ℂ) R))

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeTransInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeTransInst2
local instance freeTransInst3_r928434_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance freeTransInst4_r928434_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance freeTransInst5_r928434_1 : NormedAddCommGroup (freeModel (E := E) (Metric.closedBall (0:ℂ) S)) := inferInstance
local instance freeTransInst6_r928434_1 : NormedSpace ℝ (freeModel (E := E) (Metric.closedBall (0:ℂ) S)) := inferInstance
lemma freeTranslation_near : ∀ᶠ t in 𝓝 (0:ℂ), (freeTranslation hRS a u t).val=translationVariation a u.val t := by
  filter_upwards [Metric.ball_mem_nhds (0:ℂ) (show (0:ℝ)<1 by norm_num)] with t ht
  have ht' : ‖t‖≤1 := (show ‖t‖<1 by simpa only [Metric.mem_ball,dist_zero_right] using ht).le
  simp only [freeTranslation,dite_eq_left ht']

variable [FiniteDimensional ℝ E]

lemma translationVariation_observation_smooth (s : Finset PlaneTest) :
    ContDiff ℝ ∞ (fun t => jetObservations s (translationVariation a u.val t)) := by
  have he : (fun t => jetObservations s (translationVariation a u.val t)) =
      (fun t => jetObservations s (constJetCLM (complexSlope a t))+
        jetObservations s (jetTranslate t u.val-u.val)) := by
    funext t
    rw [←map_add]
    apply congrArg (jetObservations s)
    change constJet (t • a)+jetTranslate t u.val-u.val = constJet (t • a)+(jetTranslate t u.val-u.val)
    abel
  rw [he]
  exact ((jetObservations s).contDiff.comp ((constJetCLM (E := E)).contDiff.comp
    (complexSlope a).contDiff)).add (jetObservations_translation_smooth_bp240 s u.val)

lemma freeTranslation_observation_smoothAt (s : Finset PlaneTest) :
    ContDiffAt ℝ ∞ (fun t => subspaceObservations (freeModel (E := E) (Metric.closedBall (0:ℂ) S)) s
      (freeTranslation hRS a u t)) 0 := by
  apply (translationVariation_observation_smooth a u s).contDiffAt.congr_of_eventuallyEq
  filter_upwards [freeTranslation_near hRS a u] with t ht
  exact congrArg (jetObservations s) ht

end HolderCompletion

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_TranslationContinuity
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frozenTargetCoefficient_zero _root_.OAI.HigherDimensionalBallPacking.Rigidity.geometricHolder_value _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

variable {J : E → E →L[ℝ] E} (hJ : BoundedCThree J) (b : ContDiffBump (0:ℂ)) (p a : E)
variable (u : freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) {B : ℝ}
  (hstd : ∀ x, B<‖x‖ → J x=complexI (E := E))
  (hesc : ∀ᶠ v in 𝓝 (0 : freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)),
    ∀ z, b.rIn≤‖z‖ → B<‖affineCurve p (complexSlope a) (u.val+v.val) z‖)

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.teInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.teInst2
local instance teInst3_r928434_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance teInst4_r928434_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.teInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.teInst6
include hstd in
lemma freeChart_zero_of_CR (v : freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut))
    (he : ∀ z, b.rIn≤‖z‖ → B<‖affineCurve p (complexSlope a) (u.val+v.val) z‖)
    (hcr : ∀ z, fderiv ℝ (affineCurve p (complexSlope a) (u.val+v.val)) z Complex.I =
      J (affineCurve p (complexSlope a) (u.val+v.val) z)
        (fderiv ℝ (affineCurve p (complexSlope a) (u.val+v.val)) z 1)) :
    freeChart hJ b p a u v=0 := by
  apply Subtype.ext
  apply value_ext
  intro z
  have hv := freeChart_true_value hJ b p a u hstd v he z
  have hzero := (crSection_eq_zero_iff hJ p (complexSlope a) (u.val+v.val)).mpr hcr
  apply hv.trans
  rw [hzero]
  rfl

include hstd hesc in
lemma freeChart_translation_zero_near
    (V : ℂ → freeModel (E := E) (Metric.closedBall (0:ℂ) b.rOut))
    (hV : ContinuousAt V 0) (hV0 : V 0=0)
    (hv : ∀ᶠ t in 𝓝 (0:ℂ), (V t).val=translationVariation a u.val t)
    (hcr : ∀ z, fderiv ℝ (affineCurve p (complexSlope a) u.val) z Complex.I =
      J (affineCurve p (complexSlope a) u.val z) (fderiv ℝ (affineCurve p (complexSlope a) u.val) z 1)) :
    ∀ᶠ t in 𝓝 (0:ℂ), freeChart hJ b p a u (V t)=0 := by
  have ht : Tendsto V (𝓝 0) (𝓝 0) := by simpa only [hV0] using hV.tendsto
  filter_upwards [ht.eventually hesc,hv] with t hte htv
  apply freeChart_zero_of_CR hJ b p a u hstd (V t) hte
  intro z
  rw [htv]
  exact affineCurve_translation_CR_bp240 J p a u.val hcr t z

end

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
section
variable {n : ℕ}
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst6
variable {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) (hc : ∀ x, Compatible (J x)) {B : ℝ}
  (hstd : ∀ x, B<‖x‖ → J x=standardJ n) (b : ContDiffBump (0:ℂ)) (p q : Phase n)
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst10
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst11
variable (w : freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) {R : ℝ}
  (hRS : R+1≤b.rOut) (hsupp : w.val ∈ freeModel (E := Phase n) (Metric.closedBall (0:ℂ) R))
  (hesc : FreeEscapeNeighborhood b p (markedSlope p q w.val) w.val B)
  (hcr : ∀ z, fderiv ℝ (markedCurve p q w.val) z Complex.I =
    J (markedCurve p q w.val z) (fderiv ℝ (markedCurve p q w.val) z 1))

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst8
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst9
include hJ hstd hc hesc hcr hRS hsupp in
lemma regularityTranslation_smooth_bp240_oai : ContDiffAt ℝ ∞ (regularityTranslation b p q w hRS hsupp) 0 := by
  let V := regularityTranslation b p q w hRS hsupp
  let D := fderiv ℝ (actualFreeChart hJ hstd p q b w) 0
  have hf := actualFreeChart_contDiff_bp240 hJ hstd p q b w
  have hD : D.IsFredholm := actualFreeChart_fderiv_fredholm_bp240 hJ hc hstd p q b w hesc
  obtain ⟨s,L,hL⟩ := exists_jet_fredholm_observations
    (freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) D hD
  have hd : HasFDerivAt (actualFreeChart hJ hstd p q b w) D (V 0) := by
    change HasFDerivAt _ D (regularityTranslation b p q w hRS hsupp 0)
    rw [regularityTranslation_zero_bp240]
    exact (hf.differentiable (by simp) 0).hasFDerivAt
  have hV : ContinuousAt V 0 := regularityTranslation_continuous_bp240 hJ hc hstd b p q w hRS hsupp hesc hcr
  have hQ : ContDiffAt ℝ ∞ (fun t => subspaceObservations
      (freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) s (V t)) 0 :=
    freeTranslation_observation_smoothAt hRS (markedSlope p q w.val) ⟨w.val,hsupp⟩ s
  have hz : ∀ᶠ t in 𝓝 (0:ℂ), actualFreeChart hJ hstd p q b w (V t)=0 :=
    freeChart_translation_zero_near (actualStructureBound hJ hstd) b p (markedSlope p q w.val) w hstd hesc V hV
      (regularityTranslation_zero_bp240 b p q w hRS hsupp) (regularityTranslation_near_bp240 b p q w hRS hsupp) hcr
  exact nonlinear_stabilized_regularity_bp240 hf hd _ L hL hV hQ hz

end

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.regularityTranslation_smooth_bp240_oai := @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.regularityTranslation_smooth_bp240_oai
