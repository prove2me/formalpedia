-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualFreeChart_fderiv_fredholm_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:54:21.16232+00:00
-- url     : https://prove2.me/submissions/3417254c-9907-40f6-93b8-94de7534d7e8

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp020
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_actualFreeChart_crSection_fderiv_eval_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_completedFreeLinearized_fredholm_bp240

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


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_FreeLinearization
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
variable {n : ℕ}
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst6
variable {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) (hc : ∀ x, Compatible (J x)) {B : ℝ}
  (hstd : ∀ x, B < ‖x‖ → J x=standardJ n) (p q : Phase n) (u : COne ℂ (Phase n))
  {K : Set ℂ} (hK : IsCompact K) (he : ∀ z ∉ K, B < ‖markedCurve p q u z‖)

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst8
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst9
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst10
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst11
local instance afInst12_r7b55c7_1 : NormedSpace ℝ (markedModel (E := Phase n) K) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst13
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst15
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst16
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst17
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst18
lemma completedFreeLinearized_value (v : freeModel (E := Phase n) K) (z : ℂ) :
    valueCLM _ (completedFreeLinearized hJ hstd p q u he v).val z =
      cDeriv v.val z Complex.I-J (markedCurve p q u z) (cDeriv v.val z 1)-
      fderiv ℝ J (markedCurve p q u z) (cValue v.val z) (fderiv ℝ (markedCurve p q u) z 1) := by
  have hp := freePrincipal_value (E := Phase n) (K := K) (jetValueCLM _ (completedStructureJet hJ hstd p q u))
    (fun z hz => hstd _ (he z hz)) v z
  have hq := freeZeroOrder_value (E := Phase n) (K := K) (completedQ hJ hstd p q u)
    (completedQ_zero_outside hJ hstd p q u he) v z
  have hq' := hq.trans (completedQ_value hJ hstd p q u z (cValue v.val z))
  exact congrArg₂ (fun x y : Phase n => x-y) hp hq'

variable (b : ContDiffBump (0:ℂ))
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst19
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst20
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst21
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst22
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst23
variable (w : freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut))
  (hesc : ∀ᶠ v in 𝓝 (0 : freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)),
    ∀ z, b.rIn ≤ ‖z‖ → B < ‖affineCurve p (complexSlope (markedSlope p q w.val)) (w.val+v.val) z‖)

lemma completedFreeLinearized_crSection (z : ℂ) :
    (((BoundedContinuousFunction.evalCLM ℝ z).comp (valueCLM _)).comp
      ((crSectionDeriv (actualStructureBound hJ hstd) p (complexSlope (markedSlope p q w.val)) w.val).comp
        (freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)).subtypeL)) =
    (supportedEval (E := Phase n) (K := Metric.closedBall (0:ℂ) b.rOut) z).comp
      (completedFreeLinearized hJ hstd p q w.val (free_escape_base p q b w hesc)) := by
  apply ContinuousLinearMap.ext
  intro v
  have hval := crSectionDeriv_value (actualStructureBound hJ hstd) p (complexSlope (markedSlope p q w.val)) w.val v.val z
  have hh := congrArg (fun d : ℂ →L[ℝ] Phase n =>
    d Complex.I-J (markedCurve p q w.val z) (d 1)-
      fderiv ℝ J (markedCurve p q w.val z) (cValue v.val z) (fderiv ℝ (markedCurve p q w.val) z 1))
    (c_fderiv v.val z)
  exact hval.trans (hh.trans (completedFreeLinearized_value hJ hstd p q w.val (free_escape_base p q b w hesc) v z).symm)

lemma actualFreeChart_fderiv_eval (z : ℂ) :
    (supportedEval (E := Phase n) (K := Metric.closedBall (0:ℂ) b.rOut) z).comp
      (fderiv ℝ (actualFreeChart hJ hstd p q b w) 0) =
    (supportedEval (E := Phase n) (K := Metric.closedBall (0:ℂ) b.rOut) z).comp
      (completedFreeLinearized hJ hstd p q w.val (free_escape_base p q b w hesc)) :=
  (actualFreeChart_crSection_fderiv_eval_bp240 hJ hstd p q b w hesc z).trans
    (completedFreeLinearized_crSection hJ hstd p q b w hesc z)

lemma actualFreeChart_fderiv_eq : fderiv ℝ (actualFreeChart hJ hstd p q b w) 0 =
    completedFreeLinearized hJ hstd p q w.val (free_escape_base p q b w hesc) := by
  apply ContinuousLinearMap.ext
  intro v
  apply Subtype.ext
  apply value_ext
  intro z
  exact congrArg (fun L : freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut) →L[ℝ] Phase n => L v)
    (actualFreeChart_fderiv_eval hJ hstd p q b w hesc z)

include hc hesc in
lemma actualFreeChart_fderiv_fredholm_bp240_oai : (fderiv ℝ (actualFreeChart hJ hstd p q b w) 0).IsFredholm := by
  rw [actualFreeChart_fderiv_eq hJ hstd p q b w hesc]
  exact completedFreeLinearized_fredholm_bp240 hJ hc hstd p q w.val (isCompact_closedBall (0:ℂ) b.rOut)
    (free_escape_base p q b w hesc)

end HolderCompletion

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualFreeChart_fderiv_fredholm_bp240_oai := @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualFreeChart_fderiv_fredholm_bp240_oai
