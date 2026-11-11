-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualMarkedChart_derivative_eq_linearized_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:54:48.565046+00:00
-- url     : https://prove2.me/submissions/70c9a903-85cc-49f6-ba98-02509c315c62

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp020
import Definitions.Def_OAIQ240Bp021
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_actualMarkedChart_contDiff_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_actualMarkedChart_value_bp240

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_MarkedFrame
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

variable (b : ContDiffBump (0:ℂ))

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineCutInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineCutInst2
local instance affineCutInst3_r0c26fd_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance affineCutInst4_r0c26fd_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineCutInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineCutInst6
omit [CompleteSpace E] in
lemma markedSlope_add (p q : E) (u h : COne ℂ E) :
    markedSlope p q (u+h) = markedSlope p q u-cValue h 1 := by
  simp only [markedSlope,cValue_add]
  abel


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_FrameFredholm
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedDX_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedQ_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freePrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeZeroOrder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.holderTranslate_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTest_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTranslate_deriv _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTranslate_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedDerivEval_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedDerivativeVariation_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedVariation_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.realConstantJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedEval_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.translationVariation_deriv _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.translationVariation_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.geometricHolder_value _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst6
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst8
local instance markedChartInst13_r0c26fd_1 : NormedAddCommGroup (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance markedChartInst14_r0c26fd_1 : NormedSpace ℝ (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
omit [CompleteSpace E] in
@[simp] lemma markedDX_value [CompleteSpace E] (p q : E) (u h : COne ℂ E) (z : ℂ) :
    valueCLM _ (markedDX p q u h) z = fderiv ℝ (markedCurve p q (u+h)) z 1 := by
  rw [markedCurve_fderiv,markedSlope_add]
  simp only [add_apply,complexSlope_apply,one_smul]
  rfl

variable {P : E → E →L[ℝ] E} (hP : BoundedCThree P) (b : ContDiffBump (0:ℂ))

@[simp] lemma chartNonlinearity_value (p q : E) (u h : COne ℂ E) (z : ℂ) :
    valueCLM _ (chartNonlinearity hP b p q u h) z = P (truncatedCurve b p q u h z)
      (fderiv ℝ (markedCurve p q (u+h)) z 1) := by
  rw [chartNonlinearity,bilinCLM_value,truncatedCoefficient_value,markedDX_value]
  rfl



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_PointwiseMarkedCR
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frozenTargetCoefficient_zero _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.holderTranslate_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTest_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTranslate_deriv _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTranslate_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.translationVariation_deriv _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.translationVariation_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.geometricHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.normalizedPrimitive_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.realCurve_zero _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {K : Set ℂ}

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ptCRInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ptCRInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ptCRInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ptCRInst4
local instance ptCRInst5_r0c26fd_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance ptCRInst6_r0c26fd_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ptCRInst7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ptCRInst8
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ptCRInst9
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ptCRInst10
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ptCRInst11
omit [CompleteSpace E] in
lemma markedCurve_variation [CompleteSpace E] (p q : E) (u : COne ℂ E) (h : markedModel (E := E) K) (z : ℂ) :
    markedCurve p q (u+h.val) z = markedCurve p q u z + markedVariation (E := E) (K := K) z h := by
  simp only [markedCurve,markedSlope_add,cValue_add,markedVariation_value,smul_sub]
  abel

omit [CompleteSpace E] in
lemma markedCurve_derivative_variation [CompleteSpace E] (p q : E) (u : COne ℂ E)
    (h : markedModel (E := E) K) (z v : ℂ) :
    fderiv ℝ (markedCurve p q (u+h.val)) z v =
      fderiv ℝ (markedCurve p q u) z v + markedDerivativeVariation (E := E) (K := K) z v h := by
  have h₁ := congrArg (fun L : ℂ →L[ℝ] E => L v) (markedCurve_fderiv p q (u+h.val) z)
  have h₂ := congrArg (fun L : ℂ →L[ℝ] E => L v) (markedCurve_fderiv p q u z)
  calc
    _ = (complexSlope (markedSlope p q (u+h.val))+cDeriv (u+h.val) z) v := h₁
    _ = (complexSlope (markedSlope p q u)+cDeriv u z) v +
        markedDerivativeVariation (E := E) (K := K) z v h := by
      simp only [add_apply,complexSlope_apply,markedSlope_add,smul_sub,
        markedDerivativeVariation_value]
      change v • markedSlope p q u-v • cValue h.val 1 + (cDeriv u z v+cDeriv h.val z v) = _
      abel
    _ = _ := congrArg (fun w : E => w+markedDerivativeVariation (E := E) (K := K) z v h) h₂.symm

lemma markedCurve_model_hasFDerivAt (p q : E) (u : COne ℂ E) (z : ℂ) :
    HasFDerivAt (fun h : markedModel (E := E) K => markedCurve p q (u+h.val) z)
      (markedVariation z) 0 := by
  have hd := (hasFDerivAt_const (markedCurve p q u z) (0 : markedModel (E := E) K)).add
    (markedVariation (E := E) (K := K) z).hasFDerivAt
  have hd' : HasFDerivAt (fun h : markedModel (E := E) K =>
      markedCurve p q u z + markedVariation (E := E) (K := K) z h)
      (markedVariation (E := E) (K := K) z) 0 := by
    convert! hd using 1
    all_goals try with_reducible_and_instances rfl
    simp only [zero_add]
  apply hd'.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun h => markedCurve_variation p q u h z)

lemma markedCurve_derivative_model_hasFDerivAt (p q : E) (u : COne ℂ E) (z v : ℂ) :
    HasFDerivAt (fun h : markedModel (E := E) K => fderiv ℝ (markedCurve p q (u+h.val)) z v)
      (markedDerivativeVariation z v) 0 := by
  have hd := (hasFDerivAt_const (fderiv ℝ (markedCurve p q u) z v)
    (0 : markedModel (E := E) K)).add
    (markedDerivativeVariation (E := E) (K := K) z v).hasFDerivAt
  have hd' : HasFDerivAt (fun h : markedModel (E := E) K =>
      fderiv ℝ (markedCurve p q u) z v + markedDerivativeVariation (E := E) (K := K) z v h)
      (markedDerivativeVariation (E := E) (K := K) z v) 0 := by
    convert! hd using 1
    all_goals try with_reducible_and_instances rfl
    simp only [zero_add]
  apply hd'.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun h => markedCurve_derivative_variation p q u h z v)

lemma pointMarkedCR_hasFDerivAt {J : E → E →L[ℝ] E} (hJ : Differentiable ℝ J)
    (p q : E) (u : COne ℂ E) (z : ℂ) :
    HasFDerivAt (pointMarkedCR (K := K) J p q u z) (pointMarkedCRDeriv J p q u z) 0 := by
  have hU := markedCurve_model_hasFDerivAt (K := K) p q u z
  have hY := markedCurve_derivative_model_hasFDerivAt (K := K) p q u z Complex.I
  have hX := markedCurve_derivative_model_hasFDerivAt (K := K) p q u z 1
  have hJC := (hJ (markedCurve p q (u+(0 : markedModel (E := E) K).val) z)).hasFDerivAt.comp 0 hU
  have hN := hJC.clm_apply hX
  convert! hY.sub hN using 1
  all_goals try with_reducible_and_instances rfl
  apply ContinuousLinearMap.ext
  intro h
  simp only [pointMarkedCRDeriv,sub_apply,add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,Function.comp_apply,Submodule.coe_zero,add_zero]

omit [CompleteSpace E] in
lemma pointMarkedCRDeriv_value [CompleteSpace E] (J : E → E →L[ℝ] E) (p q : E) (u : COne ℂ E)
    (z : ℂ) (h : markedModel (E := E) K) :
    pointMarkedCRDeriv J p q u z h =
      cDeriv h.val z Complex.I - J (markedCurve p q u z) (cDeriv h.val z 1) -
        fderiv ℝ J (markedCurve p q u z) (cValue h.val z) (fderiv ℝ (markedCurve p q u) z 1) +
      (J (markedCurve p q u z) (cValue h.val 1) - Complex.I • cValue h.val 1 +
        fderiv ℝ J (markedCurve p q u z) (z • cValue h.val 1) (fderiv ℝ (markedCurve p q u) z 1)) := by
  simp only [pointMarkedCRDeriv,sub_apply,add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,markedDerivativeVariation_value,markedVariation_value,
    one_smul,map_sub,sub_apply]
  abel


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {n : ℕ}

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compLinInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compLinInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compLinInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compLinInst4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compLinInst5
local instance compLinInst6_r0c26fd_1 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compLinInst7
local instance compLinInst8_r0c26fd_1 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
local instance compLinInst9_r0c26fd_1 : NormedAddCommGroup (HMap ℂ (End n)) := inferInstance
local instance compLinInst10_r0c26fd_1 : NormedSpace ℝ (HMap ℂ (End n)) := inferInstance
variable {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) (hc : ∀ x, Compatible (J x)) {B : ℝ}
  (hstd : ∀ x, B < ‖x‖ → J x=standardJ n) (p q : Phase n) (u : COne ℂ (Phase n))

variable {K : Set ℂ} (hK : IsCompact K) (he : ∀ z ∉ K, B < ‖markedCurve p q u z‖)

variable (b : ContDiffBump (0:ℂ)) (hb : K ⊆ Metric.closedBall (0:ℂ) b.rIn)

local instance compLinInst11_r0c26fd_1 : NormedAddCommGroup (markedModel (E := Phase n) K) := inferInstance
local instance compLinInst12_r0c26fd_1 : NormedSpace ℝ (markedModel (E := Phase n) K) := inferInstance
local instance compLinInst13_r0c26fd_1 : NormedAddCommGroup (supportedHolder (E := Phase n) K) := inferInstance
local instance compLinInst14_r0c26fd_1 : NormedSpace ℝ (supportedHolder (E := Phase n) K) := inferInstance
lemma completedLinearized_value (v : markedModel (E := Phase n) K) (z : ℂ) :
    valueCLM _ (completedLinearized hJ hstd p q u he b hb v).val z = pointMarkedCRDeriv J p q u z v := by
  have hQ := completedQ_value hJ hstd p q u z (cValue v.val z)
  have hM := completedMarkHolder_value hJ hstd p q u he b hb z (cValue v.val 1)
  change (cDeriv v.val z Complex.I-J (markedCurve p q u z) (cDeriv v.val z 1)) +
    (-valueCLM _ (completedQ hJ hstd p q u) z (cValue v.val z) +
      valueCLM _ (completedMarkHolder hJ hstd p q u b) z (cValue v.val 1)) = _
  calc
    _ = (cDeriv v.val z Complex.I-J (markedCurve p q u z) (cDeriv v.val z 1)) +
        (-fderiv ℝ J (markedCurve p q u z) (cValue v.val z) (fderiv ℝ (markedCurve p q u) z 1) +
        (J (markedCurve p q u z) (cValue v.val 1)-Complex.I • cValue v.val 1 +
        fderiv ℝ J (markedCurve p q u z) (z • cValue v.val 1) (fderiv ℝ (markedCurve p q u) z 1))) :=
      congrArg₂ (fun x y : Phase n =>
        (cDeriv v.val z Complex.I-J (markedCurve p q u z) (cDeriv v.val z 1))+(-x+y)) hQ hM
    _ = _ := by
      have hv := pointMarkedCRDeriv_value J p q u z v
      calc
        _ = cDeriv v.val z Complex.I-J (markedCurve p q u z) (cDeriv v.val z 1) -
          fderiv ℝ J (markedCurve p q u z) (cValue v.val z) (fderiv ℝ (markedCurve p q u) z 1) +
          (J (markedCurve p q u z) (cValue v.val 1)-Complex.I • cValue v.val 1 +
          fderiv ℝ J (markedCurve p q u z) (z • cValue v.val 1) (fderiv ℝ (markedCurve p q u) z 1)) := by abel
        _ = _ := hv.symm


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {K : Set ℂ}

variable {n : ℕ}

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst6
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst8
variable {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) {B : ℝ}
    (hstd : ∀ x, B < ‖x‖ → J x = standardJ n)

variable (b : ContDiffBump (0:ℂ)) (p q : Phase n)
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst9
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst10
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst11
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst12
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst13
set_option synthInstance.maxHeartbeats 400000 in
local instance chartDerInst14 : ContinuousSMul ℝ
    (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) :=
  IsBoundedSMul.continuousSMul

variable (u : markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut))

lemma actualMarkedChart_fderiv_eval
    (he : ∀ᶠ h in 𝓝 (0 : markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)),
      ∀ z : ℂ, b.rIn ≤ ‖z‖ → B < ‖markedCurve p q (u.val+h.val) z‖ ∧
        B < ‖truncatedCurve b p q u.val h.val z‖) (z : ℂ) :
    (supportedEval (E := Phase n) (K := Metric.closedBall (0:ℂ) b.rOut) z).comp
      (fderiv ℝ (actualMarkedChart hJ hstd b p q u) 0) =
        pointMarkedCRDeriv J p q u.val z := by
  have hd := ((actualMarkedChart_contDiff_bp240 hJ hstd b p q u).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) 0).hasFDerivAt
  have hdE := (supportedEval (E := Phase n) (K := Metric.closedBall (0:ℂ) b.rOut) z).hasFDerivAt.comp 0 hd
  have hdP := pointMarkedCR_hasFDerivAt (K := Metric.closedBall (0:ℂ) b.rOut)
    (hJ.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) p q u.val z
  have heq : (fun h : markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut) =>
      supportedEval (E := Phase n) z (actualMarkedChart hJ hstd b p q u h)) =ᶠ[𝓝 0]
      pointMarkedCR J p q u.val z := by
    filter_upwards [he] with h hh
    exact actualMarkedChart_value_bp240 hJ hstd b p q u h hh z
  exact hdE.unique (hdP.congr_of_eventuallyEq heq)


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_TranslationContinuity
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
section
variable {n : ℕ}
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst6
variable {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) (hc : ∀ x, Compatible (J x)) {B : ℝ}
  (hstd : ∀ x, B < ‖x‖ → J x=standardJ n) (b : ContDiffBump (0:ℂ)) (p q : Phase n)
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst8
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst9
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst10
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst11
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst12
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst13
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst14
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst15
variable (u : markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut))
  (he : ∀ᶠ h in 𝓝 (0 : markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)),
    ∀ z : ℂ, b.rIn ≤ ‖z‖ → B < ‖markedCurve p q (u.val+h.val) z‖ ∧
      B < ‖truncatedCurve b p q u.val h.val z‖)

lemma actualMarkedChart_derivative_eq_linearized_bp240_oai
    (b₁ : ContDiffBump (0:ℂ)) (hb₁ : Metric.closedBall (0:ℂ) b.rOut ⊆ Metric.closedBall (0:ℂ) b₁.rIn) :
    fderiv ℝ (actualMarkedChart hJ hstd b p q u) 0 =
      completedLinearized hJ hstd p q u.val (marked_escape_base b p q u he) b₁ hb₁ := by
  apply ContinuousLinearMap.ext
  intro v
  apply Subtype.ext
  apply value_ext
  intro z
  have hd := congrArg (fun L : markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut) →L[ℝ] Phase n => L v)
    (actualMarkedChart_fderiv_eval hJ hstd b p q u he z)
  exact hd.trans (completedLinearized_value hJ hstd p q u.val (marked_escape_base b p q u he) b₁ hb₁ v z).symm

end

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualMarkedChart_derivative_eq_linearized_bp240_oai := @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualMarkedChart_derivative_eq_linearized_bp240_oai
