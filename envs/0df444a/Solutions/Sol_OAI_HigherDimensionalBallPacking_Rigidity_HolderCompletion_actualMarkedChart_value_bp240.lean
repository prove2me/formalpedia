-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualMarkedChart_value_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:54:50.607594+00:00
-- url     : https://prove2.me/submissions/4f19da05-90d6-4c99-abc1-a4e6441c02bd

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp020

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_MarkedJets
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
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

variable {K : Set ℂ} (hK : IsCompact K)

local instance markedAffineInst1_rdfffba_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance markedAffineInst2_rdfffba_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance markedAffineInst3_rdfffba_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance markedAffineInst4_rdfffba_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance markedAffineInst5_rdfffba_1 : NormedAddCommGroup (markedModel (E := E) K) := inferInstance
local instance markedAffineInst6_rdfffba_1 : NormedSpace ℝ (markedModel (E := E) K) := inferInstance
local instance markedAffineInst7_rdfffba_1 : NormedAddCommGroup (supportedHolder (E := E) K) := inferInstance
local instance markedAffineInst8_rdfffba_1 : NormedSpace ℝ (supportedHolder (E := E) K) := inferInstance
omit [CompleteSpace E] in
lemma markedCurve_standardResidual (p q : E) (u : COne ℂ E) (z : ℂ) :
    fderiv ℝ (markedCurve p q u) z Complex.I -
      Complex.I • fderiv ℝ (markedCurve p q u) z 1 = valueCLM _ (standardJetCR u) z := by
  rw [markedCurve_fderiv,standardJetCR_value]
  simp only [add_apply,complexSlope_apply,one_smul,smul_add]
  abel



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

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
local instance affineCutInst3_rdfffba_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance affineCutInst4_rdfffba_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineCutInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineCutInst6
omit [CompleteSpace E] in
lemma markedSlope_add (p q : E) (u h : COne ℂ E) :
    markedSlope p q (u+h) = markedSlope p q u-cValue h 1 := by
  simp only [markedSlope,cValue_add]
  abel

omit [CompleteSpace E] in
lemma truncatedCurve_value (p q : E) (u h : COne ℂ E) (z : ℂ) :
    truncatedCurve b p q u h z = p+z • markedSlope p q u+cValue u z+cValue h z-
      b z • (z • cValue h 1) := by
  simp only [truncatedCurve,affineCurve,affine,complexSlope_apply,cValue_add,truncateShift_value]
  abel

omit [CompleteSpace E] in
lemma truncatedCurve_eq_marked (p q : E) (u h : COne ℂ E) {z : ℂ}
    (hz : z ∈ Metric.closedBall 0 b.rIn) :
    truncatedCurve b p q u h z = markedCurve p q (u+h) z := by
  rw [truncatedCurve_value,b.one_of_mem_closedBall hz,one_smul,markedCurve,markedSlope_add]
  simp only [cValue_add,smul_sub]
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

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

variable {F : Type*} [Zero F]

local instance affineEscapeInst1_rdfffba_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance affineEscapeInst2_rdfffba_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
omit [CompleteSpace E] in
lemma compact_coefficient_truncated [CompleteSpace E] {P : E → F} {B : ℝ}
    (hP : ∀ x, B < ‖x‖ → P x = 0) (p q : E) (u : COne ℂ E)
    (b : ContDiffBump (0:ℂ)) {h : COne ℂ E}
    (he : ∀ z : ℂ, b.rIn ≤ ‖z‖ → B < ‖markedCurve p q (u+h) z‖ ∧
      B < ‖truncatedCurve b p q u h z‖) (z : ℂ) :
    P (truncatedCurve b p q u h z) = P (markedCurve p q (u+h) z) := by
  by_cases hz : z ∈ Metric.closedBall 0 b.rIn
  · rw [truncatedCurve_eq_marked b p q u h hz]
  · have hz' : b.rIn ≤ ‖z‖ := by
      simp only [Metric.mem_closedBall,dist_zero_right] at hz
      exact (lt_of_not_ge hz).le
    rw [hP _ (he z hz').1,hP _ (he z hz').2]

omit [CompleteSpace E] in
lemma compact_coefficient_zero_outside [CompleteSpace E] {P : E → F} {B : ℝ}
    (hP : ∀ x, B < ‖x‖ → P x = 0) (p q : E) (u : COne ℂ E)
    (b : ContDiffBump (0:ℂ)) {h : COne ℂ E}
    (he : ∀ z : ℂ, b.rIn ≤ ‖z‖ → B < ‖markedCurve p q (u+h) z‖)
    {z : ℂ} (hz : z ∉ Metric.closedBall 0 b.rIn) :
    P (markedCurve p q (u+h) z) = 0 := by
  apply hP
  apply he
  simp only [Metric.mem_closedBall,dist_zero_right] at hz
  exact (lt_of_not_ge hz).le


end
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
local instance markedChartInst13_rdfffba_1 : NormedAddCommGroup (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance markedChartInst14_rdfffba_1 : NormedSpace ℝ (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
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

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst9
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst10
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst11
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst12
lemma markedChart_value (p q : E)
    (u h : markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) (z : ℂ) :
    valueCLM _ (markedChart hP b p q u h).val z =
      valueCLM _ (standardJetCR (u.val+h.val)) z - b z •
      P (truncatedCurve b p q u.val h.val z) (fderiv ℝ (markedCurve p q (u.val+h.val)) z 1) := by
  exact congrArg (fun w : E => valueCLM _ (standardJetCR (u.val+h.val)) z - b z • w)
    (chartNonlinearity_value hP b p q u.val h.val z)

omit [CompleteSpace E] in
lemma cutoff_action_eq [CompleteSpace E] {A₀ A₁ : E →L[ℝ] E} {z : ℂ} (hA : A₀ = A₁)
    (hz0 : z ∉ Metric.closedBall 0 b.rIn → A₁ = 0) (v : E) :
    b z • A₀ v = A₁ v := by
  subst A₀
  by_cases hz : z ∈ Metric.closedBall 0 b.rIn
  · calc
      b z • A₁ v = (1:ℝ) • A₁ v := congrArg (fun c : ℝ => c • A₁ v) (b.one_of_mem_closedBall hz)
      _ = A₁ v := one_smul ℝ _
  · have ha : A₁ v = 0 := congrArg (fun A : E →L[ℝ] E => A v) (hz0 hz)
    calc
      b z • A₁ v = b z • (0:E) := congrArg (fun w : E => b z • w) ha
      _ = 0 := smul_zero _
      _ = A₁ v := ha.symm

lemma markedChart_actual_value {B : ℝ} (hPB : ∀ x, B < ‖x‖ → P x = 0) (p q : E)
    (u h : markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut))
    (he : ∀ z : ℂ, b.rIn ≤ ‖z‖ → B < ‖markedCurve p q (u.val+h.val) z‖ ∧
      B < ‖truncatedCurve b p q u.val h.val z‖) (z : ℂ) :
    valueCLM _ (markedChart hP b p q u h).val z =
      fderiv ℝ (markedCurve p q (u.val+h.val)) z Complex.I -
      (Complex.I • fderiv ℝ (markedCurve p q (u.val+h.val)) z 1 +
        P (markedCurve p q (u.val+h.val) z) (fderiv ℝ (markedCurve p q (u.val+h.val)) z 1)) := by
  have hPz : P (truncatedCurve b p q u.val h.val z) =
      P (markedCurve p q (u.val+h.val) z) :=
    compact_coefficient_truncated hPB p q u.val b he z
  have hS := markedCurve_standardResidual p q (u.val+h.val) z
  have hN := cutoff_action_eq b hPz
    (compact_coefficient_zero_outside hPB p q u.val b (fun w hw => (he w hw).1))
    (fderiv ℝ (markedCurve p q (u.val+h.val)) z 1)
  calc
    _ = valueCLM _ (standardJetCR (u.val+h.val)) z - b z •
        P (truncatedCurve b p q u.val h.val z) (fderiv ℝ (markedCurve p q (u.val+h.val)) z 1) :=
      markedChart_value hP b p q u h z
    _ = (fderiv ℝ (markedCurve p q (u.val+h.val)) z Complex.I -
        Complex.I • fderiv ℝ (markedCurve p q (u.val+h.val)) z 1) -
        P (markedCurve p q (u.val+h.val) z) (fderiv ℝ (markedCurve p q (u.val+h.val)) z 1) :=
      congrArg₂ (· - ·) hS.symm hN
    _ = _ := sub_sub _ _ _



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
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

include hstd in
lemma compactJPerturbation_outside : ∀ x, B < ‖x‖ → compactJPerturbation J x = 0 := by
  intro x hx
  exact sub_eq_zero.mpr (hstd x hx)

variable (b : ContDiffBump (0:ℂ)) (p q : Phase n)

variable (u : markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut))

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst9
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst10
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst11
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst12
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst13
lemma actualMarkedChart_value_bp240_oai
    (h : markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut))
    (he : ∀ z : ℂ, b.rIn ≤ ‖z‖ → B < ‖markedCurve p q (u.val+h.val) z‖ ∧
      B < ‖truncatedCurve b p q u.val h.val z‖) (z : ℂ) :
    supportedEval (E := Phase n) z (actualMarkedChart hJ hstd b p q u h) =
      pointMarkedCR J p q u.val z h := by
  have hx := markedChart_actual_value (compactJPerturbationBound hJ hstd) b
    (compactJPerturbation_outside hstd) p q u h he z
  change valueCLM _ ((markedChart (compactJPerturbationBound hJ hstd) b p q u h).val) z = _
  rw [hx]
  have hI (v : Phase n) : standardJ n v = Complex.I • v := rfl
  simp only [pointMarkedCR,compactJPerturbation,sub_apply,hI]
  abel


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualMarkedChart_value_bp240_oai := @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualMarkedChart_value_bp240_oai
