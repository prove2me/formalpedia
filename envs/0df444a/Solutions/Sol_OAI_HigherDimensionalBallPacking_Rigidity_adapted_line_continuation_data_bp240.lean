-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.adapted_line_continuation_data_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:55:23.312542+00:00
-- url     : https://prove2.me/submissions/16251efc-1ee2-4ee6-adfe-98532ed48d15

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp021
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_compact_subset_bump_inner_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_exact_marked_zeroSet_compact_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_fullLineEndpointMap_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_fullLineProperPath_bp240

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_RadialForm
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

theorem capacity_smooth (n : ℕ) : ContDiff ℝ ∞ (@capacity n) := by
  have hd : ContDiff ℝ ∞ (fun x : Phase n => stdDot n x x) :=
    ((stdDot n).contDiff.comp contDiff_id).clm_apply contDiff_id
  have he : (@capacity n) = fun y => Real.pi * stdDot n y y := funext capacity_eq_stdDot
  rw [he]
  exact contDiff_const.mul hd

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


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

variable {K : Set ℂ} (hK : IsCompact K)

local instance markedAffineInst1_ra71882_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance markedAffineInst2_ra71882_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance markedAffineInst3_ra71882_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance markedAffineInst4_ra71882_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance markedAffineInst5_ra71882_1 : NormedAddCommGroup (markedModel (E := E) K) := inferInstance
local instance markedAffineInst6_ra71882_1 : NormedSpace ℝ (markedModel (E := E) K) := inferInstance
local instance markedAffineInst7_ra71882_1 : NormedAddCommGroup (supportedHolder (E := E) K) := inferInstance
local instance markedAffineInst8_ra71882_1 : NormedSpace ℝ (supportedHolder (E := E) K) := inferInstance
omit [CompleteSpace E] in
lemma markedSlope_continuous (p q : E) : Continuous (markedSlope p q : COne ℂ E → E) :=
  continuous_const.sub (jetEval (E := E) 1).continuous

omit [CompleteSpace E] in
lemma markedCurve_asymptote (p q : E) (u : COne ℂ E) :
    Tendsto (fun z : ℂ => z⁻¹ • markedCurve p q u z) (cocompact ℂ)
      (𝓝 (markedSlope p q u)) := by
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa only [← Metric.cobounded_eq_cocompact] using (tendsto_inv₀_cobounded (α := ℂ))
  have hb : IsBoundedUnder (· ≤ ·) (cocompact ℂ) (norm ∘ (cValue u : ℂ → E)) :=
    ⟨‖cValue u‖, eventually_map.mpr (Eventually.of_forall fun z => (cValue u).norm_coe_le_norm z)⟩
  have hzero := hi.zero_smul_isBoundedUnder_le hb
  have ht := ((hi.smul_const p).add_const (markedSlope p q u)).add hzero
  simp only [zero_smul,zero_add,add_zero] at ht
  apply ht.congr'
  filter_upwards [(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz
  have hz0 : z ≠ 0 := by simpa only [mem_compl_iff,mem_singleton_iff] using hz
  simp only [markedCurve,smul_add,smul_smul,inv_mul_cancel₀ hz0,one_smul]



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
local instance affineCutInst3_ra71882_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance affineCutInst4_ra71882_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
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
lemma cValue_norm_le (u : COne ℂ E) (z : ℂ) : ‖cValue u z‖ ≤ ‖u‖ :=
  (norm_value_le (jetValueCLM _ u) z).trans (jetValue_norm_le u)

omit [CompleteSpace E] in
lemma truncatedCurve_norm_lower (p q : E) (u h : COne ℂ E) (z : ℂ) :
    ‖z‖*(‖markedSlope p q u‖-‖h‖)-‖p‖-‖u‖-‖h‖ ≤ ‖truncatedCurve b p q u h z‖ := by
  have hb : ‖b z • (z • cValue h 1)‖ ≤ ‖z‖*‖h‖ := by
    rw [norm_smul,norm_smul,Real.norm_eq_abs,abs_of_nonneg (b.nonneg)]
    calc
      b z*(‖z‖*‖cValue h 1‖) ≤ 1*(‖z‖*‖cValue h 1‖) :=
        mul_le_mul_of_nonneg_right (b.le_one) (by positivity)
      _ ≤ ‖z‖*‖h‖ := by rw [one_mul]; exact mul_le_mul_of_nonneg_left (cValue_norm_le h 1) (norm_nonneg z)
  have he : z • markedSlope p q u = truncatedCurve b p q u h z -p-cValue u z-cValue h z+
      b z • (z • cValue h 1) := by rw [truncatedCurve_value]; abel
  have hn := calc
    ‖z • markedSlope p q u‖ = ‖truncatedCurve b p q u h z -p-cValue u z-cValue h z+
        b z • (z • cValue h 1)‖ := congrArg norm he
    _ ≤ ‖truncatedCurve b p q u h z‖+‖p‖+‖u‖+‖h‖+‖z‖*‖h‖ := by
      apply (norm_add_le _ _).trans
      apply add_le_add _ hb
      apply (norm_sub_le _ _).trans
      apply add_le_add _ (cValue_norm_le h z)
      apply (norm_sub_le _ _).trans
      apply add_le_add _ (cValue_norm_le u z)
      exact norm_sub_le _ _
  rw [norm_smul] at hn
  nlinarith

omit [CompleteSpace E] in
lemma markedCurve_norm_lower (p q : E) (u h : COne ℂ E) (z : ℂ) :
    ‖z‖*(‖markedSlope p q u‖-‖h‖)-‖p‖-‖u‖-‖h‖ ≤ ‖markedCurve p q (u+h) z‖ := by
  have he : z • markedSlope p q u = markedCurve p q (u+h) z-p-cValue u z-cValue h z+
      z • cValue h 1 := by
    simp only [markedCurve,markedSlope_add,cValue_add,smul_sub]
    abel
  have hn := calc
    ‖z • markedSlope p q u‖ = ‖markedCurve p q (u+h) z-p-cValue u z-cValue h z+z • cValue h 1‖ := congrArg norm he
    _ ≤ ‖markedCurve p q (u+h) z‖+‖p‖+‖u‖+‖h‖+‖z‖*‖h‖ := by
      apply (norm_add_le _ _).trans
      apply add_le_add _ (by rw [norm_smul]; exact mul_le_mul_of_nonneg_left (cValue_norm_le h 1) (norm_nonneg z))
      apply (norm_sub_le _ _).trans
      apply add_le_add _ (cValue_norm_le h z)
      apply (norm_sub_le _ _).trans
      apply add_le_add _ (cValue_norm_le u z)
      exact norm_sub_le _ _
  rw [norm_smul] at hn
  nlinarith


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
local instance markedChartInst13_ra71882_1 : NormedAddCommGroup (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance markedChartInst14_ra71882_1 : NormedSpace ℝ (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
omit [CompleteSpace E] in
@[simp] lemma markedDX_value [CompleteSpace E] (p q : E) (u h : COne ℂ E) (z : ℂ) :
    valueCLM _ (markedDX p q u h) z = fderiv ℝ (markedCurve p q (u+h)) z 1 := by
  rw [markedCurve_fderiv,markedSlope_add]
  simp only [add_apply,complexSlope_apply,one_smul]
  rfl



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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

local instance feInst1_ra71882_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance feInst2_ra71882_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance feInst3_ra71882_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance feInst4_ra71882_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
omit [CompleteSpace E] in
lemma freeModel_of_elliptic [CompleteSpace E] {J : E → E →L[ℝ] E} {B R : ℝ}
    (hstd : ∀ x, B<‖x‖ → J x=complexI (E := E))
    (p a : E) (u : COne ℂ E)
    (hcr : ∀ z, fderiv ℝ (affineCurve p (complexSlope a) u) z Complex.I =
      J (affineCurve p (complexSlope a) u z) (fderiv ℝ (affineCurve p (complexSlope a) u) z 1))
    (he : ∀ z, R≤‖z‖ → B<‖affineCurve p (complexSlope a) u z‖) :
    u∈freeModel (E := E) (Metric.closedBall (0:ℂ) R) := by
  apply (mem_supportedHolder _ _).mpr
  intro z hz
  have hz' : R≤‖z‖ := (show R<‖z‖ by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hz).le
  have hh := hcr z
  rw [hstd _ (he z hz'),affineCurve_fderiv] at hh
  change Complex.I • a+cDeriv u z Complex.I=Complex.I • ((1:ℂ) • a+cDeriv u z 1) at hh
  rw [one_smul,smul_add] at hh
  have hd := add_left_cancel hh
  change valueCLM _ (standardJetCR u) z=0
  rw [standardJetCR_value]
  exact sub_eq_zero.mpr hd

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartNbInst1
local instance chartNbInst2_ra71882_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance chartNbInst3_ra71882_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance chartNbInst4_ra71882_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartNbInst5
local instance chartNbInst6_ra71882_1 (K : Set ℂ) : NormedSpace ℝ (markedModel (E := E) K) := inferInstance
local instance chartNbInst7_ra71882_1 (K : Set ℂ) : AddCommGroup (markedModel (E := E) K) := (chartNbInst5 K).toAddCommGroup
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartNbInst9
omit [CompleteSpace E] in
lemma markedEscape_of_uniform [CompleteSpace E] (p q : E) (u : COne ℂ E) (B δ R : ℝ) (hδ : 0 < δ)
    (he : ∀ h : COne ℂ E, ‖h‖ < δ → ∀ z : ℂ, R ≤ ‖z‖ →
      B < ‖markedCurve p q (u+h) z‖ ∧ ∀ b : ContDiffBump (0:ℂ), B < ‖truncatedCurve b p q u h z‖)
    (b : ContDiffBump (0:ℂ)) (hR : R ≤ b.rIn) : MarkedEscapeNeighborhood b p q u B := by
  filter_upwards [Metric.ball_mem_nhds (0 : markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) hδ] with h hh
  intro z hz
  have hh' : ‖h.val‖ < δ := by simpa only [Metric.mem_ball,dist_zero_right,Submodule.norm_coe] using hh
  exact ⟨(he h.val hh' z (hR.trans hz)).1,(he h.val hh' z (hR.trans hz)).2 b⟩

end

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Compactness_ResidualCauchy
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
open HolderCompletion
variable {n : ℕ}

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.clcInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.clcInst2
local instance clcInst3_ra71882_1 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance clcInst4_ra71882_1 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
lemma compact_structure_norm_standard {J : Phase n → End n}
    (hc : HasCompactSupport (fun x => J x-standardJ n)) :
    ∃ B : ℝ,∀ x,B<‖x‖ →J x=standardJ n := by
  obtain ⟨B,hB⟩ := hc.exists_bound_of_continuousOn (f := fun x : Phase n => x) continuous_id.continuousOn
  refine ⟨B,fun x hx => ?_⟩
  exact sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport (f := fun x => J x-standardJ n) (fun hh => (not_le_of_gt hx) (hB x hh)))

lemma represented_line_slope_nonzero {J : Phase n → End n} {p q : Phase n}
    (w : COne ℂ (Phase n)) (hu : AffineLineCurve J p q (markedCurve p q w)) :
    markedSlope p q w≠0 := by
  obtain ⟨a,ha,hlim⟩ := hu.2.2.2.2
  have he := tendsto_nhds_unique (markedCurve_asymptote p q w) hlim
  exact fun hz => ha (he ▸ hz)


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
open HolderCompletion



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Continuation_CompatibleHomotopy
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
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

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.cmn1
local instance cmn2_ra71882_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
omit [CompleteSpace E] in
lemma compact_marked_bounds [CompleteSpace E] {K : Set (COne ℂ E)} (hK : IsCompact K) (p q : E)
    (ha : ∀ w∈K,markedSlope p q w≠0) :
    ∃ M δ : ℝ,0<M ∧ 0<δ ∧ ∀ w∈K,‖w‖<M ∧ δ<‖markedSlope p q w‖ := by
  obtain ⟨M,hM,hMb⟩ := hK.isBounded.exists_pos_norm_le
  by_cases hn : K.Nonempty
  · obtain ⟨w,hw,hmin⟩ := hK.exists_isMinOn hn (markedSlope_continuous p q).norm.continuousOn
    have hp : 0<‖markedSlope p q w‖ := norm_pos_iff.mpr (ha w hw)
    refine ⟨M+1,‖markedSlope p q w‖/2,by linarith,half_pos hp,?_⟩
    intro v hv
    exact ⟨lt_of_le_of_lt (hMb v hv) (by linarith),
      (half_lt_self hp).trans_le (hmin hv)⟩
  · exact ⟨1,1,by norm_num,by norm_num,fun w hw => (hn ⟨w,hw⟩).elim⟩

omit [CompleteSpace E] in
lemma bounded_marked_uniform_escape [CompleteSpace E] (p q : E) {M δ B : ℝ}
    (hM : 0<M) (hδ : 0<δ) (hB : 0≤B) :
    ∃ R : ℝ,0<R ∧ ∀ w∈markedBoundedDomain p q M δ,
      ∀ h : COne ℂ E,‖h‖<δ/2 →∀ z : ℂ,R≤‖z‖ →
        B<‖markedCurve p q (w+h) z‖ ∧
        ∀ b : ContDiffBump (0:ℂ),B<‖truncatedCurve b p q w h z‖ := by
  let ε := δ/2
  have hε : 0<ε := half_pos hδ
  let R := (B+‖p‖+M+ε+1)/ε
  have hR : 0<R := by dsimp [R] <;> positivity
  refine ⟨R,hR,?_⟩
  intro w hw h hh z hz
  have hsl : ε≤‖markedSlope p q w‖-‖h‖ := by
    dsimp only [ε]
    linarith [hw.2]
  have hm : R*ε≤‖z‖*(‖markedSlope p q w‖-‖h‖) :=
    mul_le_mul hz hsl hε.le (norm_nonneg z)
  have he : R*ε=B+‖p‖+M+ε+1 := div_mul_cancel₀ _ hε.ne'
  rw [he] at hm
  have hl : B<‖z‖*(‖markedSlope p q w‖-‖h‖)-‖p‖-‖w‖-‖h‖ := by
    change ‖h‖<ε at hh
    linarith [hw.1]
  exact ⟨hl.trans_le (markedCurve_norm_lower p q w h z),
    fun b => hl.trans_le (truncatedCurve_norm_lower b p q w h z)⟩

lemma bounded_marked_escape_neighborhood (p q : E) {M δ B R : ℝ} (hδ : 0<δ)
    (he : ∀ w∈markedBoundedDomain p q M δ,∀ h : COne ℂ E,‖h‖<δ/2 →∀ z : ℂ,R≤‖z‖ →
      B<‖markedCurve p q (w+h) z‖ ∧ ∀ b : ContDiffBump (0:ℂ),B<‖truncatedCurve b p q w h z‖)
    (b : ContDiffBump (0:ℂ)) (hRb : R≤b.rIn)
    {w : COne ℂ E} (hw : w∈markedBoundedDomain p q M δ) :
    MarkedEscapeNeighborhood b p q w B :=
  markedEscape_of_uniform p q w B (δ/2) R (half_pos hδ) (he w hw) b hRb

omit [CompleteSpace E] in
lemma marked_escape_neighborhood_base [CompleteSpace E] (b : ContDiffBump (0:ℂ)) (p q : E)
    {w : COne ℂ E} {B : ℝ} (he : MarkedEscapeNeighborhood b p q w B) :
    ∀ z,b.rIn≤‖z‖ →B<‖markedCurve p q w z‖ := by
  intro z hz
  have hh := (he.self_of_nhds z hz).1
  simpa only [Submodule.coe_zero,add_zero] using hh

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
open HolderCompletion

private lemma normed_t2 (X : Type*) [NormedAddCommGroup X] : T2Space X := inferInstance

variable {n : ℕ}
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.fmp1
local instance fmp2_ra71882_1 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance fmp3_ra71882_1 : MetricSpace (COne ℂ (Phase n)) := (fmp1 (n := n)).toMetricSpace
local instance fmp4 : T2Space (COne ℂ (Phase n)) := normed_t2 _

lemma full_marked_compact_of_exact {J : Phase n → End n} {p q : Phase n}
    (hc : IsCompact (exactMarkedZeroSet J p q)) : IsCompact (fullMarkedZeroSet J p q) := by
  have hK := hc.image continuous_snd
  have hg : Continuous (fun v : ℝ × COne ℂ (Phase n) => (fullTime v.1,v.2)) :=
    (fullTime_smooth.continuous.comp continuous_fst).prodMk continuous_snd
  have hcl : IsClosed (fullMarkedZeroSet J p q) :=
    (isClosed_Icc.preimage continuous_fst).inter (hc.isClosed.preimage hg)
  apply (isCompact_Icc.prod hK).of_isClosed_subset hcl
  intro v hv
  exact ⟨hv.1,⟨(fullTime v.1,v.2),hv.2,rfl⟩⟩

variable {J : Phase n → End n} (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
  (hJc : HasCompactSupport (fun x => J x-standardJ n))
  {S T : ℝ} (hST : S<T) (hT : T<1) (hout : ∀ x,S < capacity x →J x=standardJ n)
  {p q : Phase n} (hpq : p≠q)

include hJs hJ hJc hST hT hout hpq in
lemma full_marked_zeroSet_compact : IsCompact (fullMarkedZeroSet J p q) :=
  full_marked_compact_of_exact (exact_marked_zeroSet_compact_bp240 hJs hJ hJc hST hT hout hpq)

include hJs hJ hJc hST hT hout hpq in
lemma exact_marked_common_neighborhood :
    ∃ (B M δ : ℝ) (b : ContDiffBump (0:ℂ)),0≤B ∧ 0<M ∧ 0<δ ∧
      (∀ x,B<‖x‖ →J x=standardJ n) ∧
      (∀ v∈exactMarkedZeroSet J p q,
        v.2∈markedBoundedDomain p q M δ ∧
        v.2∈markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) ∧
      (∀ w∈markedBoundedDomain p q M δ,MarkedEscapeNeighborhood b p q w B) := by
  obtain ⟨B₀,hB₀⟩ := compact_structure_norm_standard hJc
  let B := max B₀ 0
  have hB : 0≤B := le_max_right _ _
  have hstd : ∀ x,B<‖x‖ →J x=standardJ n := fun x hx => hB₀ x ((le_max_left _ _).trans_lt hx)
  let K := Prod.snd '' exactMarkedZeroSet J p q
  have hK : IsCompact K := (exact_marked_zeroSet_compact_bp240 hJs hJ hJc hST hT hout hpq).image continuous_snd
  have hKa : ∀ w∈K,markedSlope p q w≠0 := by
    rintro w ⟨v,hv,rfl⟩
    exact represented_line_slope_nonzero v.2 hv.2.2
  obtain ⟨M,δ,hM,hδ,hbound⟩ := compact_marked_bounds hK p q hKa
  obtain ⟨R,hR,hesc⟩ := bounded_marked_uniform_escape p q hM hδ hB
  let b : ContDiffBump (0:ℂ) := ⟨R,R+1,hR,by linarith⟩
  have hn : ∀ w∈markedBoundedDomain p q M δ,MarkedEscapeNeighborhood b p q w B :=
    fun w hw => bounded_marked_escape_neighborhood p q hδ hesc b (le_refl R) hw
  refine ⟨B,M,δ,b,hB,hM,hδ,hstd,?_,hn⟩
  intro v hv
  have hw : v.2∈markedBoundedDomain p q M δ := hbound v.2 ⟨v,hv,rfl⟩
  refine ⟨hw,hv.2.1,?_⟩
  have hstd' : ∀ x,B<‖x‖ →lineHomotopy J v.1 x=complexI (E := Phase n) := by
    intro x hx
    change interpolateJ (J x) v.1=standardJ n
    rw [hstd x hx]
    exact interpolateJ_standard hv.1
  have hcr : ∀ z,fderiv ℝ (markedCurve p q v.2) z Complex.I=
      lineHomotopy J v.1 (markedCurve p q v.2 z) (fderiv ℝ (markedCurve p q v.2) z 1) := by
    intro z
    simpa only [mul_one] using (hv.2.2.2.1 z).2 1
  have he0 : ∀ z,b.rOut≤‖z‖ → B<‖markedCurve p q v.2 z‖ := by
    intro z hz
    exact marked_escape_neighborhood_base b p q (hn v.2 hw) z
      (b.rIn_lt_rOut.le.trans hz)
  exact freeModel_of_elliptic hstd' p (markedSlope p q v.2) v.2 hcr he0

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Continuation_ParameterizedImplicit
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
open HolderCompletion
section

variable {n : ℕ} {J : Phase n → End n}
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.lcdFinal1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.lcdFinal2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.lcdFinal3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.lcdFinal4
variable (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
  (hJc : HasCompactSupport (fun x => J x-standardJ n)) (p q : Phase n)

variable {S T : ℝ} (hST : S<T) (hT : T<1) (hout : ∀ x,S < capacity x →J x=standardJ n)
  (hpq : p≠q)
include hJs hJ hJc hST hT hout hpq in

theorem full_line_continuation_data :
    ∃ (b b₁ : ContDiffBump (0:ℂ)) (M δ : ℝ),
      FullLineReady hJs hJ hJc p q b b₁ M δ := by
  obtain ⟨B,M,δ,b,hB,hM,hδ,hstd,hbound,he⟩ :=
    exact_marked_common_neighborhood (J := J) (p := p) (q := q) hJs hJ hJc hST hT hout hpq
  obtain ⟨b₁,hb₁⟩ := compact_subset_bump_inner_bp240 (K := Metric.closedBall (0:ℂ) b.rOut)
    (isCompact_closedBall (0:ℂ) b.rOut)
  have hbound' : ∀ v∈exactMarkedZeroSet J p q,v.2∈markedBoundedDomain p q M δ :=
    fun v hv => (hbound v hv).1
  refine ⟨b,b₁,M,δ,?_,?_⟩
  · exact fullLineProperPath_bp240 b hJs hJ hJc b₁ p q hb₁ hstd hδ he hbound'
      (full_marked_zeroSet_compact hJs hJ hJc hST hT hout hpq) hpq
  · exact fullLineEndpointMap_bp240 b hJs hJ hJc b₁ p q hb₁ hstd hδ he

end
variable {n : ℕ} {J : Phase n → End n}

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.alc1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.alc2
lemma adapted_structure_capacity_bound
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    (hinside : tsupport (fun x => J x-standardJ n)⊆openBall n 1) :
    ∃ S T : ℝ,S<T ∧ T<1 ∧ ∀ x,S < capacity x →J x=standardJ n := by
  let K := tsupport (fun x => J x-standardJ n) ∪ {(0:Phase n)}
  have hK : IsCompact K := hJc.union (isCompact_singleton)
  have hne : K.Nonempty := ⟨0,Or.inr (by rfl)⟩
  have hKi : K⊆openBall n 1 := by
    intro x hx
    rcases hx with hx|hx
    · exact hinside hx
    · have hx0 : x=0 := hx
      subst x
      simp [openBall,capacity]
  obtain ⟨x,hx,hmax⟩ := hK.exists_isMaxOn hne (capacity_smooth n).continuous.continuousOn
  have hS : capacity x<1 := hKi hx
  refine ⟨capacity x,(capacity x+1)/2,by linarith,by linarith,?_⟩
  intro y hy
  have hn : y∉tsupport (fun z => J z-standardJ n) := by
    intro hh
    exact (not_le_of_gt hy) (hmax (Or.inl hh))
  exact sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport (f := fun z => J z-standardJ n) hn)

lemma adapted_line_continuation_data_bp240_oai (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    (hinside : tsupport (fun x => J x-standardJ n)⊆openBall n 1) (p q : Phase n) (hpq : p≠q) :
    ∃ (b b₁ : ContDiffBump (0:ℂ)) (M δ : ℝ),
      FullLineReady hJs hJ hJc p q b b₁ M δ := by
  obtain ⟨S,T,hST,hT,hout⟩ := adapted_structure_capacity_bound hJc hinside
  exact full_line_continuation_data hJs hJ hJc p q hST hT hout hpq

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.adapted_line_continuation_data_bp240_oai := @OAI.HigherDimensionalBallPacking.Rigidity.adapted_line_continuation_data_bp240_oai
