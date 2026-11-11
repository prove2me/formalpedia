-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.fullLineEndpointMap_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:55:58.880554+00:00
-- url     : https://prove2.me/submissions/8973aee2-3534-446e-8679-a190c7ecf81e

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp021
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_completed_markedCurve_contDiff_bp240

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_CompatibleStructures
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrame_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedDX_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedQ_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedStructureJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficientHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficient_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrderHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrder_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frozenTargetCoefficient_zero _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothAlongJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothMarkedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.capacity_eq_stdDot _root_.OAI.HigherDimensionalBallPacking.Rigidity.geometricHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.lineHomotopy_one _root_.OAI.HigherDimensionalBallPacking.Rigidity.lineHomotopy_zero _root_.OAI.HigherDimensionalBallPacking.Rigidity.normalizedPrimitive_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.realCurve_zero _root_.OAI.HigherDimensionalBallPacking.Rigidity.stdDot_J_right _root_.OAI.HigherDimensionalBallPacking.Rigidity.stdOmega_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
namespace HigherDimensionalBallPacking.Rigidity

theorem stdDot_symm {n : ℕ} (v w : Phase n) : stdDot n v w = stdDot n w v := by
  simp only [stdDot_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem stdDot_nonneg {n : ℕ} (v : Phase n) : 0 ≤ stdDot n v v := by
  by_cases hv : v = 0
  · subst v
    simp
  · exact (stdDot_pos hv).le

theorem standardForm_skew {n : ℕ} (v w : Phase n) :
    standardForm v w = -standardForm w v := by
  unfold standardForm
  rw [←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem compatible_metric_symm {n : ℕ} {J : End n} (hJ : Compatible J)
    (v w : Phase n) : standardForm v (J w) = standardForm w (J v) := by
  calc
    standardForm v (J w) = standardForm (J v) (J (J w)) := (hJ.2.1 v (J w)).symm
    _ = -standardForm (J v) w := by rw [hJ.1, standardForm_neg_right]
    _ = standardForm w (J v) := by rw [standardForm_skew, neg_neg]

theorem compatible_of_sq_symmetric_positive {n : ℕ} {J : End n}
    (hJsq : ∀ v, J (J v) = -v)
    (hsym : ∀ v w, standardForm v (J w) = standardForm w (J v))
    (hpos : ∀ v, v ≠ 0 → 0 < standardForm v (J v)) : Compatible J := by
  refine ⟨hJsq, ?_, hpos⟩
  intro v w
  rw [hsym, hJsq, standardForm_neg_right, standardForm_skew, neg_neg]

theorem relativeOperator_selfadjoint {n : ℕ} {J : End n} (hJ : Compatible J)
    (v w : Phase n) :
    stdDot n (relativeOperator J v) w = stdDot n v (relativeOperator J w) := by
  rw [stdDot_symm, stdDot_relativeOperator, stdDot_relativeOperator]
  exact compatible_metric_symm hJ w v

theorem cayleyP_commute {n : ℕ} (J : End n) (a b : ℝ) (v : Phase n) :
    cayleyP J b a (cayleyP J a b v) = cayleyP J a b (cayleyP J b a v) := by
  simp only [cayleyP_apply, map_add, map_smul]
  module

theorem cayleyP_J_identity {n : ℕ} {J : End n} (hJ : Compatible J)
    (a b : ℝ) (v : Phase n) :
    cayleyP J a b (standardJ n (cayleyP J a b v)) =
      cayleyP J b a (standardJ n (cayleyP J b a v)) := by
  simp only [cayleyP_apply, map_add, map_smul, relativeOperator_J_relativeOperator hJ]
  module

theorem cayleyP_stdDot_identity {n : ℕ} {J : End n} (hJ : Compatible J)
    (a b : ℝ) (v w : Phase n) :
    stdDot n (cayleyP J b a v) (cayleyP J a b w) =
      stdDot n (cayleyP J a b v) (cayleyP J b a w) := by
  simp only [cayleyP_apply, map_add, map_smul,
    add_apply, smul_apply, smul_eq_mul]
  rw [relativeOperator_selfadjoint hJ v w]
  ring

theorem cayleyP_stdDot_positive {n : ℕ} {J : End n} (hJ : Compatible J)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) {v : Phase n} (hv : v ≠ 0) :
    0 < stdDot n (cayleyP J b a v) (cayleyP J a b v) := by
  have he : stdDot n (cayleyP J b a v) (cayleyP J a b v) =
      a * b * (stdDot n (relativeOperator J v) (relativeOperator J v) + stdDot n v v) +
      (a ^ 2 + b ^ 2) * stdDot n v (relativeOperator J v) := by
    simp only [cayleyP_apply, map_add, map_smul,
      add_apply, smul_apply, smul_eq_mul]
    rw [relativeOperator_selfadjoint hJ v v]
    ring
  rw [he]
  have hfirst : 0 ≤ a * b *
      (stdDot n (relativeOperator J v) (relativeOperator J v) + stdDot n v v) :=
    mul_nonneg (mul_nonneg ha.le hb) (add_nonneg (stdDot_nonneg _) (stdDot_nonneg _))
  have hcoeff : 0 < a ^ 2 + b ^ 2 := by nlinarith [sq_pos_of_pos ha, sq_nonneg b]
  exact add_pos_of_nonneg_of_pos hfirst (mul_pos hcoeff (relativeOperator_positive hJ hv))

theorem denominator_cayleyOperator {n : ℕ} {J : End n} {a b : ℝ}
    (hQ : (cayleyP J b a).IsInvertible) (v : Phase n) :
    cayleyP J b a (cayleyOperator J a b v) = cayleyP J a b v := by
  change cayleyP J b a (cayleyP J a b ((cayleyP J b a).inverse v)) = _
  rw [cayleyP_commute]
  obtain ⟨e,he⟩ := hQ
  simp [←he]

theorem cayleyOperator_selfadjoint {n : ℕ} {J : End n} (hJ : Compatible J)
    {a b : ℝ} (hQ : (cayleyP J b a).IsInvertible) (v w : Phase n) :
    stdDot n (cayleyOperator J a b v) w = stdDot n v (cayleyOperator J a b w) := by
  obtain ⟨e,he⟩ := hQ
  obtain ⟨x,rfl⟩ := e.surjective v
  obtain ⟨y,rfl⟩ := e.surjective w
  change stdDot n (cayleyOperator J a b ((e : End n) x)) ((e : End n) y) =
    stdDot n ((e : End n) x) (cayleyOperator J a b ((e : End n) y))
  rw [he, cayleyOperator_on_denominator ⟨e,he⟩,
    cayleyOperator_on_denominator ⟨e,he⟩]
  exact (cayleyP_stdDot_identity hJ a b x y).symm

theorem cayleyOperator_positive {n : ℕ} {J : End n} (hJ : Compatible J)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) {v : Phase n} (hv : v ≠ 0) :
    0 < stdDot n v (cayleyOperator J a b v) := by
  obtain ⟨e,he⟩ := cayleyP_invertible hJ ha hb
  obtain ⟨x,rfl⟩ := e.surjective v
  have hx : x ≠ 0 := by simpa using hv
  change 0 < stdDot n ((e : End n) x) (cayleyOperator J a b ((e : End n) x))
  rw [he, cayleyOperator_on_denominator ⟨e,he⟩]
  exact cayleyP_stdDot_positive hJ ha hb hx

theorem cayleyOperator_J_identity {n : ℕ} {J : End n} (hJ : Compatible J)
    {a b : ℝ} (hQ : (cayleyP J b a).IsInvertible) (v : Phase n) :
    cayleyOperator J a b (standardJ n (cayleyOperator J a b v)) = standardJ n v := by
  obtain ⟨e,he⟩ := hQ
  obtain ⟨x,rfl⟩ := e.surjective v
  apply e.injective
  change (e : End n) (cayleyOperator J a b (standardJ n (cayleyOperator J a b ((e : End n) x)))) =
    (e : End n) (standardJ n ((e : End n) x))
  rw [he, denominator_cayleyOperator ⟨e,he⟩, cayleyOperator_on_denominator ⟨e,he⟩]
  exact cayleyP_J_identity hJ a b x

theorem compatible_interpolateJ {n : ℕ} {J : End n} (hJ : Compatible J)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : Compatible (interpolateJ J t) := by
  have ha : 0 < 1 + t := by linarith [ht.1]
  have hb : 0 ≤ 1 - t := by linarith [ht.2]
  have hQ := cayleyP_invertible hJ ha hb
  apply compatible_of_sq_symmetric_positive
  · intro v
    change standardJ n (cayleyOperator J (1+t) (1-t)
      (standardJ n (cayleyOperator J (1+t) (1-t) v))) = -v
    rw [cayleyOperator_J_identity hJ hQ, standardJ_sq]
  · intro v w
    change standardForm v (standardJ n (cayleyOperator J (1+t) (1-t) w)) =
      standardForm w (standardJ n (cayleyOperator J (1+t) (1-t) v))
    rw [standardForm_J_right, standardForm_J_right,
      ←cayleyOperator_selfadjoint hJ hQ, stdDot_symm]
  · intro v hv
    change 0 < standardForm v (standardJ n (cayleyOperator J (1+t) (1-t) v))
    rw [standardForm_J_right]
    exact cayleyOperator_positive hJ ha hb hv

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_Adapted
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter

theorem lineHomotopy_compatible {n : ℕ} {J : Phase n → End n}
    (hJ : ∀ x, Compatible (J x)) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (x : Phase n) :
    Compatible (lineHomotopy J t x) := compatible_interpolateJ (hJ x) ht


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory



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

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

variable {K : Set ℂ} (hK : IsCompact K)

local instance markedAffineInst1_r96e216_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance markedAffineInst2_r96e216_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance markedAffineInst3_r96e216_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance markedAffineInst4_r96e216_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance markedAffineInst5_r96e216_1 : NormedAddCommGroup (markedModel (E := E) K) := inferInstance
local instance markedAffineInst6_r96e216_1 : NormedSpace ℝ (markedModel (E := E) K) := inferInstance
local instance markedAffineInst7_r96e216_1 : NormedAddCommGroup (supportedHolder (E := E) K) := inferInstance
local instance markedAffineInst8_r96e216_1 : NormedSpace ℝ (supportedHolder (E := E) K) := inferInstance
omit [CompleteSpace E] in
lemma markedCurve_zero (p q : E) {u : COne ℂ E} (hu : cValue u 0 = 0) :
    markedCurve p q u 0 = p := by simp [markedCurve,hu]

omit [CompleteSpace E] in
lemma markedCurve_one (p q : E) (u : COne ℂ E) : markedCurve p q u 1 = q := by
  simp only [markedCurve,one_smul,markedSlope]
  abel

omit [CompleteSpace E] in
lemma markedCurve_standardResidual (p q : E) (u : COne ℂ E) (z : ℂ) :
    fderiv ℝ (markedCurve p q u) z Complex.I -
      Complex.I • fderiv ℝ (markedCurve p q u) z 1 = valueCLM _ (standardJetCR u) z := by
  rw [markedCurve_fderiv,standardJetCR_value]
  simp only [add_apply,complexSlope_apply,one_smul,smul_add]
  abel

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
local instance affineCutInst3_r96e216_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance affineCutInst4_r96e216_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
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
local instance markedChartInst13_r96e216_1 : NormedAddCommGroup (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance markedChartInst14_r96e216_1 : NormedSpace ℝ (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
omit [CompleteSpace E] in
@[simp] lemma markedDX_value [CompleteSpace E] (p q : E) (u h : COne ℂ E) (z : ℂ) :
    valueCLM _ (markedDX p q u h) z = fderiv ℝ (markedCurve p q (u+h)) z 1 := by
  rw [markedCurve_fderiv,markedSlope_add]
  simp only [add_apply,complexSlope_apply,one_smul]
  rfl

variable {P : E → E →L[ℝ] E} (hP : BoundedCThree P) (b : ContDiffBump (0:ℂ))

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



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_TranslationContinuity
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
open Set Function Filter
section

lemma realCR_axis_implies_all {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] E) (hA : ∀ v, A (A v) = -v) (L : ℂ →L[ℝ] E)
    (hL : L Complex.I = A (L 1)) (w : ℂ) : L (Complex.I*w) = A (L w) := by
  have hw : w = w.re • (1:ℂ)+w.im • Complex.I := by
    apply Complex.ext <;> simp [Complex.real_smul]
  have hIw : Complex.I*w = (-w.im) • (1:ℂ)+w.re • Complex.I := by
    apply Complex.ext <;> simp [Complex.real_smul,Complex.mul_re,Complex.mul_im]
  calc
    L (Complex.I*w) = (-w.im) • L 1 + w.re • L Complex.I := by
      rw [hIw,map_add,map_smul,map_smul]
    _ = A (w.re • L 1+w.im • L Complex.I) := by
      rw [map_add,map_smul,map_smul,hL,hA]
      module
    _ = A (L w) := congrArg A (by simpa only [map_add,map_smul] using (congrArg L hw).symm)

end

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
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

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter

variable {n : ℕ}

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.ghInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.ghInst2
variable {J : Phase n → End n} (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x))

lemma fullCoefficient_outside {B : ℝ} (hstd : ∀ x, B<‖x‖ → J x=standardJ n) :
    ∀ t x, B<‖x‖ → fullCoefficient J (t,x)=0 := by
  intro t x hx
  simp only [fullCoefficient,hstd x hx,interpolateJ_standard_initial
    ⟨lt_of_lt_of_le (by norm_num) (fullTime_range _).1,(fullTime_range _).2⟩,sub_self,smul_zero]

lemma fullCoefficient_exact {t : ℝ} (ht : t∈Icc (0:ℝ) 1) (x : Phase n) :
    standardJ n+fullCoefficient J (t,x)=lineHomotopy J (fullTime t) x := by
  have hb : t∈Metric.closedBall (0:ℝ) fullTimeBump.rIn := by
    rw [Metric.mem_closedBall,dist_zero_right,Real.norm_eq_abs,abs_of_nonneg ht.1]
    exact ht.2.trans (by norm_num [fullTimeBump])
  rw [fullCoefficient,fullTimeBump.one_of_mem_closedBall hb,one_smul]
  change standardJ n+(interpolateJ (J x) (fullTime t)-standardJ n)=_
  abel

end HigherDimensionalBallPacking.Rigidity

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.cmn1
local instance cmn2_r96e216_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
omit [CompleteSpace E] in
lemma markedBoundedDomain_slope [CompleteSpace E] {p q : E} {M δ : ℝ} (hδ : 0<δ)
    {w : COne ℂ E} (hw : w∈markedBoundedDomain p q M δ) : markedSlope p q w≠0 :=
  norm_pos_iff.mp (hδ.trans hw.2)

omit [CompleteSpace E] in
lemma marked_escape_neighborhood_base [CompleteSpace E] (b : ContDiffBump (0:ℂ)) (p q : E)
    {w : COne ℂ E} {B : ℝ} (he : MarkedEscapeNeighborhood b p q w B) :
    ∀ z,b.rIn≤‖z‖ →B<‖markedCurve p q w z‖ := by
  intro z hz
  have hh := (he.self_of_nhds z hz).1
  simpa only [Submodule.coe_zero,add_zero] using hh

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable (b₁ : ContDiffBump (0:ℂ)) (p q : E)

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmc1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmc2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmc3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmc4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmc5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmc6
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmc7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmc8
omit [CompleteSpace E] in
lemma globalMarkedJet_value [CompleteSpace E] (w : COne ℂ E) (z : ℂ) :
    cValue (globalMarkedJet b₁ p q w) z=p+b₁ z • (z • markedSlope p q w)+cValue w z := by
  change p+cValue (cutoffSlope b₁ (markedSlope p q w)) z+cValue w z=_
  rw [cutoffSlope_value]

lemma globalMarkedJet_eq_marked (w : COne ℂ E) {z : ℂ}
    (hz : z∈Metric.closedBall (0:ℂ) b₁.rIn) :
    cValue (globalMarkedJet b₁ p q w) z=markedCurve p q w z := by
  rw [globalMarkedJet_value,b₁.one_of_mem_closedBall hz,one_smul]
  rfl

omit [CompleteSpace E] in
lemma globalParameterJet_value [CompleteSpace E] (v : ℝ × COne ℂ E) (z : ℂ) :
    cValue (globalParameterJet b₁ p q v) z=(v.1,cValue (globalMarkedJet b₁ p q v.2) z) := by
  change (v.1,0)+(0,cValue (globalMarkedJet b₁ p q v.2) z)=_
  simp only [Prod.mk_add_mk,zero_add,add_zero]

variable {P : ℝ × E → E →L[ℝ] E} (hP : BoundedCThree P)

lemma globalCoefficient_value (v : ℝ × COne ℂ E) (z : ℂ) :
    valueCLM _ (globalCoefficient b₁ p q hP v) z=P (v.1,cValue (globalMarkedJet b₁ p q v.2) z) := by
  change P (0+cValue (globalParameterJet b₁ p q v) z)=_
  rw [zero_add,globalParameterJet_value]

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
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

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology
open Filter
open scoped BoundedContinuousFunction
open Set Function
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable (b b₁ : ContDiffBump (0:ℂ)) (p q : E)
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst6
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst8
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst9
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst10
local instance gmChartInst11_r96e216_1 : AddCommGroup (markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := (gmChartInst9 b).toAddCommGroup
local instance gmChartInst12_r96e216_1 : Module ℝ (markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := (gmChartInst10 b).toModule
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst13
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst14
local instance gmChartInst15_r96e216_1 : AddCommGroup (supportedHolder (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := (gmChartInst13 b).toAddCommGroup
local instance gmChartInst16_r96e216_1 : Module ℝ (supportedHolder (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := (gmChartInst14 b).toModule
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst17
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst18
local instance gmChartInst19_r96e216_1 : AddCommGroup (ℝ × markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := (gmChartInst17 b).toAddCommGroup
local instance gmChartInst20_r96e216_1 : Module ℝ (ℝ × markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := (gmChartInst18 b).toModule
variable {P : ℝ × E → E →L[ℝ] E} (hP : BoundedCThree P)

lemma globalChart_value (t : ℝ) (w : markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) (z : ℂ) :
    valueCLM _ (globalChart b b₁ p q hP (t,w)).val z=valueCLM _ (standardJetCR w.val) z-
      b z • P (t,cValue (globalMarkedJet b₁ p q w.val) z) (fderiv ℝ (markedCurve p q w.val) z 1) := by
  change valueCLM _ (standardJetCR w.val) z-b z • valueCLM _ (globalNonlinearity b b₁ p q hP (t,w)) z=_
  simp only [globalNonlinearity,bilinCLM_value,globalCoefficient_value,markedDX_value,zero_add]
  rfl

lemma globalChart_actual_value
    (hb₁ : Metric.closedBall (0:ℂ) b.rOut⊆Metric.closedBall (0:ℂ) b₁.rIn)
    {B : ℝ} (hPB : ∀ t x,B<‖x‖ → P (t,x)=0) (t : ℝ)
    (w : markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut))
    (he : ∀ z,b.rIn≤‖z‖ → B<‖markedCurve p q w.val z‖) (z : ℂ) :
    valueCLM _ (globalChart b b₁ p q hP (t,w)).val z=
      fderiv ℝ (markedCurve p q w.val) z Complex.I-
        (Complex.I • fderiv ℝ (markedCurve p q w.val) z 1+
          P (t,markedCurve p q w.val z) (fderiv ℝ (markedCurve p q w.val) z 1)) := by
  have hz0 : z∉Metric.closedBall (0:ℂ) b.rIn → P (t,markedCurve p q w.val z)=0 := by
    intro hz
    apply hPB
    apply he
    exact (lt_of_not_ge (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz)).le
  have hN : b z • P (t,cValue (globalMarkedJet b₁ p q w.val) z)
      (fderiv ℝ (markedCurve p q w.val) z 1)=
      P (t,markedCurve p q w.val z) (fderiv ℝ (markedCurve p q w.val) z 1) := by
    by_cases hz : z∈Metric.closedBall (0:ℂ) b.rOut
    · apply cutoff_action_eq b _ hz0
      rw [globalMarkedJet_eq_marked b₁ p q w.val (hb₁ hz)]
    · have hb0 : b z=0 := image_eq_zero_of_notMem_tsupport (by rwa [b.tsupport_eq])
      have hz' : z∉Metric.closedBall (0:ℂ) b.rIn :=
        fun h => hz (Metric.closedBall_subset_closedBall b.rIn_lt_rOut.le h)
      rw [hb0,hz0 hz',zero_apply,zero_smul]
  have hS := markedCurve_standardResidual p q w.val z
  calc
    _ = valueCLM _ (standardJetCR w.val) z-b z •
        P (t,cValue (globalMarkedJet b₁ p q w.val) z) (fderiv ℝ (markedCurve p q w.val) z 1) :=
      globalChart_value b b₁ p q hP t w z
    _ = (fderiv ℝ (markedCurve p q w.val) z Complex.I-
        Complex.I • fderiv ℝ (markedCurve p q w.val) z 1)-
        P (t,markedCurve p q w.val z) (fderiv ℝ (markedCurve p q w.val) z 1) :=
      congrArg₂ (· - ·) hS.symm hN
    _ = _ := sub_sub _ _ _

end
section
variable {n : ℕ}
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gle1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gle2
local instance gle3_r96e216_1 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance gle4_r96e216_1 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance gle5_r96e216_1 : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance
local instance gle6_r96e216_1 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
variable {J : Phase n → End n} (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
  (hJc : HasCompactSupport (fun x => J x-standardJ n))
variable (b b₁ : ContDiffBump (0:ℂ)) (p q : Phase n)

variable (hb₁ : Metric.closedBall (0:ℂ) b.rOut⊆Metric.closedBall (0:ℂ) b₁.rIn)
  {B : ℝ} (hstd : ∀ x,B<‖x‖ → J x=standardJ n)
  {t : ℝ} (ht : t∈Icc (0:ℝ) 1)
  (w : markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut))
  (he : ∀ z,b.rIn≤‖z‖ → B<‖markedCurve p q w.val z‖)

local instance gle7_r96e216_1 : NormedAddCommGroup (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gle8_r96e216_1 : NormedSpace ℝ (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gle9_r96e216_1 : NormedAddCommGroup (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gle10_r96e216_1 : NormedSpace ℝ (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
include hb₁ hstd ht he in
lemma fullLineEquation_value (z : ℂ) :
    valueCLM _ (fullLineEquation hJs hJ hJc b b₁ p q (t,w)).val z=
      fderiv ℝ (markedCurve p q w.val) z Complex.I-
        lineHomotopy J (fullTime t) (markedCurve p q w.val z)
          (fderiv ℝ (markedCurve p q w.val) z 1) := by
  have hx := globalChart_actual_value b b₁ p q (fullCoefficientBound hJs hJ hJc)
    hb₁ (fullCoefficient_outside hstd) t w he z
  have hc := congrArg (fun A : End n => A (fderiv ℝ (markedCurve p q w.val) z 1))
    (fullCoefficient_exact (J := J) ht (markedCurve p q w.val z))
  change Complex.I • fderiv ℝ (markedCurve p q w.val) z 1+
    fullCoefficient J (t,markedCurve p q w.val z) (fderiv ℝ (markedCurve p q w.val) z 1)=_ at hc
  exact hx.trans (congrArg (fun v : Phase n => fderiv ℝ (markedCurve p q w.val) z Complex.I-v) hc)

include hb₁ hstd ht he in
lemma fullLineEquation_zero_iff
    (ha : markedSlope p q w.val≠0) :
    fullLineEquation hJs hJ hJc b b₁ p q (t,w)=0 ↔
      AffineLineCurve (lineHomotopy J (fullTime t)) p q (markedCurve p q w.val) := by
  have hc := lineHomotopy_compatible hJ (fullTime_range t)
  have hs := lineHomotopy_slice_contDiff hJs hJ (fullTime_range t)
  have hstd' : ∀ x,B<‖x‖ → lineHomotopy J (fullTime t) x=standardJ n := by
    intro x hx
    change interpolateJ (J x) (fullTime t)=standardJ n
    rw [hstd x hx]
    exact interpolateJ_standard_initial
      ⟨lt_of_lt_of_le (by norm_num) (fullTime_range t).1,(fullTime_range t).2⟩
  constructor
  · intro hz
    have hcr (z : ℂ) : fderiv ℝ (markedCurve p q w.val) z Complex.I=
        lineHomotopy J (fullTime t) (markedCurve p q w.val z)
          (fderiv ℝ (markedCurve p q w.val) z 1) := by
      have hv := fullLineEquation_value hJs hJ hJc b b₁ p q hb₁ hstd ht w he z
      have hzero : valueCLM _ (fullLineEquation hJs hJ hJc b b₁ p q (t,w)).val z=0 := by
        rw [hz]; rfl
      exact sub_eq_zero.mp (hv.symm.trans hzero)
    refine ⟨completed_markedCurve_contDiff_bp240 hs hc hstd' p q w.val ha hcr,?_,
      markedCurve_zero p q w.property.1,markedCurve_one p q w.val,
      markedSlope p q w.val,ha,markedCurve_asymptote p q w.val⟩
    intro z
    exact ⟨(markedCurve_hasFDerivAt p q w.val z).differentiableAt,
      realCR_axis_implies_all _ (hc _).1 _ (hcr z)⟩
  · intro hu
    apply Subtype.ext
    apply value_ext
    intro z
    have hv := fullLineEquation_value hJs hJ hJc b b₁ p q hb₁ hstd ht w he z
    have hcr := (hu.2.1 z).2 1
    simp only [mul_one] at hcr
    exact hv.trans (sub_eq_zero.mpr hcr)

end

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
open HolderCompletion
section

variable {n : ℕ}

variable (b : ContDiffBump (0:ℂ))

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.lcdEnd1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.lcdEnd2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.lcd1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.lcd2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.lcd3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.lcd4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.lcd5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.lcd6
local instance lcd7_r96e216_1 : AddCommGroup (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (lcd3 (n := n) b).toAddCommGroup
local instance lcd8_r96e216_1 : Module ℝ (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (lcd4 (n := n) b).toModule
local instance lcd9_r96e216_1 : AddCommGroup (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (lcd5 (n := n) b).toAddCommGroup
local instance lcd10_r96e216_1 : Module ℝ (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (lcd6 (n := n) b).toModule
local instance lcd11_r96e216_1 : NormedAddCommGroup (ℝ × markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance lcd12_r96e216_1 : NormedSpace ℝ (ℝ × markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
variable {J : Phase n → End n} (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
  (hJc : HasCompactSupport (fun x => J x-standardJ n)) (b₁ : ContDiffBump (0:ℂ)) (p q : Phase n)
  (hb₁ : Metric.closedBall (0:ℂ) b.rOut⊆Metric.closedBall (0:ℂ) b₁.rIn)
  {B M δ : ℝ} (hstd : ∀ x,B<‖x‖ →J x=standardJ n) (hδ : 0<δ)
  (he : ∀ w∈markedBoundedDomain p q M δ,MarkedEscapeNeighborhood b p q w B)

include hb₁ hstd hδ he in
lemma fullLineEndpointMap_bp240_oai : ∀ w∈fullLineDomain b p q M δ,
    fullLineEquation hJs hJ hJc b b₁ p q (1,w)=0 →
      AffineLineCurve J p q (markedCurve p q w.val) := by
  intro w hw hz
  have hesc := marked_escape_neighborhood_base b p q (he w.val hw)
  have hl := (fullLineEquation_zero_iff hJs hJ hJc b b₁ p q hb₁ hstd (t := 1)
    (by constructor <;> norm_num) w hesc (markedBoundedDomain_slope hδ hw)).mp hz
  have ht : lineHomotopy J (fullTime 1)=J := by
    funext x
    rw [fullTime_one,lineHomotopy_one hJ]
  rwa [ht] at hl

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.fullLineEndpointMap_bp240_oai := @OAI.HigherDimensionalBallPacking.Rigidity.fullLineEndpointMap_bp240_oai
