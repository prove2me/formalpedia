-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.completed_line_closed_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:55:24.545419+00:00
-- url     : https://prove2.me/submissions/ee30ee37-b96c-474d-b873-08be93f740d9

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp021
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_completed_markedCurve_contDiff_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_exact_normalized_line_energy_bp240

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

theorem lineHomotopy_support {n : ℕ} (J : Phase n → End n)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    tsupport (fun x => lineHomotopy J t x - standardJ n) ⊆
      tsupport (fun x => J x - standardJ n) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  by_contra hn
  have hzero := image_eq_zero_of_notMem_tsupport hn
  have hJx : J x = standardJ n := sub_eq_zero.mp hzero
  apply hx
  change interpolateJ (J x) t - standardJ n = 0
  rw [hJx,interpolateJ_standard ht,sub_self]

theorem lineHomotopy_compact {n : ℕ} {J : Phase n → End n}
    (hJc : HasCompactSupport (fun x => J x - standardJ n))
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    HasCompactSupport (fun x => lineHomotopy J t x - standardJ n) :=
  hJc.of_isClosed_subset (isClosed_tsupport _) (lineHomotopy_support J ht)


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_RadialForm
attribute [-instance] _root_.OAI.HigherDimensionalBallPacking.Rigidity.squareMeasure_finite _root_.OAI.HigherDimensionalBallPacking.Rigidity.translatedSquare_finite _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SymplecticBallPacking.Hamiltonian
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

theorem HasCompactSupport.comp_radiusSq {F : Type*} [Zero F] {g : ℝ → F}
    (hg : HasCompactSupport g) : HasCompactSupport (fun z : Plane => g (radiusSq z)) := by
  obtain ⟨B,hB,hbound⟩ := hg.isBounded.exists_pos_norm_le
  apply HasCompactSupport.intro ((isCompact_Icc : IsCompact (Icc (-(B+1)) (B+1))).prod (isCompact_Icc : IsCompact (Icc (-(B+1)) (B+1))))
  intro z hz
  by_contra hg0
  have hb := hbound (radiusSq z) (subset_tsupport g hg0)
  have hq : 0 ≤ radiusSq z := add_nonneg (sq_nonneg _) (sq_nonneg _)
  rw [Real.norm_eq_abs,abs_of_nonneg hq] at hb
  apply hz
  dsimp only [radiusSq] at hb
  constructor <;> constructor <;> nlinarith [sq_nonneg z.1,sq_nonneg z.2]

end SymplecticBallPacking.Hamiltonian
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

local instance markedAffineInst1_r62dbe7_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance markedAffineInst2_r62dbe7_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance markedAffineInst3_r62dbe7_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance markedAffineInst4_r62dbe7_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance markedAffineInst5_r62dbe7_1 : NormedAddCommGroup (markedModel (E := E) K) := inferInstance
local instance markedAffineInst6_r62dbe7_1 : NormedSpace ℝ (markedModel (E := E) K) := inferInstance
local instance markedAffineInst7_r62dbe7_1 : NormedAddCommGroup (supportedHolder (E := E) K) := inferInstance
local instance markedAffineInst8_r62dbe7_1 : NormedSpace ℝ (supportedHolder (E := E) K) := inferInstance
omit [CompleteSpace E] in
lemma markedCurve_zero (p q : E) {u : COne ℂ E} (hu : cValue u 0 = 0) :
    markedCurve p q u 0 = p := by simp [markedCurve,hu]

omit [CompleteSpace E] in
lemma markedCurve_one (p q : E) (u : COne ℂ E) : markedCurve p q u 1 = q := by
  simp only [markedCurve,one_smul,markedSlope]
  abel

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
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_CurveArea
attribute [-instance] _root_.OAI.HigherDimensionalBallPacking.Rigidity.squareMeasure_finite _root_.OAI.HigherDimensionalBallPacking.Rigidity.translatedSquare_finite _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)

theorem realCurve_smooth {n : ℕ} {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (realCurve u) := hu.comp Complex.equivRealProdCLM.symm.contDiff


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_Correction
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
open SymplecticBallPacking.Hamiltonian

theorem outerProfile_smooth (A : ℝ) : ContDiff ℝ ∞ (outerProfile A) :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).mul
    (contDiff_const.sub (Real.smoothTransition.contDiff.comp
      ((contDiff_id.sub contDiff_const).div_const A)))

theorem outerProfile_compact {A : ℝ} (hA : 0 < A) : HasCompactSupport (outerProfile A) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (-2:ℝ)) (b := 2*A))
  intro t ht
  have ht' : t < -2 ∨ 2*A < t := by simpa only [mem_Icc,not_and_or,not_le] using ht
  rcases ht' with ht' | ht'
  · simp only [outerProfile,Real.smoothTransition.zero_of_nonpos (by linarith : t+2 ≤ 0),zero_mul]
  · have h : 1 ≤ (t-A)/A := (le_div_iff₀ hA).mpr (by linarith)
    simp only [outerProfile,Real.smoothTransition.one_of_one_le h,sub_self,mul_zero]

theorem outerProfile_nonneg (A t : ℝ) : 0 ≤ outerProfile A t :=
  mul_nonneg (Real.smoothTransition.nonneg _) (sub_nonneg.mpr (Real.smoothTransition.le_one _))



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Compactness_AffineCorrectionInfinity
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity

lemma outerProfile_one_before {A t : ℝ} (ht : 0≤t) (htA : t≤A) (hA : 0<A) :
    outerProfile A t=1 := by
  have h1 : 1≤t+2 := by linarith
  have h2 : (t-A)/A≤0 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr htA) hA.le
  simp only [outerProfile,Real.smoothTransition.one_of_one_le h1,
    Real.smoothTransition.zero_of_nonpos h2,sub_zero,mul_one]

end HigherDimensionalBallPacking.Rigidity

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
-- module Solutions.OAIQ240_BP.BallPacking_Energy_ResidualEnergy
attribute [-instance] _root_.OAI.HigherDimensionalBallPacking.Rigidity.squareMeasure_finite _root_.OAI.HigherDimensionalBallPacking.Rigidity.translatedSquare_finite _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frozenTargetCoefficient_zero _root_.OAI.HigherDimensionalBallPacking.Rigidity.geometricHolder_value _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

lemma sourceRadialCutoff_smooth (A : ℝ) : ContDiff ℝ ∞ (sourceRadialCutoff A) :=
  (outerProfile_smooth A).comp radiusSq_smooth

lemma sourceRadialCutoff_compact {A : ℝ} (hA : 0<A) : HasCompactSupport (sourceRadialCutoff A) :=
  HasCompactSupport.comp_radiusSq (outerProfile_compact hA)

lemma sourceRadialCutoff_nonneg (A : ℝ) (z : Plane) : 0 ≤ sourceRadialCutoff A z :=
  outerProfile_nonneg A _

lemma smooth_cutoff_integrable_mul {A : ℝ} (hA : 0<A) {e : Plane → ℝ} (he : Continuous e) :
    Integrable (fun z => sourceRadialCutoff A z*e z) :=
  ((sourceRadialCutoff_smooth A).continuous.mul he).integrable_of_hasCompactSupport
    ((sourceRadialCutoff_compact hA).mul_right)


end
section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
open HolderCompletion
variable {n : ℕ}

lemma dirichletEnergy_nonneg (v : ℂ → Phase n) (z : Plane) : 0≤dirichletEnergy v z :=
  add_nonneg (stdDot_nonneg _) (stdDot_nonneg _)

lemma dirichletEnergy_continuous {v : ℂ → Phase n} (hv : ContDiff ℝ ∞ v) :
    Continuous (dirichletEnergy v) := by
  have hd := ((realCurve_smooth hv).fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuous
  have hx := hd.clm_apply (continuous_const (y := ((1,0):Plane)))
  have hy := hd.clm_apply (continuous_const (y := ((0,1):Plane)))
  exact (((stdDot n).continuous.comp hx).clm_apply hx).add (((stdDot n).continuous.comp hy).clm_apply hy)


end
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
variable {n : ℕ}

lemma stdDot_sub_self (x y : Phase n) :
    stdDot n (x-y) (x-y)=stdDot n x x-2*stdDot n x y+stdDot n y y := by
  simp only [map_sub,sub_apply]
  rw [stdDot_symm y x]
  ring

lemma interval_integral_stdDot_const {f : ℝ → Phase n} (hf : Continuous f) (a b : ℝ) (v : Phase n) :
    (∫ t in a..b, stdDot n (f t) v)=stdDot n (∫ t in a..b, f t) v :=
  ((stdDot n).flip v).intervalIntegral_comp_comm (hf.intervalIntegrable a b)

lemma interval_stdDot_variance {f : ℝ → Phase n} (hf : Continuous f) (a b : ℝ) (v : Phase n) :
    (∫ t in a..b, stdDot n (f t-v) (f t-v))=
      (∫ t in a..b, stdDot n (f t) (f t))-2*stdDot n (∫ t in a..b, f t) v+
        (b-a)*stdDot n v v := by
  have he : Continuous (fun t => stdDot n (f t) (f t)) := ((stdDot n).continuous.comp hf).clm_apply hf
  have hv : Continuous (fun t => 2*stdDot n (f t) v) := continuous_const.mul
    (((stdDot n).continuous.comp hf).clm_apply continuous_const)
  simp_rw [stdDot_sub_self]
  have hei : IntervalIntegrable (fun t => stdDot n (f t) (f t)-2*stdDot n (f t) v) volume a b :=
    (he.sub hv).intervalIntegrable a b
  rw [intervalIntegral.integral_add hei intervalIntegrable_const,
    intervalIntegral.integral_sub (he.intervalIntegrable a b) (hv.intervalIntegrable a b),
    intervalIntegral.integral_const_mul,interval_integral_stdDot_const hf,
    intervalIntegral.integral_const,smul_eq_mul]

lemma interval_stdDot_integral_sq_le {f : ℝ → Phase n} (hf : Continuous f) {a b : ℝ} (hab : a≤b) :
    stdDot n (∫ t in a..b, f t) (∫ t in a..b, f t)≤(b-a)*(∫ t in a..b, stdDot n (f t) (f t)) := by
  rcases eq_or_lt_of_le hab with heq | hab'
  · subst b
    simp only [intervalIntegral.integral_same,sub_self,zero_mul,map_zero,le_refl]
  have hL : 0<b-a := sub_pos.mpr hab'
  let v : Phase n := (b-a)⁻¹ • (∫ t in a..b, f t)
  have hv := intervalIntegral.integral_nonneg_of_forall (μ := volume) hab (fun t => stdDot_nonneg (f t-v))
  rw [interval_stdDot_variance hf] at hv
  have hm := mul_nonneg hL.le hv
  have hid : (b-a)*((∫ t in a..b, stdDot n (f t) (f t))-
      2*stdDot n (∫ t in a..b, f t) v+(b-a)*stdDot n v v)=
      (b-a)*(∫ t in a..b, stdDot n (f t) (f t))-
        stdDot n (∫ t in a..b, f t) (∫ t in a..b, f t) := by
    dsimp only [v]
    simp only [map_smul,smul_apply,smul_eq_mul]
    field_simp
    ring
  rw [hid] at hm
  linarith

lemma curve_chord_energy_le {v : ℝ → Phase n} (hv : ContDiff ℝ ∞ v) {a b t : ℝ}
    (hat : a≤t) (htb : t≤b) :
    stdDot n (v t-v a) (v t-v a)≤(b-a)*(∫ s in a..b, stdDot n (deriv v s) (deriv v s)) := by
  have hd : Continuous (deriv v) := hv.continuous_deriv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hf : (∫ s in a..t, deriv v s)=v t-v a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => (hv.differentiable (by simp) s).hasDerivAt)
      (hd.intervalIntegrable a t)
  have hj := interval_stdDot_integral_sq_le hd hat
  rw [hf] at hj
  have hec : Continuous (fun s => stdDot n (deriv v s) (deriv v s)) :=
    ((stdDot n).continuous.comp hd).clm_apply hd
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (hec.intervalIntegrable a t)
    (hec.intervalIntegrable t b)
  have h1 := intervalIntegral.integral_nonneg_of_forall (μ := volume) hat (fun s => stdDot_nonneg (deriv v s))
  have h2 := intervalIntegral.integral_nonneg_of_forall (μ := volume) htb (fun s => stdDot_nonneg (deriv v s))
  nlinarith



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Energy_CircularEnergy
attribute [-instance] _root_.OAI.HigherDimensionalBallPacking.Rigidity.squareMeasure_finite _root_.OAI.HigherDimensionalBallPacking.Rigidity.translatedSquare_finite _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
variable {n : ℕ}

lemma centeredCurve_smooth {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (c : ℂ) :
    ContDiff ℝ ∞ (centeredCurve u c) := hu.comp (contDiff_id.add contDiff_const)

lemma realCurve_centered (u : ℂ → Phase n) (c : ℂ) :
    realCurve (centeredCurve u c)=fun z => realCurve u (z+Complex.equivRealProdCLM c) := by
  funext z
  simp only [realCurve,centeredCurve,Function.comp_def,map_add,ContinuousLinearEquiv.symm_apply_apply]

lemma stdDot_add_self_le (v w : Phase n) :
    stdDot n (v+w) (v+w)≤2*stdDot n v v+2*stdDot n w w := by
  have hh := stdDot_nonneg (v-w)
  rw [stdDot_sub_self] at hh
  simp only [map_add,add_apply]
  rw [stdDot_symm w v]
  linarith



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Campanato_MeasureEnergy
attribute [-instance] _root_.OAI.HigherDimensionalBallPacking.Rigidity.translatedSquare_finite _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.FiniteMoment.Radial.instInhabitedQuadrant _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frozenTargetCoefficient_zero _root_.OAI.HigherDimensionalBallPacking.Rigidity.geometricHolder_value _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
variable {n : ℕ} {X : Type*} [MeasurableSpace X]

lemma integral_stdDot_variance {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → Phase n} (hf : Integrable f μ)
    (he : Integrable (fun x => stdDot n (f x) (f x)) μ) (v : Phase n) :
    (∫ x, stdDot n (f x-v) (f x-v) ∂μ)=
      (∫ x, stdDot n (f x) (f x) ∂μ)-2*stdDot n (∫ x,f x ∂μ) v+
        μ.real univ*stdDot n v v := by
  have hi : Integrable (fun x => 2*stdDot n (f x) v) μ :=
    (((stdDot n).flip v).integrable_comp hf).const_mul 2
  have hsub : Integrable (fun x => stdDot n (f x) (f x)-2*stdDot n (f x) v) μ := he.sub hi
  have hint : (∫ x,stdDot n (f x) v ∂μ)=stdDot n (∫ x,f x ∂μ) v :=
    ((stdDot n).flip v).integral_comp_comm hf
  simp_rw [stdDot_sub_self]
  rw [integral_add hsub (integrable_const _),integral_sub he hi,integral_const_mul,
    hint,integral_const,smul_eq_mul]

lemma stdDot_integral_sq_le {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → Phase n} (hf : Integrable f μ)
    (he : Integrable (fun x => stdDot n (f x) (f x)) μ) (hμ : 0<μ.real univ) :
    stdDot n (∫ x,f x ∂μ) (∫ x,f x ∂μ)≤μ.real univ*(∫ x,stdDot n (f x) (f x) ∂μ) := by
  let v : Phase n := (μ.real univ)⁻¹ • (∫ x,f x ∂μ)
  have hn : 0≤(∫ x,stdDot n (f x-v) (f x-v) ∂μ) :=
    integral_nonneg (fun x => stdDot_nonneg (f x-v))
  rw [integral_stdDot_variance hf he] at hn
  have hm := mul_nonneg hμ.le hn
  have hid : μ.real univ*((∫ x,stdDot n (f x) (f x) ∂μ)-
      2*stdDot n (∫ x,f x ∂μ) v+μ.real univ*stdDot n v v)=
      μ.real univ*(∫ x,stdDot n (f x) (f x) ∂μ)-stdDot n (∫ x,f x ∂μ) (∫ x,f x ∂μ) := by
    dsimp only [v]
    simp only [map_smul,smul_apply,smul_eq_mul]
    field_simp
    ring
  rw [hid] at hm
  linarith

lemma stdDot_average_sq_le {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → Phase n} (hf : Integrable f μ)
    (he : Integrable (fun x => stdDot n (f x) (f x)) μ) (hμ : 0<μ.real univ) :
    stdDot n ((μ.real univ)⁻¹ • (∫ x,f x ∂μ)) ((μ.real univ)⁻¹ • (∫ x,f x ∂μ))≤
      (μ.real univ)⁻¹*(∫ x,stdDot n (f x) (f x) ∂μ) := by
  have hh := mul_le_mul_of_nonneg_left (stdDot_integral_sq_le hf he hμ) (sq_nonneg ((μ.real univ)⁻¹))
  simp only [map_smul,smul_apply,smul_eq_mul]
  have hid : ((μ.real univ)⁻¹)^2*(μ.real univ*(∫ x,stdDot n (f x) (f x) ∂μ))=
      (μ.real univ)⁻¹*(∫ x,stdDot n (f x) (f x) ∂μ) := by field_simp
  rw [hid] at hh
  nlinarith only [hh]

lemma norm_sq_le_stdDot (v : Phase n) : ‖v‖^2≤ stdDot n v v := by
  have hroot : ‖v‖≤Real.sqrt (stdDot n v v) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    apply (Real.le_sqrt (norm_nonneg _) (stdDot_nonneg v)).mpr
    have hle : (v i).re*(v i).re+(v i).im*(v i).im≤ stdDot n v v := by
      rw [stdDot_apply]
      exact Finset.single_le_sum (f := fun j : Fin n => (v j).re*(v j).re+(v j).im*(v j).im)
        (fun j _ => add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)) (Finset.mem_univ i)
    rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply]
    exact hle
  nlinarith [Real.sq_sqrt (stdDot_nonneg v),norm_nonneg v,Real.sqrt_nonneg (stdDot n v v)]


end
section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
variable {n : ℕ} {X : Type*} [MeasurableSpace X]

lemma integrable_stdDot_const_sub {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → Phase n} (hf : Integrable f μ)
    (he : Integrable (fun x => stdDot n (f x) (f x)) μ) (v : Phase n) :
    Integrable (fun x => stdDot n (v-f x) (v-f x)) μ := by
  have hvf : Integrable (fun x => 2*stdDot n v (f x)) μ :=
    (((stdDot n) v).integrable_comp hf).const_mul 2
  have hi : Integrable (fun x => stdDot n v v-2*stdDot n v (f x)+stdDot n (f x) (f x)) μ :=
    ((integrable_const _).sub hvf).add he
  simpa only [stdDot_sub_self] using hi

lemma phaseAverage_const_sub {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → Phase n} (hf : Integrable f μ) (hμ : 0<μ.real univ) (v : Phase n) :
    phaseAverage μ (fun x => v-f x)=v-phaseAverage μ f := by
  rw [phaseAverage,integral_sub (integrable_const _) hf,integral_const,smul_sub,inv_smul_smul₀ hμ.ne']
  rfl

lemma phaseAverage_deviation_energy_le {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → Phase n} (hf : Integrable f μ)
    (he : Integrable (fun x => stdDot n (f x) (f x)) μ) (hμ : 0<μ.real univ) (v : Phase n) :
    stdDot n (v-phaseAverage μ f) (v-phaseAverage μ f)≤
      (μ.real univ)⁻¹*(∫ x,stdDot n (v-f x) (v-f x) ∂μ) := by
  have hh := stdDot_average_sq_le ((integrable_const v).sub hf) (integrable_stdDot_const_sub hf he v) hμ
  change stdDot n (phaseAverage μ (fun x => v-f x)) (phaseAverage μ (fun x => v-f x))≤_ at hh
  rw [phaseAverage_const_sub hf hμ v] at hh
  exact hh


end
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
variable {n : ℕ}

lemma stdDot_sub_self_le (v w : Phase n) :
    stdDot n (v-w) (v-w)≤2*stdDot n v v+2*stdDot n w w := by
  simpa only [map_neg,neg_apply,neg_neg,sub_eq_add_neg] using stdDot_add_self_le v (-w)

lemma curve_pair_energy_le {v : ℝ → Phase n} (hv : ContDiff ℝ ∞ v) {a b s t : ℝ}
    (hs : s∈Icc a b) (ht : t∈Icc a b) :
    stdDot n (v s-v t) (v s-v t)≤4*(b-a)*
      (∫ r in a..b,stdDot n (deriv v r) (deriv v r)) := by
  have h1 := curve_chord_energy_le hv hs.1 hs.2
  have h2 := curve_chord_energy_le hv ht.1 ht.2
  have h3 := stdDot_sub_self_le (v s-v a) (v t-v a)
  rw [sub_sub_sub_cancel_right] at h3
  nlinarith only [h1,h2,h3]

lemma horizontal_curve_deriv {v : Plane → Phase n} (hv : ContDiff ℝ ∞ v) (y x : ℝ) :
    deriv (fun s : ℝ => v (s,y)) x=fderiv ℝ v (x,y) (1,0) := by
  have hh := (hv.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (x,y)).hasFDerivAt.comp_hasDerivAt x
    ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))
  change HasDerivAt (fun s : ℝ => v (s,y)) _ x at hh
  exact hh.deriv

lemma vertical_curve_deriv {v : Plane → Phase n} (hv : ContDiff ℝ ∞ v) (x y : ℝ) :
    deriv (fun s : ℝ => v (x,s)) y=fderiv ℝ v (x,y) (0,1) := by
  have hh := (hv.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (x,y)).hasFDerivAt.comp_hasDerivAt y
    ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))
  change HasDerivAt (fun s : ℝ => v (x,s)) _ y at hh
  exact hh.deriv

lemma horizontalEnergy_continuous {v : Plane → Phase n} (hv : ContDiff ℝ ∞ v) :
    Continuous (horizontalEnergy v) := by
  have hh := (hv.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuous.clm_apply (continuous_const (y := ((1,0):Plane)))
  exact ((stdDot n).continuous.comp hh).clm_apply hh

lemma verticalEnergy_continuous {v : Plane → Phase n} (hv : ContDiff ℝ ∞ v) :
    Continuous (verticalEnergy v) := by
  have hh := (hv.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuous.clm_apply (continuous_const (y := ((0,1):Plane)))
  exact ((stdDot n).continuous.comp hh).clm_apply hh

lemma rectangle_pair_energy_bound {v : Plane → Phase n} (hv : ContDiff ℝ ∞ v)
    {a b : ℝ} {p q : Plane} (hp : p∈(Icc a b) ×ˢ (Icc a b)) (hq : q∈(Icc a b) ×ˢ (Icc a b)) :
    stdDot n (v p-v q) (v p-v q)≤
      8*(b-a)*((∫ x in a..b,horizontalEnergy v (x,p.2))+
        (∫ y in a..b,verticalEnergy v (q.1,y))) := by
  have hx := curve_pair_energy_le (v := fun x => v (x,p.2)) (hv.comp (contDiff_id.prodMk (contDiff_const (c := p.2)))) hp.1 hq.1
  have hy := curve_pair_energy_le (v := fun y => v (q.1,y)) (hv.comp ((contDiff_const (c := q.1)).prodMk contDiff_id)) hp.2 hq.2
  change stdDot n (v (p.1,p.2)-v (q.1,p.2)) (v (p.1,p.2)-v (q.1,p.2))≤_ at hx
  change stdDot n (v (q.1,p.2)-v (q.1,q.2)) (v (q.1,p.2)-v (q.1,q.2))≤_ at hy
  simp only [horizontal_curve_deriv hv] at hx
  simp only [vertical_curve_deriv hv] at hy
  have hh := stdDot_add_self_le (v p-v (q.1,p.2)) (v (q.1,p.2)-v q)
  rw [sub_add_sub_cancel] at hh
  change stdDot n (v p-v (q.1,p.2)) (v p-v (q.1,p.2))≤
    4*(b-a)*(∫ x in a..b,horizontalEnergy v (x,p.2)) at hx
  change stdDot n (v (q.1,p.2)-v q) (v (q.1,p.2)-v q)≤
    4*(b-a)*(∫ y in a..b,verticalEnergy v (q.1,y)) at hy
  nlinarith only [hx,hy,hh]


lemma squareMeasure_eq (a b : ℝ) :
    squareMeasure a b=volume.restrict ((Icc a b) ×ˢ (Icc a b)) := by
  rw [squareMeasure,Measure.prod_restrict,←Measure.volume_eq_prod]

lemma squareMeasure_mass {a b : ℝ} (hab : a≤b) :
    (squareMeasure a b).real univ=(b-a)^2 := by
  rw [squareMeasure,Measure.real,←univ_prod_univ,Measure.prod_prod]
  simp [Real.volume_Icc,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab),pow_two]

lemma intervalMeasure_mass {a b : ℝ} (hab : a≤b) :
    (volume.restrict (Icc a b)).real univ=b-a := by
  simp [Measure.real,Real.volume_Icc,ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]

lemma continuous_square_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Plane → E} (hf : Continuous f) (a b : ℝ) : Integrable f (squareMeasure a b) := by
  rw [squareMeasure_eq]
  exact hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

lemma square_ae_mem (a b : ℝ) : ∀ᵐ z ∂squareMeasure a b,z∈(Icc a b) ×ˢ (Icc a b) := by
  rw [squareMeasure_eq]
  exact ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)

lemma square_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} {f : Plane → E} (hf : Integrable f (squareMeasure a b)) :
    (∫ z,f z ∂squareMeasure a b)=∫ x in Icc a b,∫ y in Icc a b,f (x,y) :=
  integral_prod f hf

lemma square_integral_swap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} {f : Plane → E} (hf : Integrable f (squareMeasure a b)) :
    (∫ z,f z ∂squareMeasure a b)=∫ y in Icc a b,∫ x in Icc a b,f (x,y) :=
  integral_prod_symm f hf

lemma integral_Icc_eq_interval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b : ℝ} (hab : a≤b) :
    (∫ x in Icc a b,f x)=∫ x in a..b,f x := by
  rw [intervalIntegral.integral_of_le hab,integral_Icc_eq_integral_Ioc]


lemma horizontalSlice_integrable {v : Plane → Phase n} (hv : ContDiff ℝ ∞ v) (a b : ℝ) :
    Integrable (horizontalSlice v a b) (volume.restrict (Icc a b)) :=
  (continuous_square_integrable (horizontalEnergy_continuous hv) a b).integral_prod_right

lemma verticalSlice_integrable {v : Plane → Phase n} (hv : ContDiff ℝ ∞ v) (a b : ℝ) :
    Integrable (verticalSlice v a b) (volume.restrict (Icc a b)) :=
  (continuous_square_integrable (verticalEnergy_continuous hv) a b).integral_prod_left

lemma square_point_deviation_bound {v : Plane → Phase n} (hv : ContDiff ℝ ∞ v)
    {a b : ℝ} (hab : a<b) {p : Plane} (hp : p∈(Icc a b) ×ˢ (Icc a b)) :
    stdDot n (v p-phaseAverage (squareMeasure a b) v) (v p-phaseAverage (squareMeasure a b) v)≤
      8*(b-a)*horizontalSlice v a b p.2+8*(∫ z,verticalEnergy v z ∂squareMeasure a b) := by
  have hvi := continuous_square_integrable hv.continuous a b
  have hve := continuous_square_integrable (((stdDot n).continuous.comp hv.continuous).clm_apply hv.continuous) a b
  have hm : 0<(squareMeasure a b).real univ := by rw [squareMeasure_mass hab.le]; positivity
  have hj := phaseAverage_deviation_energy_le hvi hve hm (v p)
  have hvsi : Integrable (fun q : Plane => verticalSlice v a b q.1) (squareMeasure a b) :=
    (verticalSlice_integrable hv a b).comp_fst _
  have hright : Integrable (fun q : Plane => 8*(b-a)*(horizontalSlice v a b p.2+verticalSlice v a b q.1))
      (squareMeasure a b) :=
    ((integrable_const _).add hvsi).const_mul _
  have hcomp : (∫ q,stdDot n (v p-v q) (v p-v q) ∂squareMeasure a b)≤
      ∫ q,8*(b-a)*(horizontalSlice v a b p.2+verticalSlice v a b q.1) ∂squareMeasure a b := by
    apply integral_mono_ae (integrable_stdDot_const_sub hvi hve (v p)) hright
    filter_upwards [square_ae_mem a b] with q hq
    have hh := rectangle_pair_energy_bound hv hp hq
    simpa only [horizontalSlice,verticalSlice,integral_Icc_eq_interval hab.le] using hh
  have hmass := intervalMeasure_mass hab.le
  have hfub := square_integral (continuous_square_integrable (verticalEnergy_continuous hv) a b)
  have hrightVal : (∫ q,8*(b-a)*(horizontalSlice v a b p.2+verticalSlice v a b q.1) ∂squareMeasure a b)=
      8*(b-a)*((b-a)^2*horizontalSlice v a b p.2+
        (b-a)*(∫ z,verticalEnergy v z ∂squareMeasure a b)) := by
    rw [integral_const_mul,integral_add (integrable_const _) hvsi,
      integral_const,squareMeasure_mass hab.le]
    change 8*(b-a)*((b-a)^2*horizontalSlice v a b p.2+
      (∫ q,verticalSlice v a b q.1 ∂(volume.restrict (Icc a b)).prod (volume.restrict (Icc a b))))=_
    rw [integral_fun_fst,hmass]
    rw [hfub]
    rfl
  rw [hrightVal] at hcomp
  have hh := hj.trans (mul_le_mul_of_nonneg_left hcomp (inv_nonneg.mpr hm.le))
  rw [squareMeasure_mass hab.le] at hh
  have hid : ((b-a)^2)⁻¹*(8*(b-a)*((b-a)^2*horizontalSlice v a b p.2+
      (b-a)*(∫ z,verticalEnergy v z ∂squareMeasure a b)))=
      8*(b-a)*horizontalSlice v a b p.2+8*(∫ z,verticalEnergy v z ∂squareMeasure a b) := by
    field_simp [(sub_pos.mpr hab).ne']
  rwa [hid] at hh

lemma square_poincare {v : Plane → Phase n} (hv : ContDiff ℝ ∞ v)
    {a b : ℝ} (hab : a<b) :
    (∫ z,stdDot n (v z-phaseAverage (squareMeasure a b) v) (v z-phaseAverage (squareMeasure a b) v)
      ∂squareMeasure a b)≤
      8*(b-a)^2*(∫ z,horizontalEnergy v z+verticalEnergy v z ∂squareMeasure a b) := by
  have hleft : Integrable (fun z => stdDot n (v z-phaseAverage (squareMeasure a b) v)
      (v z-phaseAverage (squareMeasure a b) v)) (squareMeasure a b) := continuous_square_integrable
    (((stdDot n).continuous.comp (hv.continuous.sub continuous_const)).clm_apply
      (hv.continuous.sub continuous_const)) a b
  have hxsi : Integrable (fun p : Plane => horizontalSlice v a b p.2) (squareMeasure a b) :=
    (horizontalSlice_integrable hv a b).comp_snd _
  have hright : Integrable (fun p : Plane => 8*(b-a)*horizontalSlice v a b p.2+
      8*(∫ z,verticalEnergy v z ∂squareMeasure a b)) (squareMeasure a b) :=
    (hxsi.const_mul _).add (integrable_const _)
  have hcomp := integral_mono_ae hleft hright (by
    filter_upwards [square_ae_mem a b] with p hp
    exact square_point_deviation_bound hv hab hp)
  have hx := continuous_square_integrable (horizontalEnergy_continuous hv) a b
  have hy := continuous_square_integrable (verticalEnergy_continuous hv) a b
  have hfub := square_integral_swap hx
  rw [integral_add (hxsi.const_mul _) (integrable_const _)] at hcomp
  rw [integral_const_mul,integral_const] at hcomp
  change _≤8*(b-a)*(∫ p,horizontalSlice v a b p.2 ∂(volume.restrict (Icc a b)).prod (volume.restrict (Icc a b)))+
    (squareMeasure a b).real univ*(8*(∫ z,verticalEnergy v z ∂squareMeasure a b)) at hcomp
  rw [integral_fun_snd,intervalMeasure_mass hab.le,squareMeasure_mass hab.le] at hcomp
  change _≤8*(b-a)*((b-a)*(∫ y in Icc a b,∫ x in Icc a b,horizontalEnergy v (x,y)))+_ at hcomp
  rw [←hfub] at hcomp
  rw [integral_add hx hy]
  nlinarith only [hcomp]


lemma stdDot_sub_swap (v w : Phase n) : stdDot n (v-w) (v-w)=stdDot n (w-v) (w-v) := by
  have h : w-v=-(v-w) := by abel
  rw [h]
  simp only [map_neg,neg_apply,neg_neg]

lemma square_energy_mono {f : Plane → ℝ} (hf : Continuous f) (hn : ∀ z,0≤f z)
    {a b c d : ℝ} (hac : a ≤ c) (hdb : d≤b) :
    (∫ z,f z ∂squareMeasure c d)≤∫ z,f z ∂squareMeasure a b := by
  simp only [squareMeasure_eq]
  apply setIntegral_mono_set (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc))
    (Eventually.of_forall hn)
  exact Eventually.of_forall (fun z hz =>
    ⟨⟨hac.trans hz.1.1,hz.1.2.trans hdb⟩,⟨hac.trans hz.2.1,hz.2.2.trans hdb⟩⟩)

lemma square_means_energy {v : Plane → Phase n} (hv : ContDiff ℝ ∞ v)
    {a b c d : ℝ} (hab : a<b) (hcd : c<d) (hac : a ≤ c) (hdb : d≤b) :
    stdDot n (phaseAverage (squareMeasure a b) v-phaseAverage (squareMeasure c d) v)
      (phaseAverage (squareMeasure a b) v-phaseAverage (squareMeasure c d) v)≤
      ((d-c)^2)⁻¹*(8*(b-a)^2)*
        (∫ z,horizontalEnergy v z+verticalEnergy v z ∂squareMeasure a b) := by
  have hvi := continuous_square_integrable hv.continuous c d
  have hve := continuous_square_integrable (((stdDot n).continuous.comp hv.continuous).clm_apply hv.continuous) c d
  have hm : 0<(squareMeasure c d).real univ := by rw [squareMeasure_mass hcd.le]; positivity
  have hj := phaseAverage_deviation_energy_le hvi hve hm (phaseAverage (squareMeasure a b) v)
  rw [squareMeasure_mass hcd.le] at hj
  have hm' : 0≤((d-c)^2)⁻¹ := by positivity
  have hmono := square_energy_mono
    (((stdDot n).continuous.comp (continuous_const.sub hv.continuous)).clm_apply
      (continuous_const.sub hv.continuous))
    (fun z => stdDot_nonneg (phaseAverage (squareMeasure a b) v-v z)) hac hdb
  have hs : (∫ z,stdDot n (phaseAverage (squareMeasure a b) v-v z)
      (phaseAverage (squareMeasure a b) v-v z) ∂squareMeasure a b)≤
      8*(b-a)^2*(∫ z,horizontalEnergy v z+verticalEnergy v z ∂squareMeasure a b) := by
    simp_rw [stdDot_sub_swap (phaseAverage (squareMeasure a b) v)]
    exact square_poincare hv hab
  have hh := hj.trans (mul_le_mul_of_nonneg_left (hmono.trans hs) hm')
  simpa only [mul_assoc] using hh

lemma quarter_square_mean_norm {v : Plane → Phase n} (hv : ContDiff ℝ ∞ v)
    {r : ℝ} (hr : 0 < r) :
    ‖phaseAverage (squareMeasure (-r) r) v-phaseAverage (squareMeasure (-(r/4)) (r/4)) v‖^2≤
      128*(∫ z,horizontalEnergy v z+verticalEnergy v z ∂squareMeasure (-r) r) := by
  have hh := square_means_energy hv (a := -r) (b := r) (c := -(r/4)) (d := r/4)
    (by linarith) (by linarith) (by linarith) (by linarith)
  have hid : ((r/4-(-(r/4)))^2)⁻¹*(8*(r-(-r))^2)=(128:ℝ) := by
    field_simp [hr.ne']
    ring
  rw [hid] at hh
  exact (norm_sq_le_stdDot _).trans hh

lemma square_dirichlet_le_radial {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    {r A : ℝ} (hr : 0 ≤ r) (hA : 0<A) (hrA : 2*r^2≤A) :
    (∫ z,horizontalEnergy (realCurve u) z+verticalEnergy (realCurve u) z ∂squareMeasure (-r) r)≤
      radialCurveEnergy u A := by
  change (∫ z,dirichletEnergy u z ∂squareMeasure (-r) r)≤_
  rw [squareMeasure_eq]
  have heq : (∫ z in (Icc (-r) r) ×ˢ (Icc (-r) r),dirichletEnergy u z)=
      ∫ z in (Icc (-r) r) ×ˢ (Icc (-r) r),sourceRadialCutoff A z*dirichletEnergy u z := by
    apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
    intro z hz
    have h1 : z.1^2 ≤ r^2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg z.1) hr).mpr (abs_le.mpr hz.1)
    have h2 : z.2^2 ≤ r^2 := sq_le_sq' hz.2.1 hz.2.2
    have hrad : radiusSq z≤A := by dsimp [radiusSq] <;> nlinarith
    change dirichletEnergy u z=sourceRadialCutoff A z*dirichletEnergy u z
    rw [show sourceRadialCutoff A z=1 from
      outerProfile_one_before (radiusSq_nonneg z) hrad hA,one_mul]
  rw [heq]
  exact setIntegral_le_integral (smooth_cutoff_integrable_mul hA (dirichletEnergy_continuous hu))
    (Eventually.of_forall (fun z => mul_nonneg (sourceRadialCutoff_nonneg A z) (dirichletEnergy_nonneg u z)))


lemma phaseAverage_norm_le {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → Phase n} (hμ : 0<μ.real univ) {C : ℝ} (hf : ∀ᵐ x ∂μ,‖f x‖≤C) :
    ‖phaseAverage μ f‖≤C := by
  rw [phaseAverage,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hμ.le)]
  have hh := mul_le_mul_of_nonneg_left (norm_integral_le_of_norm_le_const hf) (inv_nonneg.mpr hμ.le)
  have hid : (μ.real univ)⁻¹*(C*μ.real univ)=C := by field_simp
  rwa [hid] at hh

lemma plane_norm_le_square {r : ℝ} {z : Plane} (hz : z∈(Icc (-r) r) ×ˢ (Icc (-r) r)) : ‖z‖ ≤ r := by
  rw [Prod.norm_def]
  exact max_le (abs_le.mpr hz.1) (abs_le.mpr hz.2)

lemma squareAverage_tendsto {v : Plane → Phase n} (hv : Continuous v)
    {r : ℕ → ℝ} (hr : ∀ k,0 < r k) (hr0 : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun k => phaseAverage (squareMeasure (-(r k)) (r k)) v) atTop (𝓝 (v 0)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨δ,hδ,hδv⟩ := Metric.continuousAt_iff.mp hv.continuousAt (ε/2) (by positivity)
  have hev : ∀ᶠ k in atTop,r k<δ := hr0.eventually (gt_mem_nhds hδ)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hev
  refine ⟨N,?_⟩
  intro k hk
  have hm : 0<(squareMeasure (-(r k)) (r k)).real univ := by
    rw [squareMeasure_mass (by linarith [hr k])]
    exact sq_pos_of_pos (by linarith [hr k])
  have hb : ∀ᵐ z ∂squareMeasure (-(r k)) (r k),‖v 0-v z‖≤ε/2 := by
    filter_upwards [square_ae_mem (-(r k)) (r k)] with z hz
    have hzδ : dist z 0<δ := by simpa only [dist_zero_right] using (plane_norm_le_square hz).trans_lt (hN k hk)
    have hh := hδv hzδ
    simpa only [dist_eq_norm,norm_sub_rev] using hh.le
  have hh := phaseAverage_norm_le hm hb
  rw [phaseAverage_const_sub (continuous_square_integrable hv _ _) hm] at hh
  rw [dist_eq_norm,norm_sub_rev]
  exact hh.trans_lt (by linarith)


lemma campRadius_pos (k : ℕ) : 0 < campRadius k := by unfold campRadius; positivity

lemma campRadius_succ (k : ℕ) : campRadius (k+1)=campRadius k/4 := by
  unfold campRadius
  rw [pow_succ]
  ring

lemma campRadius_sq (k : ℕ) : 2*(campRadius k)^2≤(1/16)^k := by
  unfold campRadius
  have hid : ((1/4:ℝ)^k)^2=(1/16:ℝ)^k := by
    rw [←pow_mul,Nat.mul_comm k 2,pow_mul]
    norm_num
  rw [mul_pow,hid]
  have hh : 0≤(1/16:ℝ)^k := by positivity
  nlinarith

lemma campRadius_tendsto : Tendsto campRadius atTop (𝓝 0) := by
  change Tendsto (fun k : ℕ => (1/2:ℝ)*(1/4)^k) atTop (𝓝 0)
  have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/4) (by norm_num : (1/4:ℝ)<1)).const_mul (1/2:ℝ)
  simpa only [campRadius,mul_zero] using hh

lemma geometric_sqrt_norm_bound {v : Phase n} {B θ : ℝ} (hB : 0≤B) (hθ : 0≤θ) (k : ℕ)
    (hv : ‖v‖^2≤128*B*θ^k) : ‖v‖≤Real.sqrt (128*B)*(Real.sqrt θ)^k := by
  have hc : 0≤Real.sqrt (128*B)*(Real.sqrt θ)^k := by positivity
  apply (sq_le_sq₀ (norm_nonneg _) hc).mp
  have hid : (Real.sqrt (128*B)*(Real.sqrt θ)^k)^2=128*B*θ^k := by
    rw [mul_pow,Real.sq_sqrt (by positivity),←pow_mul,Nat.mul_comm k 2,pow_mul,Real.sq_sqrt hθ]
  rwa [hid]

lemma campanato_point_mean {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    {B θ : ℝ} (hB : 0≤B) (hθ : 0≤θ) (hθ1 : θ<1)
    (he : ∀ k : ℕ,radialCurveEnergy u ((1/16)^k)≤B*θ^k) (k : ℕ) :
    ‖phaseAverage (squareMeasure (-(campRadius k)) (campRadius k)) (realCurve u)-u 0‖≤
      Real.sqrt (128*B)*(Real.sqrt θ)^k/(1-Real.sqrt θ) := by
  let f : ℕ → Phase n := fun j => phaseAverage (squareMeasure (-(campRadius j)) (campRadius j)) (realCurve u)
  have hf : Tendsto f atTop (𝓝 (u 0)) := by
    have hh := squareAverage_tendsto (realCurve_smooth hu).continuous campRadius_pos campRadius_tendsto
    simpa only [f,realCurve,Function.comp_apply,map_zero] using hh
  have hs (j : ℕ) : dist (f j) (f (j+1))≤Real.sqrt (128*B)*(Real.sqrt θ)^j := by
    rw [dist_eq_norm]
    apply geometric_sqrt_norm_bound hB hθ j
    have hq := quarter_square_mean_norm (realCurve_smooth hu) (campRadius_pos j)
    have hr := square_dirichlet_le_radial hu (campRadius_pos j).le
      (by positivity : (0:ℝ)<(1/16)^j) (campRadius_sq j)
    change ‖phaseAverage (squareMeasure (-(campRadius j)) (campRadius j)) (realCurve u)-
      phaseAverage (squareMeasure (-(campRadius (j+1))) (campRadius (j+1))) (realCurve u)‖^2≤_
    rw [campRadius_succ]
    exact hq.trans ((mul_le_mul_of_nonneg_left (hr.trans (he j)) (by norm_num)).trans_eq (by ring))
  have hsqrt : Real.sqrt θ<1 := (Real.sqrt_lt' (by norm_num)).mpr (by simpa using hθ1)
  simpa only [dist_eq_norm] using dist_le_of_le_geometric_of_tendsto (Real.sqrt θ) (Real.sqrt (128*B)) hsqrt hs hf k



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Campanato_TranslatedSquare
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.FiniteMoment.Radial.instInhabitedQuadrant _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frozenTargetCoefficient_zero _root_.OAI.HigherDimensionalBallPacking.Rigidity.geometricHolder_value _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
variable {n : ℕ}

lemma translatedSquare_mass (c : Plane) {r : ℝ} (hr : 0 ≤ r) :
    (translatedSquare c r).real univ=(2*r)^2 := by
  rw [translatedSquare,Measure.real,Measure.map_apply (by fun_prop) MeasurableSet.univ]
  change (squareMeasure (-r) r).real univ=(2*r)^2
  rw [squareMeasure_mass (by linarith)]
  ring

lemma translatedSquare_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Plane → E} (hf : Continuous f) (c : Plane) (r : ℝ) :
    Integrable f (translatedSquare c r) := by
  unfold translatedSquare
  apply ((Homeomorph.addRight c).isClosedEmbedding.measurableEmbedding.integrable_map_iff).mpr
  exact continuous_square_integrable (hf.comp (continuous_id.add continuous_const)) _ _

lemma translatedSquare_average (c : Plane) (r : ℝ) (v : Plane → Phase n) :
    phaseAverage (translatedSquare c r) v=
      phaseAverage (squareMeasure (-r) r) (fun z => v (z+c)) := by
  have he : MeasurableEmbedding (fun z : Plane => z+c) := (Homeomorph.addRight c).isClosedEmbedding.measurableEmbedding
  unfold phaseAverage translatedSquare
  rw [he.integral_map]
  congr 1
  rw [Measure.real,Measure.map_apply (by fun_prop) MeasurableSet.univ]
  rfl

lemma translatedSquare_le {c : Plane} {r R : ℝ} (hrr : ‖c‖+r≤R) :
    translatedSquare c r≤ squareMeasure (-R) R := by
  have hsub : (Icc (-r) r) ×ˢ (Icc (-r) r)⊆
      (fun z : Plane => z+c) ⁻¹' ((Icc (-R) R) ×ˢ (Icc (-R) R)) := by
    intro z hz
    have hc1 := norm_fst_le c
    have hc2 := norm_snd_le c
    have hc1' := abs_le.mp hc1
    have hc2' := abs_le.mp hc2
    change (z.1+c.1,z.2+c.2)∈(Icc (-R) R) ×ˢ (Icc (-R) R)
    exact ⟨⟨by linarith [hz.1.1],by linarith [hz.1.2]⟩,
      ⟨by linarith [hz.2.1],by linarith [hz.2.2]⟩⟩
  have hh := Measure.map_mono (Measure.restrict_mono hsub (le_refl (volume : Measure Plane)))
    (show Measurable (fun z : Plane => z+c) by fun_prop)
  rw [←Measure.restrict_map (by fun_prop) (measurableSet_Icc.prod measurableSet_Icc),
    (measurePreserving_add_right (volume : Measure Plane) c).map_eq] at hh
  simpa only [translatedSquare,squareMeasure_eq] using hh

lemma translated_square_means_energy {v : Plane → Phase n} (hv : ContDiff ℝ ∞ v)
    {c : Plane} {r R : ℝ} (hr : 0 < r) (hR : 0<R) (hrr : ‖c‖+r≤R) :
    ‖phaseAverage (squareMeasure (-R) R) v-phaseAverage (translatedSquare c r) v‖^2≤
      ((2*r)^2)⁻¹*(8*(2*R)^2)*
        (∫ z,horizontalEnergy v z+verticalEnergy v z ∂squareMeasure (-R) R) := by
  have hvi := translatedSquare_integrable hv.continuous c r
  have hve := translatedSquare_integrable (((stdDot n).continuous.comp hv.continuous).clm_apply hv.continuous) c r
  have hm : 0<(translatedSquare c r).real univ := by rw [translatedSquare_mass c hr.le]; positivity
  have hj := phaseAverage_deviation_energy_le hvi hve hm (phaseAverage (squareMeasure (-R) R) v)
  rw [translatedSquare_mass c hr.le] at hj
  have hii : Integrable (fun z => stdDot n (phaseAverage (squareMeasure (-R) R) v-v z)
      (phaseAverage (squareMeasure (-R) R) v-v z)) (squareMeasure (-R) R) :=
    continuous_square_integrable
      (((stdDot n).continuous.comp (continuous_const.sub hv.continuous)).clm_apply
        (continuous_const.sub hv.continuous)) _ _
  have hmono := integral_mono_measure (translatedSquare_le hrr)
    (Eventually.of_forall (fun z => stdDot_nonneg (phaseAverage (squareMeasure (-R) R) v-v z))) hii
  have hp := square_poincare hv (a := -R) (b := R) (by linarith)
  have hp' : (∫ z,stdDot n (phaseAverage (squareMeasure (-R) R) v-v z)
      (phaseAverage (squareMeasure (-R) R) v-v z) ∂squareMeasure (-R) R)≤
      8*(R-(-R))^2*(∫ z,horizontalEnergy v z+verticalEnergy v z ∂squareMeasure (-R) R) := by
    simpa only [stdDot_sub_swap (phaseAverage (squareMeasure (-R) R) v)] using hp
  have hh := (norm_sq_le_stdDot _).trans (hj.trans
    (mul_le_mul_of_nonneg_left (hmono.trans hp') (by positivity)))
  simpa only [sub_neg_eq_add,←two_mul,mul_assoc] using hh


lemma realProd_norm_le (c : ℂ) : ‖Complex.equivRealProdCLM c‖≤‖c‖ := by
  change max ‖c.re‖ ‖c.im‖≤‖c‖
  exact max_le (Complex.abs_re_le_norm c) (Complex.abs_im_le_norm c)

lemma translated_camp_mean_bound {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    {B θ : ℝ} (hB : 0≤B) (hθ : 0≤θ) (k : ℕ)
    (he : radialCurveEnergy u ((1/16)^k)≤B*θ^k)
    {c : ℂ} (hc : ‖c‖ ≤ campRadius (k+1)) :
    ‖phaseAverage (squareMeasure (-(campRadius k)) (campRadius k)) (realCurve u)-
      phaseAverage (squareMeasure (-(campRadius (k+1))) (campRadius (k+1)))
        (realCurve (centeredCurve u c))‖≤Real.sqrt (128*B)*(Real.sqrt θ)^k := by
  have hc' : ‖Complex.equivRealProdCLM c‖+campRadius (k+1) ≤ campRadius k := by
    have hh := (realProd_norm_le c).trans hc
    rw [campRadius_succ] at hh ⊢
    linarith [campRadius_pos k]
  have hh := translated_square_means_energy (realCurve_smooth hu)
    (campRadius_pos (k+1)) (campRadius_pos k) hc'
  rw [translatedSquare_average,←realCurve_centered] at hh
  have hid : ((2*campRadius (k+1))^2)⁻¹*(8*(2*campRadius k)^2)=(128:ℝ) := by
    rw [campRadius_succ]
    field_simp [(campRadius_pos k).ne']
    ring
  rw [hid] at hh
  have hr := square_dirichlet_le_radial hu (campRadius_pos k).le (by positivity : (0:ℝ)<(1/16)^k) (campRadius_sq k)
  apply geometric_sqrt_norm_bound hB hθ k
  exact hh.trans ((mul_le_mul_of_nonneg_left (hr.trans he) (by norm_num)).trans_eq (by ring))

lemma centeredCurve_zero (u : ℂ → Phase n) : centeredCurve u 0=u := by
  funext z
  simp only [centeredCurve,add_zero]

lemma centeredCurve_centered (u : ℂ → Phase n) (p q : ℂ) :
    centeredCurve (centeredCurve u p) q=centeredCurve u (q+p) := by
  funext z
  simp only [centeredCurve,add_assoc]

lemma campanato_oscillation_zero {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    {B θ : ℝ} (hB : 0≤B) (hθ : 0≤θ) (hθ1 : θ<1)
    (he : ∀ c : ℂ,∀ k : ℕ,radialCurveEnergy (centeredCurve u c) ((1/16)^k)≤B*θ^k)
    (k : ℕ) {c : ℂ} (hc : ‖c‖ ≤ campRadius (k+1)) :
    ‖u c-u 0‖≤2*Real.sqrt (128*B)*(Real.sqrt θ)^k/(1-Real.sqrt θ) := by
  have hroot : Real.sqrt θ<1 := (Real.sqrt_lt' (by norm_num)).mpr (by simpa using hθ1)
  have hden : 0<1-Real.sqrt θ := by linarith
  have he0 : ∀ j : ℕ,radialCurveEnergy u ((1/16)^j)≤B*θ^j := by
    intro j
    simpa only [centeredCurve_zero] using he 0 j
  have hpc := campanato_point_mean (centeredCurve_smooth hu c) hB hθ hθ1 (he c) (k+1)
  have hp0 := campanato_point_mean hu hB hθ hθ1 he0 (k+1)
  have hmc := translated_camp_mean_bound hu hB hθ k (he0 k) hc
  have hm0 := translated_camp_mean_bound hu hB hθ k (he0 k) (c := 0) (by simpa using (campRadius_pos (k+1)).le)
  rw [centeredCurve_zero] at hm0
  simp only [centeredCurve,zero_add] at hpc
  let m := phaseAverage (squareMeasure (-(campRadius k)) (campRadius k)) (realCurve u)
  let m0 := phaseAverage (squareMeasure (-(campRadius (k+1))) (campRadius (k+1))) (realCurve u)
  let mc := phaseAverage (squareMeasure (-(campRadius (k+1))) (campRadius (k+1))) (realCurve (centeredCurve u c))
  have htri : ‖u c-u 0‖≤‖mc-u c‖+‖m-mc‖+‖m-m0‖+‖m0-u 0‖ := by
    have h1 := dist_triangle (u c) mc (u 0)
    have h2 := dist_triangle mc m (u 0)
    have h3 := dist_triangle m m0 (u 0)
    simp only [dist_eq_norm] at h1 h2 h3
    rw [norm_sub_rev (u c) mc] at h1
    rw [norm_sub_rev mc m] at h2
    linarith
  have ht : ‖u c-u 0‖≤
      2*(Real.sqrt (128*B)*(Real.sqrt θ)^(k+1)/(1-Real.sqrt θ))+
      2*(Real.sqrt (128*B)*(Real.sqrt θ)^k) := by
    dsimp [m,m0,mc] at htri
    linarith only [htri,hpc,hp0,hmc,hm0]
  have hid : 2*(Real.sqrt (128*B)*(Real.sqrt θ)^(k+1)/(1-Real.sqrt θ))+
      2*(Real.sqrt (128*B)*(Real.sqrt θ)^k)=
      2*Real.sqrt (128*B)*(Real.sqrt θ)^k/(1-Real.sqrt θ) := by
    rw [pow_succ]
    field_simp
    ring
  exact ht.trans_eq hid

lemma campanato_oscillation {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    {B θ : ℝ} (hB : 0≤B) (hθ : 0≤θ) (hθ1 : θ<1)
    (he : ∀ c : ℂ,∀ k : ℕ,radialCurveEnergy (centeredCurve u c) ((1/16)^k)≤B*θ^k)
    (k : ℕ) {p q : ℂ} (hpq : ‖q-p‖ ≤ campRadius (k+1)) :
    ‖u q-u p‖≤2*Real.sqrt (128*B)*(Real.sqrt θ)^k/(1-Real.sqrt θ) := by
  have hh := campanato_oscillation_zero (centeredCurve_smooth hu p) hB hθ hθ1
    (fun c j => by simpa only [centeredCurve_centered] using he (c+p) j) k hpq
  simpa only [centeredCurve,sub_add_cancel,zero_add] using hh


end
section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
variable {n : ℕ}

lemma energy_uniform_modulus {B θ : ℝ} (hB : 0≤B) (hθ : 0≤θ) (hθ1 : θ<1)
    {ε : ℝ} (hε : 0<ε) : ∃ δ : ℝ,0<δ ∧
      ∀ (u : ℂ → Phase n),ContDiff ℝ ∞ u →
        (∀ c : ℂ,∀ k : ℕ,radialCurveEnergy (centeredCurve u c) ((1/16)^k)≤B*θ^k) →
        ∀ p q : ℂ,dist p q<δ →dist (u p) (u q)<ε := by
  have hroot : Real.sqrt θ<1 := (Real.sqrt_lt' (by norm_num)).mpr (by simpa using hθ1)
  have ht : Tendsto (fun k : ℕ => 2*Real.sqrt (128*B)*(Real.sqrt θ)^k/(1-Real.sqrt θ)) atTop (𝓝 0) := by
    have hh := ((tendsto_pow_atTop_nhds_zero_of_lt_one (Real.sqrt_nonneg θ) hroot).const_mul
      (2*Real.sqrt (128*B))).div_const (1-Real.sqrt θ)
    simpa only [mul_zero,zero_div] using hh
  obtain ⟨k,hk⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  refine ⟨campRadius (k+1),campRadius_pos (k+1),?_⟩
  intro u hu he p q hpq
  have hpq' : ‖q-p‖ ≤ campRadius (k+1) := by
    simpa only [dist_eq_norm,norm_sub_rev] using hpq.le
  have hh := campanato_oscillation hu hB hθ hθ1 he k hpq'
  rw [dist_eq_norm,norm_sub_rev]
  exact hh.trans_lt hk

lemma dilatedCurve_smooth {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (c : ℂ) :
    ContDiff ℝ ∞ (dilatedCurve u c) := hu.comp (contDiff_const.mul contDiff_id)


end
section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
variable {n : ℕ}


lemma dilatedCurve_original_second_mark {J : Phase n → End n} {p q : Phase n}
    {u : ℂ → Phase n} (hu : AffineLineCurve J p q u) {a : Phase n} (ha : a≠0) :
    dilatedCurve u (slopeScale a) (Real.sqrt (stdDot n a a))=q := by
  change u ((slopeScale a : ℂ)*(Real.sqrt (stdDot n a a) : ℂ))=q
  rw [←Complex.ofReal_mul]
  have hid : slopeScale a*Real.sqrt (stdDot n a a)=1 :=
    inv_mul_cancel₀ (Real.sqrt_pos.mpr (stdDot_pos ha)).ne'
  rw [hid,Complex.ofReal_one]
  exact hu.2.2.2.1

theorem exact_line_slope_lower_bound {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1)
    (hout : ∀ x,S < capacity x →J x=standardJ n)
    {p q : Phase n} (hpq : p≠q) :
    ∃ d : ℝ,0<d ∧ ∀ t∈Icc (0:ℝ) 1,∀ (u : ℂ → Phase n),
      AffineLineCurve (lineHomotopy J t) p q u →
      ∀ a : Phase n,a≠0 →Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 a) →
        d≤ stdDot n a a := by
  obtain ⟨B,θ,hB,hθ,hθ1,he⟩ := exact_normalized_line_energy_bp240 hJs hJ hJc hST hT hout
  obtain ⟨δ,hδ,hmod⟩ := energy_uniform_modulus (n := n) hB.le hθ.le hθ1 (dist_pos.mpr hpq)
  refine ⟨δ^2,sq_pos_of_pos hδ,?_⟩
  intro t ht u hu a ha hlim
  have hlower : δ≤Real.sqrt (stdDot n a a) := by
    by_contra! h
    have hc : dist (0:ℂ) (Real.sqrt (stdDot n a a) : ℂ)<δ := by
      simpa only [dist_zero_left,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)] using h
    have hh := hmod (dilatedCurve u (slopeScale a)) (dilatedCurve_smooth hu.1 _)
      (he t ht p q u hu a ha hlim) 0 (Real.sqrt (stdDot n a a)) hc
    rw [dilatedCurve_original_second_mark hu ha] at hh
    have hz : dilatedCurve u (slopeScale a) 0=p := by simpa only [dilatedCurve,mul_zero] using hu.2.2.1
    rw [hz] at hh
    exact lt_irrefl _ hh
  nlinarith [Real.sq_sqrt (stdDot_nonneg a),Real.sqrt_nonneg (stdDot n a a)]


end
open scoped ContDiff Topology
open Set Function Filter MeasureTheory



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Compactness_FrozenCR
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Filter
open HolderCompletion
open scoped BoundedContinuousFunction
section
variable {n : ℕ}

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.hcbInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.hcbInst2
local instance hcbInst3_r62dbe7_1 : NormedAddCommGroup (Phase n →L[ℝ] End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance hcbInst4_r62dbe7_1 : NormedSpace ℝ (Phase n →L[ℝ] End n) := ContinuousLinearMap.toNormedSpace
lemma lineHomotopy_joint_contDiffAt {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x)) {v : ℝ × Phase n}
    (ht : v.1∈Icc (0:ℝ) 1) :
    ContDiffAt ℝ ∞ (fun v : ℝ × Phase n => lineHomotopy J v.1 v.2) v :=
  contDiffAt_interpolateJ (hJs.contDiffAt.comp v contDiffAt_snd) contDiffAt_fst (hJ _) ht

end

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Compactness_ResidualCauchy
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.FiniteMoment.Radial.instInhabitedQuadrant _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
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
local instance clcInst3_r62dbe7_1 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance clcInst4_r62dbe7_1 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
lemma compact_structure_norm_standard {J : Phase n → End n}
    (hc : HasCompactSupport (fun x => J x-standardJ n)) :
    ∃ B : ℝ,∀ x,B<‖x‖ →J x=standardJ n := by
  obtain ⟨B,hB⟩ := hc.exists_bound_of_continuousOn (f := fun x : Phase n => x) continuous_id.continuousOn
  refine ⟨B,fun x hx => ?_⟩
  exact sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport (f := fun x => J x-standardJ n) (fun hh => (not_le_of_gt hx) (hB x hh)))

lemma marked_value_continuous (p q : Phase n) (z : ℂ) :
    Continuous (fun w : COne ℂ (Phase n) => markedCurve p q w z) :=
  (continuous_const.add ((markedSlope_continuous p q).const_smul z)).add (jetEval z).continuous

lemma cDeriv_eval_continuous (z h : ℂ) :
    Continuous (fun w : COne ℂ (Phase n) => cDeriv w z h) := by
  have hc : Continuous (fun w : COne ℂ (Phase n) => cDeriv w z) :=
    ((BoundedContinuousFunction.evalCLM ℝ z).continuous.comp
      ((valueCLM ((1:ℝ)/3)).continuous.comp (jetDerivCLM ((1:ℝ)/3)).continuous))
  exact hc.clm_apply continuous_const

lemma marked_derivative_eval_continuous (p q : Phase n) (z h : ℂ) :
    Continuous (fun w : COne ℂ (Phase n) => fderiv ℝ (markedCurve p q w) z h) := by
  simp only [markedCurve_fderiv,add_apply,complexSlope_apply]
  exact ((markedSlope_continuous p q).const_smul h).add (cDeriv_eval_continuous z h)

lemma represented_line_slope_nonzero {J : Phase n → End n} {p q : Phase n}
    (w : COne ℂ (Phase n)) (hu : AffineLineCurve J p q (markedCurve p q w)) :
    markedSlope p q w≠0 := by
  obtain ⟨a,ha,hlim⟩ := hu.2.2.2.2
  have he := tendsto_nhds_unique (markedCurve_asymptote p q w) hlim
  exact fun hz => ha (he ▸ hz)

lemma completed_line_cr_closed {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    {t : ℕ → ℝ} {s : ℝ} (hsI : s∈Icc (0:ℝ) 1) (hs : Tendsto t atTop (𝓝 s))
    {p q : Phase n} {w : ℕ → COne ℂ (Phase n)} {v : COne ℂ (Phase n)}
    (hw : Tendsto w atTop (𝓝 v))
    (hu : ∀ i,AffineLineCurve (lineHomotopy J (t i)) p q (markedCurve p q (w i))) :
    ∀ z,fderiv ℝ (markedCurve p q v) z Complex.I=
      lineHomotopy J s (markedCurve p q v z) (fderiv ℝ (markedCurve p q v) z 1) := by
  intro z
  have hz := ((marked_value_continuous p q z).tendsto v).comp hw
  have hd1 := ((marked_derivative_eval_continuous p q z 1).tendsto v).comp hw
  have hdI := ((marked_derivative_eval_continuous p q z Complex.I).tendsto v).comp hw
  have hA := (lineHomotopy_joint_contDiffAt hJs hJ (v := (s,markedCurve p q v z)) hsI).continuousAt.tendsto.comp
    (hs.prodMk_nhds hz)
  have hAp : Continuous (fun v : End n × Phase n => v.1 v.2) := continuous_fst.clm_apply continuous_snd
  have hR := ((hAp.tendsto _).comp (hA.prodMk_nhds hd1))
  have he (i : ℕ) := (hu i).2.1 z
  apply tendsto_nhds_unique hdI
  convert hR using 1
  all_goals try with_reducible_and_instances rfl
  funext i
  simpa only [mul_one,Function.comp_def] using (he i).2 1

lemma completed_line_slope_limit_nonzero {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1) (hout : ∀ x,S < capacity x →J x=standardJ n)
    {p q : Phase n} (hpq : p≠q) {t : ℕ → ℝ} (ht : ∀ i,t i∈Icc (0:ℝ) 1)
    {w : ℕ → COne ℂ (Phase n)} {v : COne ℂ (Phase n)} (hw : Tendsto w atTop (𝓝 v))
    (hu : ∀ i,AffineLineCurve (lineHomotopy J (t i)) p q (markedCurve p q (w i))) :
    markedSlope p q v≠0 := by
  obtain ⟨d,hd,hlo⟩ := exact_line_slope_lower_bound hJs hJ hJc hST hT hout hpq
  have hsl := ((markedSlope_continuous p q).tendsto v).comp hw
  have hdotc : Continuous (fun a : Phase n => stdDot n a a) := (stdDot n).continuous.clm_apply continuous_id
  have hdot := (hdotc.tendsto _).comp hsl
  have hle : d ≤ stdDot n (markedSlope p q v) (markedSlope p q v) := by
    apply ge_of_tendsto hdot
    exact Eventually.of_forall fun i => hlo (t i) (ht i) _ (hu i) _
      (represented_line_slope_nonzero (w i) (hu i)) (markedCurve_asymptote p q (w i))
  intro hz
  simp only [hz,map_zero] at hle
  exact (not_le_of_gt hd) hle

lemma completed_line_closed_bp240_oai {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1) (hout : ∀ x,S < capacity x →J x=standardJ n)
    {p q : Phase n} (hpq : p≠q) {t : ℕ → ℝ} (ht : ∀ i,t i∈Icc (0:ℝ) 1)
    {s : ℝ} (hs : Tendsto t atTop (𝓝 s))
    {w : ℕ → COne ℂ (Phase n)} {v : COne ℂ (Phase n)} (hw : Tendsto w atTop (𝓝 v))
    (hw0 : ∀ i,cValue (w i) 0=0)
    (hu : ∀ i,AffineLineCurve (lineHomotopy J (t i)) p q (markedCurve p q (w i))) :
    AffineLineCurve (lineHomotopy J s) p q (markedCurve p q v) := by
  have hsI : s∈Icc (0:ℝ) 1 := isClosed_Icc.mem_of_tendsto hs (Eventually.of_forall ht)
  have hv0 : cValue v 0=0 := tendsto_nhds_unique (((jetEval 0).continuous.tendsto v).comp hw)
    (by simpa only [Function.comp_def,jetEval_apply,hw0] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:Phase n)) atTop (𝓝 0)))
  have ha := completed_line_slope_limit_nonzero hJs hJ hJc hST hT hout hpq ht hw hu
  have hcr := completed_line_cr_closed hJs hJ hsI hs hw hu
  obtain ⟨B,hB⟩ := compact_structure_norm_standard (lineHomotopy_compact hJc hsI)
  have hcomp := lineHomotopy_compatible hJ hsI
  refine ⟨completed_markedCurve_contDiff_bp240 (lineHomotopy_slice_contDiff hJs hJ hsI) hcomp hB p q v ha hcr,
    ?_,markedCurve_zero p q hv0,markedCurve_one p q v,markedSlope p q v,ha,markedCurve_asymptote p q v⟩
  intro z
  exact ⟨(markedCurve_hasFDerivAt p q v z).differentiableAt,
    realCR_axis_implies_all _ (hcomp _).1 _ (hcr z)⟩


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
open HolderCompletion



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.completed_line_closed_bp240_oai := @OAI.HigherDimensionalBallPacking.Rigidity.completed_line_closed_bp240_oai
