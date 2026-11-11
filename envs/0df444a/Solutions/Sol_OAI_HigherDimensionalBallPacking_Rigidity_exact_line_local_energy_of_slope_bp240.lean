-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.exact_line_local_energy_of_slope_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:55:27.244117+00:00
-- url     : https://prove2.me/submissions/39b8ffc2-5d5a-4353-af32-ee8f869f4f79

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp021
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_exact_line_homotopy_residual_energy_bound_bp240

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_CompatibleStructures
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrame_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedDX_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedQ_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedStructureJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficientHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficient_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrderHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrder_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frozenTargetCoefficient_zero _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothAlongJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothMarkedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.capacity_eq_stdDot _root_.OAI.HigherDimensionalBallPacking.Rigidity.geometricHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.lineHomotopy_one _root_.OAI.HigherDimensionalBallPacking.Rigidity.lineHomotopy_zero _root_.OAI.HigherDimensionalBallPacking.Rigidity.normalizedPrimitive_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.realCurve_zero _root_.OAI.HigherDimensionalBallPacking.Rigidity.stdDot_J_right _root_.OAI.HigherDimensionalBallPacking.Rigidity.stdOmega_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HigherDimensionalBallPacking
open scoped ContDiff

noncomputable section
open scoped Topology
open Set Function Filter

namespace Rigidity

theorem complex_differentiable_of_CR {n : ℕ} {u : ℂ → Phase n} {z : ℂ}
    (hu : DifferentiableAt ℝ u z)
    (hCR : ∀ w : ℂ, fderiv ℝ u z (Complex.I * w) = standardJ n (fderiv ℝ u z w)) :
    DifferentiableAt ℂ u z := by
  let A := fderiv ℝ u z
  let L : ℂ →L[ℂ] Phase n := (ContinuousLinearMap.id ℂ ℂ).smulRight (A 1)
  have hL : L.restrictScalars ℝ = A := by
    ext w i
    have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by
      simpa only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_one, mul_one]
        using (Complex.re_add_im w).symm
    have hI : A Complex.I = standardJ n (A 1) := by
      simpa only [mul_one] using hCR 1
    have hAw : A w = w.re • A 1 + w.im • standardJ n (A 1) := by
      conv_lhs => rw [hw]
      simp only [map_add, map_smul, hI]
    rw [hAw]
    change w * A 1 i = _
    simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul, standardJ_apply]
    rw [←mul_assoc, ←add_mul]
    congr 1
    exact (Complex.re_add_im w).symm
  exact (hasFDerivAt_of_restrictScalars ℝ hu.hasFDerivAt hL).differentiableAt

end Rigidity
end
end HigherDimensionalBallPacking

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
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrame_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedDX_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedQ_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedStructureJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficientHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficient_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrderHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrder_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frozenTargetCoefficient_zero _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothMarkedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.capacity_eq_stdDot _root_.OAI.HigherDimensionalBallPacking.Rigidity.geometricHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.normalizedPrimitive_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.realCurve_zero _root_.OAI.HigherDimensionalBallPacking.Rigidity.stdDot_J_right _root_.OAI.HigherDimensionalBallPacking.Rigidity.stdOmega_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology Manifold
open Set Function Filter


theorem closedBall_isClosed (n : ℕ) (R : ℝ) : IsClosed (closedBall n R) :=
  isClosed_le (continuous_capacity n) continuous_const

theorem closedBall_isCompact (n : ℕ) (R : ℝ) : IsCompact (closedBall n R) := by
  apply (isCompact_closedBall (0 : Phase n) (max R 0 + 1)).of_isClosed_subset
    (closedBall_isClosed n R)
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ max R 0 + 1)).mpr
  intro j
  have hj : Complex.normSq (z j) ≤ ∑ k, Complex.normSq (z k) :=
    Finset.single_le_sum (fun k _ => Complex.normSq_nonneg (z k)) (Finset.mem_univ j)
  have hj' := mul_le_mul_of_nonneg_left hj Real.pi_pos.le
  have hq : 0 ≤ Complex.normSq (z j) := Complex.normSq_nonneg (z j)
  have hs : (∑ k, Complex.normSq (z k)) * Real.pi ≤ R := by
    simpa [closedBall, capacity, mul_comm] using hz
  have hb : Complex.normSq (z j) ≤ max R 0 := by
    nlinarith [Real.pi_gt_three, le_max_left R 0]
  rw [Complex.normSq_eq_norm_sq] at hb
  have hm := le_max_right R 0
  nlinarith [sq_nonneg (‖z j‖ - 1)]


end

section
open scoped ContDiff Topology
open Set Function Filter

theorem lineHomotopy_compatible {n : ℕ} {J : Phase n → End n}
    (hJ : ∀ x, Compatible (J x)) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (x : Phase n) :
    Compatible (lineHomotopy J t x) := compatible_interpolateJ (hJ x) ht

theorem lineHomotopy_smooth {n : ℕ} {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x)) :
    ContDiffOn ℝ ∞ (fun y : ℝ × Phase n => lineHomotopy J y.1 y.2)
      ((Icc (0:ℝ) 1) ×ˢ univ) := by
  intro y hy
  exact (contDiffAt_interpolateJ (hJs.contDiffAt.comp y contDiffAt_snd)
    contDiffAt_fst (hJ y.2) hy.1).contDiffWithinAt

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
attribute [-instance] _root_.OAI.HigherDimensionalBallPacking.Rigidity.squareMeasure_finite _root_.OAI.HigherDimensionalBallPacking.Rigidity.translatedSquare_finite _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.parameters_nonzero _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrame_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedDX_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedQ_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedStructureJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficientHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficient_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrderHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrder_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frozenTargetCoefficient_zero _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothMarkedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.geometricHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.normalizedPrimitive_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.realCurve_zero _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.SymplecticBallPacking.Hamiltonian.coordinateForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

theorem stdDot_standardForm_sq_le {n : ℕ} (z v : Phase n) :
    (stdDot n z v)^2 + (standardForm z v)^2 ≤ stdDot n z z * stdDot n v v := by
  let z' : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 z
  let v' : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 v
  have hr : (inner ℂ z' v').re = stdDot n z v := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, Complex.re_sum, Complex.mul_re,
      Complex.conj_re, Complex.conj_im, mul_neg, sub_neg_eq_add, stdDot_apply]
    apply Finset.sum_congr rfl
    intro i _
    change (v i).re * (z i).re + (v i).im * (z i).im = _
    ring
  have hi : (inner ℂ z' v').im = standardForm z v := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, Complex.im_sum, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, standardForm]
    apply Finset.sum_congr rfl
    intro i _
    change (v i).re * (-(z i).im) + (v i).im * (z i).re = _
    ring
  have hz : ‖z'‖^2 = stdDot n z z := by
    simp only [EuclideanSpace.norm_sq_eq, stdDot_apply, ←Complex.normSq_eq_norm_sq,
      Complex.normSq_apply]
    rfl
  have hv : ‖v'‖^2 = stdDot n v v := by
    simp only [EuclideanSpace.norm_sq_eq, stdDot_apply, ←Complex.normSq_eq_norm_sq,
      Complex.normSq_apply]
    rfl
  have hh := (sq_le_sq₀ (norm_nonneg (inner ℂ z' v'))
    (mul_nonneg (norm_nonneg z') (norm_nonneg v'))).mpr (norm_inner_le_norm z' v')
  rw [←Complex.normSq_eq_norm_sq, Complex.normSq_apply, hr, hi, mul_pow, hz, hv] at hh
  nlinarith only [hh]

theorem linear_asymptotic_norm_tendsto {n : ℕ} {u : ℂ → Phase n} {v : Phase n}
    (hv : v ≠ 0) (hlim : Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 v)) :
    Tendsto (fun z => ‖u z‖) (cocompact ℂ) atTop := by
  have hp : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hev : ∀ᶠ z : ℂ in cocompact ℂ, ‖v‖ / 2 < ‖z⁻¹ • u z‖ :=
    (tendsto_order.mp hlim.norm).1 _ (by linarith)
  have hb : (fun z : ℂ => (‖v‖ / 2) * ‖z‖) ≤ᶠ[cocompact ℂ] fun z => ‖u z‖ := by
    filter_upwards [hev,(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz hz0
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr (by simpa using hz0)
    rw [norm_smul,norm_inv,inv_mul_eq_div] at hz
    exact ((lt_div_iff₀ hn).mp hz).le
  exact tendsto_atTop_mono' _ hb
    (Tendsto.const_mul_atTop (by linarith : 0 < ‖v‖ / 2) tendsto_norm_cocompact_atTop)

theorem AffineLineCurve.tendsto_cocompact {n : ℕ} {J : Phase n → End n}
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u) :
    Tendsto u (cocompact ℂ) (cocompact (Phase n)) := by
  obtain ⟨v,hv,hlim⟩ := hu.2.2.2.2
  rw [←Metric.cobounded_eq_cocompact (α := Phase n),←tendsto_norm_atTop_iff_cobounded]
  exact linear_asymptotic_norm_tendsto hv hlim

theorem AffineLineCurve.isProperMap {n : ℕ} {J : Phase n → End n}
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u) : IsProperMap u :=
  isProperMap_iff_tendsto_cocompact.mpr ⟨hu.1.continuous,hu.tendsto_cocompact⟩

theorem AffineLineCurve.holomorphic_at_infinity {n : ℕ} {J : Phase n → End n}
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u)
    (hJc : HasCompactSupport (fun x => J x - standardJ n)) :
    ∀ᶠ z in cocompact ℂ, DifferentiableAt ℂ u z := by
  filter_upwards [hu.tendsto_cocompact.eventually hJc.compl_mem_cocompact] with z hz
  have hJ : J (u z) = standardJ n :=
    sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport (f := fun x => J x - standardJ n) hz)
  apply complex_differentiable_of_CR (hu.2.1 z).1
  intro w
  rw [(hu.2.1 z).2,hJ]

theorem infinityGerm_eventuallyEq {n : ℕ} (u : ℂ → Phase n) (v : Phase n)
    {w : ℂ} (hw : w ≠ 0) :
    infinityGerm u v =ᶠ[𝓝 w] fun z => z • u z⁻¹ := by
  filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hw] with z hz
  exact ite_eq_right hz

theorem infinityGerm_analyticAt {n : ℕ} {u : ℂ → Phase n} {v : Phase n}
    (hholo : ∀ᶠ z in cocompact ℂ, DifferentiableAt ℂ u z)
    (hlim : Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 v)) :
    AnalyticAt ℂ (infinityGerm u v) 0 := by
  have hi : Tendsto (fun w : ℂ => w⁻¹) (𝓝[≠] 0) (cocompact ℂ) := by
    rw [←Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_nhdsNE_zero
  have ht : Tendsto (fun w : ℂ => w • u w⁻¹) (𝓝[≠] 0) (𝓝 v) := by
    simpa only [Function.comp_def,inv_inv] using hlim.comp hi
  have he : infinityGerm u v = Function.update (fun w : ℂ => w • u w⁻¹) 0 v := by
    classical
    funext w
    by_cases hw : w = 0
    · subst w; simp [infinityGerm]
    · simp [infinityGerm,hw]
  have hc : ContinuousAt (infinityGerm u v) 0 := by
    classical
    rw [he,continuousAt_update_same]
    exact ht
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _ hc
  filter_upwards [hi.eventually hholo,self_mem_nhdsWithin] with w hw hw0
  have hn : w ≠ 0 := hw0
  have hd : DifferentiableAt ℂ (fun z : ℂ => z • u z⁻¹) w :=
    differentiableAt_id.smul (hw.comp w (differentiableAt_id.inv hn))
  exact hd.congr_of_eventuallyEq (infinityGerm_eventuallyEq u v hn)

end HigherDimensionalBallPacking.Rigidity

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

theorem HasCompactSupport.comp_square {F : Type*} [Zero F] {g : ℝ → F}
    (hg : HasCompactSupport g) : HasCompactSupport (fun x : ℝ => g (x^2)) := by
  simpa only [radiusSq,zero_pow (by decide : (2:ℕ)≠0),add_zero] using
    HasCompactSupport.left_slice (HasCompactSupport.comp_radiusSq hg) 0

theorem integral_radial_derivative {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) : (∫ z : Plane,2*deriv g (radiusSq z))= -2*Real.pi*g 0 := by
  let h : ℝ → ℝ := fun r => g (r^2)
  have hh : ContDiff ℝ ∞ h := hg.comp (contDiff_id.pow 2)
  have hhC : HasCompactSupport h := HasCompactSupport.comp_square hc
  have hd (r : ℝ) : deriv h r=2*r*deriv g (r^2) := by
    have H := (hg.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (r^2)).hasDerivAt.comp r ((hasDerivAt_id r).pow 2)
    change HasDerivAt h _ r at H
    rw [H.deriv]
    simp only [Nat.cast_ofNat,mul_one,id_eq]
    norm_num
    ring
  rw [← integral_comp_polarCoord_symm]
  have he : (fun p : Plane => p.1 • (2*deriv g (radiusSq (polarCoord.symm p))))=
      (fun p : Plane => deriv h p.1 * (1 : ℝ)) := by
    funext p
    rw [radiusSq_polar,hd]
    simp only [smul_eq_mul]
    ring
  rw [he,polarCoord_target,Measure.volume_eq_prod,setIntegral_prod_mul (deriv h) (fun _ : ℝ => (1 : ℝ)),
    HasCompactSupport.integral_Ioi_deriv_eq (hh.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hhC]
  simp only [h,zero_pow (by decide : (2:ℕ)≠0),integral_const,smul_eq_mul,
    Measure.real,Measure.restrict_apply_univ,Real.volume_Ioo]
  rw [ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : 0≤Real.pi-(-Real.pi))]
  ring

theorem radiusSq_hasFDerivAt (z : Plane) :
    HasFDerivAt radiusSq ((2:ℝ) • planarDot z) z := by
  have H := (((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt (x := z)).pow 2).add
    (((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt (x := z)).pow 2)
  change HasFDerivAt radiusSq _ z at H
  apply H.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  change (2 • z.1^(2-1))*v.1+(2 • z.2^(2-1))*v.2=2*(z.1*v.1+z.2*v.2)
  norm_num
  ring

end SymplecticBallPacking.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_PlanarResidueCutoff
attribute [-instance] _root_.OAI.HigherDimensionalBallPacking.Rigidity.squareMeasure_finite _root_.OAI.HigherDimensionalBallPacking.Rigidity.translatedSquare_finite _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.realCurve_zero _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.SymplecticBallPacking.Hamiltonian.coordinateForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SymplecticBallPacking.Hamiltonian
open Set Function MeasureTheory Filter
open scoped ContDiff Topology

theorem planarCurl_contDiff {β : Plane → Plane →L[ℝ] ℝ} (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (planarCurl β) :=
  (((hβ.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const).clm_apply contDiff_const).sub
    (((hβ.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const).clm_apply contDiff_const)

theorem planarCurl_compact {β : Plane → Plane →L[ℝ] ℝ} (hβ : HasCompactSupport β) :
    HasCompactSupport (planarCurl β) := by
  exact ((hβ.fderiv_apply (𝕜 := ℝ) (1,0)).comp_left
    (g := fun L : Plane →L[ℝ] ℝ => L (0,1)) rfl).sub
    ((hβ.fderiv_apply (𝕜 := ℝ) (0,1)).comp_left
    (g := fun L : Plane →L[ℝ] ℝ => L (1,0)) rfl)

theorem planarCurl_spatial_smul {f : Plane → ℝ} {β : Plane → Plane →L[ℝ] ℝ}
    {z : Plane}
    (hf : DifferentiableAt ℝ f z) (hβ : DifferentiableAt ℝ β z) :
    planarCurl (fun y => f y • β y) z=cutoffWedge f β z+f z*planarCurl β z := by
  unfold planarCurl cutoffWedge
  have H := hf.hasFDerivAt.smul hβ.hasFDerivAt
  change HasFDerivAt (fun y => f y • β y) _ z at H
  rw [H.fderiv]
  simp only [add_apply,ContinuousLinearMap.smulRight_apply,smul_apply,smul_eq_mul]
  ring

theorem integral_cutoffWedge {f : Plane → ℝ} {β : Plane → Plane →L[ℝ] ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hβ : ContDiff ℝ ∞ β) :
    (∫ z,cutoffWedge f β z)= -(∫ z,f z*planarCurl β z) := by
  have hp : ContDiff ℝ ∞ (fun z => f z • β z) := hf.smul hβ
  have hpc : HasCompactSupport (fun z => f z • β z) := hc.smul_right
  have hci : Integrable (planarCurl (fun z => f z • β z)) := (planarCurl_contDiff hp).continuous.integrable_of_hasCompactSupport (planarCurl_compact hpc)
  have hgi : Integrable (fun z => f z*planarCurl β z) := (hf.mul (planarCurl_contDiff hβ)).continuous.integrable_of_hasCompactSupport hc.mul_right
  have he : cutoffWedge f β=(fun z => planarCurl (fun y => f y • β y) z-f z*planarCurl β z) := by
    funext z
    rw [planarCurl_spatial_smul (hf.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z) (hβ.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z)]
    ring
  rw [he,integral_sub hci hgi,show (∫ z,planarCurl (fun y => f y • β y) z)=0 from compact_planar_stokes hp hpc,zero_sub]

theorem cutoffWedge_integrable {f : Plane → ℝ} {β : Plane → Plane →L[ℝ] ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hβ : ContDiff ℝ ∞ β) :
    Integrable (cutoffWedge f β) := by
  have h1 : ContDiff ℝ ∞ (fun z => fderiv ℝ f z (1,0)) := (hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply (contDiff_const (c := ((1:ℝ),(0:ℝ))))
  have h2 : ContDiff ℝ ∞ (fun z => fderiv ℝ f z (0,1)) := (hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply (contDiff_const (c := ((0:ℝ),(1:ℝ))))
  exact ((h1.mul (hβ.clm_apply contDiff_const)).continuous.integrable_of_hasCompactSupport
    (hc.fderiv_apply (𝕜 := ℝ) (1,0)).mul_right).sub
    ((h2.mul (hβ.clm_apply contDiff_const)).continuous.integrable_of_hasCompactSupport
    (hc.fderiv_apply (𝕜 := ℝ) (0,1)).mul_right)

end SymplecticBallPacking.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_CurveArea
attribute [-instance] _root_.OAI.HigherDimensionalBallPacking.Rigidity.squareMeasure_finite _root_.OAI.HigherDimensionalBallPacking.Rigidity.translatedSquare_finite _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrame_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedDX_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedQ_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedStructureJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficientHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficient_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrderHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrder_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frozenTargetCoefficient_zero _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothMarkedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.geometricHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.realCurve_zero _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.SymplecticBallPacking.Hamiltonian.coordinateForm_apply
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

theorem realCurve_fderiv {n : ℕ} {u : ℂ → Phase n} {z : Plane}
    (hu : DifferentiableAt ℝ u (Complex.equivRealProdCLM.symm z)) (v : Plane) :
    fderiv ℝ (realCurve u) z v =
      fderiv ℝ u (Complex.equivRealProdCLM.symm z) (Complex.equivRealProdCLM.symm v) := by
  rw [realCurve, fderiv_comp z hu Complex.equivRealProdCLM.symm.differentiableAt]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.fderiv]

theorem realCurve_CR {n : ℕ} {J : Phase n → End n} {u : ℂ → Phase n} {z : Plane}
    (hu : PseudoHolomorphicAt J u (Complex.equivRealProdCLM.symm z)) :
    fderiv ℝ (realCurve u) z (0,1) =
      J (realCurve u z) (fderiv ℝ (realCurve u) z (1,0)) := by
  rw [realCurve_fderiv hu.1,realCurve_fderiv hu.1]
  simpa only [Complex.equivRealProdCLM_symm_apply, Complex.ofReal_zero, Complex.ofReal_one,
    zero_mul,one_mul,add_zero,zero_add,mul_one,realCurve,Function.comp_def] using hu.2 1

theorem planarPullback_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : Plane → E} {α : E → E →L[ℝ] ℝ}
    (hv : ContDiff ℝ ∞ v) (hα : ContDiff ℝ ∞ α) :
    ContDiff ℝ ∞ (planarPullback v α) :=
  (hα.comp hv).clm_comp (hv.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))

theorem oneForm_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α : E → E →L[ℝ] ℝ} (hα : ContDiff ℝ ∞ α) : ContDiff ℝ ∞ (oneForm α) :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ)
    (0 : Fin 1)).toContinuousLinearEquiv.contDiff.comp hα

theorem planarCurl_eq_extDeriv {α : Plane → Plane →L[ℝ] ℝ}
    (hα : ContDiff ℝ ∞ α) (z : Plane) :
    planarCurl α z = extDeriv (oneForm α) z ![(1,0),(0,1)] := by
  rw [extDeriv_apply ((oneForm_smooth hα).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z)]
  rw [Fin.sum_univ_succ]
  simp only [Fin.sum_univ_one, Fin.val_zero, pow_zero, one_smul, Fin.val_succ,
    pow_one, neg_smul, zero_add]
  change planarCurl α z =
    fderiv ℝ (fun y => α y (0,1)) z (1,0) - fderiv ℝ (fun y => α y (1,0)) z (0,1)
  rw [fderiv_clm_apply (hα.differentiable (by simp) z) (differentiableAt_const _),
    fderiv_clm_apply (hα.differentiable (by simp) z) (differentiableAt_const _)]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    fderiv_const_apply, zero_apply, map_zero, zero_add]
  rfl

theorem planarPullback_curl {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : Plane → E} {α : E → E →L[ℝ] ℝ}
    (hv : ContDiff ℝ ∞ v) (hα : ContDiff ℝ ∞ α) (z : Plane) :
    planarCurl (planarPullback v α) z =
      extDeriv (oneForm α) (v z) ![fderiv ℝ v z (1,0), fderiv ℝ v z (0,1)] := by
  rw [planarCurl_eq_extDeriv (planarPullback_smooth hv hα)]
  have he : oneForm (planarPullback v α) = fun y =>
      (oneForm α (v y)).compContinuousLinearMap (fderiv ℝ v y) := by
    funext y
    ext w
    rfl
  rw [he,extDeriv_pullback ((oneForm_smooth hα).differentiable (by simp) (v z))
    hv.contDiffAt (by
      norm_num [minSmoothness] <;> first | done | exact WithTop.coe_le_coe.mpr le_top)]
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  ext i
  fin_cases i <;> rfl


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_Correction
attribute [-instance] _root_.OAI.HigherDimensionalBallPacking.Rigidity.squareMeasure_finite _root_.OAI.HigherDimensionalBallPacking.Rigidity.translatedSquare_finite _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.SymplecticBallPacking.Hamiltonian.coordinateForm_apply
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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem oneForm_extDeriv_apply {α : E → E →L[ℝ] ℝ} {x : E}
    (hα : DifferentiableAt ℝ α x) (v w : E) :
    extDeriv (oneForm α) x ![v,w] = fderiv ℝ α x v w - fderiv ℝ α x w v := by
  have hω : DifferentiableAt ℝ (oneForm α) x :=
    (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ)
      (0 : Fin 1)).toContinuousLinearEquiv.differentiableAt.comp x hα
  rw [extDeriv_apply hω,Fin.sum_univ_succ]
  simp only [Fin.sum_univ_one, Fin.val_zero, pow_zero, one_smul, Fin.val_succ,
    pow_one, neg_smul, zero_add]
  change fderiv ℝ (fun y => α y w) x v - fderiv ℝ (fun y => α y v) x w = _
  rw [fderiv_clm_apply hα (differentiableAt_const w),
    fderiv_clm_apply hα (differentiableAt_const v)]
  simp


end

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

theorem outerProfile_zero_value {A : ℝ} (hA : 0 < A) : outerProfile A 0 = 1 := by
  have h : (0-A)/A ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hA.le
  simp only [outerProfile,zero_add,Real.smoothTransition.one_of_one_le (by norm_num : (1:ℝ)≤2),
    Real.smoothTransition.zero_of_nonpos h,sub_zero,mul_one]

theorem outerProfile_deriv {A t : ℝ} (ht : 0 ≤ t) :
    deriv (outerProfile A) t = -(deriv Real.smoothTransition ((t-A)/A) / A) := by
  have he : outerProfile A =ᶠ[𝓝 t] fun s => 1 - Real.smoothTransition ((s-A)/A) := by
    filter_upwards [isOpen_Ioi.mem_nhds (by linarith : (-1:ℝ) < t)] with s hs
    have hs' : -1 < s := hs
    simp only [outerProfile,Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ s + 2),one_mul]
  rw [he.deriv_eq]
  have hs : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hh := (hs.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) ((t-A)/A)).hasDerivAt.comp t
    (((hasDerivAt_id t).sub_const A).div_const A)
  have hd := hh.const_sub 1
  change HasDerivAt (fun s => 1 - Real.smoothTransition ((s-A)/A)) _ t at hd
  rw [hd.deriv]
  simp only [div_eq_mul_inv,one_mul]

theorem outerProfile_deriv_nonpos {A t : ℝ} (hA : 0 < A) (ht : 0 ≤ t) :
    deriv (outerProfile A) t ≤ 0 := by
  rw [outerProfile_deriv ht]
  exact neg_nonpos.mpr (div_nonneg Real.smoothTransition.monotone.deriv_nonneg hA.le)

theorem outerProfile_deriv_zero_before {A t : ℝ} (hA : 0 < A) (ht : 0 ≤ t) (htA : t < A) :
    deriv (outerProfile A) t = 0 := by
  have he : outerProfile A =ᶠ[𝓝 t] fun _ => 1 := by
    filter_upwards [isOpen_Ioo.mem_nhds (show t ∈ Ioo (-1:ℝ) A from ⟨by linarith,htA⟩)] with s hs
    have hn : (s-A)/A ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith [hs.2]) hA.le
    simp only [outerProfile,Real.smoothTransition.one_of_one_le (by linarith [hs.1] : 1 ≤ s + 2),
      Real.smoothTransition.zero_of_nonpos hn,sub_zero,mul_one]
  rw [he.deriv_eq,deriv_const]

theorem cutoffWedge_radial_rotation {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (β : Plane → Plane →L[ℝ] ℝ) (z : Plane) :
    cutoffWedge (fun y => g (radiusSq y)) β z =
      2 * deriv g (radiusSq z) * β z (planeRotation z) := by
  have hh := (hg.differentiable (by simp) (radiusSq z)).hasDerivAt.comp_hasFDerivAt z
    (radiusSq_hasFDerivAt z)
  change HasFDerivAt (fun y => g (radiusSq y)) _ z at hh
  have he : planeRotation z = (-z.2) • ((1,0) : Plane) + z.1 • (0,1) := by
    ext <;> simp [planeRotation]
  unfold cutoffWedge
  rw [hh.fderiv, he,map_add,map_smul,map_smul]
  simp only [smul_apply,smul_eq_mul,planarDot_apply]
  simp only [mul_one,mul_zero,add_zero,zero_add]
  ring



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_AngularPoles
attribute [-instance] _root_.OAI.HigherDimensionalBallPacking.Rigidity.squareMeasure_finite _root_.OAI.HigherDimensionalBallPacking.Rigidity.translatedSquare_finite _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.SymplecticBallPacking.Hamiltonian.coordinateForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian (Plane)

theorem equivRealProd_rotation (z : Plane) :
    Complex.equivRealProdCLM.symm (planeRotation z) =
      Complex.I * Complex.equivRealProdCLM.symm z := by
  apply Complex.ext <;> simp [planeRotation,Complex.equivRealProdCLM_symm_apply]



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Compactness_AffineCorrectionInfinity
attribute [-instance] _root_.OAI.HigherDimensionalBallPacking.Rigidity.squareMeasure_finite _root_.OAI.HigherDimensionalBallPacking.Rigidity.translatedSquare_finite _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrame_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedDX_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedQ_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedStructureJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficientHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficient_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrderHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrder_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frozenTargetCoefficient_zero _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothAlongJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothMarkedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.geometricHolder_value _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open SymplecticBallPacking.Hamiltonian (Plane)
namespace HigherDimensionalBallPacking.Rigidity
variable {n : ℕ}

lemma analyticAt_dslope_zero {h : ℂ → Phase n} (hh : AnalyticAt ℂ h 0) :
    AnalyticAt ℂ (dslope h 0) 0 := by
  obtain ⟨P,hP⟩ := hh
  exact ⟨P.fslope,hP.has_fpower_series_dslope_fslope⟩

lemma infinityGerm_affine_reconstruction (u : ℂ → Phase n) (a : Phase n) {z : ℂ} (hz : z≠0) :
    u z=z • a+dslope (infinityGerm u a) 0 z⁻¹ := by
  rw [dslope_of_ne _ (inv_ne_zero hz),slope,sub_zero]
  simp only [infinityGerm,inv_ne_zero hz,ite_false, if_false,inv_inv,ite_true, if_true,vsub_eq_sub]
  rw [smul_sub,smul_smul,mul_inv_cancel₀ hz,one_smul]
  abel

lemma analytic_inverse_angular_fderiv_limit {h : ℂ → Phase n} (hh : AnalyticAt ℂ h 0) :
    Tendsto (fun z : ℂ => fderiv ℝ (fun w : ℂ => h w⁻¹) z (Complex.I*z))
      (cocompact ℂ) (𝓝 0) := by
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa only [←Metric.cobounded_eq_cocompact] using (tendsto_inv₀_cobounded (α := ℂ))
  have hc : ContDiffAt ℝ ∞ h 0 := hh.contDiffAt.restrict_scalars ℝ
  have hdh : Tendsto (fun z : ℂ => fderiv ℝ h z⁻¹) (cocompact ℂ) (𝓝 (fderiv ℝ h 0)) :=
    (hc.fderiv_right (m := 0) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuousAt.tendsto.comp hi
  have harg : Tendsto (fun z : ℂ => -Complex.I*z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa using hi.const_mul (-Complex.I)
  have hvec : Tendsto (fun z : ℂ => fderiv ℝ h z⁻¹ (-Complex.I*z⁻¹))
      (cocompact ℂ) (𝓝 0) := by
    simpa only [Function.comp_def,map_zero] using
      (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp (hdh.prodMk_nhds harg)
  have hd : ∀ᶠ w in 𝓝 (0:ℂ), DifferentiableAt ℝ h w :=
    hh.eventually_analyticAt.mono fun _ hx => hx.differentiableAt.restrictScalars ℝ
  apply hvec.congr'
  filter_upwards [hi.eventually hd,(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz hz0
  have hid := (hasDerivAt_inv hz0).hasFDerivAt.restrictScalars ℝ
  have hder := hz.hasFDerivAt.comp z hid
  change HasFDerivAt (fun w : ℂ => h w⁻¹) _ z at hder
  rw [hder.fderiv]
  change fderiv ℝ h z⁻¹ (-Complex.I*z⁻¹)=
    fderiv ℝ h z⁻¹ ((Complex.I*z) • (-(z^2)⁻¹))
  rw [smul_eq_mul]
  congr 1
  field_simp

lemma affineCorrection_smooth {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (a : Phase n) :
    ContDiff ℝ ∞ (affineCorrection u a) := hu.sub (contDiff_id.smul contDiff_const)

lemma affineCorrection_locally_inverse {u : ℂ → Phase n} {a : Phase n} {h : ℂ → Phase n}
    (he : ∀ z : ℂ, z≠0 → u z=z • a+h z⁻¹) {z : ℂ} (hz : z≠0) :
    affineCorrection u a =ᶠ[𝓝 z] fun w : ℂ => h w⁻¹ := by
  filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hz] with w hw
  rw [affineCorrection,he w hw]
  abel

lemma affineCorrection_limit {u : ℂ → Phase n} {a : Phase n} {h : ℂ → Phase n}
    (hh : AnalyticAt ℂ h 0) (he : ∀ z : ℂ, z≠0 → u z=z • a+h z⁻¹) :
    Tendsto (affineCorrection u a) (cocompact ℂ) (𝓝 (h 0)) := by
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa only [←Metric.cobounded_eq_cocompact] using (tendsto_inv₀_cobounded (α := ℂ))
  apply (hh.continuousAt.tendsto.comp hi).congr'
  filter_upwards [(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz
  exact ((affineCorrection_locally_inverse he hz).self_of_nhds).symm

lemma affineCorrection_angular_fderiv_limit {u : ℂ → Phase n} {a : Phase n} {h : ℂ → Phase n}
    (hh : AnalyticAt ℂ h 0) (he : ∀ z : ℂ, z≠0 → u z=z • a+h z⁻¹) :
    Tendsto (fun z : ℂ => fderiv ℝ (affineCorrection u a) z (Complex.I*z))
      (cocompact ℂ) (𝓝 0) := by
  apply (analytic_inverse_angular_fderiv_limit hh).congr'
  filter_upwards [(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz
  rw [(affineCorrection_locally_inverse he hz).fderiv_eq]

lemma affineCorrection_primitive_flux_zero {u : ℂ → Phase n} {a : Phase n} {h : ℂ → Phase n}
    (hh : AnalyticAt ℂ h 0) (he : ∀ z : ℂ, z≠0 → u z=z • a+h z⁻¹) :
    Tendsto (fun z : ℂ => stdOmega n (affineCorrection u a z)
      (fderiv ℝ (affineCorrection u a) z (Complex.I*z))) (cocompact ℂ) (𝓝 0) := by
  have hv := affineCorrection_limit hh he
  have hd := affineCorrection_angular_fderiv_limit hh he
  have ho : Tendsto (fun z => stdOmega n (affineCorrection u a z))
      (cocompact ℂ) (𝓝 (stdOmega n (h 0))) := (stdOmega n).continuous.continuousAt.tendsto.comp hv
  simpa only [Function.comp_def,map_zero] using
    (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp (ho.prodMk_nhds hd)

end HigherDimensionalBallPacking.Rigidity

end
noncomputable section
open scoped ContDiff Topology
open Set Filter
namespace HigherDimensionalBallPacking.Rigidity
variable {n : ℕ}

local instance ceInst1_r424994_1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance ceInst2_r424994_1 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
lemma defectEnergy_standard (v : Phase n) : defectEnergy (standardJ n) v=0 := by
  simp only [defectEnergy,sub_self,zero_apply,map_zero]

lemma defectEnergy_smul (A : End n) (r : ℝ) (v : Phase n) :
    defectEnergy A (r • v)=r^2*defectEnergy A v := by
  simp only [defectEnergy,map_smul,smul_apply,smul_eq_mul]
  ring

lemma symplecticEnergy_smul (A : End n) (r : ℝ) (v : Phase n) :
    symplecticEnergy A (r • v)=r^2*symplecticEnergy A v := by
  simp only [symplecticEnergy,map_smul,smul_apply,smul_eq_mul]
  ring

lemma symplecticEnergy_pos {A : End n} (hA : Compatible A) {v : Phase n} (hv : v≠0) :
    0 < symplecticEnergy A v := by
  rw [symplecticEnergy,stdOmega_apply]
  exact hA.2.2 v hv

lemma defectEnergy_continuous : Continuous (fun z : End n × Phase n => defectEnergy z.1 z.2) := by
  have h : Continuous (fun z : End n × Phase n => (z.1-standardJ n) z.2) :=
    (continuous_fst.sub continuous_const).clm_apply continuous_snd
  exact (((stdDot n).continuous.comp h).clm_apply h)

lemma symplecticEnergy_continuous : Continuous (fun z : End n × Phase n => symplecticEnergy z.1 z.2) := by
  exact ((stdOmega n).continuous.comp continuous_snd).clm_apply (continuous_fst.clm_apply continuous_snd)

lemma energyRatio_continuousOn {X : Type*} [TopologicalSpace X]
    {K : Set X} {A : X → End n} (hAc : ContinuousOn A K)
    (hA : ∀ x∈K, Compatible (A x)) :
    ContinuousOn (fun z : X × Phase n => defectEnergy (A z.1) z.2 / symplecticEnergy (A z.1) z.2)
      (K ×ˢ Metric.sphere (0:Phase n) 1) := by
  have hpair : ContinuousOn (fun z : X × Phase n => (A z.1,z.2))
      (K ×ˢ Metric.sphere (0:Phase n) 1) :=
    (hAc.comp continuous_fst.continuousOn (fun _ h => h.1)).prodMk continuous_snd.continuousOn
  apply (defectEnergy_continuous.comp_continuousOn hpair).div
    (symplecticEnergy_continuous.comp_continuousOn hpair)
  intro z hz
  apply (symplecticEnergy_pos (hA z.1 hz.1) ?_).ne'
  have hn : ‖z.2‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hz.2
  exact norm_ne_zero_iff.mp (by rw [hn]; norm_num)

lemma energyRatio_bounded_on_sphere {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) {A : X → End n} (hAc : ContinuousOn A K)
    (hA : ∀ x∈K, Compatible (A x)) :
    ∃ B : ℝ, 0<B ∧ ∀ x∈K, ∀ v : Phase n, ‖v‖=1 →
      defectEnergy (A x) v≤B*symplecticEnergy (A x) v := by
  let f (z : X × Phase n) : ℝ := defectEnergy (A z.1) z.2 / symplecticEnergy (A z.1) z.2
  have hf : ContinuousOn f (K ×ˢ Metric.sphere (0:Phase n) 1) := energyRatio_continuousOn hAc hA
  have hL : IsCompact (K ×ˢ Metric.sphere (0:Phase n) 1) := hK.prod (isCompact_sphere _ _)
  obtain ⟨B,hB,hbound⟩ := (hL.image_of_continuousOn hf).isBounded.exists_pos_norm_le
  refine ⟨B,hB,?_⟩
  intro x hx v hv
  have hwL : (x,v)∈K ×ˢ Metric.sphere (0:Phase n) 1 :=
    ⟨hx,by simpa only [Metric.mem_sphere,dist_zero_right] using hv⟩
  have hnorm := hbound (f (x,v)) ⟨(x,v),hwL,rfl⟩
  have hb : f (x,v)≤B := (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hnorm)
  have hv0 : v≠0 := norm_ne_zero_iff.mp (by rw [hv]; norm_num)
  exact (div_le_iff₀ (symplecticEnergy_pos (hA x hx) hv0)).mp hb

lemma energyRatio_extend_from_sphere {A : End n} {B : ℝ}
    (hB : ∀ w : Phase n, ‖w‖=1 → defectEnergy A w≤B*symplecticEnergy A w)
    (v : Phase n) : defectEnergy A v≤B*symplecticEnergy A v := by
  by_cases hv : v=0
  · subst v
    simp [defectEnergy,symplecticEnergy]
  let w : Phase n := ‖v‖⁻¹ • v
  have hnv : ‖v‖≠0 := norm_ne_zero_iff.mpr hv
  have hw : ‖w‖=1 := by
    simp only [w,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,inv_mul_cancel₀ hnv]
  have hratio := hB w hw
  rw [show w=‖v‖⁻¹ • v from rfl,defectEnergy_smul,symplecticEnergy_smul] at hratio
  have hp : 0<(‖v‖⁻¹)^2 := sq_pos_of_ne_zero (inv_ne_zero hnv)
  apply (mul_le_mul_iff_right₀ hp).mp
  calc
    (‖v‖⁻¹)^2*defectEnergy A v ≤ B*((‖v‖⁻¹)^2*symplecticEnergy A v) := hratio
    _ = (‖v‖⁻¹)^2*(B*symplecticEnergy A v) := by ring

lemma exists_defectEnergy_bound {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) {A : X → End n} (hAc : ContinuousOn A K)
    (hA : ∀ x∈K, Compatible (A x)) :
    ∃ C : ℝ, 0<C ∧ ∀ x∈K, ∀ v : Phase n,
      defectEnergy (A x) v≤C*symplecticEnergy (A x) v := by
  obtain ⟨B,hB,hbound⟩ := energyRatio_bounded_on_sphere hK hAc hA
  exact ⟨B,hB,fun x hx v => energyRatio_extend_from_sphere (hbound x hx) v⟩

end HigherDimensionalBallPacking.Rigidity

end
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

lemma radiusSq_pos_bound_of_compact {K : Set Plane} (hK : IsCompact K) :
    ∃ A : ℝ, 0<A ∧ ∀ z∈K, radiusSq z<A := by
  obtain ⟨B,hB,hb⟩ := (hK.image radiusSq_smooth.continuous).isBounded.exists_pos_norm_le
  refine ⟨B+1,by linarith,?_⟩
  intro z hz
  have hh := hb (radiusSq z) ⟨z,hz,rfl⟩
  rw [Real.norm_eq_abs,abs_of_nonneg (radiusSq_nonneg z)] at hh
  linarith

end HigherDimensionalBallPacking.Rigidity

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

variable {n : ℕ}

local instance gcInst1_r424994_1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance gcInst2_r424994_1 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
local instance gcInst3_r424994_1 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance gcInst4_r424994_1 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance gcInst5_r424994_1 : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance
local instance gcInst6_r424994_1 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
local instance gcInst7_r424994_1 (K : Set ℂ) : NormedAddCommGroup (markedModel (E := Phase n) K) := inferInstance
local instance gcInst8_r424994_1 (K : Set ℂ) : NormedSpace ℝ (markedModel (E := Phase n) K) := inferInstance
local instance gcInst9_r424994_1 (K : Set ℂ) : NormedAddCommGroup (supportedHolder (E := Phase n) K) := inferInstance
local instance gcInst10_r424994_1 (K : Set ℂ) : NormedSpace ℝ (supportedHolder (E := Phase n) K) := inferInstance
lemma geometricResidual_compact {J : Phase n → End n} {p q : Phase n} {u : ℂ → Phase n}
    (hu : AffineLineCurve J p q u) (hJc : HasCompactSupport (fun x => J x-standardJ n)) :
    HasCompactSupport (geometricResidual u) := by
  apply HasCompactSupport.of_support_subset_isCompact (hu.isProperMap.isCompact_preimage hJc)
  intro z hz
  by_contra hn
  have hstd : J (u z)=standardJ n := sub_eq_zero.mp
    (image_eq_zero_of_notMem_tsupport (f := fun x => J x-standardJ n) hn)
  have hcr := (hu.2.1 z).2 1
  simp only [mul_one,hstd] at hcr
  apply hz
  exact sub_eq_zero.mpr hcr

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Energy_ResidualEnergy
attribute [-instance] _root_.OAI.HigherDimensionalBallPacking.Rigidity.squareMeasure_finite _root_.OAI.HigherDimensionalBallPacking.Rigidity.translatedSquare_finite _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.FiniteMoment.Radial.instInhabitedQuadrant _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
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
open HolderCompletion
variable {n : ℕ}

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.reInst2
lemma lineResidualEnergy_continuous {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) :
    Continuous (lineResidualEnergy u) := by
  have h := (geometricResidual_smooth hu).continuous.comp Complex.equivRealProdCLM.symm.continuous
  exact ((stdDot n).continuous.comp h).clm_apply h

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.reInst1
lemma lineResidualEnergy_compact {J : Phase n → End n} {p q : Phase n} {u : ℂ → Phase n}
    (hu : AffineLineCurve J p q u) (hJc : HasCompactSupport (fun x => J x-standardJ n)) :
    HasCompactSupport (lineResidualEnergy u) := by
  have h := (geometricResidual_compact hu hJc).comp_left
    (g := fun v : Phase n => stdDot n v v) (by simp only [map_zero])
  exact h.comp_isClosedEmbedding Complex.equivRealProdCLM.symm.toHomeomorph.isClosedEmbedding

lemma geometricResidual_at_CR {J : Phase n → End n} {u : ℂ → Phase n} {z : ℂ}
    (hu : PseudoHolomorphicAt J u z) :
    geometricResidual u z=(J (u z)-standardJ n) (fderiv ℝ u z 1) := by
  have hh := hu.2 1
  simp only [mul_one] at hh
  rw [geometricResidual,hh]
  rfl

lemma realCurve_dx {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (z : Plane) :
    fderiv ℝ (realCurve u) z (1,0)=fderiv ℝ u (Complex.equivRealProdCLM.symm z) 1 := by
  rw [realCurve_fderiv ((hu.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) _)]
  congr 1

lemma lineResidualEnergy_eq_defect {J : Phase n → End n} {u : ℂ → Phase n}
    (hus : ContDiff ℝ ∞ u) (hu : ∀ z, PseudoHolomorphicAt J u z) (z : Plane) :
    lineResidualEnergy u z=defectEnergy (J (realCurve u z)) (fderiv ℝ (realCurve u) z (1,0)) := by
  rw [lineResidualEnergy,geometricResidual_at_CR (hu _),realCurve_dx hus]
  rfl

lemma lineHomotopy_outside {J : Phase n → End n} {S t : ℝ}
    (hout : ∀ x, S < capacity x → J x=standardJ n) (ht : t∈Icc (0:ℝ) 1)
    (x : Phase n) (hx : S < capacity x) : lineHomotopy J t x=standardJ n := by
  unfold lineHomotopy
  rw [hout x hx,interpolateJ_standard ht]


end
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

lemma sourceRadialCutoff_le_one (A : ℝ) (z : Plane) : sourceRadialCutoff A z≤1 := by
  have h : 1 ≤ radiusSq z+2 := by linarith [radiusSq_nonneg z]
  simp only [sourceRadialCutoff,outerProfile,Real.smoothTransition.one_of_one_le h,one_mul]
  linarith [Real.smoothTransition.nonneg ((radiusSq z-A)/A)]

lemma sourceRadialCutoff_eventually_one_on_compact {K : Set Plane} (hK : IsCompact K) :
    ∀ᶠ A : ℝ in atTop, ∀ z∈K, sourceRadialCutoff A z=1 := by
  obtain ⟨B,hB,hbound⟩ := radiusSq_pos_bound_of_compact hK
  filter_upwards [eventually_ge_atTop B] with A hA z hz
  exact outerProfile_one_before (radiusSq_nonneg z) ((hbound z hz).le.trans hA) (hB.trans_le hA)

lemma sourceRadialCutoff_tendsto (z : Plane) :
    Tendsto (fun A : ℝ => sourceRadialCutoff A z) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [sourceRadialCutoff_eventually_one_on_compact (isCompact_singleton (x := z))] with A hA
  exact (hA z (mem_singleton z)).symm

lemma smooth_cutoff_integrable_mul {A : ℝ} (hA : 0<A) {e : Plane → ℝ} (he : Continuous e) :
    Integrable (fun z => sourceRadialCutoff A z*e z) :=
  ((sourceRadialCutoff_smooth A).continuous.mul he).integrable_of_hasCompactSupport
    ((sourceRadialCutoff_compact hA).mul_right)

lemma radial_curl_integral_between {β : Plane → Plane →L[ℝ] ℝ}
    (hβ : ContDiff ℝ ∞ β) {A a b : ℝ} (hA : 0<A)
    (hb : ∀ z : Plane, A ≤ radiusSq z → a≤β z (planeRotation z) ∧ β z (planeRotation z)≤b) :
    2*Real.pi*a≤(∫ z, sourceRadialCutoff A z*planarCurl β z) ∧
      (∫ z, sourceRadialCutoff A z*planarCurl β z)≤2*Real.pi*b := by
  let g := outerProfile A
  have hg : ContDiff ℝ ∞ g := outerProfile_smooth A
  have hc : HasCompactSupport g := outerProfile_compact hA
  have hpoint (z : Plane) :
      2*deriv g (radiusSq z)*b ≤ cutoffWedge (sourceRadialCutoff A) β z ∧
      cutoffWedge (sourceRadialCutoff A) β z≤2*deriv g (radiusSq z)*a := by
    rw [show sourceRadialCutoff A=fun y => g (radiusSq y) from rfl,cutoffWedge_radial_rotation hg]
    by_cases hd : deriv g (radiusSq z)=0
    · simp only [hd,mul_zero,zero_mul,le_refl,and_self]
    have hzA : A ≤ radiusSq z := by
      by_contra! hz
      exact hd (outerProfile_deriv_zero_before hA (radiusSq_nonneg z) hz)
    have hneg : 2*deriv g (radiusSq z)≤0 :=
      mul_nonpos_of_nonneg_of_nonpos (by norm_num) (outerProfile_deriv_nonpos hA (radiusSq_nonneg z))
    exact ⟨mul_le_mul_of_nonpos_left (hb z hzA).2 hneg,
      mul_le_mul_of_nonpos_left (hb z hzA).1 hneg⟩
  have hdi (c : ℝ) : Integrable (fun z : Plane => 2*deriv g (radiusSq z)*c) :=
    ((((hg.continuous_deriv (by simp)).comp radiusSq_smooth.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.comp_radiusSq hc.deriv)).const_mul 2).mul_const c
  have hwi := cutoffWedge_integrable (sourceRadialCutoff_smooth A) (sourceRadialCutoff_compact hA) hβ
  have hlow := integral_mono (hdi b) hwi (fun z => (hpoint z).1)
  have hupp := integral_mono hwi (hdi a) (fun z => (hpoint z).2)
  have hg0 : g 0=1 := outerProfile_zero_value hA
  rw [integral_mul_const,integral_radial_derivative hg hc,hg0,mul_one] at hlow hupp
  rw [integral_cutoffWedge (sourceRadialCutoff_smooth A) (sourceRadialCutoff_compact hA) hβ] at hlow hupp
  constructor <;> nlinarith only [hlow,hupp]

lemma radial_curl_integral_tendsto {β : Plane → Plane →L[ℝ] ℝ}
    (hβ : ContDiff ℝ ∞ β) {k : ℝ}
    (hlim : Tendsto (fun z => β z (planeRotation z)) (cocompact Plane) (𝓝 k)) :
    Tendsto (fun A : ℝ => ∫ z, sourceRadialCutoff A z*planarCurl β z)
      atTop (𝓝 (2*Real.pi*k)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hp : 0<2*Real.pi := by positivity
  let δ := ε/(4*Real.pi)
  have hδ : 0<δ := div_pos hε (by positivity)
  have hev : ∀ᶠ z in cocompact Plane,
      k-δ<β z (planeRotation z) ∧ β z (planeRotation z)<k+δ :=
    hlim.eventually (Ioo_mem_nhds (by linarith) (by linarith))
  obtain ⟨K,hK,hKb⟩ := mem_cocompact.mp hev
  obtain ⟨B,hB,hbound⟩ := radiusSq_pos_bound_of_compact hK
  refine ⟨B,?_⟩
  intro A hA
  have hAp : 0<A := hB.trans_le hA
  have hh : ∀ z : Plane, A ≤ radiusSq z →
      k-δ≤β z (planeRotation z) ∧ β z (planeRotation z)≤k+δ := by
    intro z hz
    have hzK : z∉K := by
      intro hzK
      exact (not_lt_of_ge (hA.trans hz)) (hbound z hzK)
    exact ⟨(hKb hzK).1.le,(hKb hzK).2.le⟩
  have hb := radial_curl_integral_between hβ hAp hh
  rw [Real.dist_eq]
  apply abs_lt.mpr
  have he : 2*Real.pi*δ=ε/2 := by dsimp [δ]; field_simp <;> ring_nf
  constructor <;> nlinarith only [hb.1,hb.2,he,hε]

lemma compact_integral_cutoff_eventually {e : Plane → ℝ} (he : HasCompactSupport e) :
    ∀ᶠ A : ℝ in atTop, (fun z => sourceRadialCutoff A z*e z)=e := by
  filter_upwards [sourceRadialCutoff_eventually_one_on_compact he] with A hA
  funext z
  by_cases hz : z∈tsupport e
  · rw [hA z hz,one_mul]
  · rw [image_eq_zero_of_notMem_tsupport hz,mul_zero]



lemma integrable_of_radial_exhaustion_limit {e : Plane → ℝ}
    (he : Continuous e) (hn : ∀ z, 0 ≤ e z) {L : ℝ}
    (hlim : Tendsto (fun A : ℝ => ∫ z, sourceRadialCutoff A z * e z) atTop (𝓝 L)) :
    Integrable e ∧ (∫ z, e z)=L := by
  let a : ℕ → ℝ := fun i => (i:ℝ)+1
  have ha : Tendsto a atTop atTop := tendsto_atTop_add_const_right atTop (1:ℝ) tendsto_natCast_atTop_atTop
  have hap (i : ℕ) : 0<a i := by dsimp [a] <;> positivity
  let f : ℕ → Plane → ℝ := fun i z => sourceRadialCutoff (a i) z * e z
  have hfn (i : ℕ) (z : Plane) : 0≤f i z := mul_nonneg (sourceRadialCutoff_nonneg _ _) (hn _)
  have hfc (i : ℕ) : Continuous (f i) := (sourceRadialCutoff_smooth _).continuous.mul he
  have hfi (i : ℕ) : Integrable (f i) := smooth_cutoff_integrable_mul (hap i) he
  have hfl (z : Plane) : Tendsto (fun i => f i z) atTop (𝓝 (e z)) := by
    simpa only [one_mul, f, Function.comp_def] using ((sourceRadialCutoff_tendsto z).comp ha).mul_const (e z)
  have hlim' : Tendsto (fun i => ∫ z, f i z) atTop (𝓝 L) := hlim.comp ha
  have hfat := lintegral_liminf_le' (u := (atTop : Filter ℕ)) (μ := (volume : Measure Plane))
    (f := fun i z => ENNReal.ofReal (f i z)) (fun i => (hfc i).measurable.ennreal_ofReal.aemeasurable)
  have hpoint (z : Plane) : liminf (fun i => ENNReal.ofReal (f i z)) atTop=ENNReal.ofReal (e z) :=
    (ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hfl z)).liminf_eq
  simp only [hpoint] at hfat
  have hil : Tendsto (fun i => ∫⁻ z, ENNReal.ofReal (f i z)) atTop (𝓝 (ENNReal.ofReal L)) := by
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim'
    simpa only [Function.comp_def, ofReal_integral_eq_lintegral_ofReal (hfi _) (ae_of_all _ (hfn _))] using h
  rw [hil.liminf_eq] at hfat
  have hei : Integrable e := (lintegral_ofReal_ne_top_iff_integrable he.aestronglyMeasurable
    (ae_of_all _ hn)).mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfat)
  refine ⟨hei,?_⟩
  have hdc := tendsto_integral_filter_of_dominated_convergence (F := fun A z => sourceRadialCutoff A z * e z) e
    (Eventually.of_forall fun A : ℝ =>
      ((sourceRadialCutoff_smooth A).continuous.mul he).aestronglyMeasurable)
    (Eventually.of_forall fun A : ℝ => ae_of_all _ fun z => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sourceRadialCutoff_nonneg _ _) (hn z))]
      exact mul_le_of_le_one_left (hn z) (sourceRadialCutoff_le_one A z)) hei
    (ae_of_all _ fun z => by simpa only [one_mul] using (sourceRadialCutoff_tendsto z).mul_const (e z))
  exact tendsto_nhds_unique hdc hlim


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

lemma residual_energy_algebra (x y : Phase n) :
    stdDot n x x+stdDot n y y-stdDot n (y-standardJ n x) (y-standardJ n x)=2*stdOmega n x y := by
  simp only [map_sub,sub_apply,stdDot_J_right,stdOmega_apply]
  rw [stdDot_symm (standardJ n x) y,stdDot_J_right,standardForm_skew (standardJ n x) x,standardForm_J_right,
    standardForm_skew y x]
  ring

lemma lineResidualEnergy_real {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (z : Plane) :
    lineResidualEnergy u z=stdDot n
      (fderiv ℝ (realCurve u) z (0,1)-standardJ n (fderiv ℝ (realCurve u) z (1,0)))
      (fderiv ℝ (realCurve u) z (0,1)-standardJ n (fderiv ℝ (realCurve u) z (1,0))) := by
  simp only [realCurve_fderiv (hu.differentiable (by simp) _)]
  rfl

lemma standard_primitive_curl {v : ℂ → Phase n} (hv : ContDiff ℝ ∞ v) (z : Plane) :
    planarCurl (planarPullback (realCurve v) (stdOmega n)) z=
      dirichletEnergy v z-lineResidualEnergy v z := by
  rw [planarPullback_curl (realCurve_smooth hv) (stdOmega n).contDiff,
    oneForm_extDeriv_apply (stdOmega n).differentiableAt,(stdOmega n).fderiv]
  rw [lineResidualEnergy_real hv]
  change stdOmega n _ _-stdOmega n _ _ = _
  rw [dirichletEnergy,residual_energy_algebra,stdOmega_apply,stdOmega_apply,standardForm_skew]
  ring

lemma affineCorrection_residual {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (a : Phase n) :
    geometricResidual (affineCorrection u a)=geometricResidual u := by
  funext z
  have hlin := (hasFDerivAt_id (𝕜 := ℝ) z).smul_const a
  have hd := (hu.differentiable (by simp) z).hasFDerivAt.sub hlin
  change HasFDerivAt (affineCorrection u a) _ z at hd
  rw [geometricResidual,hd.fderiv]
  simp only [sub_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply,smul_sub,one_smul,geometricResidual]
  abel

lemma affineCorrection_residual_energy {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (a : Phase n) :
    lineResidualEnergy (affineCorrection u a)=lineResidualEnergy u := by
  funext z
  simp only [lineResidualEnergy,affineCorrection_residual hu]

lemma affineCorrection_real_flux_zero {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    {a : Phase n} {h : ℂ → Phase n} (hh : AnalyticAt ℂ h 0)
    (he : ∀ z : ℂ, z≠0 → u z=z • a+h z⁻¹) :
    Tendsto (fun z : Plane => planarPullback (realCurve (affineCorrection u a)) (stdOmega n) z
      (planeRotation z)) (cocompact Plane) (𝓝 0) := by
  have ht := (affineCorrection_primitive_flux_zero hh he).comp
    (le_of_eq Complex.equivRealProdCLM.symm.toHomeomorph.map_cocompact)
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  rw [planarPullback]
  simp only [ContinuousLinearMap.comp_apply]
  rw [realCurve_fderiv ((affineCorrection_smooth hu a).differentiable (by simp) _),equivRealProd_rotation]
  rfl


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

lemma stdOmega_le_half_energy (x y : Phase n) :
    stdOmega n x y≤(stdDot n x x+stdDot n y y)/2 := by
  have h := stdDot_standardForm_sq_le x y
  have hx := stdDot_nonneg x
  have hy := stdDot_nonneg y
  rw [stdOmega_apply]
  nlinarith [sq_nonneg (stdDot n x y),sq_nonneg (stdDot n x x-stdDot n y y)]

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

theorem loop_symplectic_flux_le_energy {v : ℝ → Phase n} (hv : ContDiff ℝ ∞ v)
    {a b : ℝ} (hab : a≤b) (hloop : v b=v a) :
    (∫ t in a..b, stdOmega n (v t) (deriv v t))≤
      ((b-a)^2+1)/2*(∫ t in a..b, stdDot n (deriv v t) (deriv v t)) := by
  have hd : Continuous (deriv v) := hv.continuous_deriv (by simp)
  have hec : Continuous (fun t => stdDot n (deriv v t) (deriv v t)) :=
    ((stdDot n).continuous.comp hd).clm_apply hd
  have hfc : Continuous (fun t => stdOmega n (v t) (deriv v t)) :=
    ((stdOmega n).continuous.comp hv.continuous).clm_apply hd
  have hbc : Continuous (fun t => stdOmega n (v a) (deriv v t)) := (stdOmega n (v a)).continuous.comp hd
  have hent : (∫ t in a..b, deriv v t)=0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => (hv.differentiable (by simp) s).hasDerivAt) (hd.intervalIntegrable a b),hloop,sub_self]
  have hb : (∫ t in a..b, stdOmega n (v a) (deriv v t))=0 := by
    rw [(stdOmega n (v a)).intervalIntegral_comp_comm (hd.intervalIntegrable a b),hent,map_zero]
  have hsub : (∫ t in a..b, stdOmega n (v t-v a) (deriv v t))=
      (∫ t in a..b, stdOmega n (v t) (deriv v t)) := by
    simp only [map_sub,sub_apply]
    rw [intervalIntegral.integral_sub (hfc.intervalIntegrable a b) (hbc.intervalIntegrable a b),hb,sub_zero]
  rw [←hsub]
  let E : ℝ := ∫ s in a..b, stdDot n (deriv v s) (deriv v s)
  have hp (t : ℝ) (ht : t∈Icc a b) : stdOmega n (v t-v a) (deriv v t)≤
      ((b-a)*E+stdDot n (deriv v t) (deriv v t))/2 := by
    have hch := curve_chord_energy_le hv ht.1 ht.2
    have hω := stdOmega_le_half_energy (v t-v a) (deriv v t)
    dsimp only [E]
    linarith
  have hsc : Continuous (fun t => stdOmega n (v t-v a) (deriv v t)) :=
    ((stdOmega n).continuous.comp (hv.continuous.sub continuous_const)).clm_apply hd
  have huc : Continuous (fun t => ((b-a)*E+stdDot n (deriv v t) (deriv v t))/2) :=
    (continuous_const.add hec).div_const 2
  have hl := intervalIntegral.integral_mono_on (μ := volume) hab (hsc.intervalIntegrable a b)
    (huc.intervalIntegrable a b) hp
  have heval : (∫ t in a..b, ((b-a)*E+stdDot n (deriv v t) (deriv v t))/2)=((b-a)^2+1)/2*E := by
    rw [intervalIntegral.integral_div,intervalIntegral.integral_add intervalIntegrable_const
      (hec.intervalIntegrable a b),intervalIntegral.integral_const,smul_eq_mul]
    change ((b-a)*((b-a)*E)+E)/2=_
    ring
  rw [heval] at hl
  exact hl


attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.caInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.caInst2
lemma curveAreaDensity_nonneg {J : Phase n → End n} (hJ : ∀ x, Compatible (J x))
    {u : ℂ → Phase n} (hu : ∀ z, PseudoHolomorphicAt J u z) (z : Plane) :
    0 ≤ curveAreaDensity u z := by
  rw [curveAreaDensity,realCurve_CR (hu _),stdOmega_apply]
  by_cases hv : fderiv ℝ (realCurve u) z (1,0)=0
  · rw [hv,map_zero]
    simp [standardForm]
  · exact ((hJ _).2.2 _ hv).le

lemma dirichletEnergy_eq_residual_add_area {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (z : Plane) :
    dirichletEnergy u z=lineResidualEnergy u z+2*curveAreaDensity u z := by
  have h := residual_energy_algebra (fderiv ℝ (realCurve u) z (1,0))
    (fderiv ℝ (realCurve u) z (0,1))
  rw [←lineResidualEnergy_real hu] at h
  change dirichletEnergy u z-lineResidualEnergy u z=2*curveAreaDensity u z at h
  linarith

lemma uniform_homotopy_pointwise_calibration {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x)) {S : ℝ}
    (hout : ∀ x, S < capacity x → J x=standardJ n) :
    ∃ C : ℝ, 0<C ∧ ∀ t∈Icc (0:ℝ) 1, ∀ (u : ℂ → Phase n),
      ContDiff ℝ ∞ u → (∀ z, PseudoHolomorphicAt (lineHomotopy J t) u z) →
        ∀ z, dirichletEnergy u z≤C*curveAreaDensity u z := by
  let K : Set (ℝ × Phase n) := (Icc (0:ℝ) 1) ×ˢ closedBall n S
  have hK : IsCompact K := isCompact_Icc.prod (closedBall_isCompact n S)
  have hAc : ContinuousOn (fun y : ℝ × Phase n => lineHomotopy J y.1 y.2) K :=
    (lineHomotopy_smooth hJs hJ).continuousOn.mono (fun _ h => ⟨h.1,mem_univ _⟩)
  obtain ⟨B,hB,hbound⟩ := exists_defectEnergy_bound hK hAc
    (fun y hy => lineHomotopy_compatible hJ hy.1 y.2)
  refine ⟨B+2,by linarith,?_⟩
  intro t ht u hus hu z
  have hn := curveAreaDensity_nonneg (lineHomotopy_compatible hJ ht) hu z
  have hle : lineResidualEnergy u z≤B*curveAreaDensity u z := by
    rw [lineResidualEnergy_eq_defect hus hu]
    by_cases hx : capacity (realCurve u z)≤S
    · convert hbound (t,realCurve u z) ⟨ht,hx⟩ (fderiv ℝ (realCurve u) z (1,0)) using 1
      all_goals try with_reducible_and_instances rfl
      rw [curveAreaDensity,realCurve_CR (hu _)]
      rfl
    · rw [lineHomotopy_outside hout ht _ (lt_of_not_ge hx),defectEnergy_standard]
      exact mul_nonneg hB.le hn
  rw [dirichletEnergy_eq_residual_add_area hus]
  nlinarith only [hle]



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Energy_CircularEnergy
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
variable {n : ℕ}

lemma circlePlane_smooth (r : ℝ) : ContDiff ℝ ∞ (circlePlane r) := by
  unfold circlePlane
  fun_prop

lemma circleTrace_smooth {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (r : ℝ) :
    ContDiff ℝ ∞ (circleTrace u r) := (realCurve_smooth hu).comp (circlePlane_smooth r)

lemma circlePlane_hasDerivAt (r θ : ℝ) :
    HasDerivAt (circlePlane r) (planeRotation (circlePlane r θ)) θ := by
  have hh := ((Real.hasDerivAt_cos θ).const_mul r).prodMk ((Real.hasDerivAt_sin θ).const_mul r)
  change HasDerivAt (circlePlane r) (r * (-Real.sin θ),r * Real.cos θ) θ at hh
  simpa only [planeRotation,circlePlane,mul_neg] using hh

lemma circleTrace_deriv {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (r θ : ℝ) :
    deriv (circleTrace u r) θ=fderiv ℝ (realCurve u) (circlePlane r θ) (planeRotation (circlePlane r θ)) := by
  exact (((realCurve_smooth hu).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _).hasFDerivAt.comp_hasDerivAt θ
    (circlePlane_hasDerivAt r θ)).deriv

lemma circleTrace_closed (u : ℂ → Phase n) (r : ℝ) : circleTrace u r Real.pi=circleTrace u r (-Real.pi) := by
  simp [circleTrace,circlePlane]

lemma plane_linear_energy_identity (L : Plane →L[ℝ] Phase n) (z : Plane) :
    stdDot n (L (planeRotation z)) (L (planeRotation z))+stdDot n (L z) (L z)=
      radiusSq z*(stdDot n (L (1,0)) (L (1,0))+stdDot n (L (0,1)) (L (0,1))) := by
  have hz : z=z.1 • ((1,0):Plane)+z.2 • ((0,1):Plane) := by ext <;> simp
  have hr : planeRotation z=(-z.2) • ((1,0):Plane)+z.1 • ((0,1):Plane) := by ext <;> simp [planeRotation]
  have hLr : L (planeRotation z)=(-z.2) • L (1,0)+z.1 • L (0,1) := by
    rw [hr,map_add,map_smul,map_smul]
  have hLz : L z=z.1 • L (1,0)+z.2 • L (0,1) := by
    conv_lhs => rw [hz,map_add,map_smul,map_smul]
  rw [hLr,hLz]
  simp only [map_add,map_smul,add_apply,smul_apply,smul_eq_mul]
  rw [stdDot_symm (L (0,1)) (L (1,0))]
  dsimp only [radiusSq]
  ring

lemma circleTrace_energy_le {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (r θ : ℝ) :
    stdDot n (deriv (circleTrace u r) θ) (deriv (circleTrace u r) θ)≤
      r^2*dirichletEnergy u (circlePlane r θ) := by
  rw [circleTrace_deriv hu]
  have h := plane_linear_energy_identity (fderiv ℝ (realCurve u) (circlePlane r θ)) (circlePlane r θ)
  have hr : radiusSq (circlePlane r θ)=r^2 := by
    have htr := Real.cos_sq_add_sin_sq θ
    dsimp [radiusSq,circlePlane]
    nlinarith [sq_nonneg r]
  rw [hr] at h
  change stdDot n _ _+stdDot n _ _=r^2*dirichletEnergy u (circlePlane r θ) at h
  linarith [stdDot_nonneg (fderiv ℝ (realCurve u) (circlePlane r θ) (circlePlane r θ))]

lemma circle_pullback_flux_le {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (r : ℝ) :
    (∫ θ in (-Real.pi)..Real.pi,
      planarPullback (realCurve u) (stdOmega n) (circlePlane r θ) (planeRotation (circlePlane r θ)))≤
      ((2*Real.pi)^2+1)/2*r^2*(∫ θ in (-Real.pi)..Real.pi, dirichletEnergy u (circlePlane r θ)) := by
  have hloop := loop_symplectic_flux_le_energy (circleTrace_smooth hu r)
    (by linarith [Real.pi_pos] : -Real.pi≤Real.pi) (circleTrace_closed u r)
  have hdc : Continuous (fun θ => stdDot n (deriv (circleTrace u r) θ) (deriv (circleTrace u r) θ)) := by
    have hd := (circleTrace_smooth hu r).continuous_deriv (by simp)
    exact ((stdDot n).continuous.comp hd).clm_apply hd
  have hec : Continuous (fun θ => r^2*dirichletEnergy u (circlePlane r θ)) := continuous_const.mul
    ((dirichletEnergy_continuous hu).comp (circlePlane_smooth r).continuous)
  have hi := intervalIntegral.integral_mono (μ := volume) (by linarith [Real.pi_pos] : -Real.pi≤Real.pi)
    (hdc.intervalIntegrable _ _) (hec.intervalIntegrable _ _) (circleTrace_energy_le hu r)
  rw [intervalIntegral.integral_const_mul] at hi
  have hc : 0≤((Real.pi-(-Real.pi))^2+1)/2 := by positivity
  have hb := hloop.trans (mul_le_mul_of_nonneg_left hi hc)
  calc
    _ = (∫ θ in (-Real.pi)..Real.pi, stdOmega n (circleTrace u r θ) (deriv (circleTrace u r) θ)) := by
      apply intervalIntegral.integral_congr
      intro θ _
      dsimp only
      rw [circleTrace_deriv hu]
      rfl
    _ ≤ _ := hb
    _ = _ := by ring


end
section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

lemma integrable_polar_pullback {f : Plane → ℝ} (hf : Integrable f) :
    IntegrableOn (fun p : Plane => p.1*f (polarCoord.symm p)) polarCoord.target := by
  have hi : IntegrableOn f (polarCoord.symm '' polarCoord.target) := hf.integrableOn
  have hp := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    polarCoord.open_target.measurableSet
    (fun p _ => (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt)
    polarCoord.symm.injOn f).mp hi
  apply hp.congr_fun _ polarCoord.open_target.measurableSet
  intro p hp
  dsimp only
  rw [det_fderivPolarCoordSymm,abs_of_pos hp.1,smul_eq_mul]

lemma integral_polar_slices {f : Plane → ℝ} (hf : Integrable f) :
    (∫ z, f z)=∫ r in Ioi (0:ℝ), r*(∫ θ in (-Real.pi)..Real.pi, f (circlePlane r θ)) := by
  rw [←integral_comp_polarCoord_symm]
  have hp := integrable_polar_pullback hf
  rw [polarCoord_target,Measure.volume_eq_prod] at hp ⊢
  simp only [smul_eq_mul]
  rw [setIntegral_prod _ hp]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r _
  dsimp only [Prod.fst]
  rw [integral_const_mul,intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi≤Real.pi),
    integral_Ioc_eq_integral_Ioo]
  rfl

lemma integrable_polar_slices {f : Plane → ℝ} (hf : Integrable f) :
    IntegrableOn (fun r => r*(∫ θ in (-Real.pi)..Real.pi, f (circlePlane r θ))) (Ioi (0:ℝ)) := by
  have hp := integrable_polar_pullback hf
  rw [polarCoord_target,Measure.volume_eq_prod,IntegrableOn,←Measure.prod_restrict] at hp
  have hi := hp.integral_prod_left
  unfold IntegrableOn
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  funext r
  dsimp only [Prod.fst]
  rw [integral_const_mul,intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi≤Real.pi),
    integral_Ioc_eq_integral_Ioo]
  rfl


end
section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
variable {n : ℕ}

lemma angularCurveFlux_continuous {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) :
    Continuous (angularCurveFlux u) :=
  (planarPullback_smooth (realCurve_smooth hu) (stdOmega n).contDiff).continuous.clm_apply
    (continuous_snd.neg.prodMk continuous_fst)

lemma radiusSq_circlePlane (r θ : ℝ) : radiusSq (circlePlane r θ)=r^2 := by
  have htr := Real.cos_sq_add_sin_sq θ
  dsimp [radiusSq,circlePlane]
  nlinarith [sq_nonneg r]

lemma integral_radial_angularFlux_le {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    {k : ℝ → ℝ} (hk : Continuous k) (hkc : HasCompactSupport k)
    (hkn : ∀ s : ℝ, 0 ≤ s → 0 ≤ k s) :
    (∫ z : Plane, k (radiusSq z)*angularCurveFlux u z)≤
      ((2*Real.pi)^2+1)/2*(∫ z : Plane, k (radiusSq z)*radiusSq z*dirichletEnergy u z) := by
  have hkpc := hk.comp radiusSq_smooth.continuous
  have hkps := HasCompactSupport.comp_radiusSq hkc
  have hf : Integrable (fun z : Plane => k (radiusSq z)*angularCurveFlux u z) :=
    (hkpc.mul (angularCurveFlux_continuous hu)).integrable_of_hasCompactSupport hkps.mul_right
  have hg : Integrable (fun z : Plane => k (radiusSq z)*radiusSq z*dirichletEnergy u z) :=
    ((hkpc.mul radiusSq_smooth.continuous).mul (dirichletEnergy_continuous hu)).integrable_of_hasCompactSupport
      (hkps.mul_right.mul_right)
  rw [integral_polar_slices hf,integral_polar_slices hg,←integral_const_mul]
  apply setIntegral_mono_on (integrable_polar_slices hf)
    ((integrable_polar_slices hg).const_mul _) measurableSet_Ioi
  intro r hr
  simp_rw [radiusSq_circlePlane,intervalIntegral.integral_const_mul]
  have hn : 0 ≤ r*k (r^2) := mul_nonneg (le_of_lt hr) (hkn _ (sq_nonneg _))
  have hb := mul_le_mul_of_nonneg_left (circle_pullback_flux_le hu r) hn
  change r*(k (r^2)*(∫ θ in (-Real.pi)..Real.pi, angularCurveFlux u (circlePlane r θ)))≤_
  dsimp only [angularCurveFlux]
  nlinarith only [hb]

lemma curveAreaDensity_continuous {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) :
    Continuous (curveAreaDensity u) := by
  have hd := ((realCurve_smooth hu).fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuous
  exact ((stdOmega n).continuous.comp (hd.clm_apply continuous_const)).clm_apply
    (hd.clm_apply continuous_const)

lemma standard_primitive_curl_area {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (z : Plane) :
    planarCurl (planarPullback (realCurve u) (stdOmega n)) z=2*curveAreaDensity u z := by
  rw [standard_primitive_curl hu,dirichletEnergy_eq_residual_add_area hu]
  ring

lemma radial_stokes_area_eq_flux {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    (∫ z : Plane, g (radiusSq z)*curveAreaDensity u z)=
      ∫ z : Plane, (-deriv g (radiusSq z))*angularCurveFlux u z := by
  have hβ := planarPullback_smooth (realCurve_smooth hu) (stdOmega n).contDiff
  have he : (∫ z, cutoffWedge (fun y => g (radiusSq y))
      (planarPullback (realCurve u) (stdOmega n)) z)=
      -(∫ z, g (radiusSq z)*planarCurl (planarPullback (realCurve u) (stdOmega n)) z) :=
    integral_cutoffWedge (hg.comp radiusSq_smooth) (HasCompactSupport.comp_radiusSq hgc) hβ
  simp_rw [cutoffWedge_radial_rotation hg,standard_primitive_curl_area hu] at he
  have hleft (z : Plane) : 2*deriv g (radiusSq z)*
      planarPullback (realCurve u) (stdOmega n) z (planeRotation z)=
      -2*((-deriv g (radiusSq z))*angularCurveFlux u z) := by unfold angularCurveFlux; ring
  have hright (z : Plane) : g (radiusSq z)*(2*curveAreaDensity u z)=
      2*(g (radiusSq z)*curveAreaDensity u z) := by ring
  simp_rw [hleft,hright] at he
  rw [integral_const_mul,integral_const_mul] at he
  linarith

theorem calibrated_radial_energy_bound {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    {C : ℝ} (hC : 0≤C) (hcal : ∀ z, dirichletEnergy u z≤C*curveAreaDensity u z)
    {A : ℝ} (hA : 0<A) :
    (∫ z : Plane, sourceRadialCutoff A z*dirichletEnergy u z)≤
      C*(((2*Real.pi)^2+1)/2)*
        (∫ z : Plane, (-deriv (outerProfile A) (radiusSq z))*radiusSq z*dirichletEnergy u z) := by
  have hi := integral_mono (smooth_cutoff_integrable_mul hA (dirichletEnergy_continuous hu))
    ((smooth_cutoff_integrable_mul hA (curveAreaDensity_continuous hu)).const_mul C)
    (fun z => by
      have h := mul_le_mul_of_nonneg_left (hcal z) (sourceRadialCutoff_nonneg A z)
      nlinarith only [h])
  rw [integral_const_mul] at hi
  change (∫ z, sourceRadialCutoff A z*dirichletEnergy u z)≤
    C*(∫ z, outerProfile A (radiusSq z)*curveAreaDensity u z) at hi
  rw [radial_stokes_area_eq_flux hu (outerProfile_smooth A) (outerProfile_compact hA)] at hi
  have hb := integral_radial_angularFlux_le hu
    ((outerProfile_smooth A).continuous_deriv (by simp)).neg (outerProfile_compact hA).deriv.neg
    (fun s hs => neg_nonneg.mpr (outerProfile_deriv_nonpos hA hs))
  exact hi.trans (by simpa only [mul_assoc,Pi.neg_apply] using mul_le_mul_of_nonneg_left hb hC)


end
section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

lemma smoothTransition_deriv_zero_outside {t : ℝ} (ht : t∉Icc (0:ℝ) 1) :
    deriv Real.smoothTransition t=0 := by
  rcases (show t<0 ∨ 1<t by simpa only [mem_Icc,not_and_or,not_le] using ht) with ht | ht
  · have he : Real.smoothTransition =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
      exact Real.smoothTransition.zero_of_nonpos hs.le
    rw [he.deriv_eq,deriv_const]
  · have he : Real.smoothTransition =ᶠ[𝓝 t] fun _ => 1 := by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
      exact Real.smoothTransition.one_of_one_le hs.le
    rw [he.deriv_eq,deriv_const]

lemma smoothTransition_deriv_le_bound :
    ∃ M : ℝ, 0<M ∧ ∀ t : ℝ, deriv Real.smoothTransition t≤M := by
  have hc : HasCompactSupport (deriv Real.smoothTransition) :=
    HasCompactSupport.intro isCompact_Icc (fun t ht => smoothTransition_deriv_zero_outside ht)
  obtain ⟨B,hB⟩ := hc.exists_bound_of_continuous
    ((Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).continuous_deriv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  refine ⟨|B|+1,by positivity,fun t => ?_⟩
  have h := hB t
  rw [Real.norm_eq_abs] at h
  linarith [le_abs_self (deriv Real.smoothTransition t),le_abs_self B]

lemma outerProfile_deriv_zero_after {A t : ℝ} (hA : 0<A) (ht : 2*A<t) :
    deriv (outerProfile A) t=0 := by
  have he : outerProfile A =ᶠ[𝓝 t] fun _ => 0 := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    change 2*A < s at hs
    have h : 1≤(s-A)/A := (le_div_iff₀ hA).mpr (by linarith)
    simp only [outerProfile,Real.smoothTransition.one_of_one_le h,sub_self,mul_zero]
  rw [he.deriv_eq,deriv_const]

lemma outerProfile_weight_uniform_bound :
    ∃ B : ℝ, 0<B ∧ ∀ A : ℝ, 0<A → ∀ t : ℝ, 0≤t →
      0≤(-deriv (outerProfile A) t)*t ∧ (-deriv (outerProfile A) t)*t≤B := by
  obtain ⟨M,hM,hbound⟩ := smoothTransition_deriv_le_bound
  refine ⟨2*M,by positivity,?_⟩
  intro A hA t ht
  refine ⟨mul_nonneg (neg_nonneg.mpr (outerProfile_deriv_nonpos hA ht)) ht,?_⟩
  by_cases htA : t≤2*A
  · rw [outerProfile_deriv ht,neg_neg]
    have hd : 0≤deriv Real.smoothTransition ((t-A)/A) := Real.smoothTransition.monotone.deriv_nonneg
    have h1 := mul_le_mul_of_nonneg_right (hbound ((t-A)/A)) (div_nonneg ht hA.le)
    have h2 : t/A≤2 := (div_le_iff₀ hA).mpr (by linarith)
    have h3 := mul_le_mul_of_nonneg_left h2 hM.le
    calc
      deriv Real.smoothTransition ((t-A)/A)/A*t=deriv Real.smoothTransition ((t-A)/A)*(t/A) := by ring
      _≤M*(t/A) := h1
      _≤2*M := by linarith only [h3]
  · rw [outerProfile_deriv_zero_after hA (lt_of_not_ge htA)]
    simpa using (le_of_lt (show 0<2*M by positivity))


end
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
variable {n : ℕ}


lemma outerProfile_mono_parameter {A B t : ℝ} (hA : 0<A) (hAB : A≤B) (ht : 0≤t) :
    outerProfile A t≤outerProfile B t := by
  have hB : 0<B := hA.trans_le hAB
  have harg : (t-B)/B≤(t-A)/A := by
    rw [sub_div,sub_div,div_self hA.ne',div_self hB.ne']
    exact sub_le_sub_right (div_le_div_of_nonneg_left ht hA hAB) 1
  exact mul_le_mul_of_nonneg_left
    (sub_le_sub_left (Real.smoothTransition.monotone harg) 1)
    (Real.smoothTransition.nonneg _)

lemma outerProfile_zero_after {A t : ℝ} (hA : 0<A) (ht : 2*A≤t) :
    outerProfile A t=0 := by
  have ha : 1≤(t-A)/A := (le_div_iff₀ hA).mpr (by linarith)
  simp only [outerProfile,Real.smoothTransition.one_of_one_le ha,sub_self,mul_zero]

lemma cutoff_weight_annulus_bound {B : ℝ} (hB : 0≤B)
    (hbound : ∀ A : ℝ, 0<A → ∀ t : ℝ, 0≤t → (-deriv (outerProfile A) t)*t≤B)
    {A : ℝ} (hA : 0<A) (z : Plane) :
    (-deriv (outerProfile A) (radiusSq z))*radiusSq z≤
      B*(sourceRadialCutoff (4*A) z-sourceRadialCutoff (A/4) z) := by
  have hmono : 0 ≤ sourceRadialCutoff (4*A) z-sourceRadialCutoff (A/4) z :=
    sub_nonneg.mpr (outerProfile_mono_parameter (A := A/4) (B := 4*A) (by positivity) (by linarith) (radiusSq_nonneg z))
  by_cases hd : deriv (outerProfile A) (radiusSq z)=0
  · rw [hd,neg_zero,zero_mul]
    exact mul_nonneg hB hmono
  have hlo : A ≤ radiusSq z := by
    by_contra! h
    exact hd (outerProfile_deriv_zero_before hA (radiusSq_nonneg z) h)
  have hhi : radiusSq z≤2*A := by
    by_contra! h
    exact hd (outerProfile_deriv_zero_after hA h)
  have h4 : sourceRadialCutoff (4*A) z=1 :=
    outerProfile_one_before (radiusSq_nonneg z) (by linarith) (by positivity)
  have hq : sourceRadialCutoff (A/4) z=0 :=
    outerProfile_zero_after (by positivity) (by linarith)
  rw [h4,hq,sub_zero,mul_one]
  exact hbound A hA _ (radiusSq_nonneg z)

lemma radialCurveEnergy_mono {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    {A B : ℝ} (hA : 0<A) (hAB : A≤B) : radialCurveEnergy u A ≤ radialCurveEnergy u B :=
  integral_mono (smooth_cutoff_integrable_mul hA (dirichletEnergy_continuous hu))
    (smooth_cutoff_integrable_mul (hA.trans_le hAB) (dirichletEnergy_continuous hu))
    (fun z => mul_le_mul_of_nonneg_right (outerProfile_mono_parameter hA hAB (radiusSq_nonneg z))
      (dirichletEnergy_nonneg u z))

theorem calibrated_energy_hole_filling {C : ℝ} (hC : 0<C) :
    ∃ θ : ℝ, 0<θ ∧ θ<1 ∧ ∀ (u : ℂ → Phase n), ContDiff ℝ ∞ u →
      (∀ z, dirichletEnergy u z≤C*curveAreaDensity u z) →
      ∀ A : ℝ, 0<A → radialCurveEnergy u A≤θ*radialCurveEnergy u (16*A) := by
  obtain ⟨B,hB,hbound⟩ := outerProfile_weight_uniform_bound
  let K := C*(((2*Real.pi)^2+1)/2)*B
  have hK : 0<K := by dsimp [K] <;> positivity
  refine ⟨K/(K+1),div_pos hK (by linarith), (div_lt_one (by linarith)).mpr (by linarith),?_⟩
  intro u hu hcal A hA
  have hfour : 0<4*A := by positivity
  have he := calibrated_radial_energy_bound hu hC.le hcal hfour
  have hdi : Integrable (fun z : Plane => (-deriv (outerProfile (4*A)) (radiusSq z))*radiusSq z*dirichletEnergy u z) := by
    exact (((((outerProfile_smooth (4*A)).continuous_deriv (by simp)).comp radiusSq_smooth.continuous).neg.mul
      radiusSq_smooth.continuous).mul (dirichletEnergy_continuous hu)).integrable_of_hasCompactSupport
      (((HasCompactSupport.comp_radiusSq (outerProfile_compact hfour).deriv).neg.mul_right).mul_right)
  have hfi := smooth_cutoff_integrable_mul (show 0<16*A by positivity) (dirichletEnergy_continuous hu)
  have hgi := smooth_cutoff_integrable_mul hA (dirichletEnergy_continuous hu)
  have hpoint (z : Plane) := mul_le_mul_of_nonneg_right
    (cutoff_weight_annulus_bound hB.le (fun A hA t ht => (hbound A hA t ht).2) hfour z)
    (dirichletEnergy_nonneg u z)
  have hid := integral_mono hdi ((hfi.sub hgi).const_mul B) (fun z => by
    have h44 : 4*(4*A)=16*A := by ring
    have h4q : 4*A/4=A := by ring
    simpa only [h44,h4q,sub_mul,mul_assoc,Pi.sub_apply] using hpoint z)
  simp only [Pi.sub_apply] at hid
  rw [integral_const_mul,integral_sub hfi hgi] at hid
  have hm := radialCurveEnergy_mono hu hA (show A≤4*A by linarith)
  have hc : 0≤C*(((2*Real.pi)^2+1)/2) := by positivity
  have hh := he.trans (mul_le_mul_of_nonneg_left hid hc)
  change radialCurveEnergy u (4*A)≤C*(((2*Real.pi)^2+1)/2)*
    (B*(radialCurveEnergy u (16*A)-radialCurveEnergy u A)) at hh
  have hfin : (K+1)*radialCurveEnergy u A≤K*radialCurveEnergy u (16*A) := by
    dsimp [K]
    nlinarith only [hm,hh]
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ (by linarith : 0<K+1)).mpr (by nlinarith only [hfin])


lemma radialCurveEnergy_geometric_bound {u : ℂ → Phase n} {θ : ℝ} (hθ : 0≤θ)
    (hstep : ∀ A : ℝ, 0<A → radialCurveEnergy u A≤θ*radialCurveEnergy u (16*A))
    {A : ℝ} (hA : 0<A) (k : ℕ) :
    radialCurveEnergy u (A/16^k)≤θ^k*radialCurveEnergy u A := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hs := hstep (A/16^(k+1)) (by positivity)
    have he : 16*(A/16^(k+1))=A/16^k := by
      rw [pow_succ]
      field_simp
    rw [he] at hs
    refine hs.trans ((mul_le_mul_of_nonneg_left ih hθ).trans_eq ?_)
    rw [pow_succ]
    ring

lemma centeredCurve_smooth {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (c : ℂ) :
    ContDiff ℝ ∞ (centeredCurve u c) := hu.comp (contDiff_id.add contDiff_const)

lemma realCurve_centered (u : ℂ → Phase n) (c : ℂ) :
    realCurve (centeredCurve u c)=fun z => realCurve u (z+Complex.equivRealProdCLM c) := by
  funext z
  simp only [realCurve,centeredCurve,Function.comp_def,map_add,ContinuousLinearEquiv.symm_apply_apply]

lemma centeredCurve_fderiv {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (c : ℂ) (z : Plane) :
    fderiv ℝ (realCurve (centeredCurve u c)) z=
      fderiv ℝ (realCurve u) (z+Complex.equivRealProdCLM c) := by
  rw [realCurve_centered]
  have hh := ((realCurve_smooth hu).differentiable (by simp) (z+Complex.equivRealProdCLM c)).hasFDerivAt.comp z
    ((hasFDerivAt_id (𝕜 := ℝ) z).add_const (Complex.equivRealProdCLM c))
  change HasFDerivAt (fun z => realCurve u (z+Complex.equivRealProdCLM c)) _ z at hh
  simpa only [ContinuousLinearMap.comp_id] using hh.fderiv

lemma dirichletEnergy_centered {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (c : ℂ) (z : Plane) :
    dirichletEnergy (centeredCurve u c) z=dirichletEnergy u (z+Complex.equivRealProdCLM c) := by
  simp only [dirichletEnergy,centeredCurve_fderiv hu]

lemma curveAreaDensity_centered {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (c : ℂ) (z : Plane) :
    curveAreaDensity (centeredCurve u c) z=curveAreaDensity u (z+Complex.equivRealProdCLM c) := by
  simp only [curveAreaDensity,centeredCurve_fderiv hu]

lemma stdDot_add_self_le (v w : Phase n) :
    stdDot n (v+w) (v+w)≤2*stdDot n v v+2*stdDot n w w := by
  have hh := stdDot_nonneg (v-w)
  rw [stdDot_sub_self] at hh
  simp only [map_add,add_apply]
  rw [stdDot_symm w v]
  linarith

lemma stdDot_standardJ_self (v : Phase n) :
    stdDot n (standardJ n v) (standardJ n v)=stdDot n v v := by
  rw [stdDot_J_right,standardForm_skew (standardJ n v),standardForm_J_right,neg_neg]

lemma dirichletEnergy_add_le {u v : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (z : Plane) :
    dirichletEnergy (u+v) z≤2*dirichletEnergy u z+2*dirichletEnergy v z := by
  have hd : fderiv ℝ (realCurve (u+v)) z=fderiv ℝ (realCurve u) z+fderiv ℝ (realCurve v) z :=
    (((realCurve_smooth hu).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z).hasFDerivAt.add
      ((realCurve_smooth hv).differentiable (by simp) z).hasFDerivAt).fderiv
  have hx := stdDot_add_self_le (fderiv ℝ (realCurve u) z (1,0)) (fderiv ℝ (realCurve v) z (1,0))
  have hy := stdDot_add_self_le (fderiv ℝ (realCurve u) z (0,1)) (fderiv ℝ (realCurve v) z (0,1))
  simp only [dirichletEnergy,hd,add_apply]
  nlinarith only [hx,hy]

lemma dirichletEnergy_linear (a : Phase n) (z : Plane) :
    dirichletEnergy (fun w : ℂ => w • a) z=2*stdDot n a a := by
  have hu : ContDiff ℝ ∞ (fun w : ℂ => w • a) := contDiff_id.smul contDiff_const
  have hd := (hasFDerivAt_id (𝕜 := ℝ) (Complex.equivRealProdCLM.symm z)).smul_const a
  change HasFDerivAt (fun w : ℂ => w • a) _ (Complex.equivRealProdCLM.symm z) at hd
  simp only [dirichletEnergy,realCurve_fderiv (hu.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _), hd.fderiv,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply]
  simp only [show Complex.equivRealProdCLM.symm (1,0)=(1:ℂ) from rfl,
    show Complex.equivRealProdCLM.symm (0,1)=Complex.I from rfl,one_smul]
  change stdDot n a a+stdDot n (standardJ n a) (standardJ n a)=_
  rw [stdDot_standardJ_self]
  ring

lemma dirichletEnergy_le_affineCorrection {u : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) (a : Phase n) (z : Plane) :
    dirichletEnergy u z≤2*dirichletEnergy (affineCorrection u a) z+4*stdDot n a a := by
  have he : u=affineCorrection u a+(fun w : ℂ => w • a) := by
    funext w
    simp only [Pi.add_apply,affineCorrection,sub_add_cancel]
  have hh := dirichletEnergy_add_le (affineCorrection_smooth hu a)
    (contDiff_id.smul (contDiff_const (c := a))) z
  change dirichletEnergy (affineCorrection u a+(fun w : ℂ => w • a)) z≤
    2*dirichletEnergy (affineCorrection u a) z+2*dirichletEnergy (fun w : ℂ => w • a) z at hh
  rw [←he,dirichletEnergy_linear] at hh
  linarith only [hh]

lemma centered_unit_energy_bound {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    (a : Phase n) (hei : Integrable (dirichletEnergy (affineCorrection u a))) (c : ℂ) :
    radialCurveEnergy (centeredCurve u c) 1≤
      2*(∫ z, dirichletEnergy (affineCorrection u a) z)+
        4*stdDot n a a*(∫ z : Plane, sourceRadialCutoff 1 z) := by
  have hec := (dirichletEnergy_continuous (affineCorrection_smooth hu a)).comp
    (continuous_id.add (continuous_const (y := Complex.equivRealProdCLM c)))
  have hei' : Integrable (fun z => dirichletEnergy (affineCorrection u a) (z+Complex.equivRealProdCLM c)) :=
    (measurePreserving_add_right volume (Complex.equivRealProdCLM c)).integrable_comp_of_integrable hei
  have hcuti : Integrable (sourceRadialCutoff 1) :=
    (sourceRadialCutoff_smooth 1).continuous.integrable_of_hasCompactSupport (sourceRadialCutoff_compact (by norm_num))
  have hci := smooth_cutoff_integrable_mul (by norm_num : (0:ℝ)<1) hec
  have hu1 := smooth_cutoff_integrable_mul (by norm_num : (0:ℝ)<1)
    (dirichletEnergy_continuous (centeredCurve_smooth hu c))
  have hpoint (z : Plane) : sourceRadialCutoff 1 z*dirichletEnergy (centeredCurve u c) z≤
      2*dirichletEnergy (affineCorrection u a) (z+Complex.equivRealProdCLM c)+
        (4*stdDot n a a)*sourceRadialCutoff 1 z := by
    rw [dirichletEnergy_centered hu]
    have hh := mul_le_mul_of_nonneg_left (dirichletEnergy_le_affineCorrection hu a
      (z+Complex.equivRealProdCLM c)) (sourceRadialCutoff_nonneg 1 z)
    have hb := mul_le_of_le_one_left (dirichletEnergy_nonneg (affineCorrection u a) (z+Complex.equivRealProdCLM c))
      (sourceRadialCutoff_le_one 1 z)
    nlinarith only [hh,hb]
  have hle := integral_mono hu1 ((hei'.const_mul 2).add (hcuti.const_mul (4*stdDot n a a))) hpoint
  simp only [Pi.add_apply] at hle
  rw [integral_add (hei'.const_mul 2) (hcuti.const_mul _),integral_const_mul,integral_const_mul,
    integral_add_right_eq_self] at hle
  exact hle


theorem AffineLineCurve.affine_correction_energy_of_slope {J : Phase n → End n}
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u)
    (hJc : HasCompactSupport (fun x => J x-standardJ n)) {a : Phase n}
    (ha : Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 a)) :
    Integrable (dirichletEnergy (affineCorrection u a)) ∧
      (∫ z, dirichletEnergy (affineCorrection u a) z)=∫ z, lineResidualEnergy u z := by
  have hh := analyticAt_dslope_zero (infinityGerm_analyticAt (hu.holomorphic_at_infinity hJc) ha)
  have he := fun z hz => infinityGerm_affine_reconstruction u a (z := z) hz
  have hv := affineCorrection_smooth hu.1 a
  have hβ := planarPullback_smooth (realCurve_smooth hv) (stdOmega n).contDiff
  have hlim := radial_curl_integral_tendsto hβ (affineCorrection_real_flux_zero hu.1 hh he)
  simp only [mul_zero] at hlim
  have hfl : Tendsto (fun A : ℝ => ∫ z, sourceRadialCutoff A z * lineResidualEnergy u z)
      atTop (𝓝 (∫ z, lineResidualEnergy u z)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [compact_integral_cutoff_eventually (lineResidualEnergy_compact hu hJc)] with A hA
    rw [hA]
  have helim : Tendsto (fun A : ℝ => ∫ z, sourceRadialCutoff A z *
      dirichletEnergy (affineCorrection u a) z) atTop (𝓝 (∫ z, lineResidualEnergy u z)) := by
    have hl := hlim.add hfl
    simp only [zero_add] at hl
    apply hl.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with A hA
    rw [←integral_add
      (smooth_cutoff_integrable_mul hA ((planarCurl_contDiff hβ).continuous))
      (smooth_cutoff_integrable_mul hA (lineResidualEnergy_continuous hu.1))]
    apply integral_congr_ae
    filter_upwards [] with z
    rw [standard_primitive_curl hv,affineCorrection_residual_energy hu.1]
    ring
  exact integrable_of_radial_exhaustion_limit (dirichletEnergy_continuous hv)
    (dirichletEnergy_nonneg _) helim


theorem exact_line_uniform_local_energy {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1)
    (hout : ∀ x, S < capacity x → J x=standardJ n) :
    ∃ C M θ : ℝ, 0<C ∧ 0≤M ∧ 0<θ ∧ θ<1 ∧
      ∀ t∈Icc (0:ℝ) 1, ∀ (p q : Phase n) (u : ℂ → Phase n),
        AffineLineCurve (lineHomotopy J t) p q u →
        ∃ a : Phase n, a≠0 ∧
          Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 a) ∧
          ∀ (c : ℂ) (k : ℕ), radialCurveEnergy (centeredCurve u c) (1/16^k)≤
            θ^k*(C+M*stdDot n a a) := by
  obtain ⟨D,hD,hres⟩ := exact_line_homotopy_residual_energy_bound_bp240 hJs hJ hJc hST hT hout
  obtain ⟨L,hL,hcal⟩ := uniform_homotopy_pointwise_calibration hJs hJ hout
  obtain ⟨θ,hθ,hθ1,hstep⟩ := calibrated_energy_hole_filling (n := n) hL
  let M : ℝ := 4*(∫ z : Plane,sourceRadialCutoff 1 z)
  have hM : 0≤M := mul_nonneg (by norm_num) (integral_nonneg (sourceRadialCutoff_nonneg 1))
  refine ⟨2*D,M,θ,by positivity,hM,hθ,hθ1,?_⟩
  intro t ht p q u hu
  obtain ⟨a,ha,hlim⟩ := hu.2.2.2.2
  obtain ⟨hei,heiVal⟩ := hu.affine_correction_energy_of_slope (lineHomotopy_compact hJc ht) hlim
  refine ⟨a,ha,hlim,?_⟩
  intro c k
  have hcalC (z : Plane) : dirichletEnergy (centeredCurve u c) z≤L*curveAreaDensity (centeredCurve u c) z := by
    rw [dirichletEnergy_centered hu.1,curveAreaDensity_centered hu.1]
    exact hcal t ht u hu.1 hu.2.1 _
  have hgeom := radialCurveEnergy_geometric_bound hθ.le
    (hstep (centeredCurve u c) (centeredCurve_smooth hu.1 c) hcalC) (by norm_num : (0:ℝ)<1) k
  have hunit := centered_unit_energy_bound hu.1 a hei c
  rw [heiVal] at hunit
  have hres' := hres t ht p q u hu
  have hupp : radialCurveEnergy (centeredCurve u c) 1≤2*D+M*stdDot n a a := by
    dsimp [M]
    nlinarith only [hunit,hres']
  exact hgeom.trans (mul_le_mul_of_nonneg_left hupp (pow_nonneg hθ.le _))



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Campanato_TranslatedSquare
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
open Set Function Filter MeasureTheory
variable {n : ℕ}

lemma exact_line_local_energy_of_slope_bp240_oai {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1)
    (hout : ∀ x, S < capacity x → J x=standardJ n) :
    ∃ C M θ : ℝ,0<C ∧ 0≤M ∧ 0<θ ∧ θ<1 ∧
      ∀ t∈Icc (0:ℝ) 1,∀ (p q : Phase n) (u : ℂ → Phase n),
        AffineLineCurve (lineHomotopy J t) p q u →
        ∀ a : Phase n,Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 a) →
        ∀ (c : ℂ) (k : ℕ),radialCurveEnergy (centeredCurve u c) ((1/16)^k)≤
          (C+M*stdDot n a a)*θ^k := by
  obtain ⟨C,M,θ,hC,hM,hθ,hθ1,he⟩ := exact_line_uniform_local_energy hJs hJ hJc hST hT hout
  refine ⟨C,M,θ,hC,hM,hθ,hθ1,?_⟩
  intro t ht p q u hu a ha c k
  obtain ⟨a',ha',hlim,hbound⟩ := he t ht p q u hu
  have haa : a'=a := tendsto_nhds_unique hlim ha
  subst a'
  simpa only [one_div_pow,mul_comm] using hbound c k


end
open scoped ContDiff Topology
open Set Function Filter MeasureTheory



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.exact_line_local_energy_of_slope_bp240_oai := @OAI.HigherDimensionalBallPacking.Rigidity.exact_line_local_energy_of_slope_bp240_oai
