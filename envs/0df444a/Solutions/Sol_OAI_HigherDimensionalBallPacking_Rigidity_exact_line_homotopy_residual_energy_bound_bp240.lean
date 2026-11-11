-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.exact_line_homotopy_residual_energy_bound_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:55:26.01241+00:00
-- url     : https://prove2.me/submissions/d1f659dc-f62e-42bb-ab75-291f7636528b

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp021

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

theorem radialSwitch_smooth (σ τ : ℝ) : ContDiff ℝ ∞ (radialSwitch σ τ) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

theorem radialSwitch_nonneg (σ τ t : ℝ) : 0 ≤ radialSwitch σ τ t :=
  Real.smoothTransition.nonneg _

theorem radialSwitch_le_one (σ τ t : ℝ) : radialSwitch σ τ t ≤ 1 :=
  Real.smoothTransition.le_one _

theorem radialSwitch_zero {σ τ t : ℝ} (hστ : σ < τ) (ht : t ≤ σ) :
    radialSwitch σ τ t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sub_pos.mpr hστ).le

theorem radialSwitch_one {σ τ t : ℝ} (hστ : σ < τ) (ht : τ ≤ t) :
    radialSwitch σ τ t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  apply (le_div_iff₀ (sub_pos.mpr hστ)).mpr
  linarith

theorem radialOffset_hasDerivAt (σ τ t : ℝ) :
    HasDerivAt (radialOffset σ τ) (radialSwitch σ τ t) t := by
  have hc := (radialSwitch_smooth σ τ).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem radialOffset_smooth (σ τ : ℝ) : ContDiff ℝ ∞ (radialOffset σ τ) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun t => (radialOffset_hasDerivAt σ τ t).differentiableAt,?_⟩
  have he : deriv (radialOffset σ τ) = radialSwitch σ τ :=
    funext (fun t => (radialOffset_hasDerivAt σ τ t).deriv)
  rw [he]
  exact radialSwitch_smooth σ τ

theorem radialOffset_zero {σ τ t : ℝ} (hστ : σ < τ) (ht : t ≤ σ) :
    radialOffset σ τ t = 0 := by
  unfold radialOffset
  calc
    (∫ s in σ..t, radialSwitch σ τ s) = ∫ s in σ..t, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact radialSwitch_zero hστ ((uIcc_of_ge ht ▸ hs).2)
    _ = 0 := by simp

theorem radialOffset_nonneg {σ τ : ℝ} (hστ : σ < τ) (t : ℝ) :
    0 ≤ radialOffset σ τ t := by
  by_cases ht : t ≤ σ
  · rw [radialOffset_zero hστ ht]
  · exact intervalIntegral.integral_nonneg (le_of_not_ge ht)
      (fun s _ => radialSwitch_nonneg σ τ s)

theorem radialShift_pos {σ τ : ℝ} (hστ : σ < τ) (hτ : τ < 1) :
    0 < radialShift σ τ := by
  have hn := radialOffset_nonneg hστ τ
  unfold radialShift
  linarith

theorem radialOffset_after {σ τ t : ℝ} (hστ : σ < τ) (ht : τ ≤ t) :
    1 + radialOffset σ τ t = t + radialShift σ τ := by
  have hc := (radialSwitch_smooth σ τ).continuous
  have he := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) σ τ) (hc.intervalIntegrable τ t)
  have hI : (∫ s in τ..t, radialSwitch σ τ s) = t-τ := by
    calc
      _ = ∫ s in τ..t, (1:ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        exact radialSwitch_one hστ ((uIcc_of_le ht ▸ hs).1)
      _ = t-τ := by simp
  rw [hI] at he
  change radialOffset σ τ τ + (t-τ) = radialOffset σ τ t at he
  unfold radialShift
  linarith

theorem radialCoefficient_smooth {σ τ : ℝ} (hστ : σ < τ) :
    ContDiff ℝ ∞ (radialCoefficient σ τ) :=
  (contDiff_const.add (radialOffset_smooth σ τ)).inv
    (fun t => ne_of_gt (by linarith [radialOffset_nonneg hστ t]))

theorem radialCoefficient_hasDerivAt {σ τ : ℝ} (hστ : σ < τ) (t : ℝ) :
    HasDerivAt (radialCoefficient σ τ)
      (-radialSwitch σ τ t / (1 + radialOffset σ τ t)^2) t := by
  have hd : HasDerivAt (fun x : ℝ => 1 + radialOffset σ τ x) (radialSwitch σ τ t) t :=
    (radialOffset_hasDerivAt σ τ t).const_add 1
  exact hd.inv (ne_of_gt (by linarith [radialOffset_nonneg hστ t]))

theorem radialCoefficient_one {σ τ t : ℝ} (hστ : σ < τ) (ht : t ≤ σ) :
    radialCoefficient σ τ t = 1 := by
  simp only [radialCoefficient,radialOffset_zero hστ ht,add_zero,inv_one]

theorem radialCoefficient_after {σ τ t : ℝ} (hστ : σ < τ) (ht : τ ≤ t) :
    radialCoefficient σ τ t = (t + radialShift σ τ)⁻¹ := by
  rw [radialCoefficient,radialOffset_after hστ ht]

theorem radialMoment_derivative_pos {σ τ : ℝ} (hστ : σ < τ) (hτ : τ < 1) (t : ℝ) :
    0 < (1 + radialOffset σ τ t - t * radialSwitch σ τ t) /
      (1 + radialOffset σ τ t)^2 := by
  apply div_pos _ (sq_pos_of_pos (by linarith [radialOffset_nonneg hστ t]))
  by_cases htσ : t ≤ σ
  · rw [radialOffset_zero hστ htσ,radialSwitch_zero hστ htσ]
    norm_num
  by_cases htτ : t ≤ τ
  · have ht1 : t < 1 := htτ.trans_lt hτ
    have hs0 := radialSwitch_nonneg σ τ t
    have hs1 := radialSwitch_le_one σ τ t
    have hφ := radialOffset_nonneg hστ t
    have hm : t * radialSwitch σ τ t < 1 := by
      by_cases ht0 : 0 ≤ t
      · exact (mul_le_mul_of_nonneg_left hs1 ht0).trans_lt (by simpa using ht1)
      · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge ht0) hs0).trans_lt zero_lt_one
    linarith
  · have htτ' : τ ≤ t := le_of_not_ge htτ
    rw [radialOffset_after hστ htτ',radialSwitch_one hστ htτ',mul_one]
    linarith [radialShift_pos hστ hτ]

theorem radialMoment_after {σ τ t : ℝ} (hστ : σ < τ) (ht : τ ≤ t) :
    radialMoment σ τ t = t / (t + radialShift σ τ) := by
  rw [radialMoment, radialCoefficient_after hστ ht,div_eq_mul_inv]

theorem radialMoment_tendsto_one {σ τ : ℝ} (hστ : σ < τ) :
    Tendsto (radialMoment σ τ) atTop (𝓝 1) := by
  have ht : Tendsto (fun t : ℝ => t + radialShift σ τ) atTop atTop :=
    Filter.tendsto_atTop_add_const_right _ _ tendsto_id
  have hc : Tendsto (fun t : ℝ => radialShift σ τ / (t + radialShift σ τ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop ht
  have hl : Tendsto (fun t : ℝ => 1 - radialShift σ τ / (t + radialShift σ τ))
      atTop (𝓝 1) := by simpa using tendsto_const_nhds.sub hc
  apply hl.congr'
  filter_upwards [eventually_ge_atTop τ, eventually_gt_atTop (-radialShift σ τ)] with t htτ ht0
  rw [radialMoment_after hστ htτ]
  have hn : t + radialShift σ τ ≠ 0 := by linarith
  field_simp
  ring



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_RadialForm
attribute [-instance] _root_.OAI.HigherDimensionalBallPacking.Rigidity.squareMeasure_finite _root_.OAI.HigherDimensionalBallPacking.Rigidity.translatedSquare_finite _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.parameters_nonzero _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrame_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedDX_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedQ_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedStructureJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficientHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficient_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrderHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrder_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frozenTargetCoefficient_zero _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothAlongJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothMarkedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.geometricHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.normalizedPrimitive_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.realCurve_zero _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.SymplecticBallPacking.Hamiltonian.coordinateForm_apply
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

theorem radialSlope_nonpos (σ τ t : ℝ) : radialSlope σ τ t ≤ 0 :=
  div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (radialSwitch_nonneg σ τ t)) (sq_nonneg _)

theorem radialSlope_zero {σ τ t : ℝ} (hστ : σ < τ) (ht : t ≤ σ) :
    radialSlope σ τ t = 0 := by simp [radialSlope, radialSwitch_zero hστ ht]

theorem radialMoment_derivative_eq {σ τ : ℝ} (hστ : σ < τ) (t : ℝ) :
    radialCoefficient σ τ t + t * radialSlope σ τ t =
      (1 + radialOffset σ τ t - t * radialSwitch σ τ t) / (1 + radialOffset σ τ t)^2 := by
  have hn : 1 + radialOffset σ τ t ≠ 0 :=
    ne_of_gt (by linarith [radialOffset_nonneg hστ t])
  unfold radialCoefficient radialSlope
  field_simp
  ring

theorem radialForm_standard {n : ℕ} {σ τ : ℝ} (hστ : σ < τ) {x : Phase n}
    (hx : capacity x ≤ σ) (v w : Phase n) :
    radialForm σ τ x v w = standardForm v w := by
  simp only [radialForm, radialCoefficient_one hστ hx,radialSlope_zero hστ hx,
    one_mul,mul_zero,zero_mul,add_zero]

theorem radialForm_J_pos {n : ℕ} {σ τ : ℝ} (hστ : σ < τ) (hτ : τ < 1)
    (x : Phase n) {v : Phase n} (hv : v ≠ 0) :
    0 < radialForm σ τ x v (standardJ n v) := by
  have hcs := stdDot_standardForm_sq_le x v
  have hs : Real.pi * radialSlope σ τ (capacity x) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le (radialSlope_nonpos _ _ _)
  have hm := mul_le_mul_of_nonpos_left hcs hs
  have hp := mul_pos (radialMoment_derivative_pos hστ hτ (capacity x)) (stdDot_pos hv)
  rw [←radialMoment_derivative_eq hστ] at hp
  simp only [radialForm, standardForm_J_right, stdDot_J_right]
  rw [capacity_eq_stdDot] at hp hm ⊢
  nlinarith only [hm,hp]

theorem radialForm_adapted_pos {n : ℕ} {σ τ : ℝ} (hστ : σ < τ) (hτ : τ < 1)
    {J : Phase n → End n} (hJ : ∀ x, Compatible (J x))
    (houtside : ∀ x, σ < capacity x → J x = standardJ n) (x : Phase n)
    {v : Phase n} (hv : v ≠ 0) : 0 < radialForm σ τ x v (J x v) := by
  by_cases hx : capacity x ≤ σ
  · rw [radialForm_standard hστ hx]
    exact (hJ x).2.2 v hv
  · rw [houtside x (lt_of_not_ge hx)]
    exact radialForm_J_pos hστ hτ x hv

theorem capacity_smooth (n : ℕ) : ContDiff ℝ ∞ (@capacity n) := by
  have hd : ContDiff ℝ ∞ (fun x : Phase n => stdDot n x x) :=
    ((stdDot n).contDiff.comp contDiff_id).clm_apply contDiff_id
  have he : (@capacity n) = fun y => Real.pi * stdDot n y y := funext capacity_eq_stdDot
  rw [he]
  exact contDiff_const.mul hd

theorem capacity_hasFDerivAt {n : ℕ} (x : Phase n) :
    HasFDerivAt capacity ((2 * Real.pi) • stdDot n x) x := by
  have hd := ((stdDot n).hasFDerivAt).clm_apply (hasFDerivAt_id x)
  have hh := hd.const_mul Real.pi
  have he : Real.pi • ((stdDot n x).comp (ContinuousLinearMap.id ℝ (Phase n)) +
      (stdDot n).flip x) = (2 * Real.pi) • stdDot n x := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [smul_apply, add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.flip_apply, smul_eq_mul]
    rw [stdDot_symm v x]
    ring
  simp only [id_eq] at hh
  rw [he] at hh
  have hefunc : (@capacity n) = fun y => Real.pi * stdDot n y y := funext capacity_eq_stdDot
  rw [hefunc]
  exact hh

theorem radialPrimitiveCLM_smooth {n : ℕ} {σ τ : ℝ} (hστ : σ < τ) :
    ContDiff ℝ ∞ (@radialPrimitiveCLM n σ τ) :=
  (((radialCoefficient_smooth hστ).comp (capacity_smooth n)).div_const 2).smul
    (stdOmega n).contDiff

theorem radialPrimitiveCLM_derivative {n : ℕ} {σ τ : ℝ} (hστ : σ < τ)
    (x v w : Phase n) :
    fderiv ℝ (radialPrimitiveCLM σ τ) x v w =
      (radialCoefficient σ τ (capacity x) / 2) * standardForm v w +
      Real.pi * radialSlope σ τ (capacity x) * stdDot n x v * standardForm x w := by
  have hg : HasFDerivAt (fun y : Phase n => radialCoefficient σ τ (capacity y) / 2)
      ((radialSlope σ τ (capacity x) / 2) • ((2 * Real.pi) • stdDot n x)) x := by
    have hc := ((radialCoefficient_hasDerivAt hστ (capacity x)).div_const 2).comp_hasFDerivAt x
      (capacity_hasFDerivAt x)
    exact hc
  have hd := hg.smul (stdOmega n).hasFDerivAt
  change HasFDerivAt (radialPrimitiveCLM σ τ) _ x at hd
  rw [hd.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, stdOmega_apply]
  ring

theorem radialPrimitive_smooth {n : ℕ} {σ τ : ℝ} (hστ : σ < τ) :
    ContDiff ℝ ∞ (@radialPrimitive n σ τ) := by
  exact (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := Phase n) (F := ℝ)
    (0 : Fin 1)).toContinuousLinearEquiv.contDiff.comp (radialPrimitiveCLM_smooth hστ)

theorem radialForm_extDeriv {n : ℕ} {σ τ : ℝ} (hστ : σ < τ) (x v w : Phase n) :
    extDeriv (radialPrimitive σ τ) x ![v,w] = radialForm σ τ x v w := by
  rw [extDeriv_apply ((radialPrimitive_smooth hστ).differentiable (by simp) x)]
  rw [Fin.sum_univ_succ]
  simp only [Fin.sum_univ_one, Fin.val_zero, pow_zero, one_smul, Fin.val_succ,
    pow_one, neg_smul, zero_add]
  change fderiv ℝ (fun y => radialPrimitiveCLM σ τ y w) x v -
    fderiv ℝ (fun y => radialPrimitiveCLM σ τ y v) x w = _
  have he (a b : Phase n) :
      fderiv ℝ (fun y => radialPrimitiveCLM σ τ y a) x b =
        fderiv ℝ (radialPrimitiveCLM σ τ) x b a := by
    rw [fderiv_clm_apply ((radialPrimitiveCLM_smooth hστ).differentiable (by simp) x)
      (differentiableAt_const a)]
    simp
  rw [he w v,he v w]
  rw [radialPrimitiveCLM_derivative hστ, radialPrimitiveCLM_derivative hστ,
    standardForm_skew w v]
  unfold radialForm
  ring

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

theorem AffineLineCurve.analytic_at_infinity {n : ℕ} {J : Phase n → End n}
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u)
    (hJc : HasCompactSupport (fun x => J x - standardJ n)) :
    ∃ v : Phase n, v ≠ 0 ∧ AnalyticAt ℂ (infinityGerm u v) 0 ∧
      infinityGerm u v 0 = v := by
  obtain ⟨v,hv,hlim⟩ := hu.2.2.2.2
  exact ⟨v,hv,infinityGerm_analyticAt (hu.holomorphic_at_infinity hJc) hlim,by simp [infinityGerm]⟩

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

theorem curvePrimitive_smooth {n : ℕ} {σ τ : ℝ} (hστ : σ < τ)
    {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (curvePrimitive σ τ u) :=
  planarPullback_smooth (realCurve_smooth hu) (radialPrimitiveCLM_smooth hστ)

theorem curvePrimitive_curl {n : ℕ} {σ τ : ℝ} (hστ : σ < τ)
    {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (z : Plane) :
    planarCurl (curvePrimitive σ τ u) z = curveDensity σ τ u z := by
  rw [curvePrimitive,planarPullback_curl (realCurve_smooth hu) (radialPrimitiveCLM_smooth hστ)]
  exact radialForm_extDeriv hστ _ _ _

theorem curveDensity_nonneg {n : ℕ} {σ τ : ℝ} (hστ : σ < τ) (hτ : τ < 1)
    {J : Phase n → End n} (hJ : ∀ x, Compatible (J x))
    (houtside : ∀ x, σ < capacity x → J x = standardJ n)
    {u : ℂ → Phase n} (hu : ∀ w, PseudoHolomorphicAt J u w) (z : Plane) :
    0 ≤ curveDensity σ τ u z := by
  unfold curveDensity
  rw [realCurve_CR (hu _)]
  by_cases hz : fderiv ℝ (realCurve u) z (1,0) = 0
  · simp only [hz,map_zero,radialForm,standardForm,Pi.zero_apply,
      Complex.zero_re,Complex.zero_im,mul_zero,sub_self,Finset.sum_const_zero,
      add_zero]
    exact le_refl _
  · exact (radialForm_adapted_pos hστ hτ hJ houtside _ hz).le


end

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory



open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)

theorem capacity_smul_complex {n : ℕ} (c : ℂ) (x : Phase n) :
    capacity (c • x) = Complex.normSq c * capacity x := by
  simp only [capacity,Pi.smul_apply,smul_eq_mul,Complex.normSq_mul,Finset.mul_sum]
  ring_nf

theorem standardForm_smul_complex_same {n : ℕ} (c : ℂ) (x v : Phase n) :
    standardForm (c • x) (c • v) = Complex.normSq c * standardForm x v := by
  simp only [standardForm,Pi.smul_apply,smul_eq_mul,Complex.mul_re,Complex.mul_im,
    Finset.mul_sum,Complex.normSq_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem standardForm_smul_complex_self {n : ℕ} (c d : ℂ) (x : Phase n) :
    standardForm (c • x) (d • x) = (star c * d).im * stdDot n x x := by
  simp only [standardForm,Pi.smul_apply,smul_eq_mul,Complex.mul_re,Complex.mul_im,
    stdDot_apply,Finset.mul_sum,Complex.star_def,Complex.conj_re,Complex.conj_im]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem capacity_pos {n : ℕ} {x : Phase n} (hx : x ≠ 0) : 0 < capacity x := by
  rw [capacity_eq_stdDot]
  exact mul_pos Real.pi_pos (stdDot_pos hx)

theorem normalizedPrimitive_smoothAt {n : ℕ} {x : Phase n} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (@normalizedPrimitive n) x :=
  (contDiffAt_const.div (contDiffAt_const.mul (capacity_smooth n).contDiffAt)
    (mul_ne_zero (by norm_num) (capacity_pos hx).ne')).smul (stdOmega n).contDiff.contDiffAt

theorem normalizedPrimitive_smul {n : ℕ} {c : ℂ} (hc : c ≠ 0)
    {x : Phase n} (hx : x ≠ 0) (d : ℂ) (v : Phase n) :
    normalizedPrimitive (c • x) (d • x + c • v) =
      (c⁻¹ * d).im / (2 * Real.pi) + normalizedPrimitive x v := by
  rw [normalizedPrimitive_apply,←stdOmega_apply,map_add,stdOmega_apply,stdOmega_apply,
    standardForm_smul_complex_self,standardForm_smul_complex_same,
    capacity_smul_complex,normalizedPrimitive_apply,capacity_eq_stdDot]
  have hn : Complex.normSq c ≠ 0 := (Complex.normSq_pos.mpr hc).ne'
  have hx' : stdDot n x x ≠ 0 := (stdDot_pos hx).ne'
  have he : (c⁻¹ * d).im = (star c * d).im / Complex.normSq c := by
    simp only [Complex.mul_im,Complex.inv_re,Complex.inv_im,Complex.star_def,
      Complex.conj_re,Complex.conj_im]
    ring
  rw [he]
  field_simp


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
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrame_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedDX_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedQ_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedStructureJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficientHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficient_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrderHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrder_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frozenTargetCoefficient_zero _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothMarkedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.geometricHolder_value _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.SymplecticBallPacking.Hamiltonian.coordinateForm_apply
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

theorem complex_inv_fderiv_real {z : ℂ} (hz : z ≠ 0) (w : ℂ) :
    fderiv ℝ (fun y : ℂ => y⁻¹) z w = -(z^2)⁻¹ * w := by
  rw [((hasDerivAt_inv hz).hasFDerivAt.restrictScalars ℝ).fderiv]
  change w * (-(z^2)⁻¹) = _
  ring

theorem infinity_curve_fderiv {n : ℕ} {h : ℂ → Phase n} {z : ℂ}
    (hz : z ≠ 0) (hh : DifferentiableAt ℝ h z⁻¹) (w : ℂ) :
    fderiv ℝ (fun y : ℂ => y • h y⁻¹) z w =
      w • h z⁻¹ + z • fderiv ℝ h z⁻¹ (-(z^2)⁻¹ * w) := by
  have hi : DifferentiableAt ℝ (fun y : ℂ => y⁻¹) z :=
    (hasDerivAt_inv hz).differentiableAt.restrictScalars ℝ
  have hid : DifferentiableAt ℝ (fun y : ℂ => y) z := differentiableAt_id
  have hcomp : DifferentiableAt ℝ (fun y : ℂ => h y⁻¹) z := hh.comp z hi
  rw [fderiv_fun_smul hid hcomp]
  simp only [add_apply,smul_apply,ContinuousLinearMap.smulRight_apply,fderiv_fun_id,
    ContinuousLinearMap.id_apply]
  have hder : HasFDerivAt (fun y : ℂ => h y⁻¹)
      ((fderiv ℝ h z⁻¹).comp (fderiv ℝ (fun y : ℂ => y⁻¹) z)) z :=
    hh.hasFDerivAt.comp z hi.hasFDerivAt
  rw [hder.fderiv,ContinuousLinearMap.comp_apply,complex_inv_fderiv_real hz]
  module

theorem normalizedPrimitive_infinity_curve {n : ℕ} {h : ℂ → Phase n} {z : ℂ}
    (hz : z ≠ 0) (hh : DifferentiableAt ℝ h z⁻¹) (hh0 : h z⁻¹ ≠ 0) :
    normalizedPrimitive (z • h z⁻¹) (fderiv ℝ (fun y : ℂ => y • h y⁻¹) z (Complex.I*z)) =
      1 / (2 * Real.pi) +
      normalizedPrimitive (h z⁻¹) (fderiv ℝ h z⁻¹ (-Complex.I*z⁻¹)) := by
  rw [infinity_curve_fderiv hz hh,normalizedPrimitive_smul hz hh0]
  have h1 : z⁻¹ * (Complex.I*z) = Complex.I := by field_simp
  have h2 : -(z^2)⁻¹ * (Complex.I*z) = -Complex.I*z⁻¹ := by field_simp
  rw [h1,h2,Complex.I_im]

theorem infinityGerm_curve_eventuallyEq {n : ℕ} (u : ℂ → Phase n) (v : Phase n) :
    u =ᶠ[cocompact ℂ] fun z : ℂ => z • infinityGerm u v z⁻¹ := by
  filter_upwards [(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz
  have hz' : z ≠ 0 := hz
  simp only [infinityGerm,inv_ne_zero hz',ite_false, if_false,inv_inv,smul_smul,
    mul_inv_cancel₀ hz',one_smul]

theorem normalizedPrimitive_infinity_limit {n : ℕ} {u : ℂ → Phase n} {v : Phase n}
    (hv : v ≠ 0) (hh : AnalyticAt ℂ (infinityGerm u v) 0) :
    Tendsto (fun z : ℂ => normalizedPrimitive (u z) (fderiv ℝ u z (Complex.I*z)))
      (cocompact ℂ) (𝓝 (1 / (2 * Real.pi))) := by
  let h := infinityGerm u v
  have hh0 : h 0 ≠ 0 := by simpa [h,infinityGerm] using hv
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa only [←Metric.cobounded_eq_cocompact] using (tendsto_inv₀_cobounded (α := ℂ))
  have hc : ContDiffAt ℝ ∞ h 0 := hh.contDiffAt.restrict_scalars ℝ
  have hdh : Tendsto (fun z : ℂ => fderiv ℝ h z⁻¹) (cocompact ℂ) (𝓝 (fderiv ℝ h 0)) :=
    (hc.fderiv_right (m := 0) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuousAt.tendsto.comp hi
  have harg : Tendsto (fun z : ℂ => -Complex.I*z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa using hi.const_mul (-Complex.I)
  have hvec : Tendsto (fun z : ℂ => fderiv ℝ h z⁻¹ (-Complex.I*z⁻¹))
      (cocompact ℂ) (𝓝 0) := by
    simpa only [Function.comp_def,map_zero] using (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp (hdh.prodMk_nhds harg)
  have hprim : Tendsto (fun z : ℂ => normalizedPrimitive (h z⁻¹))
      (cocompact ℂ) (𝓝 (normalizedPrimitive (h 0))) :=
    (normalizedPrimitive_smoothAt hh0).continuousAt.tendsto.comp (hc.continuousAt.tendsto.comp hi)
  have hl : Tendsto (fun z : ℂ => 1 / (2 * Real.pi) +
      normalizedPrimitive (h z⁻¹) (fderiv ℝ h z⁻¹ (-Complex.I*z⁻¹)))
      (cocompact ℂ) (𝓝 (1 / (2 * Real.pi))) := by
    simpa only [Function.comp_def,map_zero,add_zero] using ((continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp (hprim.prodMk_nhds hvec)).const_add (1 / (2 * Real.pi))
  apply hl.congr'
  have he := infinityGerm_curve_eventuallyEq u v
  have hnear : ∀ᶠ z in cocompact ℂ, u =ᶠ[𝓝 z] fun y : ℂ => y • h y⁻¹ := by
    filter_upwards [(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz
    filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hz] with y hy
    have hy' : y ≠ 0 := hy
    simp only [h,infinityGerm,inv_ne_zero hy',ite_false, if_false,inv_inv,smul_smul,
      mul_inv_cancel₀ hy',one_smul]
  have hn : ∀ᶠ w in 𝓝 (0:ℂ), h w ≠ 0 :=
    hc.continuousAt.eventually (isClosed_singleton.isOpen_compl.mem_nhds hh0)
  have hd : ∀ᶠ w in 𝓝 (0:ℂ), DifferentiableAt ℝ h w :=
    hh.eventually_analyticAt.mono fun _ hx => hx.differentiableAt.restrictScalars ℝ
  filter_upwards [hnear,hi.eventually hn,hi.eventually hd,
    (isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hez hnz hdz hz
  rw [hez.self_of_nhds,hez.fderiv_eq]
  exact (normalizedPrimitive_infinity_curve hz hdz hnz).symm

theorem equivRealProd_rotation (z : Plane) :
    Complex.equivRealProdCLM.symm (planeRotation z) =
      Complex.I * Complex.equivRealProdCLM.symm z := by
  apply Complex.ext <;> simp [planeRotation,Complex.equivRealProdCLM_symm_apply]



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_CorrectedInfinity
attribute [-instance] _root_.OAI.HigherDimensionalBallPacking.Rigidity.squareMeasure_finite _root_.OAI.HigherDimensionalBallPacking.Rigidity.translatedSquare_finite _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrame_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedDX_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedQ_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedStructureJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficientHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficient_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrderHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrder_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frozenTargetCoefficient_zero _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothAlongJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothMarkedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.geometricHolder_value _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.SymplecticBallPacking.Hamiltonian.coordinateForm_apply
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
open SymplecticBallPacking.Hamiltonian (Plane)

theorem radialPrimitiveCLM_eq_moment {n : ℕ} (S T : ℝ) {x : Phase n}
    (hx : x ≠ 0) :
    radialPrimitiveCLM S T x = radialMoment S T (capacity x) • normalizedPrimitive x := by
  unfold radialPrimitiveCLM normalizedPrimitive radialMoment
  rw [smul_smul]
  congr 1
  have hn := (capacity_pos hx).ne'
  field_simp

theorem capacity_tendsto_atTop (n : ℕ) :
    Tendsto (@capacity n) (cocompact (Phase n)) atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [(closedBall_isCompact n b).compl_mem_cocompact] with x hx
  have hx' : ¬ capacity x ≤ b := hx
  exact (lt_of_not_ge hx').le

theorem AffineLineCurve.radial_infinity_limit {n : ℕ} {J : Phase n → End n}
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u)
    (hJc : HasCompactSupport (fun x => J x - standardJ n))
    {S T : ℝ} (hST : S < T) :
    Tendsto (fun z : Plane => planarPullback (realCurve u) (radialPrimitiveCLM S T) z
      (planeRotation z)) (cocompact Plane) (𝓝 (1 / (2 * Real.pi))) := by
  obtain ⟨v,hv,hh,_⟩ := hu.analytic_at_infinity hJc
  have hr : Tendsto Complex.equivRealProdCLM.symm (cocompact Plane) (cocompact ℂ) :=
    Complex.equivRealProdCLM.symm.toHomeomorph.isClosedEmbedding.tendsto_cocompact
  have hul : Tendsto (realCurve u) (cocompact Plane) (cocompact (Phase n)) :=
    hu.tendsto_cocompact.comp hr
  have hn : Tendsto (fun z : Plane => planarPullback (realCurve u) normalizedPrimitive z
      (planeRotation z)) (cocompact Plane) (𝓝 (1 / (2 * Real.pi))) := by
    have ht := (normalizedPrimitive_infinity_limit hv hh).comp hr
    apply ht.congr
    intro z
    change normalizedPrimitive _ _ = normalizedPrimitive _ _
    have he := realCurve_fderiv (z := z) ((hu.1.differentiable (by simp)) _) (planeRotation z)
    rw [equivRealProd_rotation] at he
    exact congrArg (normalizedPrimitive (u (Complex.equivRealProdCLM.symm z))) he.symm
  have hm : Tendsto (fun z : Plane => radialMoment S T (capacity (realCurve u z)))
      (cocompact Plane) (𝓝 1) :=
    (radialMoment_tendsto_one hST).comp ((capacity_tendsto_atTop n).comp hul)
  have ht : Tendsto (fun z : Plane => radialMoment S T (capacity (realCurve u z)) *
      planarPullback (realCurve u) normalizedPrimitive z (planeRotation z))
      (cocompact Plane) (𝓝 (1 / (2 * Real.pi))) := by
    simpa only [one_mul] using hm.mul hn
  apply ht.congr'
  filter_upwards [hul.eventually (isCompact_singleton (x := (0 : Phase n))).compl_mem_cocompact] with z hz
  unfold planarPullback
  rw [radialPrimitiveCLM_eq_moment S T hz]
  rfl


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory



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
open Set Filter
namespace HigherDimensionalBallPacking.Rigidity
variable {n : ℕ}

local instance ceInst1_ra421ca_1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance ceInst2_ra421ca_1 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
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

lemma integral_compact_le_infinity_flux {β : Plane → Plane →L[ℝ] ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcurl : ∀ z, 0≤planarCurl β z) {k : ℝ}
    (hlim : Tendsto (fun z => β z (planeRotation z)) (cocompact Plane) (𝓝 k))
    {e : Plane → ℝ} (he : Continuous e) (hc : HasCompactSupport e)
    (hle : ∀ z, e z≤planarCurl β z) : (∫ z, e z)≤2*Real.pi*k := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hp : 0<2*Real.pi := by positivity
  have heps : k<k+ε/(2*Real.pi) := lt_add_of_pos_right _ (div_pos hε hp)
  have hev : ∀ᶠ z in cocompact Plane, β z (planeRotation z)≤k+ε/(2*Real.pi) :=
    (hlim.eventually (eventually_lt_nhds heps)).mono fun _ h => h.le
  obtain ⟨K,hK,hKb⟩ := mem_cocompact.mp hev
  obtain ⟨A,hA,hbound⟩ := radiusSq_pos_bound_of_compact (hK.union hc)
  let g := outerProfile A
  have hg : ContDiff ℝ ∞ g := outerProfile_smooth A
  have hgc : HasCompactSupport g := outerProfile_compact hA
  have hdom (z : Plane) : e z≤g (radiusSq z)*planarCurl β z := by
    by_cases hz : z∈tsupport e
    · have hga : g (radiusSq z)=1 :=
        outerProfile_one_before (radiusSq_nonneg z) (hbound z (Or.inr hz)).le hA
      rw [hga,one_mul]
      exact hle z
    · rw [image_eq_zero_of_notMem_tsupport hz]
      exact mul_nonneg (outerProfile_nonneg A _) (hcurl z)
  have hcomp (z : Plane) :
      2*deriv g (radiusSq z)*(k+ε/(2*Real.pi))≤
        cutoffWedge (fun y => g (radiusSq y)) β z := by
    rw [cutoffWedge_radial_rotation hg]
    by_cases hd : deriv g (radiusSq z)=0
    · simp only [hd,mul_zero,zero_mul,le_refl]
    have hzA : A ≤ radiusSq z := by
      by_contra! h
      exact hd (outerProfile_deriv_zero_before hA (radiusSq_nonneg z) h)
    have hzK : z∉K := by
      intro hz
      exact (not_lt_of_ge hzA) (hbound z (Or.inl hz))
    exact mul_le_mul_of_nonpos_left (hKb hzK)
      (mul_nonpos_of_nonneg_of_nonpos (by norm_num) (outerProfile_deriv_nonpos hA (radiusSq_nonneg z)))
  have hdi : Integrable (fun z : Plane => 2*deriv g (radiusSq z)*(k+ε/(2*Real.pi))) :=
    ((((hg.continuous_deriv (by simp)).comp radiusSq_smooth.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.comp_radiusSq hgc.deriv)).const_mul 2).mul_const _
  have hwi := cutoffWedge_integrable (hg.comp radiusSq_smooth) (HasCompactSupport.comp_radiusSq hgc) hβ
  have hgi : Integrable (fun z => g (radiusSq z)*planarCurl β z) :=
    ((hg.continuous.comp radiusSq_smooth.continuous).mul
      (planarCurl_contDiff hβ).continuous).integrable_of_hasCompactSupport
        ((HasCompactSupport.comp_radiusSq hgc).mul_right)
  have hmass := integral_mono (he.integrable_of_hasCompactSupport hc) hgi hdom
  have hflux := integral_mono hdi hwi hcomp
  have hg0 : g 0=1 := outerProfile_zero_value hA
  rw [integral_mul_const,integral_radial_derivative hg hgc,hg0,mul_one] at hflux
  rw [integral_cutoffWedge (hg.comp radiusSq_smooth) (HasCompactSupport.comp_radiusSq hgc) hβ] at hflux
  dsimp only [Function.comp_def] at hflux
  have heq : (2*Real.pi)*(k+ε/(2*Real.pi))=2*Real.pi*k+ε := by
    field_simp
  nlinarith only [hmass,hflux,heq]

theorem AffineLineCurve.compact_density_mass_le_one {n : ℕ} {J : Phase n → End n}
    (hJ : ∀ x, Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1)
    (hout : ∀ x, S < capacity x → J x=standardJ n)
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u)
    {e : Plane → ℝ} (he : Continuous e) (hc : HasCompactSupport e)
    (hle : ∀ z, e z ≤ curveDensity S T u z) : (∫ z, e z)≤1 := by
  have hh := integral_compact_le_infinity_flux (curvePrimitive_smooth hST hu.1)
    (fun z => (curvePrimitive_curl hST hu.1 z).symm ▸ curveDensity_nonneg hST hT hJ hout hu.2.1 z)
    (hu.radial_infinity_limit hJc hST) he hc
    (fun z => (curvePrimitive_curl hST hu.1 z).symm ▸ hle z)
  have heq : 2*Real.pi*(1/(2*Real.pi))=1 := by field_simp
  exact heq ▸ hh

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

local instance gcInst1_ra421ca_1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance gcInst2_ra421ca_1 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
local instance gcInst3_ra421ca_1 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance gcInst4_ra421ca_1 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance gcInst5_ra421ca_1 : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance
local instance gcInst6_ra421ca_1 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
local instance gcInst7_ra421ca_1 (K : Set ℂ) : NormedAddCommGroup (markedModel (E := Phase n) K) := inferInstance
local instance gcInst8_ra421ca_1 (K : Set ℂ) : NormedSpace ℝ (markedModel (E := Phase n) K) := inferInstance
local instance gcInst9_ra421ca_1 (K : Set ℂ) : NormedAddCommGroup (supportedHolder (E := Phase n) K) := inferInstance
local instance gcInst10_ra421ca_1 (K : Set ℂ) : NormedSpace ℝ (supportedHolder (E := Phase n) K) := inferInstance
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

lemma residualEnergy_le_radialDensity {J : Phase n → End n}
    (hJ : ∀ x, Compatible (J x)) {S T C : ℝ} (hST : S<T) (hT : T<1) (hC : 0≤C)
    (hout : ∀ x, S < capacity x → J x=standardJ n)
    (hbound : ∀ x∈closedBall n S, ∀ v : Phase n, defectEnergy (J x) v≤C*symplecticEnergy (J x) v)
    {u : ℂ → Phase n} (hus : ContDiff ℝ ∞ u) (hu : ∀ z, PseudoHolomorphicAt J u z) (z : Plane) :
    lineResidualEnergy u z≤C*curveDensity S T u z := by
  rw [lineResidualEnergy_eq_defect hus hu]
  by_cases hx : capacity (realCurve u z)≤S
  · have hh := hbound (realCurve u z) hx (fderiv ℝ (realCurve u) z (1,0))
    have hd : curveDensity S T u z=symplecticEnergy (J (realCurve u z))
        (fderiv ℝ (realCurve u) z (1,0)) := by
      rw [curveDensity,realCurve_CR (hu _),radialForm_standard hST hx]
      rw [symplecticEnergy, stdOmega_apply]
    rwa [hd]
  · rw [hout _ (lt_of_not_ge hx),defectEnergy_standard]
    exact mul_nonneg hC (curveDensity_nonneg hST hT hJ hout hu z)

theorem exact_line_homotopy_residual_energy_bound_bp240_oai {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1)
    (hout : ∀ x, S < capacity x → J x=standardJ n) :
    ∃ C : ℝ, 0<C ∧ ∀ t∈Icc (0:ℝ) 1, ∀ (p q : Phase n) (u : ℂ → Phase n),
      AffineLineCurve (lineHomotopy J t) p q u → (∫ z : Plane, lineResidualEnergy u z)≤C := by
  let K : Set (ℝ × Phase n) := (Icc (0:ℝ) 1) ×ˢ closedBall n S
  have hK : IsCompact K := isCompact_Icc.prod (closedBall_isCompact n S)
  have hAc : ContinuousOn (fun y : ℝ × Phase n => lineHomotopy J y.1 y.2) K :=
    (lineHomotopy_smooth hJs hJ).continuousOn.mono (fun _ h => ⟨h.1,mem_univ _⟩)
  obtain ⟨C,hC,hbound⟩ := exists_defectEnergy_bound hK hAc
    (fun y hy => lineHomotopy_compatible hJ hy.1 y.2)
  refine ⟨C,hC,?_⟩
  intro t ht p q u hu
  have hcom := lineHomotopy_compact hJc ht
  have hcon := lineResidualEnergy_continuous hu.1
  have hec := lineResidualEnergy_compact hu hcom
  have hle : ∀ z : Plane, lineResidualEnergy u z≤C*curveDensity S T u z :=
    residualEnergy_le_radialDensity (lineHomotopy_compatible hJ ht) hST hT hC.le
      (lineHomotopy_outside hout ht) (fun x hx v => hbound (t,x) ⟨ht,hx⟩ v) hu.1 hu.2.1
  have hm := hu.compact_density_mass_le_one (lineHomotopy_compatible hJ ht) hcom hST hT
    (lineHomotopy_outside hout ht) (hcon.div_const C) (hec.comp_left (g := fun x : ℝ => x/C) (by simp))
    (fun z => (div_le_iff₀ hC).mpr (by simpa only [mul_comm C] using hle z))
  rw [integral_div] at hm
  have hres := (div_le_iff₀ hC).mp hm
  simpa only [one_mul] using hres


end
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.exact_line_homotopy_residual_energy_bound_bp240_oai := @OAI.HigherDimensionalBallPacking.Rigidity.exact_line_homotopy_residual_energy_bound_bp240_oai
