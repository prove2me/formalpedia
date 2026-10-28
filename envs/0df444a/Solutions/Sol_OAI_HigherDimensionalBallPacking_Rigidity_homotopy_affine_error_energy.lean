-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.homotopy_affine_error_energy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T17:06:34.530216+00:00
-- url     : https://prove2.me/submissions/1c9b80b7-a164-4a71-a712-fceb75b5a8e4

import Mathlib
import Definitions.Def_BallPackingNecessity
import Definitions.Def_OAIQ10Bp006
import Definitions.Def_OAIQ10Bp007
import Definitions.Def_OAIQ10Bp008

section
-- module Solutions.OAIQ10_BP.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_CompatibleStructures
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

theorem standardForm_J_pos {n : ℕ} {v : Phase n} (hv : v ≠ 0) :
    0 < standardForm v (standardJ n v) := by
  rw [standardForm_J_self]
  have hi : ∃ i, v i ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  obtain ⟨i, hi⟩ := hi
  have hpos : 0 < Complex.normSq (v i) := Complex.normSq_pos.mpr hi
  exact hpos.trans_le (Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (v j))
    (Finset.mem_univ i))

theorem compatible_standardJ (n : ℕ) : Compatible (standardJ n) :=
  ⟨standardJ_sq n, standardForm_J_J, fun _ hv => standardForm_J_pos hv⟩

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

theorem stdDot_pos {n : ℕ} {v : Phase n} (hv : v ≠ 0) : 0 < stdDot n v v := by
  rw [← standardForm_J_right]
  exact standardForm_J_pos hv

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

theorem relativeOperator_positive {n : ℕ} {J : End n} (hJ : Compatible J)
    {v : Phase n} (hv : v ≠ 0) : 0 < stdDot n v (relativeOperator J v) := by
  rw [stdDot_relativeOperator]
  exact hJ.2.2 v hv

theorem cayleyP_invertible {n : ℕ} {J : End n} (hJ : Compatible J)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) : (cayleyP J b a).IsInvertible := by
  have hi : Injective (cayleyP J b a) := by
    apply (injective_iff_map_eq_zero (cayleyP J b a)).mpr
    intro v hv
    by_contra hne
    have hp := stdDot_pos hne
    have hA := relativeOperator_positive hJ hne
    have he : stdDot n v (cayleyP J b a v) =
        b * stdDot n v (relativeOperator J v) + a * stdDot n v v := by
      simp only [cayleyP_apply, map_add, map_smul, smul_eq_mul]
    rw [hv] at he
    simp only [map_zero] at he
    have hn := mul_nonneg hb hA.le
    have hh := mul_pos ha hp
    linarith
  have hs := (LinearMap.injective_iff_surjective (f := (cayleyP J b a).toLinearMap)).mp hi
  exact ⟨ContinuousLinearEquiv.ofBijective (cayleyP J b a)
    (LinearMap.ker_eq_bot.mpr hi) (LinearMap.range_eq_top.mpr hs), rfl⟩

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

theorem cayleyOperator_on_denominator {n : ℕ} {J : End n} {a b : ℝ}
    (hQ : (cayleyP J b a).IsInvertible) (v : Phase n) :
    cayleyOperator J a b (cayleyP J b a v) = cayleyP J a b v := by
  obtain ⟨e,he⟩ := hQ
  simp only [cayleyOperator, ←he, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inverse_equiv, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]

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

@[simp] theorem interpolateJ_zero {n : ℕ} {J : End n} (hJ : Compatible J) :
    interpolateJ J 0 = standardJ n := by
  have hQ := cayleyP_invertible hJ (a := 1) (b := 1) (by norm_num) (by norm_num)
  obtain ⟨e,he⟩ := hQ
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨x,rfl⟩ := e.surjective v
  change standardJ n (cayleyOperator J (1+0) (1-0) ((e : End n) x)) = standardJ n ((e : End n) x)
  simp only [add_zero, sub_zero, he, cayleyOperator_on_denominator ⟨e,he⟩]

@[simp] theorem interpolateJ_one {n : ℕ} {J : End n} (hJ : Compatible J) :
    interpolateJ J 1 = J := by
  have hQ := cayleyP_invertible hJ (a := 2) (b := 0) (by norm_num) (by norm_num)
  obtain ⟨e,he⟩ := hQ
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨x,rfl⟩ := e.surjective v
  change standardJ n (cayleyOperator J (1+1) (1-1) ((e : End n) x)) = J ((e : End n) x)
  norm_num only [he, show (1:ℝ)+1=2 by norm_num, sub_self,
    cayleyOperator_on_denominator ⟨e,he⟩]
  simp

theorem contDiffAt_interpolateJ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {J : E → End n} {t : E → ℝ} {x : E}
    (hJs : ContDiffAt ℝ ∞ J x) (hts : ContDiffAt ℝ ∞ t x)
    (hJ : Compatible (J x)) (ht : t x ∈ Icc (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (fun y => interpolateJ (J y) (t y)) x := by
  have hA : ContDiffAt ℝ ∞ (fun y => relativeOperator (J y)) x :=
    (contDiffAt_const.clm_comp hJs).neg
  have ha : ContDiffAt ℝ ∞ (fun y => 1 + t y) x := contDiffAt_const.add hts
  have hb : ContDiffAt ℝ ∞ (fun y => 1 - t y) x := contDiffAt_const.sub hts
  have hP : ContDiffAt ℝ ∞ (fun y => cayleyP (J y) (1+t y) (1-t y)) x :=
    (ha.smul hA).add (hb.smul contDiffAt_const)
  have hQ : ContDiffAt ℝ ∞ (fun y => cayleyP (J y) (1-t y) (1+t y)) x :=
    (hb.smul hA).add (ha.smul contDiffAt_const)
  have hQi := cayleyP_invertible hJ (show 0 < 1 + t x by linarith [ht.1])
    (show 0 ≤ 1 - t x by linarith [ht.2])
  have hI : ContDiffAt ℝ ∞ (fun y => (cayleyP (J y) (1-t y) (1+t y)).inverse) x :=
    ContDiffAt.comp x (g := ContinuousLinearMap.inverse)
      (ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse (n := ∞) hQi) hQ
  exact contDiffAt_const.clm_comp (hP.clm_comp hI)

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_Adapted
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

theorem interpolateJ_standard {n : ℕ} {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    interpolateJ (standardJ n) t = standardJ n := by
  have ha : 0 < 1+t := by linarith [ht.1]
  have hb : 0 ≤ 1-t := by linarith [ht.2]
  obtain ⟨e,he⟩ := cayleyP_invertible (compatible_standardJ n) ha hb
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨x,rfl⟩ := e.surjective v
  change standardJ n (cayleyOperator (standardJ n) (1+t) (1-t) ((e : End n) x)) =
    standardJ n ((e : End n) x)
  rw [he,cayleyOperator_on_denominator ⟨e,he⟩]
  congr 1
  simp only [cayleyP_apply,relativeOperator_apply,standardJ_sq,neg_neg]
  module

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

@[simp] theorem lineHomotopy_zero {n : ℕ} {J : Phase n → End n}
    (hJ : ∀ x, Compatible (J x)) (x : Phase n) : lineHomotopy J 0 x = standardJ n :=
  interpolateJ_zero (hJ x)

@[simp] theorem lineHomotopy_one {n : ℕ} {J : Phase n → End n}
    (hJ : ∀ x, Compatible (J x)) (x : Phase n) : lineHomotopy J 1 x = J x :=
  interpolateJ_one (hJ x)

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
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_RadialForm
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
    have H := (hg.differentiable (by simp) (r^2)).hasDerivAt.comp r ((hasDerivAt_id r).pow 2)
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
    HasCompactSupport.integral_Ioi_deriv_eq (hh.of_le (by simp)) hhC]
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
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_PlanarResidueCutoff
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
  (((hβ.fderiv_right (by simp)).clm_apply contDiff_const).clm_apply contDiff_const).sub
    (((hβ.fderiv_right (by simp)).clm_apply contDiff_const).clm_apply contDiff_const)

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
    rw [planarCurl_spatial_smul (hf.differentiable (by simp) z) (hβ.differentiable (by simp) z)]
    ring
  rw [he,integral_sub hci hgi,show (∫ z,planarCurl (fun y => f y • β y) z)=0 from compact_planar_stokes hp hpc,zero_sub]

theorem cutoffWedge_integrable {f : Plane → ℝ} {β : Plane → Plane →L[ℝ] ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hβ : ContDiff ℝ ∞ β) :
    Integrable (cutoffWedge f β) := by
  have h1 : ContDiff ℝ ∞ (fun z => fderiv ℝ f z (1,0)) := (hf.fderiv_right (by simp)).clm_apply (contDiff_const (c := ((1:ℝ),(0:ℝ))))
  have h2 : ContDiff ℝ ∞ (fun z => fderiv ℝ f z (0,1)) := (hf.fderiv_right (by simp)).clm_apply (contDiff_const (c := ((0:ℝ),(1:ℝ))))
  exact ((h1.mul (hβ.clm_apply contDiff_const)).continuous.integrable_of_hasCompactSupport
    (hc.fderiv_apply (𝕜 := ℝ) (1,0)).mul_right).sub
    ((h2.mul (hβ.clm_apply contDiff_const)).continuous.integrable_of_hasCompactSupport
    (hc.fderiv_apply (𝕜 := ℝ) (0,1)).mul_right)

end SymplecticBallPacking.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_CurveArea
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
  (hα.comp hv).clm_comp (hv.fderiv_right (by simp))

theorem oneForm_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α : E → E →L[ℝ] ℝ} (hα : ContDiff ℝ ∞ α) : ContDiff ℝ ∞ (oneForm α) :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ)
    (0 : Fin 1)).toContinuousLinearEquiv.contDiff.comp hα

theorem planarCurl_eq_extDeriv {α : Plane → Plane →L[ℝ] ℝ}
    (hα : ContDiff ℝ ∞ α) (z : Plane) :
    planarCurl α z = extDeriv (oneForm α) z ![(1,0),(0,1)] := by
  rw [extDeriv_apply ((oneForm_smooth hα).differentiable (by simp) z)]
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

theorem weightedPrimitive_differentiableAt {n : ℕ} {g : ℝ → ℝ} {x : Phase n}
    (hg : DifferentiableAt ℝ g (capacity x)) :
    DifferentiableAt ℝ (weightedPrimitive g) x :=
  ((hg.div_const (2 : ℝ)).comp x (capacity_hasFDerivAt x).differentiableAt).fun_smul
    (stdOmega n).differentiableAt

theorem weightedPrimitive_derivative {n : ℕ} {g : ℝ → ℝ} {dg : ℝ} {x : Phase n}
    (hg : HasDerivAt g dg (capacity x)) (v w : Phase n) :
    fderiv ℝ (weightedPrimitive g) x v w =
      (g (capacity x) / 2) * standardForm v w +
      Real.pi * dg * stdDot n x v * standardForm x w := by
  have hd := ((hg.div_const 2).comp_hasFDerivAt x (capacity_hasFDerivAt x)).smul
    (stdOmega n).hasFDerivAt
  change HasFDerivAt (weightedPrimitive g) _ x at hd
  rw [hd.fderiv]
  simp only [add_apply,smul_apply,ContinuousLinearMap.smulRight_apply,smul_eq_mul,stdOmega_apply,Function.comp_def]
  ring

theorem weightedPrimitive_extDeriv {n : ℕ} {g : ℝ → ℝ} {dg : ℝ} {x : Phase n}
    (hg : HasDerivAt g dg (capacity x)) (v w : Phase n) :
    extDeriv (oneForm (weightedPrimitive g)) x ![v,w] = weightedTwoForm (g (capacity x)) dg x v w := by
  have hα := weightedPrimitive_differentiableAt hg.differentiableAt
  have hω : DifferentiableAt ℝ (oneForm (weightedPrimitive g)) x :=
    (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := Phase n) (F := ℝ)
      (0 : Fin 1)).toContinuousLinearEquiv.differentiableAt.comp x hα
  rw [extDeriv_apply hω,Fin.sum_univ_succ]
  simp only [Fin.sum_univ_one, Fin.val_zero, pow_zero, one_smul, Fin.val_succ,
    pow_one, neg_smul, zero_add]
  change fderiv ℝ (fun y => weightedPrimitive g y w) x v -
    fderiv ℝ (fun y => weightedPrimitive g y v) x w = _
  have he (a b : Phase n) :
      fderiv ℝ (fun y => weightedPrimitive g y a) x b =
        fderiv ℝ (weightedPrimitive g) x b a := by
    rw [fderiv_clm_apply hα (differentiableAt_const a)]
    simp
  rw [he w v,he v w,weightedPrimitive_derivative hg,weightedPrimitive_derivative hg,
    standardForm_skew w v]
  unfold weightedTwoForm
  ring



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_Correction
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

theorem stdPrimitive_smooth (n : ℕ) : ContDiff ℝ ∞ (@stdPrimitive n) :=
  (contDiff_const (c := (1/2 : ℝ))).smul (stdOmega n).contDiff



open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)


end

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem stdPrimitive_extDeriv {n : ℕ} (x v w : Phase n) :
    extDeriv (oneForm stdPrimitive) x ![v,w] = standardForm v w := by
  have he : (@stdPrimitive n) = weightedPrimitive (fun _ => 1) := rfl
  rw [he,weightedPrimitive_extDeriv (hasDerivAt_const (capacity x) (1 : ℝ))]
  simp [weightedTwoForm]


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
  have hh := (hs.differentiable (by simp) ((t-A)/A)).hasDerivAt.comp t
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
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_AngularPoles
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
  simp only [infinityGerm,inv_ne_zero hz',ite_false,inv_inv,smul_smul,
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
    (hc.fderiv_right (m := 0) (by simp)).continuousAt.tendsto.comp hi
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
    simp only [h,infinityGerm,inv_ne_zero hy',ite_false,inv_inv,smul_smul,
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
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_CorrectedInfinity
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
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_GlobalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity

theorem outerProfile_one {A t : ℝ} (hA : 0 < A) (ht : 0 ≤ t) (htA : t ≤ A) :
    outerProfile A t = 1 := by
  simp only [outerProfile,
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ t + 2),
    Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr htA) hA.le),
    sub_zero, mul_one]

theorem outerProfile_le_one (A t : ℝ) : outerProfile A t ≤ 1 := by
  unfold outerProfile
  calc
    _ ≤ 1 * (1 - Real.smoothTransition ((t-A)/A)) :=
      mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one _)
        (sub_nonneg.mpr (Real.smoothTransition.le_one _))
    _ ≤ 1 := by linarith [Real.smoothTransition.nonneg ((t-A)/A)]

theorem outerProfile_mono {A B t : ℝ} (hA : 0 < A) (hAB : A ≤ B) (ht : 0 ≤ t) :
    outerProfile A t ≤ outerProfile B t := by
  have hB : 0 < B := hA.trans_le hAB
  have hd : (t-B)/B ≤ (t-A)/A := by
    rw [div_le_div_iff₀ hB hA]
    nlinarith
  unfold outerProfile
  apply mul_le_mul_of_nonneg_left _ (Real.smoothTransition.nonneg _)
  exact sub_le_sub_left (Real.smoothTransition.monotone hd) 1


theorem cutoffCurl_integrable {β : Plane → Plane →L[ℝ] ℝ}
    (hβ : ContDiff ℝ ∞ β) {A : ℝ} (hA : 0 < A) : Integrable (cutoffCurl β A) := by
  exact (((outerProfile_smooth A).comp radiusSq_smooth).mul
    (planarCurl_contDiff hβ)).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.comp_radiusSq (outerProfile_compact hA)).mul_right

theorem cutoffCurl_stokes {β : Plane → Plane →L[ℝ] ℝ}
    (hβ : ContDiff ℝ ∞ β) {A : ℝ} (hA : 0 < A) :
    (∫ z, cutoffCurl β A z) =
      - ∫ z : Plane, 2 * deriv (outerProfile A) (radiusSq z) * β z (planeRotation z) := by
  have he := integral_cutoffWedge ((outerProfile_smooth A).comp radiusSq_smooth)
    (HasCompactSupport.comp_radiusSq (outerProfile_compact hA)) hβ
  dsimp only [Function.comp_def] at he
  simp_rw [cutoffWedge_radial_rotation (outerProfile_smooth A)] at he
  change _ = - ∫ z, cutoffCurl β A z at he
  linarith

theorem cutoffCurl_bounds {β : Plane → Plane →L[ℝ] ℝ}
    (hβ : ContDiff ℝ ∞ β) {A k ε : ℝ} (hA : 0 < A)
    (he : ∀ z : Plane, A ≤ radiusSq z → |β z (planeRotation z) - k| ≤ ε) :
    2 * Real.pi * (k-ε) ≤ (∫ z, cutoffCurl β A z) ∧
      (∫ z, cutoffCurl β A z) ≤ 2 * Real.pi * (k+ε) := by
  let g := outerProfile A
  have hg : ContDiff ℝ ∞ g := outerProfile_smooth A
  have hgc : HasCompactSupport g := outerProfile_compact hA
  have hdi : Integrable (fun z : Plane => 2 * deriv g (radiusSq z)) :=
    (((hg.continuous_deriv (by simp)).comp radiusSq_smooth.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.comp_radiusSq hgc.deriv)).const_mul 2
  have hwi : Integrable (fun z : Plane => 2 * deriv g (radiusSq z) * β z (planeRotation z)) := by
    have hh := cutoffWedge_integrable (hg.comp radiusSq_smooth)
      (HasCompactSupport.comp_radiusSq hgc) hβ
    dsimp only [Function.comp_def] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    exact (cutoffWedge_radial_rotation hg (β := β) z).symm
  have hp (z : Plane) :
      2 * deriv g (radiusSq z) * (k+ε) ≤ 2 * deriv g (radiusSq z) * β z (planeRotation z) ∧
      2 * deriv g (radiusSq z) * β z (planeRotation z) ≤ 2 * deriv g (radiusSq z) * (k-ε) := by
    by_cases hd : deriv g (radiusSq z) = 0
    · simp only [hd, mul_zero, zero_mul, le_refl, and_self]
    have hz : A ≤ radiusSq z := by
      by_contra! hn
      exact hd (outerProfile_deriv_zero_before hA (radiusSq_nonneg z) hn)
    have hb := abs_le.mp (he z hz)
    have hdn : 2 * deriv g (radiusSq z) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by norm_num)
        (outerProfile_deriv_nonpos hA (radiusSq_nonneg z))
    exact ⟨mul_le_mul_of_nonpos_left (by linarith [hb.2]) hdn,
      mul_le_mul_of_nonpos_left (by linarith [hb.1]) hdn⟩
  have hlo := integral_mono (hdi.mul_const (k+ε)) hwi (fun z => (hp z).1)
  have hhi := integral_mono hwi (hdi.mul_const (k-ε)) (fun z => (hp z).2)
  have hg0 : g 0 = 1 := outerProfile_zero_value hA
  rw [integral_mul_const, integral_radial_derivative hg hgc, hg0] at hlo hhi
  rw [cutoffCurl_stokes hβ hA]
  change _ ≤ - ∫ z : Plane, 2 * deriv g (radiusSq z) * β z (planeRotation z) ∧ _
  constructor <;> nlinarith

theorem tendsto_integral_cutoffCurl {β : Plane → Plane →L[ℝ] ℝ}
    (hβ : ContDiff ℝ ∞ β) {k : ℝ}
    (hlim : Tendsto (fun z => β z (planeRotation z)) (cocompact Plane) (𝓝 k)) :
    Tendsto (fun A : ℝ => ∫ z, cutoffCurl β A z) atTop (𝓝 (2 * Real.pi * k)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε / (4 * Real.pi)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδeq : 2 * Real.pi * δ = ε / 2 := by
    dsimp [δ]
    field_simp
    ring
  have he : ∀ᶠ z in cocompact Plane, |β z (planeRotation z) - k| ≤ δ := by
    filter_upwards [(Metric.tendsto_nhds.mp hlim) δ hδ] with z hz
    exact (Real.dist_eq _ _ ▸ hz).le
  obtain ⟨K,hK,hKs⟩ := mem_cocompact.mp he
  obtain ⟨B,hB,hbound⟩ := (hK.image radiusSq_smooth.continuous).isBounded.exists_pos_norm_le
  filter_upwards [eventually_ge_atTop (B+1)] with A hA
  have hApos : 0 < A := by linarith
  have hb := cutoffCurl_bounds hβ hApos (k := k) (ε := δ) (by
    intro z hz
    apply hKs
    intro hzK
    have hx := hbound (radiusSq z) ⟨z,hzK,rfl⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (radiusSq_nonneg z)] at hx
    linarith)
  rw [Real.dist_eq]
  apply abs_lt.mpr
  constructor <;> nlinarith [hb.1, hb.2]

 

theorem integral_planarCurl_of_nonneg_of_angular_limit
    {β : Plane → Plane →L[ℝ] ℝ} (hβ : ContDiff ℝ ∞ β)
    (hpos : ∀ z, 0 ≤ planarCurl β z) {k : ℝ}
    (hlim : Tendsto (fun z => β z (planeRotation z)) (cocompact Plane) (𝓝 k)) :
    Integrable (planarCurl β) ∧ (∫ z, planarCurl β z) = 2 * Real.pi * k := by
  have hA (j : ℕ) : 0 < (j : ℝ) + 1 := by positivity
  have hcpos (A : ℝ) (z : Plane) : 0 ≤ cutoffCurl β A z :=
    mul_nonneg (outerProfile_nonneg _ _) (hpos z)
  have hnlim : Tendsto (fun j : ℕ => (j : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hcutlim := (tendsto_integral_cutoffCurl hβ hlim).comp hnlim
  have hknonneg : 0 ≤ 2 * Real.pi * k :=
    ge_of_tendsto hcutlim (Filter.Eventually.of_forall fun j => integral_nonneg (hcpos _))
  have hmeas (j : ℕ) : AEMeasurable (fun z => ENNReal.ofReal (cutoffCurl β ((j:ℝ)+1) z)) :=
    (ENNReal.continuous_ofReal.comp
      ((((outerProfile_smooth _).comp radiusSq_smooth).mul
        (planarCurl_contDiff hβ)).continuous)).aemeasurable
  have hmono : ∀ᵐ z : Plane, Monotone (fun j : ℕ => ENNReal.ofReal (cutoffCurl β ((j:ℝ)+1) z)) := by
    apply Filter.Eventually.of_forall
    intro z i j hij
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right
      (outerProfile_mono (hA i) (by exact_mod_cast Nat.add_le_add_right hij 1)
        (radiusSq_nonneg z)) (hpos z)
  have hpoint : ∀ᵐ z : Plane, Tendsto
      (fun j : ℕ => ENNReal.ofReal (cutoffCurl β ((j:ℝ)+1) z)) atTop
      (𝓝 (ENNReal.ofReal (planarCurl β z))) := by
    apply Filter.Eventually.of_forall
    intro z
    apply Filter.EventuallyEq.tendsto
    filter_upwards [hnlim.eventually (eventually_ge_atTop (radiusSq z))] with j hj
    simp only [cutoffCurl, outerProfile_one (hA j) (radiusSq_nonneg z) hj, one_mul]
  have hm := lintegral_tendsto_of_tendsto_of_monotone hmeas hmono hpoint
  have heq (j : ℕ) : (∫⁻ z, ENNReal.ofReal (cutoffCurl β ((j:ℝ)+1) z)) =
      ENNReal.ofReal (∫ z, cutoffCurl β ((j:ℝ)+1) z) :=
    (ofReal_integral_eq_lintegral_ofReal (cutoffCurl_integrable hβ (hA j))
      (Filter.Eventually.of_forall (hcpos _))).symm
  simp_rw [heq] at hm
  have hmval := tendsto_nhds_unique hm (ENNReal.tendsto_ofReal hcutlim)
  have hi : Integrable (planarCurl β) := by
    refine ⟨(planarCurl_contDiff hβ).continuous.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    simp only [Real.norm_eq_abs, abs_of_nonneg (hpos _)]
    rw [hmval]
    exact ENNReal.ofReal_lt_top
  refine ⟨hi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hpos)
    hi.aestronglyMeasurable, hmval, ENNReal.toReal_ofReal hknonneg]

 

theorem AffineLineCurve.total_radial_area {n : ℕ} {J : Phase n → End n}
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u)
    (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x - standardJ n))
    {S T : ℝ} (hST : S < T) (hT : T < 1)
    (houtside : ∀ x, S < capacity x → J x = standardJ n) :
    Integrable (curveDensity S T u) ∧ (∫ z, curveDensity S T u z) = 1 := by
  have hcureq : planarCurl (curvePrimitive S T u) = curveDensity S T u :=
    funext (curvePrimitive_curl hST hu.1)
  have hh := integral_planarCurl_of_nonneg_of_angular_limit
    (curvePrimitive_smooth hST hu.1)
    (by simpa only [hcureq] using curveDensity_nonneg hST hT hJ houtside hu.2.1)
    (hu.radial_infinity_limit hc hST)
  rw [hcureq] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  field_simp

 

theorem affine_primitive_angular_limit_zero {n : ℕ} {u v : ℂ → Phase n}
    (hv : ContDiffAt ℝ ∞ v 0)
    (he : u =ᶠ[cocompact ℂ] fun z : ℂ => v z⁻¹)
    {α : Phase n → Phase n →L[ℝ] ℝ} (hα : Continuous α) :
    Tendsto (fun z : ℂ => α (u z) (fderiv ℝ u z (Complex.I*z)))
      (cocompact ℂ) (𝓝 0) := by
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa only [←Metric.cobounded_eq_cocompact] using (tendsto_inv₀_cobounded (α := ℂ))
  have hdu := (hv.fderiv_right (m := 0) (by simp)).continuousAt.tendsto.comp hi
  have harg : Tendsto (fun z : ℂ => -Complex.I*z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa using hi.const_mul (-Complex.I)
  have hdv : Tendsto (fun z : ℂ => fderiv ℝ v z⁻¹ (-Complex.I*z⁻¹))
      (cocompact ℂ) (𝓝 0) := by
    simpa only [Function.comp_def, map_zero] using
      (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp (hdu.prodMk_nhds harg)
  have hprim : Tendsto (fun z : ℂ => α (v z⁻¹)) (cocompact ℂ) (𝓝 (α (v 0))) :=
    hα.continuousAt.tendsto.comp (hv.continuousAt.tendsto.comp hi)
  have hl : Tendsto (fun z : ℂ => α (v z⁻¹) (fderiv ℝ v z⁻¹ (-Complex.I*z⁻¹)))
      (cocompact ℂ) (𝓝 0) := by
    simpa only [Function.comp_def, map_zero] using
      (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp (hprim.prodMk_nhds hdv)
  have hnear : ∀ᶠ z in cocompact ℂ, u =ᶠ[𝓝 z] fun y : ℂ => v y⁻¹ := by
    obtain ⟨K,hK,hKs⟩ := mem_cocompact.mp he
    filter_upwards [hK.compl_mem_cocompact] with z hz
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hz] with y hy
    exact hKs hy
  have hd : ∀ᶠ w in 𝓝 (0:ℂ), DifferentiableAt ℝ v w :=
    ((hv.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)).eventually (by simp)).mono
      (fun _ hw => hw.differentiableAt (by simp))
  apply hl.congr'
  filter_upwards [hnear, hi.eventually hd,
    (isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz hvz hz0
  rw [hz.self_of_nhds, hz.fderiv_eq]
  have hiD : DifferentiableAt ℝ (fun y : ℂ => y⁻¹) z :=
    (hasDerivAt_inv hz0).differentiableAt.restrictScalars ℝ
  have hh : HasFDerivAt (fun y : ℂ => v y⁻¹)
      ((fderiv ℝ v z⁻¹).comp (fderiv ℝ (fun y : ℂ => y⁻¹) z)) z :=
    hvz.hasFDerivAt.comp z hiD.hasFDerivAt
  rw [hh.fderiv]
  change _ = α (v z⁻¹) (fderiv ℝ v z⁻¹ (fderiv ℝ (fun w : ℂ => w⁻¹) z (Complex.I*z)))
  rw [complex_inv_fderiv_real hz0]
  have heq : -(z^2)⁻¹ * (Complex.I*z) = -Complex.I*z⁻¹ := by field_simp
  rw [heq]



theorem exists_common_radial_interval {n : ℕ} {J : Phase n → End n}
    (hc : HasCompactSupport (fun x => J x - standardJ n))
    (hs : tsupport (fun x => J x - standardJ n) ⊆ openBall n 1) :
    ∃ S T : ℝ, 0 ≤ S ∧ S < T ∧ T < 1 ∧
      ∀ t ∈ Icc (0:ℝ) 1, ∀ x, S < capacity x →
        lineHomotopy J t x = standardJ n := by
  let K := insert (0 : Phase n) (tsupport (fun x => J x - standardJ n))
  have hK : IsCompact K := hc.insert 0
  obtain ⟨x,hx,hmax⟩ := hK.exists_isMaxOn (by exact ⟨0,mem_insert _ _⟩)
    (capacity_smooth n).continuous.continuousOn
  have hS0 : 0 ≤ capacity x := by
    convert hmax (mem_insert (0 : Phase n) _) using 1
    all_goals try with_reducible_and_instances rfl
    simp [capacity]
  have hS1 : capacity x < 1 := by
    rcases hx with rfl | hx
    · simp [capacity]
    · exact hs hx
  refine ⟨capacity x,(capacity x+1)/2,hS0,by linarith,by linarith,?_⟩
  intro t ht y hy
  apply sub_eq_zero.mp
  apply image_eq_zero_of_notMem_tsupport (f := fun x => lineHomotopy J t x - standardJ n)
  intro hm
  exact (not_le_of_gt hy) (hmax (mem_insert_of_mem _ (lineHomotopy_support J ht hm)))



end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_AffineBubble
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity

theorem radialForm_self_smul {n : ℕ} (S T : ℝ) (J : Phase n → End n)
    (x v : Phase n) (a : ℝ) :
    radialForm S T x (a • v) (J x (a • v)) = a^2 * radialForm S T x v (J x v) := by
  simp only [radialForm, ← stdOmega_apply, map_smul,
    smul_apply, smul_eq_mul]
  ring

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_AffineEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity

theorem standardCurvePrimitive_smooth {n : ℕ} {u : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (standardCurvePrimitive u) :=
  planarPullback_smooth (realCurve_smooth hu) (stdPrimitive_smooth n)

theorem standardCurvePrimitive_curl {n : ℕ} {u : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) (z : Plane) :
    planarCurl (standardCurvePrimitive u) z =
      standardForm (fderiv ℝ (realCurve u) z (1,0))
        (fderiv ℝ (realCurve u) z (0,1)) := by
  rw [standardCurvePrimitive,planarPullback_curl (realCurve_smooth hu) (stdPrimitive_smooth n)]
  exact stdPrimitive_extDeriv _ _ _

theorem stdDot_defect_identity {n : ℕ} (v w : Phase n) :
    stdDot n v v + stdDot n w w =
      2 * standardForm v w + stdDot n (w-standardJ n v) (w-standardJ n v) := by
  simp only [stdDot_apply, standardForm, standardJ_apply, Pi.sub_apply,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, zero_add]
  rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem dirichlet_defect_identity {n : ℕ} {u : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) (z : Plane) :
    dirichletDensity u z = 2 * planarCurl (standardCurvePrimitive u) z + defectDensity u z := by
  rw [standardCurvePrimitive_curl hu]
  exact stdDot_defect_identity _ _

theorem dirichletDensity_nonneg {n : ℕ} (u : ℂ → Phase n) (z : Plane) :
    0 ≤ dirichletDensity u z := add_nonneg (stdDot_nonneg _) (stdDot_nonneg _)

theorem dirichletDensity_smooth {n : ℕ} {u : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (dirichletDensity u) := by
  have hd := (realCurve_smooth hu).fderiv_right (show (∞ : WithTop ℕ∞)+1≤∞ by simp)
  have hx := hd.clm_apply (contDiff_const (c := ((1,0):Plane)))
  have hy := hd.clm_apply (contDiff_const (c := ((0,1):Plane)))
  exact (((stdDot n).contDiff.comp hx).clm_apply hx).add
    (((stdDot n).contDiff.comp hy).clm_apply hy)

theorem defectDensity_smooth {n : ℕ} {u : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (defectDensity u) := by
  have hd := (realCurve_smooth hu).fderiv_right (show (∞ : WithTop ℕ∞)+1≤∞ by simp)
  have hx := hd.clm_apply (contDiff_const (c := ((1,0):Plane)))
  have hy := hd.clm_apply (contDiff_const (c := ((0,1):Plane)))
  have he := hy.sub ((standardJ n).contDiff.comp hx)
  exact ((stdDot n).contDiff.comp he).clm_apply he

theorem outerCutoff_integral_tendsto {f : Plane → ℝ} (hf : Integrable f) :
    Tendsto (fun j : ℕ => ∫ z, outerProfile ((j:ℝ)+1) (radiusSq z) * f z)
      atTop (𝓝 (∫ z, f z)) := by
  have hn : Tendsto (fun j : ℕ => (j:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  apply tendsto_integral_of_dominated_convergence (fun z => ‖f z‖)
  · intro j
    exact (((outerProfile_smooth _).comp radiusSq_smooth).continuous.aestronglyMeasurable).mul
      hf.aestronglyMeasurable
  · exact hf.norm
  · intro j
    apply Filter.Eventually.of_forall
    intro z
    rw [norm_mul,Real.norm_of_nonneg (outerProfile_nonneg _ _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (outerProfile_le_one _ _)
  · apply Filter.Eventually.of_forall
    intro z
    apply Filter.EventuallyEq.tendsto
    filter_upwards [hn.eventually (eventually_ge_atTop (radiusSq z))] with j hj
    rw [outerProfile_one (by positivity) (radiusSq_nonneg z) hj,one_mul]

theorem outerCutoff_integrable {f : Plane → ℝ} (hf : Continuous f) {A : ℝ} (hA : 0<A) :
    Integrable (fun z => outerProfile A (radiusSq z)*f z) := by
  apply (((outerProfile_smooth A).comp radiusSq_smooth).continuous.mul hf).integrable_of_hasCompactSupport
  exact (HasCompactSupport.comp_radiusSq (outerProfile_compact hA)).mul_right

theorem integrable_of_nonneg_of_outerCutoff_limit {f : Plane → ℝ}
    (hf : Continuous f) (hp : ∀ z, 0 ≤ f z) {E : ℝ}
    (hlim : Tendsto (fun j : ℕ => ∫ z, outerProfile ((j:ℝ)+1) (radiusSq z)*f z)
      atTop (𝓝 E)) : Integrable f ∧ (∫ z, f z) = E := by
  let g (j : ℕ) (z : Plane) := outerProfile ((j:ℝ)+1) (radiusSq z)*f z
  have hA (j : ℕ) : 0 < (j:ℝ)+1 := by positivity
  have hgpos (j : ℕ) (z : Plane) : 0 ≤ g j z := mul_nonneg (outerProfile_nonneg _ _) (hp z)
  have hn : Tendsto (fun j : ℕ => (j:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hEn : 0 ≤ E := ge_of_tendsto hlim (Filter.Eventually.of_forall fun j => integral_nonneg (hgpos j))
  have hmeas (j : ℕ) : AEMeasurable (fun z => ENNReal.ofReal (g j z)) :=
    (ENNReal.continuous_ofReal.comp
      (((outerProfile_smooth _).comp radiusSq_smooth).continuous.mul hf)).aemeasurable
  have hmono : ∀ᵐ z : Plane, Monotone (fun j : ℕ => ENNReal.ofReal (g j z)) := by
    apply Filter.Eventually.of_forall
    intro z i j hij
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right
      (outerProfile_mono (hA i) (by exact_mod_cast Nat.add_le_add_right hij 1)
        (radiusSq_nonneg z)) (hp z)
  have hpoint : ∀ᵐ z : Plane, Tendsto
      (fun j : ℕ => ENNReal.ofReal (g j z)) atTop (𝓝 (ENNReal.ofReal (f z))) := by
    apply Filter.Eventually.of_forall
    intro z
    apply Filter.EventuallyEq.tendsto
    filter_upwards [hn.eventually (eventually_ge_atTop (radiusSq z))] with j hj
    simp only [g,outerProfile_one (hA j) (radiusSq_nonneg z) hj,one_mul]
  have hm := lintegral_tendsto_of_tendsto_of_monotone hmeas hmono hpoint
  have heq (j : ℕ) : (∫⁻ z, ENNReal.ofReal (g j z)) = ENNReal.ofReal (∫ z, g j z) :=
    (ofReal_integral_eq_lintegral_ofReal (outerCutoff_integrable hf (hA j))
      (Filter.Eventually.of_forall (hgpos j))).symm
  simp_rw [heq] at hm
  have hmval := tendsto_nhds_unique hm (ENNReal.tendsto_ofReal hlim)
  have hi : Integrable f := by
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    simp only [Real.norm_eq_abs,abs_of_nonneg (hp _)]
    rw [hmval]
    exact ENNReal.ofReal_lt_top
  refine ⟨hi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hp)
    hi.aestronglyMeasurable,hmval,ENNReal.toReal_ofReal hEn]

theorem AffineLineCurve.affine_remainder_extends {n : ℕ} {J : Phase n → End n}
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u)
    (hc : HasCompactSupport (fun x => J x-standardJ n)) :
    ∃ a : Phase n, a ≠ 0 ∧
      Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 a) ∧
      ∃ v : ℂ → Phase n, ContDiffAt ℝ ∞ v 0 ∧
        (fun z : ℂ => u z-z • a) =ᶠ[cocompact ℂ] fun z => v z⁻¹ := by
  obtain ⟨a,ha,hl⟩ := hu.2.2.2.2
  let V := infinityGerm u a
  have hV : AnalyticAt ℂ V 0 := infinityGerm_analyticAt (hu.holomorphic_at_infinity hc) hl
  have hV0 : V 0 = a := by simp [V,infinityGerm]
  obtain ⟨r,hr,hVr⟩ := hV.exists_ball_analyticOnNhd
  have hball : Metric.ball (0:ℂ) r ∈ 𝓝 (0:ℂ) := Metric.ball_mem_nhds _ hr
  have hv := ((Complex.differentiableOn_dslope hball).mpr
    hVr.differentiableOn).analyticAt hball
  refine ⟨a,ha,hl,dslope V 0,hv.contDiffAt.restrict_scalars ℝ,?_⟩
  filter_upwards [(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz
  have hz0 : z ≠ 0 := by simpa using hz
  rw [dslope_of_ne V (inv_ne_zero hz0)]
  simp only [slope_def_module,sub_zero,inv_inv,V,infinityGerm,inv_ne_zero hz0,
    ite_false,ite_true,inv_inv,smul_sub,smul_smul,mul_inv_cancel₀ hz0,one_smul]

theorem standardCurvePrimitive_angular_limit_zero {n : ℕ} {u v : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiffAt ℝ ∞ v 0)
    (he : u =ᶠ[cocompact ℂ] fun z : ℂ => v z⁻¹) :
    Tendsto (fun z : Plane => standardCurvePrimitive u z (planeRotation z))
      (cocompact Plane) (𝓝 0) := by
  have hr : Tendsto Complex.equivRealProdCLM.symm (cocompact Plane) (cocompact ℂ) :=
    Complex.equivRealProdCLM.symm.toHomeomorph.isClosedEmbedding.tendsto_cocompact
  have hh := (affine_primitive_angular_limit_zero hv he (stdPrimitive_smooth n).continuous).comp hr
  apply hh.congr
  intro z
  change stdPrimitive _ _ = stdPrimitive _ _
  have hd := realCurve_fderiv (z := z) (hu.differentiable (by simp) _) (planeRotation z)
  rw [equivRealProd_rotation] at hd
  exact congrArg (stdPrimitive (u (Complex.equivRealProdCLM.symm z))) hd.symm

theorem affine_smooth {n : ℕ} (a : Phase n) : ContDiff ℝ ∞ (fun z : ℂ => z • a) :=
  (contDiff_id.smul (contDiff_const (c := a)) : ContDiff ℂ ∞ _).restrict_scalars ℝ

theorem realCurve_affine_fderiv {n : ℕ} (a : Phase n) (z w : Plane) :
    fderiv ℝ (realCurve (fun ζ : ℂ => ζ • a)) z w = Complex.equivRealProdCLM.symm w • a := by
  let A : Plane →L[ℝ] Phase n :=
    (((ContinuousLinearMap.id ℂ ℂ).smulRight a).restrictScalars ℝ).comp
      Complex.equivRealProdCLM.symm.toContinuousLinearMap
  change fderiv ℝ (A : Plane → Phase n) z w = _
  rw [A.fderiv]
  rfl

theorem complexDefect_sub_affine {n : ℕ} {u : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) (a : Phase n) (z : Plane) :
    complexDefect (fun ζ : ℂ => u ζ-ζ • a) z = complexDefect u z := by
  have he : realCurve (fun ζ : ℂ => u ζ-ζ • a) =
      realCurve u-realCurve (fun ζ : ℂ => ζ • a) := rfl
  unfold complexDefect
  rw [he,fderiv_sub ((realCurve_smooth hu).differentiable (by simp) z)
    ((realCurve_smooth (affine_smooth a)).differentiable (by simp) z)]
  simp only [sub_apply,realCurve_affine_fderiv,map_sub]
  have hx : Complex.equivRealProdCLM.symm ((1,0):Plane) = 1 := rfl
  have hy : Complex.equivRealProdCLM.symm ((0,1):Plane) = Complex.I := rfl
  rw [hx,hy,one_smul]
  change _ - Complex.I • a - (_ - Complex.I • a) = _
  abel

theorem defectDensity_sub_affine {n : ℕ} {u : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) (a : Phase n) :
    defectDensity (fun z : ℂ => u z-z • a) = defectDensity u := by
  funext z
  simp only [defectDensity,complexDefect_sub_affine hu]

theorem affine_remainder_energy_identity {n : ℕ} {J : Phase n → End n}
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u)
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    (hdef : Integrable (defectDensity u)) :
    ∃ a : Phase n, a ≠ 0 ∧
      Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 a) ∧
      Integrable (dirichletDensity (fun z : ℂ => u z-z • a)) ∧
      (∫ z, dirichletDensity (fun ζ : ℂ => u ζ-ζ • a) z) = ∫ z, defectDensity u z := by
  obtain ⟨a,ha,hl,v,hv,he⟩ := hu.affine_remainder_extends hc
  let w : ℂ → Phase n := fun z => u z-z • a
  have hw : ContDiff ℝ ∞ w := hu.1.sub (affine_smooth a)
  have hcurl := (tendsto_integral_cutoffCurl (standardCurvePrimitive_smooth hw)
    (standardCurvePrimitive_angular_limit_zero hw hv he)).comp
      (tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop :
        Tendsto (fun j : ℕ => (j:ℝ)) atTop atTop))
  have hid (z : Plane) : dirichletDensity w z =
      2 * planarCurl (standardCurvePrimitive w) z + defectDensity u z := by
    rw [dirichlet_defect_identity hw]
    congr 1
    exact congrFun (defectDensity_sub_affine hu.1 a) z
  have hEq (j : ℕ) : (∫ z, outerProfile ((j:ℝ)+1) (radiusSq z)*dirichletDensity w z) =
      2 * (∫ z, cutoffCurl (standardCurvePrimitive w) ((j:ℝ)+1) z) +
      ∫ z, outerProfile ((j:ℝ)+1) (radiusSq z)*defectDensity u z := by
    have heq : (fun z => outerProfile ((j:ℝ)+1) (radiusSq z)*dirichletDensity w z) =
        fun z => 2 * cutoffCurl (standardCurvePrimitive w) ((j:ℝ)+1) z +
          outerProfile ((j:ℝ)+1) (radiusSq z)*defectDensity u z := by
      funext z
      rw [hid]
      unfold cutoffCurl
      ring
    rw [heq,integral_add ((cutoffCurl_integrable (standardCurvePrimitive_smooth hw)
      (by positivity)).const_mul 2) (outerCutoff_integrable (defectDensity_smooth hu.1).continuous
        (by positivity)),integral_const_mul]
  have hlim : Tendsto (fun j : ℕ => ∫ z, outerProfile ((j:ℝ)+1) (radiusSq z)*dirichletDensity w z)
      atTop (𝓝 (∫ z, defectDensity u z)) := by
    simp_rw [hEq]
    convert (hcurl.const_mul 2).add (outerCutoff_integral_tendsto hdef) using 1 <;> simp
  obtain ⟨hwi,hwie⟩ := integrable_of_nonneg_of_outerCutoff_limit
    (dirichletDensity_smooth hw).continuous (dirichletDensity_nonneg w) hlim
  exact ⟨a,ha,hl,hwi,hwie⟩

theorem radialForm_joint_continuous {n : ℕ} {S T : ℝ} (hST : S < T) :
    Continuous (fun y : Phase n × Phase n × Phase n => radialForm S T y.1 y.2.1 y.2.2) := by
  have hc : Continuous (fun y : Phase n × Phase n × Phase n => capacity y.1) :=
    (capacity_smooth n).continuous.comp continuous_fst
  have hr := (radialCoefficient_smooth hST).continuous.comp hc
  have hs : Continuous (radialSlope S T) := by
    apply ((radialSwitch_smooth S T).continuous.neg).div
      ((continuous_const.add (radialOffset_smooth S T).continuous).pow 2)
    intro t
    exact pow_ne_zero 2 (ne_of_gt (show 0 < 1 + radialOffset S T t from by
      linarith [radialOffset_nonneg hST t]))
  have ho (a b : Phase n × Phase n × Phase n → Phase n) (ha : Continuous a) (hb : Continuous b) :
      Continuous (fun y => standardForm (a y) (b y)) := by
    simpa only [Function.comp_apply,stdOmega_apply] using ((stdOmega n).continuous.comp ha).clm_apply hb
  have hd (a b : Phase n × Phase n × Phase n → Phase n) (ha : Continuous a) (hb : Continuous b) :
      Continuous (fun y => stdDot n (a y) (b y)) :=
    ((stdDot n).continuous.comp ha).clm_apply hb
  exact (hr.mul (ho _ _ continuous_snd.fst continuous_snd.snd)).add
    ((continuous_const.mul (hs.comp hc)).mul
      (((hd _ _ continuous_fst continuous_snd.fst).mul (ho _ _ continuous_fst continuous_snd.snd)).sub
        ((hd _ _ continuous_fst continuous_snd.snd).mul (ho _ _ continuous_fst continuous_snd.fst))))

theorem stdDot_self_smul {n : ℕ} (a : ℝ) (v : Phase n) :
    stdDot n (a • v) (a • v) = a^2 * stdDot n v v := by
  simp only [map_smul,smul_apply,smul_eq_mul]
  ring

theorem homotopy_defect_continuousOn {n : ℕ} {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x)) :
    ContinuousOn (fun y : (ℝ × Phase n) × Phase n =>
      stdDot n ((lineHomotopy J y.1.1 y.1.2-standardJ n) y.2)
        ((lineHomotopy J y.1.1 y.1.2-standardJ n) y.2))
      (((Icc (0:ℝ) 1) ×ˢ univ) ×ˢ univ) := by
  have hj : ContinuousOn (fun y : (ℝ × Phase n) × Phase n => lineHomotopy J y.1.1 y.1.2)
      (((Icc (0:ℝ) 1) ×ˢ univ) ×ˢ univ) :=
    (lineHomotopy_smooth hJs hJ).continuousOn.comp continuous_fst.continuousOn
      (fun y hy => hy.1)
  have h := (hj.sub (continuous_const (y := standardJ n)).continuousOn).clm_apply continuous_snd.continuousOn
  exact ((stdDot n).continuous.comp_continuousOn h).clm_apply h

theorem homotopy_radial_graph_continuousOn {n : ℕ} {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x))
    {S T : ℝ} (hST : S<T) :
    ContinuousOn (fun y : (ℝ × Phase n) × Phase n =>
      radialForm S T y.1.2 y.2 (lineHomotopy J y.1.1 y.1.2 y.2))
      (((Icc (0:ℝ) 1) ×ˢ univ) ×ˢ univ) := by
  have hj : ContinuousOn (fun y : (ℝ × Phase n) × Phase n => lineHomotopy J y.1.1 y.1.2)
      (((Icc (0:ℝ) 1) ×ˢ univ) ×ˢ univ) :=
    (lineHomotopy_smooth hJs hJ).continuousOn.comp continuous_fst.continuousOn
      (fun y hy => hy.1)
  have hxy : ContinuousOn (fun y : (ℝ × Phase n) × Phase n =>
      (y.1.2, y.2, lineHomotopy J y.1.1 y.1.2 y.2))
      (((Icc (0:ℝ) 1) ×ˢ univ) ×ˢ univ) :=
    (continuous_fst.snd.continuousOn).prodMk
      (continuous_snd.continuousOn.prodMk (hj.clm_apply continuous_snd.continuousOn))
  simpa only [Function.comp_def] using (radialForm_joint_continuous (n := n) hST).comp_continuousOn hxy

 

theorem homotopy_defect_unit_bound {n : ℕ} {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1)
    (hout : ∀ t ∈ Icc (0:ℝ) 1, ∀ x, S < capacity x → lineHomotopy J t x = standardJ n) :
    ∃ C > 0, ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ tsupport (fun x => J x-standardJ n), ∀ v : Phase n, ‖v‖ = 1 →
      stdDot n ((lineHomotopy J t x-standardJ n) v) ((lineHomotopy J t x-standardJ n) v) ≤
        C * radialForm S T x v (lineHomotopy J t x v) := by
  let K := tsupport (fun x => J x-standardJ n)
  let L := ((Icc (0:ℝ) 1) ×ˢ K) ×ˢ Metric.sphere (0:Phase n) 1
  let e (y : (ℝ × Phase n) × Phase n) :=
    stdDot n ((lineHomotopy J y.1.1 y.1.2-standardJ n) y.2)
      ((lineHomotopy J y.1.1 y.1.2-standardJ n) y.2)
  let d (y : (ℝ × Phase n) × Phase n) :=
    radialForm S T y.1.2 y.2 (lineHomotopy J y.1.1 y.1.2 y.2)
  have hL : IsCompact L := (isCompact_Icc.prod hc).prod (isCompact_sphere _ _)
  have hsub : L ⊆ (((Icc (0:ℝ) 1) ×ˢ univ) ×ˢ univ) :=
    fun y hy => ⟨⟨hy.1.1,mem_univ _⟩,mem_univ _⟩
  have he : ContinuousOn e L := (homotopy_defect_continuousOn hJs hJ).mono hsub
  have hd : ContinuousOn d L := (homotopy_radial_graph_continuousOn hJs hJ hST).mono hsub
  have hdp (y : (ℝ × Phase n) × Phase n) (hy : y ∈ L) : 0 < d y := by
    have hv : y.2 ≠ 0 := by
      intro hv
      have hh := hy.2
      simp [hv] at hh
    exact radialForm_adapted_pos hST hT (lineHomotopy_compatible hJ hy.1.1)
      (hout y.1.1 hy.1.1) y.1.2 hv
  obtain ⟨C,hC,hCb⟩ := (hL.image_of_continuousOn (he.div hd (fun y hy => (hdp y hy).ne'))).isBounded.exists_pos_norm_le
  refine ⟨C,hC,?_⟩
  intro t ht x hx v hv
  have hl : ((t,x),v) ∈ L := by
    exact ⟨⟨ht,hx⟩, by simpa [Metric.mem_sphere, dist_zero_right] using hv⟩
  have hr := hCb _ (mem_image_of_mem (fun y => e y / d y) hl)
  exact (div_le_iff₀ (hdp _ hl)).mp ((le_abs_self _).trans
    (by simpa only [Real.norm_eq_abs,Pi.div_apply] using hr))

 

theorem homotopy_defect_bound {n : ℕ} {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1)
    (hout : ∀ t ∈ Icc (0:ℝ) 1, ∀ x, S < capacity x → lineHomotopy J t x = standardJ n) :
    ∃ C > 0, ∀ t ∈ Icc (0:ℝ) 1, ∀ x v : Phase n,
      stdDot n ((lineHomotopy J t x-standardJ n) v) ((lineHomotopy J t x-standardJ n) v) ≤
        C * radialForm S T x v (lineHomotopy J t x v) := by
  obtain ⟨C,hC,hCb⟩ := homotopy_defect_unit_bound hJs hJ hc hST hT hout
  let K := tsupport (fun x => J x-standardJ n)
  refine ⟨C,hC,?_⟩
  intro t ht x v
  have hpos : 0 ≤ radialForm S T x v (lineHomotopy J t x v) := by
    by_cases hv : v = 0
    · simp [hv,radialForm, ←stdOmega_apply]
    · exact (radialForm_adapted_pos hST hT (lineHomotopy_compatible hJ ht) (hout t ht) x hv).le
  by_cases hx : x ∈ K
  · by_cases hv : v = 0
    · simp [hv,radialForm, ←stdOmega_apply]
    let w : Phase n := ‖v‖⁻¹ • v
    have hw : ‖w‖ = 1 := by
      simp only [w,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
    have hh := hCb t ht x hx w hw
    change stdDot n ((lineHomotopy J t x-standardJ n) w)
      ((lineHomotopy J t x-standardJ n) w) ≤
        C * radialForm S T x w (lineHomotopy J t x w) at hh
    dsimp only [w] at hh
    rw [radialForm_self_smul, (lineHomotopy J t x-standardJ n).map_smul,
      stdDot_self_smul] at hh
    have hs : 0 < (‖v‖⁻¹)^2 := sq_pos_of_pos (inv_pos.mpr (norm_pos_iff.mpr hv))
    nlinarith
  · have he0 : lineHomotopy J t x-standardJ n = 0 := by
      apply image_eq_zero_of_notMem_tsupport (f := fun y => lineHomotopy J t y-standardJ n)
      exact fun hy => hx (lineHomotopy_support J ht hy)
    simp only [he0,zero_apply,map_zero]
    exact mul_nonneg hC.le hpos

theorem homotopy_affine_error_energy_oai (n : ℕ) (_hn : 3 ≤ n)
    (J : Phase n → End n) (hJs : ContDiff ℝ ∞ J)
    (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    (hs : tsupport (fun x => J x-standardJ n) ⊆ openBall n 1)
    (p q : Phase n) (_hpq : p ≠ q) :
    ∃ C > 0, ∀ t ∈ Icc (0:ℝ) 1, ∀ u : ℂ → Phase n,
      AffineLineCurve (lineHomotopy J t) p q u →
      ∃ v : Phase n, v ≠ 0 ∧
        Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 v) ∧
        Integrable (dirichletDensity (fun z : ℂ => u z-z • v)) ∧
        (∫ z, dirichletDensity (fun z : ℂ => u z-z • v) z) ≤ C := by
  obtain ⟨S,T,hS,hST,hT,hout⟩ := exists_common_radial_interval hc hs
  obtain ⟨C,hC,hbound⟩ := homotopy_defect_bound hJs hJ hc hST hT hout
  refine ⟨C,hC,?_⟩
  intro t ht u hu
  have harea := hu.total_radial_area (lineHomotopy_compatible hJ ht)
    (lineHomotopy_compact hc ht) hST hT (hout t ht)
  have hdefb (z : Plane) : defectDensity u z ≤ C * curveDensity S T u z := by
    unfold defectDensity complexDefect curveDensity
    rw [realCurve_CR (hu.2.1 _)]
    exact hbound t ht _ _
  have hdefi : Integrable (defectDensity u) :=
    (harea.1.const_mul C).mono' (defectDensity_smooth hu.1).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_of_nonneg (show 0 ≤ defectDensity u z from stdDot_nonneg _)]
        exact hdefb z)
  obtain ⟨v,hv,hl,hwi,hwe⟩ := affine_remainder_energy_identity hu (lineHomotopy_compact hc ht) hdefi
  refine ⟨v,hv,hl,hwi,?_⟩
  rw [hwe]
  have hi := integral_mono hdefi (harea.1.const_mul C) hdefb
  rwa [integral_const_mul,harea.2,mul_one] at hi

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.homotopy_affine_error_energy_oai := @OAI.HigherDimensionalBallPacking.Rigidity.homotopy_affine_error_energy_oai
