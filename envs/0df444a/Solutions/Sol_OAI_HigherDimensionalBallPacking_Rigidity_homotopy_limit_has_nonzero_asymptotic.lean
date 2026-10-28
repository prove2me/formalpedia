-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.homotopy_limit_has_nonzero_asymptotic
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T17:16:25.842139+00:00
-- url     : https://prove2.me/submissions/2e3cbcbf-d0c3-46a5-ae0d-649f68fa923c

import Mathlib
import Definitions.Def_BallPackingNecessity
import Definitions.Def_OAIQ10Bp009
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_homotopy_affine_error_energy
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_homotopy_slopes_bounded_above

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


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory



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

end HigherDimensionalBallPacking.Rigidity

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



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Energy_ResidualEnergy
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

lemma stdDot_sub_self (x y : Phase n) :
    stdDot n (x-y) (x-y)=stdDot n x x-2*stdDot n x y+stdDot n y y := by
  simp only [map_sub,sub_apply]
  rw [stdDot_symm y x]
  ring



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Energy_CircularEnergy
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

theorem dirichletDensity_nonneg {n : ℕ} (u : ℂ → Phase n) (z : Plane) :
    0 ≤ dirichletDensity u z := add_nonneg (stdDot_nonneg _) (stdDot_nonneg _)

theorem dirichletDensity_smooth {n : ℕ} {u : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (dirichletDensity u) := by
  have hd := (realCurve_smooth hu).fderiv_right (show (∞ : WithTop ℕ∞)+1≤∞ by simp)
  have hx := hd.clm_apply (contDiff_const (c := ((1,0):Plane)))
  have hy := hd.clm_apply (contDiff_const (c := ((0,1):Plane)))
  exact (((stdDot n).contDiff.comp hx).clm_apply hx).add
    (((stdDot n).contDiff.comp hy).clm_apply hy)

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

theorem stdDot_self_smul {n : ℕ} (a : ℝ) (v : Phase n) :
    stdDot n (a • v) (a • v) = a^2 * stdDot n v v := by
  simp only [map_smul,smul_apply,smul_eq_mul]
  ring

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_PlanarEnergy
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

theorem euclideanNorm_nonneg {n : ℕ} (v : Phase n) : 0 ≤ euclideanNorm v := norm_nonneg _

theorem euclideanNorm_add_le {n : ℕ} (v w : Phase n) :
    euclideanNorm (v+w) ≤ euclideanNorm v + euclideanNorm w := by
  simpa only [euclideanNorm,map_add] using norm_add_le (phaseEuclidean n v) (phaseEuclidean n w)

theorem standardForm_abs_le {n : ℕ} (v w : Phase n) :
    |standardForm v w| ≤ euclideanNorm v * euclideanNorm w := by
  have h := stdDot_standardForm_sq_le v w
  have hp := sq_nonneg (stdDot n v w)
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (euclideanNorm_nonneg _) (euclideanNorm_nonneg _))).mp
  rw [sq_abs,mul_pow,euclideanNorm_sq,euclideanNorm_sq]
  linarith

theorem standard_graph_energy_smul {n : ℕ} (A : End n) (v : Phase n) (a : ℝ) :
    stdDot n (a • v) (a • v) + stdDot n (A (a • v)) (A (a • v)) =
      a^2 * (stdDot n v v + stdDot n (A v) (A v)) := by
  rw [A.map_smul,stdDot_self_smul,stdDot_self_smul]
  ring

theorem standard_graph_area_smul {n : ℕ} (A : End n) (v : Phase n) (a : ℝ) :
    standardForm (a • v) (A (a • v)) = a^2 * standardForm v (A v) := by
  simp only [A.map_smul,←stdOmega_apply,map_smul,smul_apply,smul_eq_mul]
  ring

theorem homotopy_standard_graph_continuousOn {n : ℕ} {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x)) :
    ContinuousOn (fun y : (ℝ × Phase n) × Phase n =>
      (stdDot n y.2 y.2 + stdDot n (lineHomotopy J y.1.1 y.1.2 y.2)
          (lineHomotopy J y.1.1 y.1.2 y.2)) /
        standardForm y.2 (lineHomotopy J y.1.1 y.1.2 y.2))
      (((Icc (0:ℝ) 1) ×ˢ univ) ×ˢ (Metric.sphere (0:Phase n) 1)) := by
  have hj : ContinuousOn (fun y : (ℝ × Phase n) × Phase n => lineHomotopy J y.1.1 y.1.2)
      (((Icc (0:ℝ) 1) ×ˢ univ) ×ˢ (Metric.sphere (0:Phase n) 1)) :=
    (lineHomotopy_smooth hJs hJ).continuousOn.comp continuous_fst.continuousOn
      (fun y hy => hy.1)
  have hv := hj.clm_apply continuous_snd.continuousOn
  have he : ContinuousOn (fun y : (ℝ × Phase n) × Phase n =>
      stdDot n y.2 y.2 + stdDot n (lineHomotopy J y.1.1 y.1.2 y.2)
          (lineHomotopy J y.1.1 y.1.2 y.2))
      (((Icc (0:ℝ) 1) ×ˢ univ) ×ˢ (Metric.sphere (0:Phase n) 1)) :=
    (((stdDot n).continuous.comp continuous_snd).clm_apply continuous_snd).continuousOn.add
      (((stdDot n).continuous.comp_continuousOn hv).clm_apply hv)
  have hd : ContinuousOn (fun y : (ℝ × Phase n) × Phase n =>
      standardForm y.2 (lineHomotopy J y.1.1 y.1.2 y.2))
      (((Icc (0:ℝ) 1) ×ˢ univ) ×ˢ (Metric.sphere (0:Phase n) 1)) := by
    simpa only [stdOmega_apply,Function.comp_apply] using
      (((stdOmega n).continuous.comp continuous_snd).continuousOn.clm_apply hv)
  apply he.div hd
  intro y hy
  have hv0 : y.2 ≠ 0 := by
    intro hz
    have h := hy.2
    simp [hz] at h
  exact (lineHomotopy_compatible hJ hy.1.1 _).2.2 _ hv0 |>.ne'

theorem homotopy_standard_unit_bound {n : ℕ} {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x-standardJ n)) :
    ∃ C > 0, ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ tsupport (fun x => J x-standardJ n),
      ∀ v : Phase n, ‖v‖ = 1 →
      stdDot n v v + stdDot n (lineHomotopy J t x v) (lineHomotopy J t x v) ≤
        C * standardForm v (lineHomotopy J t x v) := by
  let K := tsupport (fun x => J x-standardJ n)
  let L := ((Icc (0:ℝ) 1) ×ˢ K) ×ˢ Metric.sphere (0:Phase n) 1
  let f (y : (ℝ × Phase n) × Phase n) :=
    (stdDot n y.2 y.2 + stdDot n (lineHomotopy J y.1.1 y.1.2 y.2)
      (lineHomotopy J y.1.1 y.1.2 y.2)) / standardForm y.2 (lineHomotopy J y.1.1 y.1.2 y.2)
  have hL : IsCompact L := (isCompact_Icc.prod hc).prod (isCompact_sphere _ _)
  have hcont : ContinuousOn f L :=
    (homotopy_standard_graph_continuousOn hJs hJ).mono (fun y hy => ⟨⟨hy.1.1,mem_univ _⟩,hy.2⟩)
  obtain ⟨C,hC,hCb⟩ := (hL.image_of_continuousOn hcont).isBounded.exists_pos_norm_le
  refine ⟨C,hC,?_⟩
  intro t ht x hx v hv
  have hl : ((t,x),v) ∈ L := ⟨⟨ht,hx⟩,by simpa [Metric.mem_sphere,dist_zero_right] using hv⟩
  have hv0 : v ≠ 0 := fun hh => by simp [hh] at hv
  have hp := (lineHomotopy_compatible hJ ht x).2.2 v hv0
  apply (div_le_iff₀ hp).mp
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hCb _ (mem_image_of_mem f hl))

theorem homotopy_standard_energy_bound {n : ℕ} {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x-standardJ n)) :
    ∃ C > 0, ∀ t ∈ Icc (0:ℝ) 1, ∀ x v : Phase n,
      stdDot n v v + stdDot n (lineHomotopy J t x v) (lineHomotopy J t x v) ≤
        C * standardForm v (lineHomotopy J t x v) := by
  obtain ⟨C,hC,hCb⟩ := homotopy_standard_unit_bound hJs hJ hc
  refine ⟨max C 2, lt_max_of_lt_left hC, ?_⟩
  intro t ht x v
  have hpos : 0 ≤ standardForm v (lineHomotopy J t x v) := by
    by_cases hv : v = 0
    · simp [hv,standardForm]
    · exact ((lineHomotopy_compatible hJ ht x).2.2 v hv).le
  by_cases hx : x ∈ tsupport (fun x => J x-standardJ n)
  · by_cases hv : v = 0
    · simp [hv,standardForm]
    have hw : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
      simp only [norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
    have hh := hCb t ht x hx _ hw
    rw [standard_graph_energy_smul,standard_graph_area_smul] at hh
    have hs : 0 < (‖v‖⁻¹)^2 := sq_pos_of_pos (inv_pos.mpr (norm_pos_iff.mpr hv))
    have hb : stdDot n v v + stdDot n (lineHomotopy J t x v) (lineHomotopy J t x v) ≤
        C * standardForm v (lineHomotopy J t x v) := by nlinarith
    exact hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpos)
  · have he : lineHomotopy J t x = standardJ n := by
      apply sub_eq_zero.mp
      apply image_eq_zero_of_notMem_tsupport (f := fun y => lineHomotopy J t y-standardJ n)
      exact fun hy => hx (lineHomotopy_support J ht hy)
    rw [he]
    have hi : stdDot n (standardJ n v) (standardJ n v) = stdDot n v v := by
      simp only [← standardForm_J_right]
      exact (compatible_standardJ n).2.1 v (standardJ n v)
    rw [hi,standardForm_J_right]
    nlinarith [stdDot_nonneg v,le_max_right C (2:ℝ)]

 
theorem interval_integral_sq_le {f : ℝ → ℝ} (hf : Continuous f)
    {a b : ℝ} (hab : a ≤ b) :
    (∫ x in a..b, f x)^2 ≤ (b-a) * (∫ x in a..b, (f x)^2) := by
  rcases hab.eq_or_lt with h | h
  · subst b; simp
  let m : ℝ := (∫ x in a..b, f x) / (b-a)
  have hm : (b-a)*m = ∫ x in a..b, f x := by
    dsimp [m]
    field_simp
  have he : (∫ x in a..b, (f x-m)^2) =
      (∫ x in a..b, (f x)^2) - 2*m*(∫ x in a..b, f x) + (b-a)*m^2 := by
    have hfun : (fun x => (f x-m)^2) = (fun x => (f x)^2 - (2*m)*f x + m^2) := by
      funext x; ring
    have hfi : IntervalIntegrable (fun x => (f x)^2) volume a b := (hf.pow 2).intervalIntegrable _ _
    have hgi : IntervalIntegrable (fun x => (2*m)*f x) volume a b :=
      (hf.const_mul (2*m)).intervalIntegrable _ _
    have hci : IntervalIntegrable (fun _ : ℝ => m^2) volume a b :=
      continuous_const.intervalIntegrable _ _
    rw [hfun, intervalIntegral.integral_add (hfi.sub hgi) hci,
      intervalIntegral.integral_sub hfi hgi,
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const]
    simp only [smul_eq_mul]
  have hp := intervalIntegral.integral_nonneg (μ := volume) h.le (fun x _ => sq_nonneg (f x-m))
  rw [he] at hp
  nlinarith [mul_nonneg (sub_pos.mpr h).le hp]

theorem euclidean_displacement_le_integral {n : ℕ} {v v' : ℝ → Phase n}
    (hv : ∀ x, HasDerivAt v (v' x) x) (hd : Continuous v')
    {a b : ℝ} (hab : a ≤ b) :
    euclideanNorm (v b-v a) ≤ ∫ x in a..b, euclideanNorm (v' x) := by
  have hdu (x : ℝ) : HasDerivAt (fun t => phaseEuclidean n (v t)) (phaseEuclidean n (v' x)) x :=
    (phaseEuclidean n).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x (hv x)
  have hi : IntervalIntegrable (fun x => phaseEuclidean n (v' x)) volume a b :=
    ((phaseEuclidean n).continuous.comp hd).intervalIntegrable _ _
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hdu x) hi
  have hb := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := fun x => phaseEuclidean n (v' x)) hab
  rw [he] at hb
  simpa only [euclideanNorm,map_sub] using hb

theorem planar_partial_continuous {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) (e : Plane) : Continuous (fun z => fderiv ℝ v z e) :=
  ((hv.fderiv_right (show (∞ : WithTop ℕ∞)+1 ≤ ∞ by simp)).clm_apply contDiff_const).continuous

theorem euclideanNorm_continuous {n : ℕ} : Continuous (@euclideanNorm n) :=
  (phaseEuclidean n).continuous.norm

theorem horizontalSpeed_continuous {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) (y : ℝ) : Continuous (horizontalSpeed v y) :=
  euclideanNorm_continuous.comp ((planar_partial_continuous hv (1,0)).comp
    (continuous_id.prodMk continuous_const))

theorem verticalSpeed_continuous {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) (x : ℝ) : Continuous (verticalSpeed v x) :=
  euclideanNorm_continuous.comp ((planar_partial_continuous hv (0,1)).comp
    (continuous_const.prodMk continuous_id))

theorem horizontal_displacement_bound {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) {a b : ℝ} (hab : a ≤ b) (y : ℝ) :
    euclideanNorm (v (b,y)-v (a,y)) ≤ ∫ x in a..b, horizontalSpeed v y x := by
  apply euclidean_displacement_le_integral _ _ hab
  · intro x
    exact (hv.differentiable (by simp) (x,y)).hasFDerivAt.comp_hasDerivAt x
      ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))
  · exact (planar_partial_continuous hv (1,0)).comp (continuous_id.prodMk continuous_const)

theorem vertical_displacement_bound {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    euclideanNorm (v (x,b)-v (x,a)) ≤ ∫ y in a..b, verticalSpeed v x y := by
  apply euclidean_displacement_le_integral _ _ hab
  · intro y
    exact (hv.differentiable (by simp) (x,y)).hasFDerivAt.comp_hasDerivAt y
      ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))
  · exact (planar_partial_continuous hv (0,1)).comp (continuous_const.prodMk continuous_id)


theorem planar_stokes_rectangle {β : Plane → Plane →L[ℝ] ℝ}
    (hβ : ContDiff ℝ ∞ β) {a b : Plane} (hab : a ≤ b) :
    (∫ z in Icc a b, planarCurl β z) =
      (∫ x in a.1..b.1, β (x,a.2) (1,0)) -
      (∫ x in a.1..b.1, β (x,b.2) (1,0)) +
      (∫ y in a.2..b.2, β (b.1,y) (0,1)) -
      (∫ y in a.2..b.2, β (a.1,y) (0,1)) := by
  have hf : ContDiff ℝ ∞ (fun z => β z (0,1)) := hβ.clm_apply contDiff_const
  have hg : ContDiff ℝ ∞ (fun z => -(β z (1,0))) := (hβ.clm_apply contDiff_const).neg
  have hdf (z : Plane) : HasFDerivAt (fun w => β w (0,1))
      ((fderiv ℝ β z).flip (0,1)) z := by
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
      fderiv_const_apply,add_apply,zero_apply,
      map_zero,ContinuousLinearMap.comp_zero,zero_add] using
      ((hβ.differentiable (by simp) z).hasFDerivAt.clm_apply (hasFDerivAt_const (0,1) z))
  have hdg (z : Plane) : HasFDerivAt (fun w => -(β w (1,0)))
      (-((fderiv ℝ β z).flip (1,0))) z := by
    have hh : HasFDerivAt (fun w => β w (1,0)) ((fderiv ℝ β z).flip (1,0)) z := by
      simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
        fderiv_const_apply,add_apply,zero_apply,
        map_zero,ContinuousLinearMap.comp_zero,zero_add] using
        ((hβ.differentiable (by simp) z).hasFDerivAt.clm_apply (hasFDerivAt_const (1,0) z))
    exact hh.neg
  have hi : IntegrableOn (planarCurl β) (Icc a b) :=
    (planarCurl_contDiff hβ).continuous.continuousOn.integrableOn_Icc
  change IntegrableOn (fun z => fderiv ℝ β z (1,0) (0,1) - fderiv ℝ β z (0,1) (1,0)) (Icc a b) at hi
  have he := integral_divergence_prod_Icc_of_hasFDerivAt_of_le
    (fun z => β z (0,1)) (fun z => -(β z (1,0)))
    (fun z => (fderiv ℝ β z).flip (0,1)) (fun z => -((fderiv ℝ β z).flip (1,0)))
    a b hab hf.continuous.continuousOn hg.continuous.continuousOn
    (fun z _ => hdf z) (fun z _ => hdg z) (by simpa only [ContinuousLinearMap.flip_apply,neg_apply,sub_eq_add_neg] using hi)
  simp only [ContinuousLinearMap.flip_apply,neg_apply,
    ←sub_eq_add_neg,intervalIntegral.integral_neg] at he
  change (∫ z in Icc a b, planarCurl β z) = _ at he
  rw [he]
  ring

theorem translatedPlanarPrimitive_smooth {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) (c : Phase n) :
    ContDiff ℝ ∞ (translatedPlanarPrimitive v c) :=
  planarPullback_smooth (hv.sub contDiff_const) (stdPrimitive_smooth n)

theorem translatedPlanarPrimitive_apply {n : ℕ} (v : Plane → Phase n)
    (c : Phase n) (z e : Plane) :
    translatedPlanarPrimitive v c z e =
      (1/2:ℝ) * standardForm (v z-c) (fderiv ℝ v z e) := by
  simp only [translatedPlanarPrimitive,planarPullback,stdPrimitive,
    ContinuousLinearMap.comp_apply,smul_apply,smul_eq_mul,
    stdOmega_apply,fderiv_sub_const]

theorem translatedPlanarPrimitive_curl {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) (c : Phase n) (z : Plane) :
    planarCurl (translatedPlanarPrimitive v c) z =
      standardForm (fderiv ℝ v z (1,0)) (fderiv ℝ v z (0,1)) := by
  rw [translatedPlanarPrimitive,planarPullback_curl (hv.sub contDiff_const)
    (stdPrimitive_smooth n),stdPrimitive_extDeriv,fderiv_sub_const]

theorem rectangle_boundary_displacement {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) {a b : Plane} (hab : a ≤ b) :
    (∀ x ∈ Icc a.1 b.1, euclideanNorm (v (x,a.2)-v a) ≤ rectangleBoundaryLength v a b) ∧
    (∀ x ∈ Icc a.1 b.1, euclideanNorm (v (x,b.2)-v a) ≤ rectangleBoundaryLength v a b) ∧
    (∀ y ∈ Icc a.2 b.2, euclideanNorm (v (a.1,y)-v a) ≤ rectangleBoundaryLength v a b) ∧
    (∀ y ∈ Icc a.2 b.2, euclideanNorm (v (b.1,y)-v a) ≤ rectangleBoundaryLength v a b) := by
  have hpH (y : ℝ) : 0 ≤ ∫ x in a.1..b.1, horizontalSpeed v y x :=
    intervalIntegral.integral_nonneg hab.1 (fun _ _ => euclideanNorm_nonneg _)
  have hpV (x : ℝ) : 0 ≤ ∫ y in a.2..b.2, verticalSpeed v x y :=
    intervalIntegral.integral_nonneg hab.2 (fun _ _ => euclideanNorm_nonneg _)
  have hH (y : ℝ) (x : ℝ) (hx : x ∈ Icc a.1 b.1) :
      euclideanNorm (v (x,y)-v (a.1,y)) ≤ ∫ t in a.1..b.1, horizontalSpeed v y t := by
    refine (horizontal_displacement_bound hv hx.1 y).trans ?_
    exact intervalIntegral.integral_mono_interval le_rfl hx.1 hx.2
      (Filter.Eventually.of_forall fun _ => euclideanNorm_nonneg _)
      ((horizontalSpeed_continuous hv y).intervalIntegrable _ _)
  have hV (x : ℝ) (y : ℝ) (hy : y ∈ Icc a.2 b.2) :
      euclideanNorm (v (x,y)-v (x,a.2)) ≤ ∫ t in a.2..b.2, verticalSpeed v x t := by
    refine (vertical_displacement_bound hv hy.1 x).trans ?_
    exact intervalIntegral.integral_mono_interval le_rfl hy.1 hy.2
      (Filter.Eventually.of_forall fun _ => euclideanNorm_nonneg _)
      ((verticalSpeed_continuous hv x).intervalIntegrable _ _)
  have htri (w u z : Phase n) : euclideanNorm (w-z) ≤ euclideanNorm (w-u)+euclideanNorm (u-z) := by
    simpa only [sub_add_sub_cancel] using euclideanNorm_add_le (w-u) (u-z)
  refine ⟨?_,?_,?_,?_⟩
  · intro x hx
    have hh := hH a.2 x hx
    change euclideanNorm (v (x,a.2)-v a) ≤ _ at hh
    unfold rectangleBoundaryLength
    linarith [hpH b.2,hpV a.1,hpV b.1]
  · intro x hx
    have hh := htri (v (x,b.2)) (v (a.1,b.2)) (v a)
    have h1 := hH b.2 x hx
    have h2 := hV a.1 b.2 ⟨hab.2,le_rfl⟩
    change euclideanNorm (v (a.1,b.2)-v a) ≤ _ at h2
    unfold rectangleBoundaryLength
    linarith [hpH a.2,hpV b.1]
  · intro y hy
    have hh := hV a.1 y hy
    change euclideanNorm (v (a.1,y)-v a) ≤ _ at hh
    unfold rectangleBoundaryLength
    linarith [hpH a.2,hpH b.2,hpV b.1]
  · intro y hy
    have hh := htri (v (b.1,y)) (v (b.1,a.2)) (v a)
    have h1 := hV b.1 y hy
    have h2 := hH a.2 b.1 ⟨hab.1,le_rfl⟩
    change euclideanNorm (v (b.1,a.2)-v a) ≤ _ at h2
    unfold rectangleBoundaryLength
    linarith [hpH b.2,hpV a.1]

 
theorem standard_area_rectangle_le_length_sq {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) {a b : Plane} (hab : a ≤ b) :
    (∫ z in Icc a b, standardForm (fderiv ℝ v z (1,0)) (fderiv ℝ v z (0,1))) ≤
      (1/2:ℝ) * (rectangleBoundaryLength v a b)^2 := by
  let β := translatedPlanarPrimitive v (v a)
  let L := rectangleBoundaryLength v a b
  have hβ := translatedPlanarPrimitive_smooth hv (v a)
  have hcurl : (fun z => standardForm (fderiv ℝ v z (1,0)) (fderiv ℝ v z (0,1))) =
      planarCurl β := by
    funext z
    exact (translatedPlanarPrimitive_curl hv (v a) z).symm
  rw [hcurl,planar_stokes_rectangle hβ hab]
  have hbd := rectangle_boundary_displacement hv hab
  have hbound (l r : ℝ) (c : ℝ → Plane) (e : Plane) (hc : Continuous c)
      (he : Continuous (fun t => euclideanNorm (fderiv ℝ v (c t) e)))
      (hlr : l ≤ r) (hd : ∀ t ∈ Icc l r, euclideanNorm (v (c t)-v a) ≤ L) :
      |∫ t in l..r, β (c t) e| ≤ (1/2:ℝ)*L*(∫ t in l..r, euclideanNorm (fderiv ℝ v (c t) e)) := by
    refine (intervalIntegral.abs_integral_le_integral_abs hlr).trans ?_
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hlr
    · exact (((hβ.continuous.comp hc).clm_apply continuous_const).abs).intervalIntegrable _ _
    · exact (he.const_mul _).intervalIntegrable _ _
    intro t ht
    rw [translatedPlanarPrimitive_apply,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
    calc
      (1/2:ℝ) * |standardForm (v (c t)-v a) (fderiv ℝ v (c t) e)| ≤
          (1/2:ℝ)*(euclideanNorm (v (c t)-v a)*euclideanNorm (fderiv ℝ v (c t) e)) :=
        mul_le_mul_of_nonneg_left (standardForm_abs_le _ _) (by norm_num)
      _ ≤ (1/2:ℝ)*(L*euclideanNorm (fderiv ℝ v (c t) e)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hd t ht) (euclideanNorm_nonneg _)) (by norm_num)
      _ = _ := by ring
  have h0 := hbound a.1 b.1 (fun x => (x,a.2)) (1,0)
    (continuous_id.prodMk continuous_const) (horizontalSpeed_continuous hv a.2) hab.1 hbd.1
  have h1 := hbound a.1 b.1 (fun x => (x,b.2)) (1,0)
    (continuous_id.prodMk continuous_const) (horizontalSpeed_continuous hv b.2) hab.1 hbd.2.1
  have h2 := hbound a.2 b.2 (fun y => (a.1,y)) (0,1)
    (continuous_const.prodMk continuous_id) (verticalSpeed_continuous hv a.1) hab.2 hbd.2.2.1
  have h3 := hbound a.2 b.2 (fun y => (b.1,y)) (0,1)
    (continuous_const.prodMk continuous_id) (verticalSpeed_continuous hv b.1) hab.2 hbd.2.2.2
  have hh0 := le_abs_self (∫ x in a.1..b.1, β (x,a.2) (1,0))
  have hh1 := neg_le_abs (∫ x in a.1..b.1, β (x,b.2) (1,0))
  have hh2 := neg_le_abs (∫ y in a.2..b.2, β (a.1,y) (0,1))
  have hh3 := le_abs_self (∫ y in a.2..b.2, β (b.1,y) (0,1))
  change _ ≤ (1/2:ℝ)*L^2
  have hL : L = (∫ x in a.1..b.1, euclideanNorm (fderiv ℝ v (x,a.2) (1,0))) +
      (∫ x in a.1..b.1, euclideanNorm (fderiv ℝ v (x,b.2) (1,0))) +
      (∫ y in a.2..b.2, euclideanNorm (fderiv ℝ v (a.1,y) (0,1))) +
      (∫ y in a.2..b.2, euclideanNorm (fderiv ℝ v (b.1,y) (0,1))) := rfl
  dsimp only [β] at h0 h1 h2 h3 hh0 hh1 hh2 hh3
  nlinarith [congrArg (fun x : ℝ => L*x) hL]

theorem planarDirichlet_nonneg {n : ℕ} (v : Plane → Phase n) (z : Plane) :
    0 ≤ planarDirichlet v z := add_nonneg (stdDot_nonneg _) (stdDot_nonneg _)

theorem planarDirichlet_continuous {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) : Continuous (planarDirichlet v) := by
  have hx := planar_partial_continuous hv (1,0)
  have hy := planar_partial_continuous hv (0,1)
  exact (((stdDot n).continuous.comp hx).clm_apply hx).add
    (((stdDot n).continuous.comp hy).clm_apply hy)

theorem rectangleBoundaryLength_sq_le {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) {a b : Plane} (hab : a ≤ b)
    {d : ℝ} (h1 : b.1-a.1 ≤ d) (h2 : b.2-a.2 ≤ d) :
    (rectangleBoundaryLength v a b)^2 ≤ 4*d*rectangleBoundaryEnergy v a b := by
  have hH (y : ℝ) : (∫ x in a.1..b.1, horizontalSpeed v y x)^2 ≤
      d * (∫ x in a.1..b.1, planarDirichlet v (x,y)) := by
    refine (interval_integral_sq_le (horizontalSpeed_continuous hv y) hab.1).trans ?_
    have hi : (∫ x in a.1..b.1, (horizontalSpeed v y x)^2) ≤
        ∫ x in a.1..b.1, planarDirichlet v (x,y) := by
      apply intervalIntegral.integral_mono_on hab.1
        (((horizontalSpeed_continuous hv y).pow 2).intervalIntegrable _ _)
        (((planarDirichlet_continuous hv).comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _)
      intro x hx
      change (euclideanNorm (fderiv ℝ v (x,y) (1,0)))^2 ≤
        stdDot n (fderiv ℝ v (x,y) (1,0)) (fderiv ℝ v (x,y) (1,0)) +
          stdDot n (fderiv ℝ v (x,y) (0,1)) (fderiv ℝ v (x,y) (0,1))
      rw [euclideanNorm_sq]
      exact le_add_of_nonneg_right (stdDot_nonneg _)
    calc
      (b.1-a.1) * (∫ x in a.1..b.1, (horizontalSpeed v y x)^2) ≤
          (b.1-a.1) * (∫ x in a.1..b.1, planarDirichlet v (x,y)) :=
        mul_le_mul_of_nonneg_left hi (sub_nonneg.mpr hab.1)
      _ ≤ d * (∫ x in a.1..b.1, planarDirichlet v (x,y)) :=
        mul_le_mul_of_nonneg_right h1 (intervalIntegral.integral_nonneg hab.1 (fun _ _ => planarDirichlet_nonneg _ _))
  have hV (x : ℝ) : (∫ y in a.2..b.2, verticalSpeed v x y)^2 ≤
      d * (∫ y in a.2..b.2, planarDirichlet v (x,y)) := by
    refine (interval_integral_sq_le (verticalSpeed_continuous hv x) hab.2).trans ?_
    have hi : (∫ y in a.2..b.2, (verticalSpeed v x y)^2) ≤
        ∫ y in a.2..b.2, planarDirichlet v (x,y) := by
      apply intervalIntegral.integral_mono_on hab.2
        (((verticalSpeed_continuous hv x).pow 2).intervalIntegrable _ _)
        (((planarDirichlet_continuous hv).comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)
      intro y hy
      change (euclideanNorm (fderiv ℝ v (x,y) (0,1)))^2 ≤
        stdDot n (fderiv ℝ v (x,y) (1,0)) (fderiv ℝ v (x,y) (1,0)) +
          stdDot n (fderiv ℝ v (x,y) (0,1)) (fderiv ℝ v (x,y) (0,1))
      rw [euclideanNorm_sq]
      exact le_add_of_nonneg_left (stdDot_nonneg _)
    calc
      (b.2-a.2) * (∫ y in a.2..b.2, (verticalSpeed v x y)^2) ≤
          (b.2-a.2) * (∫ y in a.2..b.2, planarDirichlet v (x,y)) :=
        mul_le_mul_of_nonneg_left hi (sub_nonneg.mpr hab.2)
      _ ≤ d * (∫ y in a.2..b.2, planarDirichlet v (x,y)) :=
        mul_le_mul_of_nonneg_right h2 (intervalIntegral.integral_nonneg hab.2 (fun _ _ => planarDirichlet_nonneg _ _))
  let l0 := ∫ x in a.1..b.1, horizontalSpeed v a.2 x
  let l1 := ∫ x in a.1..b.1, horizontalSpeed v b.2 x
  let l2 := ∫ y in a.2..b.2, verticalSpeed v a.1 y
  let l3 := ∫ y in a.2..b.2, verticalSpeed v b.1 y
  have hs : (l0+l1+l2+l3)^2 ≤ 4*(l0^2+l1^2+l2^2+l3^2) := by
    nlinarith [sq_nonneg (l0-l1),sq_nonneg (l0-l2),sq_nonneg (l0-l3),
      sq_nonneg (l1-l2),sq_nonneg (l1-l3),sq_nonneg (l2-l3)]
  apply hs.trans
  dsimp only [l0,l1,l2,l3,rectangleBoundaryEnergy]
  nlinarith [hH a.2,hH b.2,hV a.1,hV b.1]

theorem standard_area_rectangle_le_boundaryEnergy {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) {a b : Plane} (hab : a ≤ b)
    {d : ℝ} (h1 : b.1-a.1 ≤ d) (h2 : b.2-a.2 ≤ d) :
    (∫ z in Icc a b, standardForm (fderiv ℝ v z (1,0)) (fderiv ℝ v z (0,1))) ≤
      2*d*rectangleBoundaryEnergy v a b := by
  have hh := standard_area_rectangle_le_length_sq hv hab
  have he := rectangleBoundaryLength_sq_le hv hab h1 h2
  linarith

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_SquareBounds
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

theorem planeSquare_mono (c : Plane) {r s : ℝ} (hrs : r ≤ s) : planeSquare c r ⊆ planeSquare c s := by
  intro z hz
  exact ⟨⟨by linarith [hz.1.1],by linarith [hz.1.2]⟩,
    ⟨by linarith [hz.2.1],by linarith [hz.2.2]⟩⟩

theorem squareEnergy_nonneg {n : ℕ} (v : Plane → Phase n) (c : Plane) (r : ℝ) :
    0 ≤ squareEnergy v c r := integral_nonneg (fun z => planarDirichlet_nonneg v z)

theorem rectangle_integral_eq_iterated {f : Plane → ℝ} (hf : Continuous f)
    {a b : Plane} (hab : a ≤ b) :
    (∫ z in Icc a b, f z) = ∫ x in a.1..b.1, ∫ y in a.2..b.2, f (x,y) := by
  have hi : IntegrableOn f (Icc a b) := hf.continuousOn.integrableOn_Icc
  rw [← Icc_prod_Icc,Measure.volume_eq_prod] at hi ⊢
  rw [setIntegral_prod f hi]
  simp_rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le hab.1,
    ←intervalIntegral.integral_of_le hab.2]

theorem rectangle_integral_eq_iterated_swap {f : Plane → ℝ} (hf : Continuous f)
    {a b : Plane} (hab : a ≤ b) :
    (∫ z in Icc a b, f z) = ∫ y in a.2..b.2, ∫ x in a.1..b.1, f (x,y) := by
  rw [rectangle_integral_eq_iterated hf hab]
  apply intervalIntegral_intervalIntegral_swap
  have hi : IntegrableOn f (Icc a b) := hf.continuousOn.integrableOn_Icc
  apply hi.mono_set
  intro z hz
  rw [uIoc_of_le hab.1,uIoc_of_le hab.2] at hz
  exact ⟨⟨hz.1.1.le,hz.2.1.le⟩,⟨hz.1.2,hz.2.2⟩⟩

theorem exists_interval_mean {f : ℝ → ℝ} (hf : Continuous f)
    {a b : ℝ} (hab : a ≤ b) :
    ∃ t ∈ Icc a b, (b-a)*f t = ∫ x in a..b, f x := by
  obtain ⟨t,ht,he⟩ := exists_eq_const_mul_intervalIntegral_of_nonneg
    (μ := volume) hf.continuousOn (continuous_const.intervalIntegrable a b)
    (fun _ _ => (by norm_num : (0:ℝ) ≤ 1))
  refine ⟨t,by simpa only [uIcc_of_le hab] using ht,?_⟩
  simpa [intervalIntegral.integral_const,mul_comm] using he.symm

theorem horizontal_integral_continuous {f : Plane → ℝ} (hf : Continuous f) (a b : ℝ) :
    Continuous (fun y => ∫ x in a..b, f (x,y)) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact hf.comp continuous_swap

theorem vertical_integral_continuous {f : Plane → ℝ} (hf : Continuous f) (a b : ℝ) :
    Continuous (fun x => ∫ y in a..b, f (x,y)) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact hf

theorem planar_energy_rectangle_bound {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) {C : ℝ} (hC : 0 ≤ C)
    (hE : ∀ z, planarDirichlet v z ≤ C * standardForm
      (fderiv ℝ v z (1,0)) (fderiv ℝ v z (0,1)))
    {a b : Plane} (hab : a ≤ b) {d : ℝ}
    (h1 : b.1-a.1 ≤ d) (h2 : b.2-a.2 ≤ d) :
    (∫ z in Icc a b, planarDirichlet v z) ≤ 2*C*d*rectangleBoundaryEnergy v a b := by
  have hA : Continuous (fun z => standardForm (fderiv ℝ v z (1,0)) (fderiv ℝ v z (0,1))) := by
    simpa only [stdOmega_apply,Function.comp_def] using
      (((stdOmega n).continuous.comp (planar_partial_continuous hv (1,0))).clm_apply
        (planar_partial_continuous hv (0,1)))
  have hi : (∫ z in Icc a b, planarDirichlet v z) ≤
      ∫ z in Icc a b, C * standardForm (fderiv ℝ v z (1,0)) (fderiv ℝ v z (0,1)) :=
    integral_mono ((planarDirichlet_continuous hv).continuousOn.integrableOn_Icc)
      ((hA.const_mul C).continuousOn.integrableOn_Icc) hE
  rw [integral_const_mul] at hi
  have hb := mul_le_mul_of_nonneg_left (standard_area_rectangle_le_boundaryEnergy hv hab h1 h2) hC
  nlinarith

 

theorem exists_low_energy_rectangle {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) (c : Plane) {r : ℝ} (hr : 0 < r) :
    ∃ a b : Plane, a ≤ b ∧ planeSquare c (r/2) ⊆ Icc a b ∧
      Icc a b ⊆ planeSquare c r ∧ b.1-a.1 ≤ 2*r ∧ b.2-a.2 ≤ 2*r ∧
      r*rectangleBoundaryEnergy v a b ≤
        16 * (∫ z in planeSquare c r \ planeSquare c (r/2), planarDirichlet v z) := by
  let e := planarDirichlet v
  let A := ∫ z in planeSquare c r \ planeSquare c (r/2), e z
  have he : Continuous e := planarDirichlet_continuous hv
  have he0 (z : Plane) : 0 ≤ e z := planarDirichlet_nonneg v z
  have hi : IntegrableOn e (planeSquare c r \ planeSquare c (r/2)) :=
    he.continuousOn.integrableOn_Icc.mono_set sdiff_subset
  have hset {a b : Plane} (hsub : Icc a b ⊆ planeSquare c r \ planeSquare c (r/2)) :
      (∫ z in Icc a b, e z) ≤ A :=
    setIntegral_mono_set hi (Eventually.of_forall he0) hsub.eventuallyLE
  have hH (l u : ℝ) (hlu : l ≤ u)
      (hsub : Icc (c.1-r,l) (c.1+r,u) ⊆ planeSquare c r \ planeSquare c (r/2)) :
      ∃ y ∈ Icc l u, (u-l)*(∫ x in c.1-r..c.1+r, e (x,y)) ≤ A := by
    obtain ⟨y,hy,hm⟩ := exists_interval_mean (horizontal_integral_continuous he (c.1-r) (c.1+r)) hlu
    refine ⟨y,hy,?_⟩
    rw [hm,←rectangle_integral_eq_iterated_swap he (show (c.1-r,l) ≤ (c.1+r,u) from ⟨by linarith,hlu⟩)]
    exact hset hsub
  have hV (l u : ℝ) (hlu : l ≤ u)
      (hsub : Icc (l,c.2-r) (u,c.2+r) ⊆ planeSquare c r \ planeSquare c (r/2)) :
      ∃ x ∈ Icc l u, (u-l)*(∫ y in c.2-r..c.2+r, e (x,y)) ≤ A := by
    obtain ⟨x,hx,hm⟩ := exists_interval_mean (vertical_integral_continuous he (c.2-r) (c.2+r)) hlu
    refine ⟨x,hx,?_⟩
    rw [hm,←rectangle_integral_eq_iterated he (show (l,c.2-r) ≤ (u,c.2+r) from ⟨hlu,by linarith⟩)]
    exact hset hsub
  have hlowH : Icc (c.1-r,c.2-r) (c.1+r,c.2-3*r/4) ⊆
      planeSquare c r \ planeSquare c (r/2) := by
    intro z hz
    refine ⟨⟨hz.1,⟨hz.2.1,by linarith [hz.2.2]⟩⟩,?_⟩
    intro hh
    linarith [hz.2.2,hh.1.2]
  have hhighH : Icc (c.1-r,c.2+3*r/4) (c.1+r,c.2+r) ⊆
      planeSquare c r \ planeSquare c (r/2) := by
    intro z hz
    refine ⟨⟨⟨hz.1.1,by linarith [hz.1.2]⟩,hz.2⟩,?_⟩
    intro hh
    linarith [hz.1.2,hh.2.2]
  have hlowV : Icc (c.1-r,c.2-r) (c.1-3*r/4,c.2+r) ⊆
      planeSquare c r \ planeSquare c (r/2) := by
    intro z hz
    refine ⟨⟨hz.1,⟨by linarith [hz.2.1],hz.2.2⟩⟩,?_⟩
    intro hh
    linarith [hz.2.1,hh.1.1]
  have hhighV : Icc (c.1+3*r/4,c.2-r) (c.1+r,c.2+r) ⊆
      planeSquare c r \ planeSquare c (r/2) := by
    intro z hz
    refine ⟨⟨⟨by linarith [hz.1.1],hz.1.2⟩,hz.2⟩,?_⟩
    intro hh
    linarith [hz.1.1,hh.2.1]
  obtain ⟨a2,ha2,hEa2⟩ := hH (c.2-r) (c.2-3*r/4) (by linarith) hlowH
  obtain ⟨b2,hb2,hEb2⟩ := hH (c.2+3*r/4) (c.2+r) (by linarith) hhighH
  obtain ⟨a1,ha1,hEa1⟩ := hV (c.1-r) (c.1-3*r/4) (by linarith) hlowV
  obtain ⟨b1,hb1,hEb1⟩ := hV (c.1+3*r/4) (c.1+r) (by linarith) hhighV
  have h1 : a1 ≤ b1 := by linarith [ha1.2,hb1.1]
  have h2 : a2 ≤ b2 := by linarith [ha2.2,hb2.1]
  refine ⟨(a1,a2),(b1,b2),⟨h1,h2⟩,?_,?_,?_,?_,?_⟩
  · intro z hz
    exact ⟨⟨by linarith [ha1.2,hz.1.1],by linarith [ha2.2,hz.1.2]⟩,
      ⟨by linarith [hb1.1,hz.2.1],by linarith [hb2.1,hz.2.2]⟩⟩
  · intro z hz
    exact ⟨⟨ha1.1.trans hz.1.1,ha2.1.trans hz.1.2⟩,
      ⟨hz.2.1.trans hb1.2,hz.2.2.trans hb2.2⟩⟩
  · dsimp; linarith [ha1.1,hb1.2]
  · dsimp; linarith [ha2.1,hb2.2]
  · have hhb (y : ℝ) : (∫ x in a1..b1, e (x,y)) ≤ ∫ x in c.1-r..c.1+r, e (x,y) :=
      intervalIntegral.integral_mono_interval ha1.1 h1 hb1.2 (Eventually.of_forall fun x => he0 (x,y))
        ((he.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _)
    have hvb (x : ℝ) : (∫ y in a2..b2, e (x,y)) ≤ ∫ y in c.2-r..c.2+r, e (x,y) :=
      intervalIntegral.integral_mono_interval ha2.1 h2 hb2.2 (Eventually.of_forall fun y => he0 (x,y))
        ((he.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)
    have hh0 := mul_le_mul_of_nonneg_left (hhb a2) hr.le
    have hh1 := mul_le_mul_of_nonneg_left (hhb b2) hr.le
    have hh2 := mul_le_mul_of_nonneg_left (hvb a1) hr.le
    have hh3 := mul_le_mul_of_nonneg_left (hvb b1) hr.le
    change r*((∫ x in a1..b1, e (x,a2))+(∫ x in a1..b1, e (x,b2))+
      (∫ y in a2..b2, e (a1,y))+(∫ y in a2..b2, e (b1,y))) ≤ 16*A
    nlinarith

 
theorem square_energy_hole_filling {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) {C : ℝ} (hC : 0 ≤ C)
    (hE : ∀ z, planarDirichlet v z ≤ C * standardForm
      (fderiv ℝ v z (1,0)) (fderiv ℝ v z (0,1)))
    (c : Plane) {r : ℝ} (hr : 0 < r) :
    squareEnergy v c (r/2) ≤ 64*C*(squareEnergy v c r-squareEnergy v c (r/2)) := by
  obtain ⟨a,b,hab,hinner,houter,h1,h2,hbd⟩ := exists_low_energy_rectangle hv c hr
  have hi : squareEnergy v c (r/2) ≤ ∫ z in Icc a b, planarDirichlet v z :=
    setIntegral_mono_set ((planarDirichlet_continuous hv).continuousOn.integrableOn_Icc)
      (Eventually.of_forall fun z => planarDirichlet_nonneg v z) hinner.eventuallyLE
  have hrect := planar_energy_rectangle_bound hv hC hE hab h1 h2
  have hAnn : (∫ z in planeSquare c r \ planeSquare c (r/2), planarDirichlet v z) =
      squareEnergy v c r-squareEnergy v c (r/2) := by
    exact setIntegral_sdiff measurableSet_Icc
      ((planarDirichlet_continuous hv).continuousOn.integrableOn_Icc)
      (planeSquare_mono c (by linarith))
  rw [hAnn] at hbd
  have hh := mul_le_mul_of_nonneg_left hbd hC
  nlinarith

theorem decayRatio_nonneg {C : ℝ} (hC : 0 ≤ C) : 0 ≤ decayRatio C :=
  div_nonneg (by positivity) (by positivity)

theorem decayRatio_lt_one {C : ℝ} (hC : 0 ≤ C) : decayRatio C < 1 := by
  unfold decayRatio
  apply (div_lt_one (by positivity)).mpr
  linarith

theorem square_energy_decay_half {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) {C : ℝ} (hC : 0 ≤ C)
    (hE : ∀ z, planarDirichlet v z ≤ C * standardForm
      (fderiv ℝ v z (1,0)) (fderiv ℝ v z (0,1)))
    (c : Plane) {r : ℝ} (hr : 0 < r) :
    squareEnergy v c (r/2) ≤ decayRatio C * squareEnergy v c r := by
  have h := square_energy_hole_filling hv hC hE c hr
  unfold decayRatio
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith

theorem square_energy_decay_dyadic {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) {C : ℝ} (hC : 0 ≤ C)
    (hE : ∀ z, planarDirichlet v z ≤ C * standardForm
      (fderiv ℝ v z (1,0)) (fderiv ℝ v z (0,1)))
    (c : Plane) {r : ℝ} (hr : 0 < r) (k : ℕ) :
    squareEnergy v c (r*(1/2:ℝ)^k) ≤ (decayRatio C)^k * squareEnergy v c r := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := square_energy_decay_half hv hC hE c
      (show 0 < r*(1/2:ℝ)^k by positivity)
    have he : r*(1/2:ℝ)^(k+1) = (r*(1/2:ℝ)^k)/2 := by rw [pow_succ]; ring
    rw [he]
    exact h.trans (by simpa only [pow_succ,mul_assoc,mul_comm,mul_left_comm] using
      mul_le_mul_of_nonneg_left ih (decayRatio_nonneg hC))


 

 

 

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

theorem lineMean_const (d : ℝ) {a b : ℝ} (hab : a < b) :
    lineMean (fun _ => d) a b = d := by
  simp only [lineMean,intervalIntegral.integral_const,smul_eq_mul]
  field_simp [sub_ne_zero.mpr hab.ne']

theorem lineMean_sub {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (a b : ℝ) :
    lineMean (fun x => f x-g x) a b = lineMean f a b-lineMean g a b := by
  simp [lineMean,intervalIntegral.integral_sub (hf.intervalIntegrable a b) (hg.intervalIntegrable a b),sub_div]

theorem lineMean_mono {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {a b : ℝ} (hab : a < b) (hfg : ∀ x ∈ Icc a b, f x ≤ g x) :
    lineMean f a b ≤ lineMean g a b := by
  apply div_le_div_of_nonneg_right _ (sub_pos.mpr hab).le
  exact intervalIntegral.integral_mono_on hab.le (hf.intervalIntegrable a b)
    (hg.intervalIntegrable a b) hfg

theorem lineMean_abs_le (f : ℝ → ℝ) {a b : ℝ} (hab : a < b) :
    |lineMean f a b| ≤ lineMean (fun x => |f x|) a b := by
  simp only [lineMean,abs_div,abs_of_pos (sub_pos.mpr hab)]
  exact div_le_div_of_nonneg_right (intervalIntegral.abs_integral_le_integral_abs hab.le)
    (sub_pos.mpr hab).le

theorem exists_lineMean_eq {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a < b) :
    ∃ x ∈ Icc a b, lineMean f a b = f x := by
  obtain ⟨x,hx,he⟩ := exists_interval_mean hf hab.le
  refine ⟨x,hx,?_⟩
  unfold lineMean
  rw [←he]
  field_simp [sub_ne_zero.mpr hab.ne']

theorem lineMean_horizontal_continuous {f : Plane → ℝ} (hf : Continuous f) (a b : ℝ) :
    Continuous (fun y => lineMean (fun x => f (x,y)) a b) :=
  (horizontal_integral_continuous hf a b).div_const _

theorem lineMean_vertical_continuous {f : Plane → ℝ} (hf : Continuous f) (a b : ℝ) :
    Continuous (fun x => lineMean (fun y => f (x,y)) a b) :=
  (vertical_integral_continuous hf a b).div_const _

theorem rectangleMean_eq_integral {f : Plane → ℝ} (hf : Continuous f)
    {a b : Plane} (hab : a ≤ b) :
    rectangleMean f a b = (∫ z in Icc a b, f z)/((b.1-a.1)*(b.2-a.2)) := by
  rw [rectangle_integral_eq_iterated_swap hf hab]
  simp only [rectangleMean,lineMean,intervalIntegral.integral_div,div_div]

theorem rectangleMean_swap {f : Plane → ℝ} (hf : Continuous f)
    {a b : Plane} (hab : a ≤ b) :
    rectangleMean f a b = lineMean (fun x => lineMean (fun y => f (x,y)) a.2 b.2) a.1 b.1 := by
  rw [rectangleMean_eq_integral hf hab,rectangle_integral_eq_iterated hf hab]
  simp only [lineMean,intervalIntegral.integral_div,div_div,mul_comm]

theorem real_displacement_le_integral {f g : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : Continuous g)
    {a b : ℝ} (hab : a ≤ b) :
    |f b-f a| ≤ ∫ x in a..b, |g x| := by
  rw [←intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hf x) (hg.intervalIntegrable a b)]
  exact intervalIntegral.abs_integral_le_integral_abs hab

theorem real_displacement_le_integral_outer {f g : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : Continuous g)
    {a b x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    |f x-f y| ≤ ∫ s in a..b, |g s| := by
  wlog hxy : y ≤ x generalizing x y
  · rw [abs_sub_comm]
    exact this hy hx (le_of_not_ge hxy)
  have h := real_displacement_le_integral hf hg hxy
  exact h.trans (intervalIntegral.integral_mono_interval hy.1 hxy hx.2
    (Eventually.of_forall fun s => abs_nonneg (g s)) (hg.abs.intervalIntegrable a b))

theorem lineMean_oscillation {f g : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : Continuous g)
    {a b l u s t : ℝ} (hlu : l < u) (hst : s < t)
    (hl : a ≤ l) (hu : u ≤ b) (hs : a ≤ s) (ht : t ≤ b) :
    |lineMean f l u-lineMean f s t| ≤ ∫ x in a..b, |g x| := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  obtain ⟨x,hx,hxe⟩ := exists_lineMean_eq hc hlu
  obtain ⟨y,hy,hye⟩ := exists_lineMean_eq hc hst
  rw [hxe,hye]
  exact real_displacement_le_integral_outer hf hg ⟨hl.trans hx.1,hx.2.trans hu⟩
    ⟨hs.trans hy.1,hy.2.trans ht⟩

theorem rectangle_integral_sq_le {f : Plane → ℝ} (hf : Continuous f)
    {a b : Plane} (hab : a ≤ b) :
    (∫ z in Icc a b, f z)^2 ≤
      ((b.1-a.1)*(b.2-a.2)) * (∫ z in Icc a b, (f z)^2) := by
  rw [rectangle_integral_eq_iterated_swap hf hab,
    rectangle_integral_eq_iterated_swap (f := fun z => (f z)^2) (hf.pow 2) hab]
  have h1 := interval_integral_sq_le (horizontal_integral_continuous hf a.1 b.1) hab.2
  have h2 := intervalIntegral.integral_mono_on (μ := volume) hab.2
    ((horizontal_integral_continuous hf a.1 b.1).pow 2 |>.intervalIntegrable _ _)
    ((horizontal_integral_continuous (hf.pow 2) a.1 b.1).const_mul (b.1-a.1) |>.intervalIntegrable _ _)
    (fun y _ => interval_integral_sq_le (hf.comp (continuous_id.prodMk continuous_const)) hab.1)
  rw [intervalIntegral.integral_const_mul] at h2
  have h3 := mul_le_mul_of_nonneg_left h2 (sub_nonneg.mpr hab.2)
  exact h1.trans (by simpa only [Pi.pow_apply,mul_assoc,mul_comm,mul_left_comm] using h3)

theorem square_integral_abs_le {f e : Plane → ℝ} (hf : Continuous f) (he : Continuous e)
    (hfe : ∀ z, (f z)^2 ≤ e z) (c : Plane) {r : ℝ} (hr : 0 < r) :
    (∫ z in planeSquare c r, |f z|) ≤
      2*r*Real.sqrt (∫ z in planeSquare c r, e z) := by
  have hab : (c.1-r,c.2-r) ≤ (c.1+r,c.2+r) := ⟨by linarith,by linarith⟩
  have h0 : 0 ≤ ∫ z in planeSquare c r, e z :=
    integral_nonneg (fun z => (sq_nonneg (f z)).trans (hfe z))
  have h1 := rectangle_integral_sq_le hf.abs hab
  simp only [sq_abs] at h1
  have h2 := integral_mono (μ := volume.restrict (planeSquare c r)) ((hf.pow 2).continuousOn.integrableOn_Icc)
    (he.continuousOn.integrableOn_Icc) hfe
  have h3 := mul_le_mul_of_nonneg_left h2
    (show 0 ≤ ((c.1+r)-(c.1-r))*((c.2+r)-(c.2-r)) from
      mul_nonneg (by linarith) (by linarith))
  have hs := Real.sq_sqrt h0
  have ht : 0 ≤ 2*r*Real.sqrt (∫ z in planeSquare c r, e z) := by positivity
  change (∫ z in planeSquare c r, |f z|)^2 ≤
    ((c.1+r)-(c.1-r))*((c.2+r)-(c.2-r))*(∫ z in planeSquare c r, (f z)^2) at h1
  change ((c.1+r)-(c.1-r))*((c.2+r)-(c.2-r))*(∫ z in planeSquare c r, (f z)^2) ≤ _ at h3
  have hh := h1.trans h3
  apply (sq_le_sq₀ (integral_nonneg (fun z => abs_nonneg (f z))) ht).mp
  calc
    _ ≤ ((c.1+r)-(c.1-r))*((c.2+r)-(c.2-r))*(∫ z in planeSquare c r, e z) := hh
    _ = (2*r*Real.sqrt (∫ z in planeSquare c r, e z))^2 := by rw [mul_pow,hs]; ring

theorem squareMean_half_bound {f dx dy e : Plane → ℝ}
    (hf : Continuous f) (hdx : Continuous dx) (hdy : Continuous dy) (he : Continuous e)
    (hfX : ∀ x y, HasDerivAt (fun s => f (s,y)) (dx (x,y)) x)
    (hfY : ∀ x y, HasDerivAt (fun s => f (x,s)) (dy (x,y)) y)
    (hxE : ∀ z, (dx z)^2 ≤ e z) (hyE : ∀ z, (dy z)^2 ≤ e z)
    (c : Plane) {r : ℝ} (hr : 0 < r) :
    |squareMean f c (r/2)-squareMean f c r| ≤
      4*Real.sqrt (∫ z in planeSquare c r, e z) := by
  let F : ℝ → ℝ := fun y => lineMean (fun x => f (x,y)) (c.1-r/2) (c.1+r/2)
  let G : ℝ → ℝ := fun y => lineMean (fun x => f (x,y)) (c.1-r) (c.1+r)
  let H : ℝ → ℝ := fun y => ∫ x in c.1-r..c.1+r, |dx (x,y)|
  let V : ℝ → ℝ := fun x => ∫ y in c.2-r..c.2+r, |dy (x,y)|
  have hF : Continuous F := lineMean_horizontal_continuous hf _ _
  have hG : Continuous G := lineMean_horizontal_continuous hf _ _
  have hH : Continuous H := horizontal_integral_continuous hdx.abs _ _
  have hV : Continuous V := vertical_integral_continuous hdy.abs _ _
  have hH0 (y : ℝ) : 0 ≤ H y := intervalIntegral.integral_nonneg (by linarith)
    (fun _ _ => abs_nonneg _)
  have hab : (c.1-r,c.2-r) ≤ (c.1+r,c.2+r) := ⟨by linarith,by linarith⟩
  have hFG (y : ℝ) : |F y-G y| ≤ H y :=
    lineMean_oscillation (fun x => hfX x y) (hdx.comp (continuous_id.prodMk continuous_const))
      (by linarith) (by linarith) (by linarith) (by linarith) le_rfl le_rfl
  have hstep1 : |lineMean F (c.2-r/2) (c.2+r/2)-lineMean G (c.2-r/2) (c.2+r/2)| ≤
      (∫ z in planeSquare c r, |dx z|)/r := by
    rw [←lineMean_sub hF hG]
    apply (lineMean_abs_le _ (by linarith)).trans
    apply (lineMean_mono (hF.sub hG).abs hH (by linarith) (fun y _ => hFG y)).trans
    have hm := intervalIntegral.integral_mono_interval (μ := volume) (by linarith : c.2-r ≤ c.2-r/2)
      (by linarith : c.2-r/2 ≤ c.2+r/2) (by linarith : c.2+r/2 ≤ c.2+r)
      (Eventually.of_forall hH0) (hH.intervalIntegrable (c.2-r) (c.2+r))
    change (∫ y in c.2-r/2..c.2+r/2, H y)/((c.2+r/2)-(c.2-r/2)) ≤ _
    rw [show (c.2+r/2)-(c.2-r/2)=r by ring]
    apply div_le_div_of_nonneg_right _ hr.le
    exact hm.trans_eq (rectangle_integral_eq_iterated_swap hdx.abs hab).symm
  let L : ℝ → ℝ := fun x => lineMean (fun y => f (x,y)) (c.2-r/2) (c.2+r/2)
  let M : ℝ → ℝ := fun x => lineMean (fun y => f (x,y)) (c.2-r) (c.2+r)
  have hL : Continuous L := lineMean_vertical_continuous hf _ _
  have hM : Continuous M := lineMean_vertical_continuous hf _ _
  have hLM (x : ℝ) : |L x-M x| ≤ V x :=
    lineMean_oscillation (fun y => hfY x y) (hdy.comp (continuous_const.prodMk continuous_id))
      (by linarith) (by linarith) (by linarith) (by linarith) le_rfl le_rfl
  have hstep2 : |lineMean G (c.2-r/2) (c.2+r/2)-squareMean f c r| ≤
      (∫ z in planeSquare c r, |dy z|)/(2*r) := by
    have hs1 : lineMean G (c.2-r/2) (c.2+r/2) = lineMean L (c.1-r) (c.1+r) :=
      rectangleMean_swap (a := (c.1-r,c.2-r/2)) (b := (c.1+r,c.2+r/2)) hf ⟨by dsimp; linarith,by dsimp; linarith⟩
    have hs2 : squareMean f c r = lineMean M (c.1-r) (c.1+r) := rectangleMean_swap hf hab
    rw [hs1,hs2,←lineMean_sub hL hM]
    apply (lineMean_abs_le _ (by linarith)).trans
    apply (lineMean_mono (hL.sub hM).abs hV (by linarith) (fun x _ => hLM x)).trans
    change (∫ x in c.1-r..c.1+r, V x)/((c.1+r)-(c.1-r)) ≤ _
    rw [show (c.1+r)-(c.1-r)=2*r by ring]
    exact le_of_eq (congrArg (fun v : ℝ => v/(2*r)) (rectangle_integral_eq_iterated hdy.abs hab).symm)
  have hX := square_integral_abs_le hdx he hxE c hr
  have hY := square_integral_abs_le hdy he hyE c hr
  have hX' : (∫ z in planeSquare c r, |dx z|)/r ≤
      2*Real.sqrt (∫ z in planeSquare c r, e z) := by
    apply (div_le_iff₀ hr).mpr
    nlinarith
  have hY' : (∫ z in planeSquare c r, |dy z|)/(2*r) ≤
      Real.sqrt (∫ z in planeSquare c r, e z) := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have ht := abs_sub_le (squareMean f c (r/2))
    (lineMean G (c.2-r/2) (c.2+r/2)) (squareMean f c r)
  change |squareMean f c (r/2)-lineMean G (c.2-r/2) (c.2+r/2)| ≤ _ at hstep1
  linarith [Real.sqrt_nonneg (∫ z in planeSquare c r, e z)]

theorem exists_squareMean_eq {f : Plane → ℝ} (hf : Continuous f)
    (c : Plane) {r : ℝ} (hr : 0 < r) :
    ∃ z ∈ planeSquare c r, squareMean f c r = f z := by
  obtain ⟨y,hy,hey⟩ := exists_lineMean_eq (lineMean_horizontal_continuous hf (c.1-r) (c.1+r))
    (show c.2-r < c.2+r by linarith)
  obtain ⟨x,hx,hex⟩ := exists_lineMean_eq (hf.comp (continuous_id.prodMk continuous_const))
    (show c.1-r < c.1+r by linarith)
  exact ⟨(x,y),⟨⟨hx.1,hy.1⟩,⟨hx.2,hy.2⟩⟩,hey.trans hex⟩

theorem planeSquare_dist_le {c z : Plane} {r : ℝ} (hz : z ∈ planeSquare c r) :
    dist z c ≤ r := by
  rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
  exact max_le (abs_le.mpr ⟨by linarith [hz.1.1],by linarith [hz.2.1]⟩)
    (abs_le.mpr ⟨by linarith [hz.1.2],by linarith [hz.2.2]⟩)

theorem squareMean_tendsto {f : Plane → ℝ} (hf : Continuous f) (c : Plane)
    {r : ℕ → ℝ} (hr : ∀ k, 0 < r k) (hl : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun k => squareMean f c (r k)) atTop (𝓝 (f c)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ,hδ,hfδ⟩ := Metric.continuousAt_iff.mp hf.continuousAt ε hε
  filter_upwards [(tendsto_order.mp hl).2 δ hδ] with k hk
  obtain ⟨z,hz,he⟩ := exists_squareMean_eq hf c (hr k)
  rw [he]
  exact hfδ ((planeSquare_dist_le hz).trans_lt hk)

theorem morreyConstant_pos {C : ℝ} (hC : 0 ≤ C) : 0 < morreyConstant C := by
  have hs : Real.sqrt (decayRatio C) < 1 := (Real.sqrt_lt' (by norm_num)).mpr
    (by simpa using decayRatio_lt_one hC)
  unfold morreyConstant
  positivity

theorem squareMean_point_bound {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) {C : ℝ} (hC : 0 ≤ C)
    (hE : ∀ z, planarDirichlet v z ≤ C * standardForm
      (fderiv ℝ v z (1,0)) (fderiv ℝ v z (0,1)))
    {f dx dy : Plane → ℝ} (hf : Continuous f) (hdx : Continuous dx) (hdy : Continuous dy)
    (hfX : ∀ x y, HasDerivAt (fun s => f (s,y)) (dx (x,y)) x)
    (hfY : ∀ x y, HasDerivAt (fun s => f (x,s)) (dy (x,y)) y)
    (hxE : ∀ z, (dx z)^2 ≤ planarDirichlet v z)
    (hyE : ∀ z, (dy z)^2 ≤ planarDirichlet v z)
    (c : Plane) {r : ℝ} (hr : 0 < r) :
    |f c-squareMean f c r| ≤ morreyConstant C * Real.sqrt (squareEnergy v c r) := by
  let s := Real.sqrt (decayRatio C)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs1 : s < 1 := (Real.sqrt_lt' (by norm_num)).mpr (by simpa using decayRatio_lt_one hC)
  have hpow (k : ℕ) : Real.sqrt ((decayRatio C)^k) = s^k := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ,Real.sqrt_mul (pow_nonneg (decayRatio_nonneg hC) k),ih,pow_succ]
  have hsd (k : ℕ) : Real.sqrt (squareEnergy v c (r*(1/2:ℝ)^k)) ≤
      s^k * Real.sqrt (squareEnergy v c r) := by
    have hh := Real.sqrt_le_sqrt (square_energy_decay_dyadic hv hC hE c hr k)
    rwa [Real.sqrt_mul (pow_nonneg (decayRatio_nonneg hC) k),hpow k] at hh
  let m : ℕ → ℝ := fun k => squareMean f c (r*(1/2:ℝ)^k)
  have hstep (k : ℕ) : dist (m k) (m (k+1)) ≤
      (4*Real.sqrt (squareEnergy v c r))*s^k := by
    have hh := squareMean_half_bound hf hdx hdy (planarDirichlet_continuous hv)
      hfX hfY hxE hyE c (show 0 < r*(1/2:ℝ)^k by positivity)
    have hh2 := mul_le_mul_of_nonneg_left (hsd k) (by norm_num : (0:ℝ) ≤ 4)
    have he : r*(1/2:ℝ)^(k+1) = (r*(1/2:ℝ)^k)/2 := by rw [pow_succ]; ring
    simpa only [m,Real.dist_eq,abs_sub_comm,he,squareEnergy,mul_assoc,mul_comm,mul_left_comm]
      using hh.trans hh2
  have hl : Tendsto m atTop (𝓝 (f c)) := by
    apply squareMean_tendsto hf c (fun k => by positivity)
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) < 1)).const_mul r
  have hh := dist_le_tsum_of_dist_le_of_tendsto₀
    (fun k => (4*Real.sqrt (squareEnergy v c r))*s^k) hstep
    ((summable_geometric_of_lt_one hs0 hs1).mul_left _) hl
  rw [tsum_mul_left,tsum_geometric_of_lt_one hs0 hs1] at hh
  simpa only [m,pow_zero,mul_one,Real.dist_eq,abs_sub_comm,morreyConstant,div_eq_mul_inv,
    mul_assoc,mul_comm,mul_left_comm] using hh


 

 

 

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

theorem squareMean_translate_bound {f dx dy e : Plane → ℝ}
    (hf : Continuous f) (hdx : Continuous dx) (hdy : Continuous dy) (he : Continuous e)
    (hfX : ∀ x y, HasDerivAt (fun s => f (s,y)) (dx (x,y)) x)
    (hfY : ∀ x y, HasDerivAt (fun s => f (x,s)) (dy (x,y)) y)
    (hxE : ∀ z, (dx z)^2 ≤ e z) (hyE : ∀ z, (dy z)^2 ≤ e z)
    (hi : Integrable e) {D : ℝ} (hD : (∫ z, e z) ≤ D)
    (c : Plane) {R r : ℝ} (hR : 0 ≤ R) (hr : 0 < r)
    (hc1 : |c.1| ≤ R) (hc2 : |c.2| ≤ R) :
    |squareMean f c r-squareMean f 0 r| ≤ 2*(R+r)/r*Real.sqrt D := by
  let L := R+r
  have hL : 0 < L := by dsimp [L]; linarith
  have hc1' := abs_le.mp hc1
  have hc2' := abs_le.mp hc2
  let F : ℝ → ℝ := fun y => lineMean (fun x => f (x,y)) (c.1-r) (c.1+r)
  let G : ℝ → ℝ := fun y => lineMean (fun x => f (x,y)) (-r) r
  let H : ℝ → ℝ := fun y => ∫ x in -L..L, |dx (x,y)|
  let V : ℝ → ℝ := fun x => ∫ y in -L..L, |dy (x,y)|
  have hF : Continuous F := lineMean_horizontal_continuous hf _ _
  have hG : Continuous G := lineMean_horizontal_continuous hf _ _
  have hH : Continuous H := horizontal_integral_continuous hdx.abs _ _
  have hV : Continuous V := vertical_integral_continuous hdy.abs _ _
  have hH0 (y : ℝ) : 0 ≤ H y := intervalIntegral.integral_nonneg (by linarith)
    (fun _ _ => abs_nonneg _)
  have hV0 (x : ℝ) : 0 ≤ V x := intervalIntegral.integral_nonneg (by linarith)
    (fun _ _ => abs_nonneg _)
  have hFG (y : ℝ) : |F y-G y| ≤ H y :=
    lineMean_oscillation (fun x => hfX x y) (hdx.comp (continuous_id.prodMk continuous_const))
      (by linarith) (by linarith) (by dsimp [L]; linarith) (by dsimp [L]; linarith)
      (by dsimp [L]; linarith) (by dsimp [L]; linarith)
  have hab : (-L,-L) ≤ (L,L) := ⟨by linarith,by linarith⟩
  have hsquare : Icc (-L,-L) (L,L) = planeSquare 0 L := by simp [planeSquare]
  have hstep1 : |lineMean F (c.2-r) (c.2+r)-lineMean G (c.2-r) (c.2+r)| ≤
      (∫ z in planeSquare 0 L, |dx z|)/(2*r) := by
    rw [←lineMean_sub hF hG]
    apply (lineMean_abs_le _ (by linarith)).trans
    apply (lineMean_mono (hF.sub hG).abs hH (by linarith) (fun y _ => hFG y)).trans
    have hm := intervalIntegral.integral_mono_interval (μ := volume)
      (by dsimp [L]; linarith : -L ≤ c.2-r) (by linarith : c.2-r ≤ c.2+r)
      (by dsimp [L]; linarith : c.2+r ≤ L) (Eventually.of_forall hH0) (hH.intervalIntegrable (-L) L)
    change (∫ y in c.2-r..c.2+r, H y)/((c.2+r)-(c.2-r)) ≤ _
    rw [show (c.2+r)-(c.2-r)=2*r by ring]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact hm.trans_eq (by rw [←rectangle_integral_eq_iterated_swap hdx.abs hab,hsquare])
  let F' : ℝ → ℝ := fun x => lineMean (fun y => f (x,y)) (c.2-r) (c.2+r)
  let G' : ℝ → ℝ := fun x => lineMean (fun y => f (x,y)) (-r) r
  have hF' : Continuous F' := lineMean_vertical_continuous hf _ _
  have hG' : Continuous G' := lineMean_vertical_continuous hf _ _
  have hFG' (x : ℝ) : |F' x-G' x| ≤ V x :=
    lineMean_oscillation (fun y => hfY x y) (hdy.comp (continuous_const.prodMk continuous_id))
      (by linarith) (by linarith) (by dsimp [L]; linarith) (by dsimp [L]; linarith)
      (by dsimp [L]; linarith) (by dsimp [L]; linarith)
  have hstep2 : |lineMean G (c.2-r) (c.2+r)-squareMean f 0 r| ≤
      (∫ z in planeSquare 0 L, |dy z|)/(2*r) := by
    have hs1 : lineMean G (c.2-r) (c.2+r) = lineMean F' (-r) r :=
      rectangleMean_swap (a := (-r,c.2-r)) (b := (r,c.2+r)) hf ⟨by dsimp; linarith,by dsimp; linarith⟩
    have hs2 : squareMean f 0 r = lineMean G' (-r) r := by
      simpa only [squareMean,Prod.fst_zero,Prod.snd_zero,zero_sub,zero_add] using
        rectangleMean_swap (a := (-r,-r)) (b := (r,r)) hf ⟨by dsimp; linarith,by dsimp; linarith⟩
    rw [hs1,hs2,←lineMean_sub hF' hG']
    apply (lineMean_abs_le _ (by linarith)).trans
    apply (lineMean_mono (hF'.sub hG').abs hV (by linarith) (fun x _ => hFG' x)).trans
    have hm := intervalIntegral.integral_mono_interval (μ := volume)
      (by dsimp [L]; linarith : -L ≤ -r) (by linarith : -r ≤ r)
      (by dsimp [L]; linarith : r ≤ L) (Eventually.of_forall hV0) (hV.intervalIntegrable (-L) L)
    change (∫ x in -r..r, V x)/(r-(-r)) ≤ _
    rw [show r-(-r)=2*r by ring]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact hm.trans_eq (by rw [←rectangle_integral_eq_iterated hdy.abs hab,hsquare])
  have he0 (z : Plane) : 0 ≤ e z := (sq_nonneg (dx z)).trans (hxE z)
  have hE : (∫ z in planeSquare 0 L, e z) ≤ D :=
    (setIntegral_le_integral hi (Eventually.of_forall he0)).trans hD
  have hX := (square_integral_abs_le hdx he hxE 0 hL).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hE) (by positivity : 0 ≤ 2*L))
  have hY := (square_integral_abs_le hdy he hyE 0 hL).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hE) (by positivity : 0 ≤ 2*L))
  have hX' : (∫ z in planeSquare 0 L, |dx z|)/(2*r) ≤ L/r*Real.sqrt D := by
    apply (div_le_iff₀ (by positivity)).mpr
    calc
      _ ≤ 2*L*Real.sqrt D := hX
      _ = L/r*Real.sqrt D*(2*r) := by field_simp
  have hY' : (∫ z in planeSquare 0 L, |dy z|)/(2*r) ≤ L/r*Real.sqrt D := by
    apply (div_le_iff₀ (by positivity)).mpr
    calc
      _ ≤ 2*L*Real.sqrt D := hY
      _ = L/r*Real.sqrt D*(2*r) := by field_simp
  have ht := abs_sub_le (squareMean f c r) (lineMean G (c.2-r) (c.2+r)) (squareMean f 0 r)
  change |squareMean f c r-lineMean G (c.2-r) (c.2+r)| ≤ _ at hstep1
  calc
    _ ≤ L/r*Real.sqrt D+L/r*Real.sqrt D :=
      ht.trans (add_le_add (hstep1.trans hX') (hstep2.trans hY'))
    _ = 2*(R+r)/r*Real.sqrt D := by dsimp [L]; ring


 

 

 

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

theorem phaseProjection_self {n : ℕ} (a : Phase n) :
    phaseProjection a a = euclideanNorm a := by
  change (euclideanNorm a)⁻¹ * stdDot n a a = _
  rw [←euclideanNorm_sq]
  by_cases h : euclideanNorm a = 0
  · simp [h]
  · field_simp

theorem phaseProjection_sq_le {n : ℕ} (a v : Phase n) :
    (phaseProjection a v)^2 ≤ stdDot n v v := by
  change ((euclideanNorm a)⁻¹ * stdDot n a v)^2 ≤ _
  by_cases h : euclideanNorm a = 0
  · simpa [h] using stdDot_nonneg v
  · have hp : 0 < (euclideanNorm a)^2 := sq_pos_of_ne_zero h
    have hh := stdDot_standardForm_sq_le a v
    have hb : (stdDot n a v)^2 ≤ (euclideanNorm a)^2 * stdDot n v v := by
      rw [euclideanNorm_sq]
      nlinarith [sq_nonneg (standardForm a v)]
    rw [mul_pow,inv_pow]
    calc
      _ ≤ ((euclideanNorm a)^2)⁻¹ * ((euclideanNorm a)^2 * stdDot n v v) :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hp.le)
      _ = stdDot n v v := by rw [←mul_assoc,inv_mul_cancel₀ hp.ne',one_mul]

theorem projection_point_bound {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) {C : ℝ} (hC : 0 ≤ C)
    (hE : ∀ z, planarDirichlet v z ≤ C * standardForm
      (fderiv ℝ v z (1,0)) (fderiv ℝ v z (0,1)))
    (ℓ : Phase n →L[ℝ] ℝ) (hℓ : ∀ a, (ℓ a)^2 ≤ stdDot n a a)
    (c : Plane) {r : ℝ} (hr : 0 < r) :
    |ℓ (v c)-squareMean (fun z => ℓ (v z)) c r| ≤
      morreyConstant C * Real.sqrt (squareEnergy v c r) := by
  apply squareMean_point_bound hv hC hE (ℓ.continuous.comp hv.continuous)
    (ℓ.continuous.comp (planar_partial_continuous hv (1,0)))
    (ℓ.continuous.comp (planar_partial_continuous hv (0,1)))
  · intro x y
    exact ℓ.hasFDerivAt.comp_hasDerivAt x
      ((hv.differentiable (by simp) (x,y)).hasFDerivAt.comp_hasDerivAt x
        ((hasDerivAt_id x).prodMk (hasDerivAt_const x y)))
  · intro x y
    exact ℓ.hasFDerivAt.comp_hasDerivAt y
      ((hv.differentiable (by simp) (x,y)).hasFDerivAt.comp_hasDerivAt y
        ((hasDerivAt_const y x).prodMk (hasDerivAt_id y)))
  · intro z
    exact (hℓ _).trans (le_add_of_nonneg_right (stdDot_nonneg _))
  · intro z
    exact (hℓ _).trans (le_add_of_nonneg_left (stdDot_nonneg _))
  · exact hr

theorem projection_translate_bound {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) (ℓ : Phase n →L[ℝ] ℝ)
    (hℓ : ∀ a, (ℓ a)^2 ≤ stdDot n a a)
    (hi : Integrable (planarDirichlet v)) {D : ℝ} (hD : (∫ z, planarDirichlet v z) ≤ D)
    (c : Plane) {R r : ℝ} (hR : 0 ≤ R) (hr : 0 < r)
    (hc1 : |c.1| ≤ R) (hc2 : |c.2| ≤ R) :
    |squareMean (fun z => ℓ (v z)) c r-squareMean (fun z => ℓ (v z)) 0 r| ≤
      2*(R+r)/r*Real.sqrt D := by
  apply squareMean_translate_bound (ℓ.continuous.comp hv.continuous)
    (ℓ.continuous.comp (planar_partial_continuous hv (1,0)))
    (ℓ.continuous.comp (planar_partial_continuous hv (0,1))) (planarDirichlet_continuous hv)
  · intro x y
    exact ℓ.hasFDerivAt.comp_hasDerivAt x
      ((hv.differentiable (by simp) (x,y)).hasFDerivAt.comp_hasDerivAt x
        ((hasDerivAt_id x).prodMk (hasDerivAt_const x y)))
  · intro x y
    exact ℓ.hasFDerivAt.comp_hasDerivAt y
      ((hv.differentiable (by simp) (x,y)).hasFDerivAt.comp_hasDerivAt y
        ((hasDerivAt_const y x).prodMk (hasDerivAt_id y)))
  · intro z
    exact (hℓ _).trans (le_add_of_nonneg_right (stdDot_nonneg _))
  · intro z
    exact (hℓ _).trans (le_add_of_nonneg_left (stdDot_nonneg _))
  · exact hi
  · exact hD
  · exact hR
  · exact hr
  · exact hc1
  · exact hc2

theorem lineMean_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (a b : ℝ) :
    lineMean (fun x => f x+g x) a b = lineMean f a b+lineMean g a b := by
  simp [lineMean,intervalIntegral.integral_add (hf.intervalIntegrable a b) (hg.intervalIntegrable a b),add_div]

theorem squareMean_sub {f g : Plane → ℝ} (hf : Continuous f) (hg : Continuous g)
    (c : Plane) (r : ℝ) :
    squareMean (fun z => f z-g z) c r = squareMean f c r-squareMean g c r := by
  unfold squareMean rectangleMean
  have hrow (y : ℝ) := lineMean_sub (f := fun x => f (x,y)) (g := fun x => g (x,y))
    (hf.comp (continuous_id.prodMk continuous_const))
    (hg.comp (continuous_id.prodMk continuous_const)) (c.1-r) (c.1+r)
  simp_rw [hrow]
  exact lineMean_sub (lineMean_horizontal_continuous hf _ _) (lineMean_horizontal_continuous hg _ _) _ _

theorem lineMean_linear (a b c : ℝ) {r : ℝ} (hr : 0 < r) :
    lineMean (fun x => a*x+b) (c-r) (c+r) = a*c+b := by
  rw [lineMean_add (f := fun x => a*x) (g := fun _ => b) (continuous_const.mul continuous_id) continuous_const,
    lineMean_const b (by linarith)]
  change (∫ x in c-r..c+r, a*x)/((c+r)-(c-r))+b = a*c+b
  rw [intervalIntegral.integral_const_mul,integral_id]
  have hn : (c+r)-(c-r) ≠ 0 := by linarith
  field_simp
  ring

theorem squareMean_affine_scalar (a b : ℝ) (c : Plane) {r : ℝ} (hr : 0 < r) :
    squareMean (fun z => a*z.1+b*z.2) c r = a*c.1+b*c.2 := by
  unfold squareMean rectangleMean
  simp_rw [lineMean_linear a _ c.1 hr]
  have he : (fun y : ℝ => a*c.1+b*y) = fun y => b*y+a*c.1 := by funext y; ring
  rw [he,lineMean_linear b _ c.2 hr]
  ring

theorem realCurve_affine_eq {n : ℕ} (a : Phase n) (z : Plane) :
    realCurve (fun ζ : ℂ => ζ • a) z = z.1 • a+z.2 • (Complex.I • a) := by
  ext i
  simp only [realCurve,Function.comp_apply,Complex.equivRealProdCLM_symm_apply,
    Pi.smul_apply,Pi.add_apply,smul_eq_mul,Complex.real_smul]
  ring

theorem projection_squareMean_affine {n : ℕ} (ℓ : Phase n →L[ℝ] ℝ)
    (a : Phase n) (c : Plane) {r : ℝ} (hr : 0 < r) :
    squareMean (fun z => ℓ (realCurve (fun ζ : ℂ => ζ • a) z)) c r =
      ℓ (realCurve (fun ζ : ℂ => ζ • a) c) := by
  simp only [realCurve_affine_eq,map_add,map_smul,smul_eq_mul]
  have he : (fun z : Plane => z.1*ℓ a+z.2*ℓ (Complex.I • a)) =
      fun z => ℓ a*z.1+ℓ (Complex.I • a)*z.2 := by funext z; ring
  rw [he,squareMean_affine_scalar _ _ c hr]
  ring

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_AffineSlopes
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

theorem stdDot_I_smul_self {n : ℕ} (a : Phase n) :
    stdDot n (Complex.I • a) (Complex.I • a) = stdDot n a a := by
  change stdDot n (standardJ n a) (standardJ n a) = _
  simp only [←standardForm_J_right]
  exact (compatible_standardJ n).2.1 a (standardJ n a)

theorem affineError_smooth {n : ℕ} {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (a : Phase n) :
    ContDiff ℝ ∞ (affineError u a) := hu.sub (affine_smooth a)

theorem dirichlet_le_affineError {n : ℕ} {u : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) (a : Phase n) (z : Plane) :
    dirichletDensity u z ≤ 2*dirichletDensity (affineError u a) z+4*(euclideanNorm a)^2 := by
  have he : realCurve (affineError u a) = realCurve u-realCurve (fun ζ : ℂ => ζ • a) := rfl
  have hd := fderiv_sub ((realCurve_smooth hu).differentiable (by simp) z)
    ((realCurve_smooth (affine_smooth a)).differentiable (by simp) z)
  have hx : Complex.equivRealProdCLM.symm ((1,0):Plane) = 1 := rfl
  have hy : Complex.equivRealProdCLM.symm ((0,1):Plane) = Complex.I := rfl
  unfold dirichletDensity
  rw [he,hd]
  simp only [sub_apply,realCurve_affine_fderiv,hx,hy,one_smul,euclideanNorm_sq]
  have h1 := stdDot_add_self_le (fderiv ℝ (realCurve u) z (1,0)-a) a
  have h2 := stdDot_add_self_le (fderiv ℝ (realCurve u) z (0,1)-Complex.I • a) (Complex.I • a)
  simp only [sub_add_cancel] at h1 h2
  rw [stdDot_I_smul_self] at h2
  linarith

theorem integral_constant_square (d : ℝ) (c : Plane) {r : ℝ} (hr : 0 ≤ r) :
    (∫ _ in planeSquare c r, d) = 4*r^2*d := by
  unfold planeSquare
  rw [rectangle_integral_eq_iterated continuous_const (show (c.1-r,c.2-r) ≤ (c.1+r,c.2+r) from
    ⟨by linarith,by linarith⟩)]
  simp only [intervalIntegral.integral_const,smul_eq_mul]
  ring

theorem squareEnergy_le_affineError {n : ℕ} {u : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) (a : Phase n)
    (hi : Integrable (dirichletDensity (affineError u a))) {D : ℝ}
    (hD : (∫ z, dirichletDensity (affineError u a) z) ≤ D)
    (c : Plane) {r : ℝ} (hr : 0 ≤ r) :
    squareEnergy (realCurve u) c r ≤ 16*r^2*(euclideanNorm a)^2+2*D := by
  have hwi : IntegrableOn (dirichletDensity (affineError u a)) (planeSquare c r) := hi.integrableOn
  have hci : IntegrableOn (fun _ : Plane => 4*(euclideanNorm a)^2) (planeSquare c r) :=
    continuous_const.integrableOn_Icc
  have hb := integral_mono (μ := volume.restrict (planeSquare c r))
    ((dirichletDensity_smooth hu).continuous.integrableOn_Icc) ((hwi.const_mul 2).add hci)
    (fun z => dirichlet_le_affineError hu a z)
  change (∫ z in planeSquare c r, dirichletDensity u z) ≤
    ∫ z in planeSquare c r, 2*dirichletDensity (affineError u a) z+4*(euclideanNorm a)^2 at hb
  rw [integral_add (hwi.const_mul 2) hci,integral_const_mul,integral_constant_square _ c hr] at hb
  have hh := (setIntegral_le_integral (s := planeSquare c r) hi
    (Eventually.of_forall (dirichletDensity_nonneg (affineError u a)))).trans hD
  change (∫ z in planeSquare c r, dirichletDensity u z) ≤ _
  nlinarith

theorem sqrt_squareEnergy_le_affineError {n : ℕ} {u : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) (a : Phase n)
    (hi : Integrable (dirichletDensity (affineError u a))) {D : ℝ}
    (hD : (∫ z, dirichletDensity (affineError u a) z) ≤ D)
    (hD0 : 0 ≤ D) (c : Plane) {r : ℝ} (hr : 0 ≤ r) :
    Real.sqrt (squareEnergy (realCurve u) c r) ≤ 4*r*euclideanNorm a+2*Real.sqrt D := by
  have hh := squareEnergy_le_affineError hu a hi hD c hr
  have ha0 := euclideanNorm_nonneg a
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (squareEnergy_nonneg _ _ _)]
  have hs := Real.sq_sqrt hD0
  nlinarith [euclideanNorm_nonneg a,Real.sqrt_nonneg D,
    mul_nonneg (mul_nonneg hr (euclideanNorm_nonneg a)) (Real.sqrt_nonneg D)]

theorem projection_squareMean_error {n : ℕ} {u : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) (a : Phase n) (ℓ : Phase n →L[ℝ] ℝ)
    (c : Plane) {r : ℝ} (hr : 0 < r) :
    squareMean (fun z => ℓ (realCurve (affineError u a) z)) c r =
      squareMean (fun z => ℓ (realCurve u z)) c r-
        ℓ (realCurve (fun ζ : ℂ => ζ • a) c) := by
  have he : (fun z => ℓ (realCurve (affineError u a) z)) =
      fun z => ℓ (realCurve u z)-ℓ (realCurve (fun ζ : ℂ => ζ • a) z) := by
    funext z
    exact ℓ.map_sub _ _
  rw [he]
  have hs := squareMean_sub (f := fun z => ℓ (realCurve u z))
    (g := fun z => ℓ (realCurve (fun ζ : ℂ => ζ • a) z))
    (ℓ.continuous.comp (realCurve_smooth hu).continuous)
    (ℓ.continuous.comp (realCurve_smooth (affine_smooth a)).continuous) c r
  rw [hs,projection_squareMean_affine ℓ a c hr]


 

 

 

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian








open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian








open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

theorem squareMean_translate_local_bound {f dx dy e : Plane → ℝ}
    (hf : Continuous f) (hdx : Continuous dx) (hdy : Continuous dy) (he : Continuous e)
    (hfX : ∀ x y, HasDerivAt (fun s => f (s,y)) (dx (x,y)) x)
    (hfY : ∀ x y, HasDerivAt (fun s => f (x,s)) (dy (x,y)) y)
    (hxE : ∀ z, (dx z)^2 ≤ e z) (hyE : ∀ z, (dy z)^2 ≤ e z)
    {D : ℝ} (c : Plane) {R r : ℝ} (hR : 0 ≤ R) (hr : 0 < r)
    (hD : (∫ z in planeSquare 0 (R+r), e z) ≤ D)
    (hc1 : |c.1| ≤ R) (hc2 : |c.2| ≤ R) :
    |squareMean f c r-squareMean f 0 r| ≤ 2*(R+r)/r*Real.sqrt D := by
  let L := R+r
  have hL : 0 < L := by dsimp [L]; linarith
  have hc1' := abs_le.mp hc1
  have hc2' := abs_le.mp hc2
  let F : ℝ → ℝ := fun y => lineMean (fun x => f (x,y)) (c.1-r) (c.1+r)
  let G : ℝ → ℝ := fun y => lineMean (fun x => f (x,y)) (-r) r
  let H : ℝ → ℝ := fun y => ∫ x in -L..L, |dx (x,y)|
  let V : ℝ → ℝ := fun x => ∫ y in -L..L, |dy (x,y)|
  have hF : Continuous F := lineMean_horizontal_continuous hf _ _
  have hG : Continuous G := lineMean_horizontal_continuous hf _ _
  have hH : Continuous H := horizontal_integral_continuous hdx.abs _ _
  have hV : Continuous V := vertical_integral_continuous hdy.abs _ _
  have hH0 (y : ℝ) : 0 ≤ H y := intervalIntegral.integral_nonneg (by linarith)
    (fun _ _ => abs_nonneg _)
  have hV0 (x : ℝ) : 0 ≤ V x := intervalIntegral.integral_nonneg (by linarith)
    (fun _ _ => abs_nonneg _)
  have hFG (y : ℝ) : |F y-G y| ≤ H y :=
    lineMean_oscillation (fun x => hfX x y) (hdx.comp (continuous_id.prodMk continuous_const))
      (by linarith) (by linarith) (by dsimp [L]; linarith) (by dsimp [L]; linarith)
      (by dsimp [L]; linarith) (by dsimp [L]; linarith)
  have hab : (-L,-L) ≤ (L,L) := ⟨by linarith,by linarith⟩
  have hsquare : Icc (-L,-L) (L,L) = planeSquare 0 L := by simp [planeSquare]
  have hstep1 : |lineMean F (c.2-r) (c.2+r)-lineMean G (c.2-r) (c.2+r)| ≤
      (∫ z in planeSquare 0 L, |dx z|)/(2*r) := by
    rw [←lineMean_sub hF hG]
    apply (lineMean_abs_le _ (by linarith)).trans
    apply (lineMean_mono (hF.sub hG).abs hH (by linarith) (fun y _ => hFG y)).trans
    have hm := intervalIntegral.integral_mono_interval (μ := volume)
      (by dsimp [L]; linarith : -L ≤ c.2-r) (by linarith : c.2-r ≤ c.2+r)
      (by dsimp [L]; linarith : c.2+r ≤ L) (Eventually.of_forall hH0) (hH.intervalIntegrable (-L) L)
    change (∫ y in c.2-r..c.2+r, H y)/((c.2+r)-(c.2-r)) ≤ _
    rw [show (c.2+r)-(c.2-r)=2*r by ring]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact hm.trans_eq (by rw [←rectangle_integral_eq_iterated_swap hdx.abs hab,hsquare])
  let F' : ℝ → ℝ := fun x => lineMean (fun y => f (x,y)) (c.2-r) (c.2+r)
  let G' : ℝ → ℝ := fun x => lineMean (fun y => f (x,y)) (-r) r
  have hF' : Continuous F' := lineMean_vertical_continuous hf _ _
  have hG' : Continuous G' := lineMean_vertical_continuous hf _ _
  have hFG' (x : ℝ) : |F' x-G' x| ≤ V x :=
    lineMean_oscillation (fun y => hfY x y) (hdy.comp (continuous_const.prodMk continuous_id))
      (by linarith) (by linarith) (by dsimp [L]; linarith) (by dsimp [L]; linarith)
      (by dsimp [L]; linarith) (by dsimp [L]; linarith)
  have hstep2 : |lineMean G (c.2-r) (c.2+r)-squareMean f 0 r| ≤
      (∫ z in planeSquare 0 L, |dy z|)/(2*r) := by
    have hs1 : lineMean G (c.2-r) (c.2+r) = lineMean F' (-r) r :=
      rectangleMean_swap (a := (-r,c.2-r)) (b := (r,c.2+r)) hf ⟨by dsimp; linarith,by dsimp; linarith⟩
    have hs2 : squareMean f 0 r = lineMean G' (-r) r := by
      simpa only [squareMean,Prod.fst_zero,Prod.snd_zero,zero_sub,zero_add] using
        rectangleMean_swap (a := (-r,-r)) (b := (r,r)) hf ⟨by dsimp; linarith,by dsimp; linarith⟩
    rw [hs1,hs2,←lineMean_sub hF' hG']
    apply (lineMean_abs_le _ (by linarith)).trans
    apply (lineMean_mono (hF'.sub hG').abs hV (by linarith) (fun x _ => hFG' x)).trans
    have hm := intervalIntegral.integral_mono_interval (μ := volume)
      (by dsimp [L]; linarith : -L ≤ -r) (by linarith : -r ≤ r)
      (by dsimp [L]; linarith : r ≤ L) (Eventually.of_forall hV0) (hV.intervalIntegrable (-L) L)
    change (∫ x in -r..r, V x)/(r-(-r)) ≤ _
    rw [show r-(-r)=2*r by ring]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact hm.trans_eq (by rw [←rectangle_integral_eq_iterated hdy.abs hab,hsquare])
  have he0 (z : Plane) : 0 ≤ e z := (sq_nonneg (dx z)).trans (hxE z)
  have hE : (∫ z in planeSquare 0 L, e z) ≤ D := hD
  have hX := (square_integral_abs_le hdx he hxE 0 hL).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hE) (by positivity : 0 ≤ 2*L))
  have hY := (square_integral_abs_le hdy he hyE 0 hL).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hE) (by positivity : 0 ≤ 2*L))
  have hX' : (∫ z in planeSquare 0 L, |dx z|)/(2*r) ≤ L/r*Real.sqrt D := by
    apply (div_le_iff₀ (by positivity)).mpr
    calc
      _ ≤ 2*L*Real.sqrt D := hX
      _ = L/r*Real.sqrt D*(2*r) := by field_simp
  have hY' : (∫ z in planeSquare 0 L, |dy z|)/(2*r) ≤ L/r*Real.sqrt D := by
    apply (div_le_iff₀ (by positivity)).mpr
    calc
      _ ≤ 2*L*Real.sqrt D := hY
      _ = L/r*Real.sqrt D*(2*r) := by field_simp
  have ht := abs_sub_le (squareMean f c r) (lineMean G (c.2-r) (c.2+r)) (squareMean f 0 r)
  change |squareMean f c r-lineMean G (c.2-r) (c.2+r)| ≤ _ at hstep1
  calc
    _ ≤ L/r*Real.sqrt D+L/r*Real.sqrt D :=
      ht.trans (add_le_add (hstep1.trans hX') (hstep2.trans hY'))
    _ = 2*(R+r)/r*Real.sqrt D := by dsimp [L]; ring

theorem projection_translate_local_bound {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) (ℓ : Phase n →L[ℝ] ℝ)
    (hℓ : ∀ a, (ℓ a)^2 ≤ stdDot n a a)
    {D : ℝ} (c : Plane) {R r : ℝ} (hR : 0 ≤ R) (hr : 0 < r)
    (hD : (∫ z in planeSquare 0 (R+r), planarDirichlet v z) ≤ D)
    (hc1 : |c.1| ≤ R) (hc2 : |c.2| ≤ R) :
    |squareMean (fun z => ℓ (v z)) c r-squareMean (fun z => ℓ (v z)) 0 r| ≤
      2*(R+r)/r*Real.sqrt D := by
  apply squareMean_translate_local_bound (ℓ.continuous.comp hv.continuous)
    (ℓ.continuous.comp (planar_partial_continuous hv (1,0)))
    (ℓ.continuous.comp (planar_partial_continuous hv (0,1))) (planarDirichlet_continuous hv)
  · intro x y
    exact ℓ.hasFDerivAt.comp_hasDerivAt x
      ((hv.differentiable (by simp) (x,y)).hasFDerivAt.comp_hasDerivAt x
        ((hasDerivAt_id x).prodMk (hasDerivAt_const x y)))
  · intro x y
    exact ℓ.hasFDerivAt.comp_hasDerivAt y
      ((hv.differentiable (by simp) (x,y)).hasFDerivAt.comp_hasDerivAt y
        ((hasDerivAt_const y x).prodMk (hasDerivAt_id y)))
  · intro z
    exact (hℓ _).trans (le_add_of_nonneg_right (stdDot_nonneg _))
  · intro z
    exact (hℓ _).trans (le_add_of_nonneg_left (stdDot_nonneg _))
  · exact hR
  · exact hr
  · exact hD
  · exact hc1
  · exact hc2


 

 

 

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

theorem planeSquare_subset_origin {c : Plane} {R r : ℝ}
    (hc1 : |c.1| ≤ R) (hc2 : |c.2| ≤ R) :
    planeSquare c r ⊆ planeSquare 0 (R+r) := by
  intro z hz
  rcases hz with ⟨⟨h11,h12⟩,⟨h21,h22⟩⟩
  have ha := abs_le.mp hc1
  have hb := abs_le.mp hc2
  change ((0:ℝ)-(R+r) ≤ z.1 ∧ (0:ℝ)-(R+r) ≤ z.2) ∧ (z.1 ≤ 0+(R+r) ∧ z.2 ≤ 0+(R+r))
  dsimp at h11 h12 h21 h22
  exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

theorem squareEnergy_le_origin {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) {c : Plane} {R r : ℝ}
    (hc1 : |c.1| ≤ R) (hc2 : |c.2| ≤ R) :
    squareEnergy v c r ≤ squareEnergy v 0 (R+r) :=
  setIntegral_mono_set (planarDirichlet_continuous hv).integrableOn_Icc
    (Eventually.of_forall (planarDirichlet_nonneg v)) (planeSquare_subset_origin hc1 hc2).eventuallyLE

theorem marked_distance_le_energy {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) {C : ℝ} (hC : 0 ≤ C)
    (hE : ∀ z, planarDirichlet v z ≤ C * standardForm
      (fderiv ℝ v z (1,0)) (fderiv ℝ v z (0,1))) :
    euclideanNorm (v (1,0)-v 0) ≤ (2*morreyConstant C+4)*Real.sqrt (squareEnergy v 0 2) := by
  let ℓ := phaseProjection (v (1,0)-v 0)
  have hℓ := phaseProjection_sq_le (v (1,0)-v 0)
  have h0 := projection_point_bound hv hC hE ℓ hℓ 0 (by norm_num : (0:ℝ)<1)
  have h1 := projection_point_bound hv hC hE ℓ hℓ (1,0) (by norm_num : (0:ℝ)<1)
  have hb0 : squareEnergy v 0 1 ≤ squareEnergy v 0 2 := by
    simpa only [show (1:ℝ)+1=2 by norm_num] using squareEnergy_le_origin hv
      (c := 0) (r := 1) (by norm_num : |(0:Plane).1| ≤ 1) (by norm_num)
  have hb1 : squareEnergy v (1,0) 1 ≤ squareEnergy v 0 2 := by
    simpa only [show (1:ℝ)+1=2 by norm_num] using squareEnergy_le_origin hv
      (c := (1,0)) (r := 1) (by norm_num : |((1,0):Plane).1| ≤ 1) (by norm_num)
  have h0' := h0.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hb0) (morreyConstant_pos hC).le)
  have h1' := h1.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hb1) (morreyConstant_pos hC).le)
  have ht := projection_translate_local_bound hv ℓ hℓ (1,0)
    (by norm_num : (0:ℝ)≤1) (by norm_num : (0:ℝ)<1)
    (le_refl (squareEnergy v 0 (1+1))) (by norm_num) (by norm_num)
  norm_num only [add_self_div_two,one_add_one_eq_two,div_one,show (2:ℝ)*2=4 by norm_num] at ht
  have he : ℓ (v (1,0))-ℓ (v 0) = euclideanNorm (v (1,0)-v 0) := by
    rw [←map_sub]
    exact phaseProjection_self _
  have h01 := (abs_le.mp h0').1
  have h11 := (abs_le.mp h1').2
  have ht1 := (abs_le.mp ht).2
  linarith

theorem scaled_sqrt_energy_bound {n : ℕ} {u : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) {C : ℝ} (hC : 0 ≤ C)
    (hE : ∀ z, planarDirichlet (realCurve u) z ≤ C * standardForm
      (fderiv ℝ (realCurve u) z (1,0)) (fderiv ℝ (realCurve u) z (0,1)))
    (a : Phase n) (hi : Integrable (dirichletDensity (affineError u a))) {D : ℝ}
    (hD : (∫ z, dirichletDensity (affineError u a) z) ≤ D) (hD0 : 0 ≤ D) (k : ℕ) :
    Real.sqrt (squareEnergy (realCurve u) 0 2) ≤
      8*(2:ℝ)^k*euclideanNorm a+2*(Real.sqrt (decayRatio C))^k*Real.sqrt D := by
  have hd := Real.sqrt_le_sqrt (square_energy_decay_dyadic (realCurve_smooth hu) hC hE 0
    (show 0 < 2*(2:ℝ)^k by positivity) k)
  have hp : 2*(2:ℝ)^k*(1/2:ℝ)^k=2 := by rw [mul_assoc,←mul_pow]; norm_num
  have he (j : ℕ) : Real.sqrt ((decayRatio C)^j) = (Real.sqrt (decayRatio C))^j := by
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ,Real.sqrt_mul (pow_nonneg (decayRatio_nonneg hC) j),ih,pow_succ]
  rw [hp,Real.sqrt_mul (pow_nonneg (decayRatio_nonneg hC) k),he] at hd
  have huB := sqrt_squareEnergy_le_affineError hu a hi hD hD0 0 (by positivity : 0 ≤ 2*(2:ℝ)^k)
  have hs1 : (Real.sqrt (decayRatio C))^k ≤ 1 := pow_le_one₀ (Real.sqrt_nonneg _)
    (by apply (Real.sqrt_le_one).mpr; exact (decayRatio_lt_one hC).le)
  have hmul := mul_le_mul_of_nonneg_left huB (by positivity : 0 ≤ (Real.sqrt (decayRatio C))^k)
  have ha := euclideanNorm_nonneg a
  have hpow := pow_nonneg (by norm_num : (0:ℝ)≤2) k
  have hm := mul_le_mul_of_nonneg_right hs1 (show 0 ≤ 8*(2:ℝ)^k*euclideanNorm a by positivity)
  nlinarith

theorem exists_positive_slope_bound {C D d : ℝ} (hC : 0 ≤ C) (_hD : 0 ≤ D) (hd : 0 < d) :
    ∃ m > 0, ∀ A : ℝ, 0 ≤ A →
      (∀ k : ℕ, d ≤ (2*morreyConstant C+4)*
        (8*(2:ℝ)^k*A+2*(Real.sqrt (decayRatio C))^k*Real.sqrt D)) → m ≤ A := by
  let H := 2*morreyConstant C+4
  have hH : 0 < H := by dsimp [H]; have := morreyConstant_pos hC; linarith
  have hs1 : Real.sqrt (decayRatio C) < 1 := (Real.sqrt_lt' (by norm_num)).mpr
    (by simpa using decayRatio_lt_one hC)
  have ht := ((tendsto_pow_atTop_nhds_zero_of_lt_one (Real.sqrt_nonneg _) hs1).const_mul
    (2*H)).mul_const (Real.sqrt D)
  have hev : ∀ᶠ k : ℕ in atTop, (2*H)*(Real.sqrt (decayRatio C))^k*Real.sqrt D < d/2 :=
    ht.eventually (eventually_lt_nhds (by linarith))
  obtain ⟨k,hk⟩ := hev.exists
  refine ⟨d/(16*H*(2:ℝ)^k),by positivity,?_⟩
  intro A hA hb
  apply (div_le_iff₀ (by positivity)).mpr
  have hh := hb k
  change d ≤ H*(8*(2:ℝ)^k*A+2*(Real.sqrt (decayRatio C))^k*Real.sqrt D) at hh
  nlinarith

theorem homotopy_slopes_bounded_below (n : ℕ) (hn : 3 ≤ n)
    (J : Phase n → End n) (hJs : ContDiff ℝ ∞ J)
    (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    (hs : tsupport (fun x => J x-standardJ n) ⊆ openBall n 1)
    (p q : Phase n) (hpq : p ≠ q) :
    ∃ m > 0, ∀ t ∈ Icc (0:ℝ) 1, ∀ u : ℂ → Phase n,
      AffineLineCurve (lineHomotopy J t) p q u →
      ∃ a : Phase n, m ≤ euclideanNorm a ∧
        Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 a) := by
  obtain ⟨D,hD,hDb⟩ := homotopy_affine_error_energy n hn J hJs hJ hc hs p q hpq
  obtain ⟨C,hC,hCb⟩ := homotopy_standard_energy_bound hJs hJ hc
  have hd : 0 < euclideanNorm (q-p) := by
    apply norm_pos_iff.mpr
    intro hh
    have he : q-p=0 := (phaseEuclidean n).injective (hh.trans (map_zero _).symm)
    exact hpq (sub_eq_zero.mp he).symm
  obtain ⟨m,hm,hmb⟩ := exists_positive_slope_bound hC.le hD.le hd
  refine ⟨m,hm,?_⟩
  intro t ht u hu
  obtain ⟨a,ha,hal,hai,haD⟩ := hDb t ht u hu
  refine ⟨a,?_,hal⟩
  apply hmb _ (euclideanNorm_nonneg a)
  intro k
  have hE (w : Plane) : planarDirichlet (realCurve u) w ≤ C * standardForm
      (fderiv ℝ (realCurve u) w (1,0)) (fderiv ℝ (realCurve u) w (0,1)) := by
    change stdDot n _ _+stdDot n _ _ ≤ _
    rw [realCurve_CR (hu.2.1 _)]
    exact hCb t ht _ _
  have hh := marked_distance_le_energy (realCurve_smooth hu.1) hC.le hE
  have hp0 : realCurve u 0 = p := hu.2.2.1
  have hq1 : realCurve u (1,0) = q := hu.2.2.2.1
  rw [hp0,hq1] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (scaled_sqrt_energy_bound hu.1 hC.le hE
    a hai haD hD.le k) (by have := morreyConstant_pos hC.le; linarith))

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_Properness
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

theorem projection_mean_double_bound {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) (ℓ : Phase n →L[ℝ] ℝ)
    (hℓ : ∀ a, (ℓ a)^2 ≤ stdDot n a a)
    (hi : Integrable (planarDirichlet v)) {D : ℝ} (hD : (∫ z, planarDirichlet v z) ≤ D)
    (c : Plane) {r : ℝ} (hr : 0 < r) :
    |squareMean (fun z => ℓ (v z)) c r-squareMean (fun z => ℓ (v z)) c (2*r)| ≤
      4*Real.sqrt D := by
  have hh : |squareMean (fun z => ℓ (v z)) c ((2*r)/2)-
      squareMean (fun z => ℓ (v z)) c (2*r)| ≤ 4*Real.sqrt (squareEnergy v c (2*r)) := by
    apply squareMean_half_bound (ℓ.continuous.comp hv.continuous)
      (ℓ.continuous.comp (planar_partial_continuous hv (1,0)))
      (ℓ.continuous.comp (planar_partial_continuous hv (0,1))) (planarDirichlet_continuous hv)
    · intro x y
      exact ℓ.hasFDerivAt.comp_hasDerivAt x
        ((hv.differentiable (by simp) (x,y)).hasFDerivAt.comp_hasDerivAt x
          ((hasDerivAt_id x).prodMk (hasDerivAt_const x y)))
    · intro x y
      exact ℓ.hasFDerivAt.comp_hasDerivAt y
        ((hv.differentiable (by simp) (x,y)).hasFDerivAt.comp_hasDerivAt y
          ((hasDerivAt_const y x).prodMk (hasDerivAt_id y)))
    · intro z
      exact (hℓ _).trans (le_add_of_nonneg_right (stdDot_nonneg _))
    · intro z
      exact (hℓ _).trans (le_add_of_nonneg_left (stdDot_nonneg _))
    · positivity
  rw [show (2*r)/2=r by ring] at hh
  have hb : squareEnergy v c (2*r) ≤ D :=
    (setIntegral_le_integral hi (Eventually.of_forall (planarDirichlet_nonneg v))).trans hD
  exact hh.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hb) (by norm_num))

theorem projection_mean_grow_bound {n : ℕ} {v : Plane → Phase n}
    (hv : ContDiff ℝ ∞ v) (ℓ : Phase n →L[ℝ] ℝ)
    (hℓ : ∀ a, (ℓ a)^2 ≤ stdDot n a a)
    (hi : Integrable (planarDirichlet v)) {D : ℝ} (hD : (∫ z, planarDirichlet v z) ≤ D)
    (c : Plane) (k : ℕ) :
    |squareMean (fun z => ℓ (v z)) c 1-squareMean (fun z => ℓ (v z)) c ((2:ℝ)^k)| ≤
      4*(k:ℝ)*Real.sqrt D := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hh := projection_mean_double_bound hv ℓ hℓ hi hD c (show 0 < (2:ℝ)^k by positivity)
    have ht := abs_sub_le (squareMean (fun z => ℓ (v z)) c 1)
      (squareMean (fun z => ℓ (v z)) c ((2:ℝ)^k))
      (squareMean (fun z => ℓ (v z)) c ((2:ℝ)^(k+1)))
    have he : (2:ℝ)^(k+1)=2*(2:ℝ)^k := by rw [pow_succ]; ring
    rw [he] at ht ⊢
    rw [Nat.cast_add,Nat.cast_one]
    linarith

theorem projection_error_point_bound {n : ℕ} {u : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) {C : ℝ} (hC : 0 ≤ C)
    (hE : ∀ z, planarDirichlet (realCurve u) z ≤ C * standardForm
      (fderiv ℝ (realCurve u) z (1,0)) (fderiv ℝ (realCurve u) z (0,1)))
    (a : Phase n) (hi : Integrable (dirichletDensity (affineError u a))) {D : ℝ}
    (hD : (∫ z, dirichletDensity (affineError u a) z) ≤ D) (hD0 : 0 ≤ D)
    (ℓ : Phase n →L[ℝ] ℝ) (hℓ : ∀ v, (ℓ v)^2 ≤ stdDot n v v) (c : Plane) :
    |ℓ (realCurve (affineError u a) c)-squareMean (fun z => ℓ (realCurve (affineError u a) z)) c 1| ≤
      morreyConstant C*(4*euclideanNorm a+2*Real.sqrt D) := by
  have hp := projection_point_bound (realCurve_smooth hu) hC hE ℓ hℓ c (by norm_num : (0:ℝ)<1)
  have hb := sqrt_squareEnergy_le_affineError hu a hi hD hD0 c (by norm_num : (0:ℝ)≤1)
  simp only [mul_one] at hb
  have hh := hp.trans (mul_le_mul_of_nonneg_left hb (morreyConstant_pos hC).le)
  rw [projection_squareMean_error hu a ℓ c (by norm_num : (0:ℝ)<1)]
  have he : ℓ (realCurve (affineError u a) c) = ℓ (realCurve u c)-ℓ (realCurve (fun z : ℂ => z • a) c) :=
    ℓ.map_sub _ _
  rw [he,sub_sub_sub_cancel_right]
  exact hh

theorem affine_error_log_bound {n : ℕ} {u : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) {C : ℝ} (hC : 0 ≤ C)
    (hE : ∀ z, planarDirichlet (realCurve u) z ≤ C * standardForm
      (fderiv ℝ (realCurve u) z (1,0)) (fderiv ℝ (realCurve u) z (0,1)))
    (a : Phase n) (hi : Integrable (dirichletDensity (affineError u a))) {D : ℝ}
    (hD : (∫ z, dirichletDensity (affineError u a) z) ≤ D) (hD0 : 0 ≤ D)
    {p : Phase n} (hp : u 0=p) (c : Plane) (k : ℕ)
    (hc1 : |c.1| ≤ (2:ℝ)^k) (hc2 : |c.2| ≤ (2:ℝ)^k) :
    euclideanNorm (realCurve (affineError u a) c-p) ≤
      2*morreyConstant C*(4*euclideanNorm a+2*Real.sqrt D)+(8*(k:ℝ)+4)*Real.sqrt D := by
  let v := realCurve (affineError u a)
  let ℓ := phaseProjection (v c-p)
  have hℓ := phaseProjection_sq_le (v c-p)
  have hv := realCurve_smooth (affineError_smooth hu a)
  have hp0 : v 0 = p := by change u 0-(0:ℂ) • a=p; simpa using hp
  have h0p := projection_error_point_bound hu hC hE a hi hD hD0 ℓ hℓ 0
  have hcp := projection_error_point_bound hu hC hE a hi hD hD0 ℓ hℓ c
  change |ℓ (v 0)-squareMean (fun z => ℓ (v z)) 0 1| ≤ _ at h0p
  rw [hp0] at h0p
  have h0g := projection_mean_grow_bound hv ℓ hℓ hi hD 0 k
  have hcg := projection_mean_grow_bound hv ℓ hℓ hi hD c k
  have ht := projection_translate_bound hv ℓ hℓ hi hD c
    (show 0 ≤ (2:ℝ)^k by positivity) (show 0 < (2:ℝ)^k by positivity) hc1 hc2
  have hcst : 2*((2:ℝ)^k+(2:ℝ)^k)/(2:ℝ)^k=4 := by
    have hn : (2:ℝ)^k ≠ 0 := by positivity
    field_simp
    ring
  rw [hcst] at ht
  have he : ℓ (v c)-ℓ p = euclideanNorm (v c-p) := by rw [←map_sub]; exact phaseProjection_self _
  have hh1 := (abs_le.mp h0p).1
  have hh2 := (abs_le.mp hcp).2
  have hh3 := (abs_le.mp h0g).1
  have hh4 := (abs_le.mp hcg).2
  have hh5 := (abs_le.mp ht).2
  change euclideanNorm (v c-p) ≤ _
  linarith


 

 

 

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

theorem euclideanNorm_complex_smul {n : ℕ} (z : ℂ) (a : Phase n) :
    euclideanNorm (z • a) = ‖z‖*euclideanNorm a := by
  change ‖(PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ)).symm (z • a)‖ = _
  have he : (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ)).symm (z • a) =
      z • (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ)).symm a := by
    ext i
    rfl
  rw [he,norm_smul]
  rfl

theorem exists_linear_lt_dyadic {m : ℝ} (hm : 0 < m) (b h : ℝ) :
    ∃ N : ℕ, ∀ k ≥ N, b+h*((k:ℝ)+1) < m*(2:ℝ)^k := by
  have h0 := tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num : (1:ℝ)<2)
  have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1:ℝ)<2)
  have ht : Tendsto (fun k : ℕ => (b+h*((k:ℝ)+1))/(2:ℝ)^k) atTop (𝓝 0) := by
    have hh := (h0.const_mul (b+h)).add (h1.const_mul h)
    convert hh using 1
    · ext k
      simp only [pow_zero,pow_one]
      ring
    · simp
  have he : ∀ᶠ k : ℕ in atTop, (b+h*((k:ℝ)+1))/(2:ℝ)^k < m :=
    ht.eventually (eventually_lt_nhds hm)
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  refine ⟨N,fun k hk => ?_⟩
  exact (div_lt_iff₀ (by positivity)).mp (hN k hk)








open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

theorem homotopy_uniform_asymptotic (n : ℕ) (hn : 3 ≤ n)
    (J : Phase n → End n) (hJs : ContDiff ℝ ∞ J)
    (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    (hs : tsupport (fun x => J x-standardJ n) ⊆ openBall n 1)
    (p q : Phase n) (hpq : p ≠ q) (ε : ℝ) (hε : 0 < ε) :
    ∃ S > 0, ∀ t ∈ Icc (0:ℝ) 1, ∀ u : ℂ → Phase n,
      AffineLineCurve (lineHomotopy J t) p q u → ∀ a : Phase n,
      Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 a) →
      ∀ z : ℂ, S < ‖z‖ → euclideanNorm (z⁻¹ • u z-a) < ε := by
  obtain ⟨D,hD,hDb⟩ := homotopy_affine_error_energy n hn J hJs hJ hc hs p q hpq
  obtain ⟨C,hC,hCb⟩ := homotopy_standard_energy_bound hJs hJ hc
  obtain ⟨L,hLb⟩ := homotopy_slopes_bounded_above n hn J hJs hJ hc hs p q hpq
  let E := 2*morreyConstant C*(4*L+2*Real.sqrt D)+4*Real.sqrt D
  obtain ⟨N,hN⟩ := exists_linear_lt_dyadic hε (E+euclideanNorm p) (8*Real.sqrt D)
  refine ⟨(2:ℝ)^N,by positivity,?_⟩
  intro t ht u hu a hal z hz
  obtain ⟨a',ha',hal',hai,haD⟩ := hDb t ht u hu
  have heq : a'=a := tendsto_nhds_unique hal' hal
  subst a'
  have hE (w : Plane) : planarDirichlet (realCurve u) w ≤ C * standardForm
      (fderiv ℝ (realCurve u) w (1,0)) (fderiv ℝ (realCurve u) w (0,1)) := by
    change stdDot n _ _+stdDot n _ _ ≤ _
    rw [realCurve_CR (hu.2.1 _)]
    exact hCb t ht _ _
  have hL := hLb t ht u hu a hal
  have hz1 : 1 ≤ ‖z‖ := (one_le_pow₀ (by norm_num : (1:ℝ)≤2)).trans hz.le
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
  obtain ⟨k,hk0,hk1⟩ := exists_nat_pow_near hz1 (by norm_num : (1:ℝ)<2)
  have hkN : N ≤ k := by
    by_contra hh
    have hh' : k+1 ≤ N := Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hh)
    have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hh'
    linarith
  have hb := affine_error_log_bound hu.1 hC.le hE a hai haD hD.le hu.2.2.1
    (z.re,z.im) (k+1) (z.abs_re_le_norm.trans hk1.le) (z.abs_im_le_norm.trans hk1.le)
  have hreal : realCurve (affineError u a) (z.re,z.im) = affineError u a z := by
    change affineError u a (Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM z)) = _
    rw [ContinuousLinearEquiv.symm_apply_apply]
  rw [hreal,Nat.cast_add,Nat.cast_one] at hb
  have hb' : euclideanNorm (affineError u a z-p) ≤ E+8*Real.sqrt D*((k:ℝ)+1) := by
    have hM := morreyConstant_pos hC.le
    dsimp [E]
    nlinarith
  have hw := euclideanNorm_add_le (affineError u a z-p) p
  rw [sub_add_cancel] at hw
  have hh := hN k hkN
  have hmk := mul_le_mul_of_nonneg_left hk0 hε.le
  have hb'' : euclideanNorm (affineError u a z) < ε*‖z‖ := by linarith
  have he : z⁻¹ • u z-a = z⁻¹ • affineError u a z := by
    simp only [affineError,smul_sub,smul_smul,inv_mul_cancel₀ hz0,one_smul]
  rw [he,euclideanNorm_complex_smul,norm_inv,inv_mul_eq_div]
  exact (div_lt_iff₀ (norm_pos_iff.mpr hz0)).mpr hb''

theorem homotopy_limit_has_nonzero_asymptotic_oai (n : ℕ) (hn : 3 ≤ n)
    (J : Phase n → End n) (hJs : ContDiff ℝ ∞ J)
    (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    (hs : tsupport (fun x => J x-standardJ n) ⊆ openBall n 1)
    (p q : Phase n) (hpq : p ≠ q)
    (t : ℕ → ℝ) (ht : ∀ j, t j ∈ Icc (0:ℝ) 1)
    (u : ℕ → ℂ → Phase n)
    (hu : ∀ j, AffineLineCurve (lineHomotopy J (t j)) p q (u j))
    (v : ℂ → Phase n) (hv : ∀ z, Tendsto (fun j => u j z) atTop (𝓝 (v z))) :
    ∃ a : Phase n, a ≠ 0 ∧ Tendsto (fun z : ℂ => z⁻¹ • v z) (cocompact ℂ) (𝓝 a) := by
  classical
  choose a ha hal using fun j => (hu j).2.2.2.2
  obtain ⟨L,hLb⟩ := homotopy_slopes_bounded_above n hn J hJs hJ hc hs p q hpq
  obtain ⟨m,hm,hmb⟩ := homotopy_slopes_bounded_below n hn J hJs hJ hc hs p q hpq
  have ham (j : ℕ) : m ≤ euclideanNorm (a j) := by
    obtain ⟨a',ha',hal'⟩ := hmb (t j) (ht j) (u j) (hu j)
    have he : a'=a j := tendsto_nhds_unique hal' (hal j)
    simpa only [he] using ha'
  have haL (j : ℕ) : euclideanNorm (a j) ≤ L := hLb (t j) (ht j) (u j) (hu j) (a j) (hal j)
  obtain ⟨b,hb,φ,hφ,hφb⟩ := (isCompact_closedBall (0 : EuclideanSpace ℂ (Fin n)) L).tendsto_subseq
    (x := fun j => phaseEuclidean n (a j)) (fun j => by simpa only [Metric.mem_closedBall,dist_zero_right,euclideanNorm] using haL j)
  let a₀ := (phaseEuclidean n).symm b
  have hφa : Tendsto (a ∘ φ) atTop (𝓝 a₀) := by
    simpa only [Function.comp_def,ContinuousLinearEquiv.symm_apply_apply] using
      (phaseEuclidean n).symm.continuous.continuousAt.tendsto.comp hφb
  have hma : m ≤ euclideanNorm a₀ := ge_of_tendsto
    (((phaseEuclidean n).continuous.continuousAt.tendsto.comp hφa).norm)
    (Eventually.of_forall fun j => ham (φ j))
  have ha₀ : a₀ ≠ 0 := by
    intro he
    have hz : euclideanNorm a₀=0 := by simp [he,euclideanNorm]
    linarith
  refine ⟨a₀,ha₀,?_⟩
  have htail : ∀ ε > 0, ∃ S > 0, ∀ z : ℂ, S < ‖z‖ → euclideanNorm (z⁻¹ • v z-a₀) < ε := by
    intro ε hε
    obtain ⟨S,hS,hSb⟩ := homotopy_uniform_asymptotic n hn J hJs hJ hc hs p q hpq
      (ε/2) (by linarith)
    refine ⟨S,hS,?_⟩
    intro z hz
    have hconv : Tendsto (fun j => z⁻¹ • u (φ j) z-a (φ j)) atTop (𝓝 (z⁻¹ • v z-a₀)) :=
      ((hv z).comp hφ.tendsto_atTop).const_smul z⁻¹ |>.sub hφa
    have hnconv := ((phaseEuclidean n).continuous.continuousAt.tendsto.comp hconv).norm
    have hle : euclideanNorm (z⁻¹ • v z-a₀) ≤ ε/2 := le_of_tendsto hnconv
      (Eventually.of_forall fun j => (hSb (t (φ j)) (ht (φ j)) (u (φ j)) (hu (φ j))
        (a (φ j)) (hal (φ j)) z hz).le)
    linarith
  have hconv : Tendsto (fun z : ℂ => phaseEuclidean n (z⁻¹ • v z)) (cocompact ℂ)
      (𝓝 (phaseEuclidean n a₀)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨S,hS,hSb⟩ := htail ε hε
    filter_upwards [tendsto_norm_cocompact_atTop.eventually (eventually_gt_atTop S)] with z hz
    rw [dist_eq_norm,←map_sub]
    exact hSb z hz
  simpa only [Function.comp_def,ContinuousLinearEquiv.symm_apply_apply] using
    (phaseEuclidean n).symm.continuous.continuousAt.tendsto.comp hconv


 

 

 

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian








open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian








open scoped ContDiff Topology
open Set Function Filter
open SymplecticBallPacking.Hamiltonian








open scoped ContDiff Topology
open Set Function Filter








open scoped ContDiff Topology
open Set Filter Function

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.homotopy_limit_has_nonzero_asymptotic_oai := @OAI.HigherDimensionalBallPacking.Rigidity.homotopy_limit_has_nonzero_asymptotic_oai
