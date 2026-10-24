-- Prove2me | solution 1 for LearnAugFL.CMP.lemma_17
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T09:22:44.210318+00:00
-- url     : https://prove2.me/submissions/114a675e-6ab3-42c0-86e5-acbded16223d

import Mathlib
import Definitions.Def_LearnAugFL_CMP_Setting
import Theorems.Thm_LearnAugFL_CMP_lemma_8

-- Complete inline checked local module: Basic.lean

namespace LearnAugFL.CMP.EqualizeProof

noncomputable def total {n : ℕ} (P : Fin n → Pt) (f : Pt) : ℝ := ∑ i, dist f (P i)

lemma total_nonneg {n : ℕ} (P : Fin n → Pt) (f : Pt) : 0 ≤ total P f :=
  Finset.sum_nonneg (fun _ _ => dist_nonneg)

lemma ucost_nonneg {n : ℕ} (P : Fin n → Pt) (z : Pt) : 0 ≤ ucost P z := by
  exact div_nonneg (total_nonneg P z) (Nat.cast_nonneg n)

lemma total_cost_bound {n : ℕ} (P : Fin n → Pt) (a b : Pt) (t : ℝ)
    (h : total P a ≤ t * total P b) : ucost P a ≤ t * ucost P b := by
  exact (div_le_div_of_nonneg_right h (Nat.cast_nonneg n)).trans_eq (by unfold ucost total; ring)

end LearnAugFL.CMP.EqualizeProof

-- Complete inline checked local module: GeometryC.lean

namespace LearnAugFL.CMP.ConsistencyProof

open EqualizeProof

lemma norm_sq_coords (p : Pt) (a b : Fin 2) (hab : a ≠ b) :
    ‖p‖ ^ 2 = (p a) ^ 2 + (p b) ^ 2 := by
  fin_cases a <;> fin_cases b <;> simp_all [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, add_comm]

lemma norm_axis (p : Pt) (a b : Fin 2) (hab : a ≠ b) (hp : p b = 0) : ‖p‖ = |p a| := by
  have hh := norm_sq_coords p a b hab
  simp only [hp, zero_pow (by decide : 2 ≠ 0), add_zero] at hh
  have ha := sq_abs (p a)
  nlinarith [norm_nonneg p, abs_nonneg (p a)]

lemma quadratic_bound (r w z s t d : ℝ) (ht : 0 ≤ t) (hd : 0 ≤ d)
    (hst : t ^ 2 = 1 + s ^ 2) (hdd : d ^ 2 = (r - w) ^ 2 + z ^ 2) :
    r ≤ t * d + w - s * z := by
  have he : (t * d) ^ 2 = (r - w + s * z) ^ 2 + (s * (r - w) - z) ^ 2 := by
    rw [mul_pow, hst, hdd]
    ring
  have hnonneg := mul_nonneg ht hd
  have hsq := sq_nonneg (s * (r - w) - z)
  nlinarith

lemma axis_positive_bound (p o : Pt) (a b : Fin 2) (hab : a ≠ b) (hp : p b = 0)
    (hpa : 0 < p a) (s t : ℝ) (ht : 0 ≤ t) (hst : t ^ 2 = 1 + s ^ 2) :
    ‖p‖ ≤ t * dist o p + o a - s * o b := by
  apply quadratic_bound _ _ _ _ _ _ ht dist_nonneg hst
  rw [dist_eq_norm, norm_sq_coords (o - p) a b hab, norm_axis p a b hab hp, abs_of_pos hpa]
  simp only [PiLp.sub_apply, hp, sub_zero]
  ring

lemma axis_nonpositive_bound (p o : Pt) (a b : Fin 2) (hab : a ≠ b) (hp : p b = 0)
    (hpa : p a ≤ 0) (s t : ℝ) (ht : 0 ≤ t) (hst : t ^ 2 = 1 + s ^ 2) :
    ‖p‖ ≤ t * dist o p - o a - s * o b := by
  have h := quadratic_bound ‖p‖ (-o a) (o b) s t (dist o p) ht dist_nonneg hst
  apply h
  rw [dist_eq_norm, norm_sq_coords (o - p) a b hab, norm_axis p a b hab hp, abs_of_nonpos hpa]
  simp only [PiLp.sub_apply, hp, sub_zero]
  ring

lemma pointwise_bound (p o : Pt) (ho : ∀ j, 0 < o j) (ho01 : o 0 ≤ o 1)
    (haxes : onX p ∨ onY p ∨ p = o) (s t : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht : 0 ≤ t) (hst : t ^ 2 = 1 + s ^ 2) :
    ‖p‖ ≤ t * dist o p - (o 0 + s * o 1) +
      (if 0 < p 0 then 2 * o 0 else 0) +
      (if 0 < p 1 then (1 - s) * o 0 + (1 + s) * o 1 else 0) := by
  rcases haxes with hpx | hpy | hpo
  · change p 1 = 0 at hpx
    simp only [hpx, lt_self_iff_false, if_false, add_zero]
    by_cases hx : 0 < p 0
    · rw [if_pos hx]
      have h := axis_positive_bound p o 0 1 (by decide) hpx hx s t ht hst
      nlinarith
    · rw [if_neg hx, add_zero]
      have h := axis_nonpositive_bound p o 0 1 (by decide) hpx (le_of_not_gt hx) s t ht hst
      linarith
  · change p 0 = 0 at hpy
    simp only [hpy, lt_self_iff_false, if_false, add_zero]
    by_cases hy : 0 < p 1
    · rw [if_pos hy]
      have h := axis_positive_bound p o 1 0 (by decide) hpy hy s t ht hst
      nlinarith
    · rw [if_neg hy, add_zero]
      have h := axis_nonpositive_bound p o 1 0 (by decide) hpy (le_of_not_gt hy) s t ht hst
      have hdiff := mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr ho01)
      nlinarith
  · subst p
    simp only [ho, if_true, dist_self, mul_zero, zero_sub]
    have hn : ‖o‖ ≤ o 0 + o 1 := by
      have h := norm_sq_coords o 0 1 (by decide)
      nlinarith [norm_nonneg o, ho 0, ho 1]
    have hh := mul_nonneg (sub_nonneg.mpr hs1) (ho 0).le
    nlinarith

open Classical in
lemma count_weight_sum {n : ℕ} (P : Fin n → Pt) (f : Pt → Prop) (D : ℝ) :
    (∑ i : Fin n, if f (P i) then D else 0) = (count P f : ℝ) * D := by
  classical
  rw [← Finset.sum_filter]
  simp [count, Set.ncard_eq_toFinset_card', nsmul_eq_mul]

lemma total_bound {n : ℕ} (P : Fin n → Pt) (o : Pt) (ho : ∀ j, 0 < o j) (ho01 : o 0 ≤ o 1)
    (haxes : ∀ i, onX (P i) ∨ onY (P i) ∨ P i = o) (s t : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht : 0 ≤ t) (hst : t ^ 2 = 1 + s ^ 2)
    (hcount : ∀ j, (1 + s) * count P (fun p => 0 < p j) ≤ s * n) :
    total P 0 ≤ t * total P o := by
  classical
  let α := 2 * o 0
  let β := (1 - s) * o 0 + (1 + s) * o 1
  have hα : 0 ≤ α := mul_nonneg (by norm_num) (ho 0).le
  have hβ : 0 ≤ β := add_nonneg (mul_nonneg (sub_nonneg.mpr hs1) (ho 0).le)
    (mul_nonneg (by linarith) (ho 1).le)
  have hx := mul_le_mul_of_nonneg_right (hcount 0) hα
  have hy := mul_le_mul_of_nonneg_right (hcount 1) hβ
  have hcoef : s * (α + β) ≤ (1 + s) * (o 0 + s * o 1) := by
    have hh := mul_nonneg (sq_nonneg (1 - s)) (ho 0).le
    dsimp [α, β]
    nlinarith
  have hcoefn := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    pointwise_bound (P i) o ho ho01 (haxes i) s t hs0 hs1 ht hst)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [count_weight_sum P (fun p => 0 < p 0) (2 * o 0),
    count_weight_sum P (fun p => 0 < p 1) ((1 - s) * o 0 + (1 + s) * o 1)] at hsum
  have hb : count P (fun p => 0 < p 0) * α + count P (fun p => 0 < p 1) * β ≤
      n * (o 0 + s * o 1) := by nlinarith
  dsimp [α, β] at hb
  simp only [total, dist_zero_left]
  linarith

end LearnAugFL.CMP.ConsistencyProof

-- Complete inline checked local module: GeometryR.lean

namespace LearnAugFL.CMP.RobustnessProof

open EqualizeProof

lemma norm_axis_x (p : Pt) (hp : p 1 = 0) : ‖p‖ = |p 0| := by
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_two, hp, Real.norm_eq_abs, Real.sqrt_sq_eq_abs]

lemma norm_axis_y (p : Pt) (hp : p 0 = 0) : ‖p‖ = |p 1| := by
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_two, hp, Real.norm_eq_abs, Real.sqrt_sq_eq_abs]

lemma norm_sq_two (p : Pt) : ‖p‖ ^ 2 = (p 0) ^ 2 + (p 1) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

lemma dist_sq_two (o p : Pt) : dist o p ^ 2 = (o 0 - p 0) ^ 2 + (o 1 - p 1) ^ 2 := by
  rw [dist_eq_norm, norm_sq_two]
  rfl

lemma quadratic_bound (r w z d s t : ℝ) (hd : 0 ≤ d) (ht : 0 ≤ t)
    (hds : d ^ 2 = (r - w) ^ 2 + z ^ 2) (hst : t ^ 2 = 1 + s ^ 2) :
    r ≤ t * d + w - s * z := by
  have he : (t*d)^2 = (r-w+s*z)^2 + (s*(r-w)-z)^2 := by
    rw [mul_pow, hds, hst]
    ring
  have htd := mul_nonneg ht hd
  have hsq := sq_nonneg (s*(r-w)-z)
  nlinarith

lemma norm_upper (o : Pt) (ho0 : 0 ≤ o 0) (ho1 : 0 ≤ o 1) :
    ‖o‖ ≤ o 0 + o 1 := by
  have hh := norm_sq_two o
  nlinarith [norm_nonneg o, mul_nonneg ho0 ho1]

lemma negative_bound (p o : Pt) (hp0 : p 0 ≤ 0) (hp1 : p 1 ≤ 0)
    (ho0 : 0 ≤ o 0) (ho1 : 0 ≤ o 1) (s t : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : t ^ 2 = 1 + s ^ 2) :
    ‖p‖ ≤ t * dist o p - s * ‖o‖ := by
  have hd : ‖p‖ ^ 2 + ‖o‖ ^ 2 ≤ dist o p ^ 2 := by
    rw [norm_sq_two p, norm_sq_two o, dist_sq_two]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos ho0 hp0,
      mul_nonpos_of_nonneg_of_nonpos ho1 hp1]
  have he : (‖p‖ + s*‖o‖)^2 ≤ (t*dist o p)^2 := by
    calc
      _ ≤ (1+s^2)*(‖p‖^2+‖o‖^2) := by nlinarith [sq_nonneg (s*‖p‖-‖o‖)]
      _ ≤ (1+s^2)*dist o p^2 := mul_le_mul_of_nonneg_left hd (by positivity)
      _ = _ := by rw [mul_pow, hst]
  have ha : 0 ≤ ‖p‖ + s*‖o‖ := by positivity
  have hb : 0 ≤ t*dist o p := mul_nonneg ht dist_nonneg
  nlinarith

open Classical in
lemma point_bound (p o : Pt) (ho0 : 0 < o 0) (ho1 : 0 < o 1)
    (hp : onX p ∨ onY p ∨ p = o) (s t : ℝ)
    (hs : 1 ≤ s) (ht : 0 ≤ t) (hst : t ^ 2 = 1 + s ^ 2) :
    ‖p‖ ≤ t * dist o p - s * ‖o‖ +
      (if 0 < p 0 then (1+s)/2*(‖o‖+o 0-o 1) else 0) +
      (if 0 < p 1 then (1+s)/2*(‖o‖-o 0+o 1) else 0) := by
  have hnorm := norm_upper o ho0.le ho1.le
  have hgap := mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hnorm)
  rcases hp with hp | hp | rfl
  · change p 1 = 0 at hp
    by_cases hx : 0 < p 0
    · simp only [hx, hp, lt_self_iff_false, if_false, if_true, add_zero]
      rw [norm_axis_x p hp, abs_of_pos hx]
      have hd : dist o p ^ 2 = (p 0 - o 0)^2+(o 1)^2 := by
        rw [dist_sq_two, hp]
        ring
      have h := quadratic_bound (p 0) (o 0) (o 1) (dist o p) s t dist_nonneg ht hd hst
      nlinarith
    · simp only [hx, hp, lt_self_iff_false, if_false, add_zero]
      exact negative_bound p o (le_of_not_gt hx) (by rw [hp]) ho0.le ho1.le s t (by linarith) ht hst
  · change p 0 = 0 at hp
    by_cases hy : 0 < p 1
    · simp only [hy, hp, lt_self_iff_false, if_false, if_true, add_zero]
      rw [norm_axis_y p hp, abs_of_pos hy]
      have hd : dist o p ^ 2 = (p 1 - o 1)^2+(o 0)^2 := by
        rw [dist_sq_two, hp]
        ring
      have h := quadratic_bound (p 1) (o 1) (o 0) (dist o p) s t dist_nonneg ht hd hst
      nlinarith
    · simp only [hy, hp, lt_self_iff_false, if_false, add_zero]
      exact negative_bound p o (by rw [hp]) (le_of_not_gt hy) ho0.le ho1.le s t (by linarith) ht hst
  · simp only [ho0, ho1, if_true, dist_self, mul_zero]
    ring_nf
    exact le_refl _

open Classical in
lemma count_weight_sum {n : ℕ} (P : Fin n → Pt) (f : Pt → Prop) (D : ℝ) :
    (∑ i : Fin n, if f (P i) then D else 0) = (count P f : ℝ) * D := by
  classical
  rw [← Finset.sum_filter]
  simp [count, Set.ncard_eq_toFinset_card', nsmul_eq_mul]

lemma total_bound {n : ℕ} (P : Fin n → Pt) (o : Pt) (ho0 : 0 < o 0) (ho1 : 0 < o 1)
    (haxes : ∀ i, onX (P i) ∨ onY (P i) ∨ P i = o) (s t : ℝ)
    (hs : 1 ≤ s) (ht : 0 ≤ t) (hst : t ^ 2 = 1 + s ^ 2)
    (hcount : ∀ j : Fin 2, (1+s)*(count P (fun p => 0 < p j) : ℝ) ≤ s*n) :
    total P 0 ≤ t * total P o := by
  classical
  let a := (1+s)/2*(‖o‖+o 0-o 1)
  let b := (1+s)/2*(‖o‖-o 0+o 1)
  have ho0n : o 0 ≤ ‖o‖ := by
    have hh := norm_sq_two o
    nlinarith [sq_nonneg (o 1), norm_nonneg o]
  have ho1n : o 1 ≤ ‖o‖ := by
    have hh := norm_sq_two o
    nlinarith [sq_nonneg (o 0), norm_nonneg o]
  have ha : 0 ≤ a := mul_nonneg (by linarith) (by linarith)
  have hb : 0 ≤ b := mul_nonneg (by linarith) (by linarith)
  have hab : a+b=(1+s)*‖o‖ := by dsimp [a,b]; ring
  have hc0 := mul_le_mul_of_nonneg_left (hcount 0) ha
  have hc1 := mul_le_mul_of_nonneg_left (hcount 1) hb
  have hc : (count P (fun p => 0 < p 0) : ℝ)*a +
      (count P (fun p => 0 < p 1) : ℝ)*b ≤ (n:ℝ)*s*‖o‖ := by
    apply (mul_le_mul_iff_right₀ (show 0 < 1+s by linarith)).mp
    nlinarith [congrArg (fun x : ℝ => x*s*n) hab]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    point_bound (P i) o ho0 ho1 (haxes i) s t hs ht hst)
  change (∑ i, ‖P i‖) ≤ ∑ i, (t*dist o (P i)-s*‖o‖+
    (if 0 < P i 0 then a else 0)+(if 0 < P i 1 then b else 0)) at hsum
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [count_weight_sum P (fun p => 0 < p 0) a,
    count_weight_sum P (fun p => 0 < p 1) b] at hsum
  simp only [total, dist_zero_left]
  nlinarith

end LearnAugFL.CMP.RobustnessProof

-- Complete inline checked local module: AxisBound.lean

namespace LearnAugFL.CMP.EqualizeProof

lemma parameter_one (s t : ℝ) (ht : 0 ≤ t) (hst : t ^ 2 = 1 + s ^ 2) : 1 ≤ t := by
  nlinarith [sq_nonneg s]

lemma axis_point_bound (p o : Pt) (ho0 : o 0 = 0) (ho1 : 0 ≤ o 1)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : t ^ 2 = 1 + s ^ 2) :
    ‖p‖ ≤ t * dist o p - s * o 1 + (if 0 < p 1 then (1+s)*o 1 else 0) := by
  have ht1 := parameter_one s t ht hst
  have hno : ‖o‖ = o 1 := by
    rw [RobustnessProof.norm_axis_y o ho0, abs_of_nonneg ho1]
  by_cases hp : 0 < p 1
  · rw [if_pos hp]
    have h := norm_add_le (p-o) o
    have he : p-o+o=p := sub_add_cancel _ _
    rw [he, ← dist_eq_norm, dist_comm, hno] at h
    have hd := mul_le_mul_of_nonneg_right ht1 (dist_nonneg (x:=o) (y:=p))
    nlinarith
  · rw [if_neg hp, add_zero]
    have hp1 : p 1 ≤ 0 := le_of_not_gt hp
    have hd : ‖p‖^2+(o 1)^2 ≤ dist o p^2 := by
      rw [RobustnessProof.norm_sq_two, RobustnessProof.dist_sq_two, ho0]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos ho1 hp1]
    have he : (‖p‖+s*o 1)^2 ≤ (t*dist o p)^2 := by
      calc
        _ ≤ (1+s^2)*(‖p‖^2+(o 1)^2) := by nlinarith [sq_nonneg (s*‖p‖-o 1)]
        _ ≤ (1+s^2)*dist o p^2 := mul_le_mul_of_nonneg_left hd (by positivity)
        _ = _ := by rw [mul_pow,hst]
    have ha : 0 ≤ ‖p‖+s*o 1 := by positivity
    have hb : 0 ≤ t*dist o p := mul_nonneg ht dist_nonneg
    nlinarith

lemma axis_total_bound {n : ℕ} (P : Fin n → Pt) (o : Pt) (ho0 : o 0 = 0) (ho1 : 0 ≤ o 1)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : t^2=1+s^2)
    (hcount : (1+s)*(count P (fun p => 0 < p 1) : ℝ) ≤ s*n) :
    total P 0 ≤ t*total P o := by
  classical
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    axis_point_bound (P i) o ho0 ho1 s t hs ht hst)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  rw [RobustnessProof.count_weight_sum P (fun p => 0 < p 1) ((1+s)*o 1)] at hh
  have hc := mul_le_mul_of_nonneg_right hcount ho1
  simp only [total,dist_zero_left]
  nlinarith

end LearnAugFL.CMP.EqualizeProof

-- Complete inline checked local module: GlobalGeometry.lean

namespace LearnAugFL.CMP.EqualizeProof

def RayProperty : Prop := ∀ (p o : Pt), (∀ j, 0 < o j) →
  ∃ q : Pt, (onX q ∨ onY q ∨ q = o) ∧ dist o p = dist o q + dist q p ∧
    (∀ j, 0 < q j → 0 < p j)

lemma weighted_indicator_mono (p q : Pt) (a : Fin 2 → ℝ) (ha : ∀ j, 0 ≤ a j)
    (h : ∀ j, 0 < q j → 0 < p j) (j : Fin 2) :
    (if 0 < q j then a j else 0) ≤ if 0 < p j then a j else 0 := by
  split_ifs with hq hp
  · rfl
  · exact False.elim (hp (h j hq))
  · exact ha j
  · rfl

lemma transfer_pointwise (hRay : RayProperty) (p o : Pt) (ho : ∀ j, 0 < o j)
    (t b : ℝ) (ht : 1 ≤ t) (a : Fin 2 → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hb : ∀ q, onX q ∨ onY q ∨ q = o →
      ‖q‖ ≤ t * dist o q + b + (if 0 < q 0 then a 0 else 0) +
        (if 0 < q 1 then a 1 else 0)) :
    ‖p‖ ≤ t * dist o p + b + (if 0 < p 0 then a 0 else 0) +
      (if 0 < p 1 then a 1 else 0) := by
  obtain ⟨q,hq,hd,hsg⟩ := hRay p o ho
  have hh := hb q hq
  have hnorm : ‖p‖ ≤ ‖q‖ + dist q p := by
    simpa only [dist_zero_left] using dist_triangle (0 : Pt) q p
  have htd := mul_le_mul_of_nonneg_right ht (dist_nonneg (x:=q) (y:=p))
  have h0 := weighted_indicator_mono p q a ha hsg 0
  have h1 := weighted_indicator_mono p q a ha hsg 1
  nlinarith

end LearnAugFL.CMP.EqualizeProof

namespace LearnAugFL.CMP.ConsistencyProof
open EqualizeProof

lemma pointwise_global (hRay : RayProperty) (p o : Pt) (ho : ∀ j, 0 < o j)
    (ho01 : o 0 ≤ o 1) (s t : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht : 0 ≤ t) (hst : t^2=1+s^2) :
    ‖p‖ ≤ t*dist o p-(o 0+s*o 1)+(if 0 < p 0 then 2*o 0 else 0)+
      (if 0 < p 1 then (1-s)*o 0+(1+s)*o 1 else 0) := by
  let a : Fin 2 → ℝ := ![2*o 0,(1-s)*o 0+(1+s)*o 1]
  have ha : ∀ j, 0 ≤ a j := by
    intro j
    fin_cases j
    · dsimp [a]; exact mul_nonneg (by norm_num) (ho 0).le
    · dsimp [a]
      exact add_nonneg (mul_nonneg (by linarith) (ho 0).le)
        (mul_nonneg (by linarith) (ho 1).le)
  exact transfer_pointwise hRay p o ho t (-(o 0+s*o 1)) (parameter_one s t ht hst) a ha
    (fun q hq => pointwise_bound q o ho ho01 hq s t hs0 hs1 ht hst)

lemma total_global (hRay : RayProperty) {n : ℕ} (P : Fin n → Pt) (o : Pt) (ho : ∀ j, 0 < o j) (ho01 : o 0 ≤ o 1)
    (s t : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht : 0 ≤ t) (hst : t ^ 2 = 1 + s ^ 2)
    (hcount : ∀ j, (1 + s) * count P (fun p => 0 < p j) ≤ s * n) :
    total P 0 ≤ t * total P o := by
  classical
  let α := 2 * o 0
  let β := (1 - s) * o 0 + (1 + s) * o 1
  have hα : 0 ≤ α := mul_nonneg (by norm_num) (ho 0).le
  have hβ : 0 ≤ β := add_nonneg (mul_nonneg (sub_nonneg.mpr hs1) (ho 0).le)
    (mul_nonneg (by linarith) (ho 1).le)
  have hx := mul_le_mul_of_nonneg_right (hcount 0) hα
  have hy := mul_le_mul_of_nonneg_right (hcount 1) hβ
  have hcoef : s * (α + β) ≤ (1 + s) * (o 0 + s * o 1) := by
    have hh := mul_nonneg (sq_nonneg (1 - s)) (ho 0).le
    dsimp [α, β]
    nlinarith
  have hcoefn := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    pointwise_global hRay (P i) o ho ho01 s t hs0 hs1 ht hst)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [count_weight_sum P (fun p => 0 < p 0) (2 * o 0),
    count_weight_sum P (fun p => 0 < p 1) ((1 - s) * o 0 + (1 + s) * o 1)] at hsum
  have hb : count P (fun p => 0 < p 0) * α + count P (fun p => 0 < p 1) * β ≤
      n * (o 0 + s * o 1) := by nlinarith
  dsimp [α, β] at hb
  simp only [total, dist_zero_left]
  linarith


end LearnAugFL.CMP.ConsistencyProof

namespace LearnAugFL.CMP.RobustnessProof
open EqualizeProof

lemma pointwise_global (hRay : RayProperty) (p o : Pt) (ho0 : 0 < o 0) (ho1 : 0 < o 1)
    (s t : ℝ) (hs : 1 ≤ s) (ht : 0 ≤ t) (hst : t^2=1+s^2) :
    ‖p‖ ≤ t*dist o p-s*‖o‖+
      (if 0 < p 0 then (1+s)/2*(‖o‖+o 0-o 1) else 0)+
      (if 0 < p 1 then (1+s)/2*(‖o‖-o 0+o 1) else 0) := by
  let a : Fin 2 → ℝ := ![(1+s)/2*(‖o‖+o 0-o 1),(1+s)/2*(‖o‖-o 0+o 1)]
  have h0 : o 0 ≤ ‖o‖ := by
    have hh := norm_sq_two o
    nlinarith [sq_nonneg (o 1), norm_nonneg o]
  have h1 : o 1 ≤ ‖o‖ := by
    have hh := norm_sq_two o
    nlinarith [sq_nonneg (o 0), norm_nonneg o]
  have ha : ∀ j, 0 ≤ a j := by
    intro j
    fin_cases j <;> dsimp [a] <;> apply mul_nonneg (by linarith) <;> linarith
  have ho : ∀ j, 0 < o j := by intro j; fin_cases j; exact ho0; exact ho1
  simpa [a, sub_eq_add_neg] using transfer_pointwise hRay p o ho t (-s*‖o‖) (parameter_one s t ht hst) a ha
    (fun q hq => by simpa [a, sub_eq_add_neg] using point_bound q o ho0 ho1 hq s t hs ht hst)

lemma total_global (hRay : RayProperty) {n : ℕ} (P : Fin n → Pt) (o : Pt) (ho0 : 0 < o 0) (ho1 : 0 < o 1)
    (s t : ℝ)
    (hs : 1 ≤ s) (ht : 0 ≤ t) (hst : t ^ 2 = 1 + s ^ 2)
    (hcount : ∀ j : Fin 2, (1+s)*(count P (fun p => 0 < p j) : ℝ) ≤ s*n) :
    total P 0 ≤ t * total P o := by
  classical
  let a := (1+s)/2*(‖o‖+o 0-o 1)
  let b := (1+s)/2*(‖o‖-o 0+o 1)
  have ho0n : o 0 ≤ ‖o‖ := by
    have hh := norm_sq_two o
    nlinarith [sq_nonneg (o 1), norm_nonneg o]
  have ho1n : o 1 ≤ ‖o‖ := by
    have hh := norm_sq_two o
    nlinarith [sq_nonneg (o 0), norm_nonneg o]
  have ha : 0 ≤ a := mul_nonneg (by linarith) (by linarith)
  have hb : 0 ≤ b := mul_nonneg (by linarith) (by linarith)
  have hab : a+b=(1+s)*‖o‖ := by dsimp [a,b]; ring
  have hc0 := mul_le_mul_of_nonneg_left (hcount 0) ha
  have hc1 := mul_le_mul_of_nonneg_left (hcount 1) hb
  have hc : (count P (fun p => 0 < p 0) : ℝ)*a +
      (count P (fun p => 0 < p 1) : ℝ)*b ≤ (n:ℝ)*s*‖o‖ := by
    apply (mul_le_mul_iff_right₀ (show 0 < 1+s by linarith)).mp
    nlinarith [congrArg (fun x : ℝ => x*s*n) hab]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    pointwise_global hRay (P i) o ho0 ho1 s t hs ht hst)
  change (∑ i, ‖P i‖) ≤ ∑ i, (t*dist o (P i)-s*‖o‖+
    (if 0 < P i 0 then a else 0)+(if 0 < P i 1 then b else 0)) at hsum
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [count_weight_sum P (fun p => 0 < p 0) a,
    count_weight_sum P (fun p => 0 < p 1) b] at hsum
  simp only [total, dist_zero_left]
  nlinarith


end LearnAugFL.CMP.RobustnessProof

-- Complete inline checked local module: Global.lean

namespace LearnAugFL.CMP.EqualizeProof

lemma normalized_consistency (hRay : RayProperty) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    {n k : ℕ} (hnk : Admissible c n k) (P : Fin n → Pt) (o : Pt)
    (ho : ∀ j, 0 ≤ o j) (ho01 : o 0 ≤ o 1)
    (hcount : ∀ j, 0 < o j → 2*count P (fun p => 0 < p j)+k ≤ n) :
    total P 0 ≤ (Real.sqrt (2*c^2+2)/(1+c))*total P o := by
  let s := (1-c)/(1+c)
  let t := Real.sqrt (2*c^2+2)/(1+c)
  have hd : 0 < 1+c := by linarith
  have hs0 : 0 ≤ s := div_nonneg (by linarith) hd.le
  have hs1 : s ≤ 1 := (div_le_one hd).mpr (by linarith)
  have ht : 0 ≤ t := div_nonneg (Real.sqrt_nonneg _) hd.le
  have hst : t^2=1+s^2 := by
    dsimp [s,t]
    rw [div_pow,Real.sq_sqrt (by positivity)]
    field_simp
    ring
  have ht1 := parameter_one s t ht hst
  have hcnt (j : Fin 2) (hj : 0 < o j) :
      (1+s)*(count P (fun p => 0 < p j) : ℝ) ≤ s*n := by
    have hm : (2:ℝ)*count P (fun p => 0 < p j) ≤ (1-c)*n := by
      have hh : (2:ℝ)*count P (fun p => 0 < p j)+k ≤ n := by exact_mod_cast hcount j hj
      rw [hnk.2] at hh
      nlinarith
    calc
      _ = (2*count P (fun p => 0 < p j))/(1+c) := by dsimp [s]; field_simp; ring
      _ ≤ ((1-c)*n)/(1+c) := div_le_div_of_nonneg_right hm hd.le
      _ = _ := by dsimp [s]; ring
  rcases eq_or_lt_of_le (ho 1) with hz | hp1
  · have hz0 : o 0 = 0 := le_antisymm (by linarith) (ho 0)
    have he : o = 0 := by ext j; fin_cases j; simpa using hz0; simpa using hz.symm
    rw [he]
    exact le_mul_of_one_le_left (total_nonneg P 0) ht1
  · rcases eq_or_lt_of_le (ho 0) with hz0 | hp0
    · exact axis_total_bound P o hz0.symm (ho 1) s t hs0 ht hst (hcnt 1 hp1)
    · have hp : ∀ j, 0 < o j := by intro j; fin_cases j; exact hp0; exact hp1
      exact ConsistencyProof.total_global hRay P o hp ho01 s t hs0 hs1 ht hst
        (fun j => hcnt j (hp j))

lemma normalized_robustness (hRay : RayProperty) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    {n k : ℕ} (hnk : Admissible c n k) (P : Fin n → Pt) (o : Pt)
    (ho : ∀ j, 0 ≤ o j) (ho01 : o 0 ≤ o 1)
    (hcount : ∀ j, 2*count P (fun p => 0 < p j) ≤ n+k) :
    total P 0 ≤ (Real.sqrt (2*c^2+2)/(1-c))*total P o := by
  let s := (1+c)/(1-c)
  let t := Real.sqrt (2*c^2+2)/(1-c)
  have hd : 0 < 1-c := by linarith
  have hs1 : 1 ≤ s := (one_le_div hd).mpr (by linarith)
  have hs0 : 0 ≤ s := le_trans (by norm_num) hs1
  have ht : 0 ≤ t := div_nonneg (Real.sqrt_nonneg _) hd.le
  have hst : t^2=1+s^2 := by
    dsimp [s,t]
    rw [div_pow,Real.sq_sqrt (by positivity)]
    field_simp
    ring
  have ht1 := parameter_one s t ht hst
  have hcnt (j : Fin 2) : (1+s)*(count P (fun p => 0 < p j) : ℝ) ≤ s*n := by
    have hm : (2:ℝ)*count P (fun p => 0 < p j) ≤ (1+c)*n := by
      have hh : (2:ℝ)*count P (fun p => 0 < p j) ≤ n+k := by exact_mod_cast hcount j
      rw [hnk.2] at hh
      nlinarith
    calc
      _ = (2*count P (fun p => 0 < p j))/(1-c) := by dsimp [s]; field_simp; ring
      _ ≤ ((1+c)*n)/(1-c) := div_le_div_of_nonneg_right hm hd.le
      _ = _ := by dsimp [s]; ring
  rcases eq_or_lt_of_le (ho 1) with hz | hp1
  · have hz0 : o 0 = 0 := le_antisymm (by linarith) (ho 0)
    have he : o = 0 := by ext j; fin_cases j; simpa using hz0; simpa using hz.symm
    rw [he]
    exact le_mul_of_one_le_left (total_nonneg P 0) ht1
  · rcases eq_or_lt_of_le (ho 0) with hz0 | hp0
    · exact axis_total_bound P o hz0.symm (ho 1) s t hs0 ht hst (hcnt 1)
    · exact RobustnessProof.total_global hRay P o hp0 hp1 s t hs1 ht hst hcnt

end LearnAugFL.CMP.EqualizeProof

-- Complete inline checked local module: Witness.lean

namespace LearnAugFL.CMP.EqualizeProof

lemma coa_to_oa_c (c : ℝ) {n k : ℕ} (P : Fin n → Pt) (h : COA_C c n k P) :
    OA_C c n k P !₂[0,1] := by
  obtain ⟨ha, ho, hm, x, hx, hp⟩ := h
  refine ⟨ha, ho, hm, by simp, by simp, ?_⟩
  intro i
  rcases hp i with hi | hi | hi <;> simp [hi,onX,onY]

lemma coa_to_oa_r (c : ℝ) {n k : ℕ} (P : Fin n → Pt) (h : COA_R c n k P) :
    OA_R c n k P !₂[0,1] := by
  obtain ⟨ha, ho, hm, x, hx, hp⟩ := h
  refine ⟨ha, ho, hm, by simp, by simp, ?_⟩
  intro i
  rcases hp i with hi | hi | hi <;> simp [hi,onX,onY]

lemma sharp_le_consistency (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hc : ∃ n k, Admissible c n k) (a : ℝ)
    (ha : ∀ (m k : ℕ) (Q : Fin m → Pt) (o : Pt), OA_C c m k Q o ∨ CA_C c m k Q o →
      ucost Q (cmp Q o k) ≤ a * ucost Q o) :
    Real.sqrt (2*c^2+2)/(1+c) ≤ a := by
  obtain ⟨n,k,Q,hQ,he⟩ := (LearnAugFL.CMP.lemma_8 c hc0 hc1 hc).1
  have ht : 0 < Real.sqrt (2*c^2+2)/(1+c) := by positivity
  have hn : ucost Q !₂[0,1] ≠ 0 := by
    intro h
    simp only [ratio,h,div_zero] at he
    linarith
  have hp : 0 < ucost Q !₂[0,1] := lt_of_le_of_ne (ucost_nonneg _ _) (Ne.symm hn)
  have hh := ha n k Q !₂[0,1] (Or.inl (coa_to_oa_c c Q hQ))
  have hh' := (div_le_iff₀ hp).mpr hh
  change ratio Q !₂[0,1] !₂[0,1] k ≤ a at hh'
  rwa [he] at hh'

lemma sharp_le_robustness (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hc : ∃ n k, Admissible c n k) (a : ℝ)
    (ha : ∀ (m k : ℕ) (Q : Fin m → Pt) (o : Pt), OA_R c m k Q o ∨ CA_R c m k Q o →
      ucost Q (cmp Q 0 k) ≤ a * ucost Q o) :
    Real.sqrt (2*c^2+2)/(1-c) ≤ a := by
  obtain ⟨n,k,Q,hQ,he⟩ := (LearnAugFL.CMP.lemma_8 c hc0 hc1 hc).2
  have ht : 0 < Real.sqrt (2*c^2+2)/(1-c) :=
    div_pos (Real.sqrt_pos.mpr (by positivity)) (by linarith)
  have hn : ucost Q !₂[0,1] ≠ 0 := by
    intro h
    simp only [ratio,h,div_zero] at he
    linarith
  have hp : 0 < ucost Q !₂[0,1] := lt_of_le_of_ne (ucost_nonneg _ _) (Ne.symm hn)
  have hh := ha n k Q !₂[0,1] (Or.inl (coa_to_oa_r c Q hQ))
  have hh' := (div_le_iff₀ hp).mpr hh
  change ratio Q 0 !₂[0,1] k ≤ a at hh'
  rwa [he] at hh'

end LearnAugFL.CMP.EqualizeProof

-- Complete inline checked local module: NormalizeRank.lean

namespace LearnAugFL.CMP.EqualizeProof.NormalizeRank

lemma median_above_count (s : Multiset ℝ) :
    2 * (s.filter (fun x => lowerMedian s < x)).card ≤ s.card := by
  classical
  by_cases hn : s.card = 0
  · have : s = 0 := Multiset.card_eq_zero.mp hn
    subst s
    simp
  let l := s.sort (· ≤ ·)
  let m := (s.card + 1) / 2 - 1
  have hlen : l.length = s.card := Multiset.length_sort (· ≤ ·)
  have hm : m < l.length := by dsimp [m]; omega
  have hzero : l[m] = lowerMedian s := by
    change l[m] = l.getD m 0
    exact (List.getD_eq_getElem _ _ hm).symm
  have hsorted : l.SortedLE := (Multiset.pairwise_sort s (· ≤ ·)).sortedLE
  have htake : (l.take (m+1)).filter (fun x => decide (lowerMedian s < x)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    obtain ⟨i, hi, hxi⟩ := List.getElem_of_mem hx
    have hi' : i < l.length := by simp only [List.length_take] at hi; omega
    have him : i ≤ m := by simp only [List.length_take] at hi; omega
    have hle : x ≤ lowerMedian s := by
      have h := hsorted.getElem_le_getElem_of_le (hi := hi') (hj := hm) him
      simp only [List.getElem_take] at hxi
      simpa only [hxi, hzero] using h
    simpa using not_lt_of_ge hle
  have hcount : (l.filter (fun x => decide (lowerMedian s < x))).length ≤ l.length - (m+1) := by
    calc
      _ = ((l.drop (m+1)).filter (fun x => decide (lowerMedian s < x))).length := by
        conv_lhs => rw [← List.take_append_drop (m+1) l, List.filter_append, htake, List.nil_append]
      _ ≤ _ := by
        simpa only [List.length_drop] using List.length_filter_le (fun x : ℝ => decide (lowerMedian s < x)) (l.drop (m+1))
  have hcard : (l.filter (fun x => decide (lowerMedian s < x))).length = (s.filter (fun x => lowerMedian s < x)).card := by
    have heq := congrArg (fun t : Multiset ℝ => (t.filter (fun x => lowerMedian s < x)).card) (Multiset.sort_eq s (· ≤ ·))
    simpa only [Multiset.filter_coe, Multiset.coe_card] using heq
  rw [hcard, hlen] at hcount
  dsimp [m] at hcount
  omega

lemma median_below_count (s : Multiset ℝ) :
    2 * (s.filter (fun x => x < lowerMedian s)).card ≤ s.card := by
  classical
  by_cases hn : s.card = 0
  · have : s = 0 := Multiset.card_eq_zero.mp hn
    subst s
    simp
  let l := s.sort (· ≤ ·)
  let m := (s.card + 1) / 2 - 1
  have hlen : l.length = s.card := Multiset.length_sort (· ≤ ·)
  have hm : m < l.length := by dsimp [m]; omega
  have hzero : l[m] = lowerMedian s := by
    change l[m] = l.getD m 0
    exact (List.getD_eq_getElem _ _ hm).symm
  have hsorted : l.SortedLE := (Multiset.pairwise_sort s (· ≤ ·)).sortedLE
  have hdrop : (l.drop m).filter (fun x => decide (x < lowerMedian s)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    obtain ⟨i, hi, hxi⟩ := List.getElem_of_mem hx
    have hi' : m+i < l.length := by simp only [List.length_drop] at hi; omega
    have hle : lowerMedian s ≤ x := by
      have h := hsorted.getElem_le_getElem_of_le (hi := hm) (hj := hi') (by omega : m ≤ m+i)
      simp only [List.getElem_drop] at hxi
      simpa only [hxi, hzero] using h
    simpa using not_lt_of_ge hle
  have hcount : (l.filter (fun x => decide (x < lowerMedian s))).length ≤ m := by
    calc
      _ = ((l.take m).filter (fun x => decide (x < lowerMedian s))).length := by
        conv_lhs => rw [← List.take_append_drop m l, List.filter_append, hdrop, List.append_nil]
      _ ≤ (l.take m).length := List.length_filter_le _ _
      _ ≤ m := by simp only [List.length_take]; omega
  have hcard : (l.filter (fun x => decide (x < lowerMedian s))).length =
      (s.filter (fun x => x < lowerMedian s)).card := by
    have heq := congrArg (fun t : Multiset ℝ => (t.filter (fun x => x < lowerMedian s)).card)
      (Multiset.sort_eq s (· ≤ ·))
    simpa only [Multiset.filter_coe, Multiset.coe_card] using heq
  rw [hcard] at hcount
  dsimp [m] at hcount
  omega

lemma count_filter {n : ℕ} (P : Fin n → Pt) (p : Pt → Prop) [DecidablePred p] :
    count P p = (Finset.univ.filter (fun i => p (P i))).card := by
  classical
  simp [count, Set.ncard_eq_toFinset_card']

lemma coord_filter_card {n : ℕ} (P : Fin n → Pt) (b : Pt) (k : ℕ) (j : Fin 2)
    (q : ℝ → Prop) [DecidablePred q] :
    ((coordValues P b k j).filter q).card = count P (fun p => q (p j)) + if q (b j) then k else 0 := by
  classical
  unfold coordValues
  rw [Multiset.filter_add, Multiset.card_add, Multiset.filter_map, Multiset.card_map]
  have hm : (Multiset.filter (q ∘ fun i : Fin n => P i j) Finset.univ.val).card =
      count P (fun p => q (p j)) := by
    rw [count_filter]
    rfl
  rw [hm]
  congr 1
  by_cases hb : q (b j)
  · rw [if_pos hb, Multiset.filter_eq_self.mpr]
    · simp
    · intro x hx
      have he := Multiset.mem_replicate.mp hx
      simpa [he.2] using hb
  · rw [if_neg hb, Multiset.filter_eq_nil.mpr]
    · rfl
    · intro x hx
      have he := Multiset.mem_replicate.mp hx
      simpa [he.2] using hb

lemma cmp_coordinate {n k : ℕ} (P : Fin n → Pt) (b : Pt) (j : Fin 2) :
    cmp P b k j = lowerMedian (coordValues P b k j) := by
  fin_cases j <;> simp [cmp]

open Classical in
lemma count_above_cmp {n k : ℕ} (P : Fin n → Pt) (b : Pt) (j : Fin 2) :
    2 * (count P (fun p => cmp P b k j < p j) + if cmp P b k j < b j then k else 0) ≤ n+k := by
  have hh := median_above_count (coordValues P b k j)
  rw [coord_filter_card] at hh
  rw [← cmp_coordinate P b j] at hh
  have hcard : (coordValues P b k j).card = n+k := by simp [coordValues]
  rw [hcard] at hh
  exact hh

open Classical in
lemma count_below_cmp {n k : ℕ} (P : Fin n → Pt) (b : Pt) (j : Fin 2) :
    2 * (count P (fun p => p j < cmp P b k j) + if b j < cmp P b k j then k else 0) ≤ n+k := by
  have hh := median_below_count (coordValues P b k j)
  rw [coord_filter_card] at hh
  rw [← cmp_coordinate P b j] at hh
  have hcard : (coordValues P b k j).card = n+k := by simp [coordValues]
  rw [hcard] at hh
  exact hh

end LearnAugFL.CMP.EqualizeProof.NormalizeRank


-- Complete inline checked local module: Normalize.lean

namespace LearnAugFL.CMP.EqualizeProof
namespace NormalizeAux

noncomputable def directed (m o x : ℝ) : ℝ := if m ≤ o then x-m else m-x

lemma directed_zero (m o : ℝ) : directed m o m = 0 := by
  unfold directed
  split_ifs <;> ring

lemma directed_opt (m o : ℝ) : directed m o o = |o-m| := by
  unfold directed
  split_ifs with h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
  · rw [abs_of_neg (by linarith : o-m < 0)]
    ring

lemma directed_diff_sq (m o x y : ℝ) :
    (directed m o x-directed m o y)^2=(x-y)^2 := by
  unfold directed
  split_ifs <;> ring

noncomputable def center (m o p : Pt) : Pt :=
  !₂[directed (m 0) (o 0) (p 0), directed (m 1) (o 1) (p 1)]

lemma center_apply (m o p : Pt) (j : Fin 2) :
    center m o p j = directed (m j) (o j) (p j) := by
  fin_cases j <;> rfl

lemma center_zero (m o : Pt) : center m o m = 0 := by
  ext j
  rw [center_apply, directed_zero]
  rfl

lemma center_nonneg (m o : Pt) (j : Fin 2) : 0 ≤ center m o o j := by
  rw [center_apply, directed_opt]
  exact abs_nonneg _

lemma center_dist (m o p q : Pt) : dist (center m o p) (center m o q) = dist p q := by
  have hsq : dist (center m o p) (center m o q)^2=dist p q^2 := by
    simp only [dist_eq_norm, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two,
      PiLp.sub_apply, center_apply, directed_diff_sq]
  nlinarith [dist_nonneg (x := center m o p) (y := center m o q), dist_nonneg (x := p) (y := q)]

open Classical in
lemma center_count {n : ℕ} (m o : Pt) (P : Fin n → Pt) (j : Fin 2) :
    count (fun i => center m o (P i)) (fun p => 0 < p j) =
      if m j ≤ o j then count P (fun p => m j < p j) else count P (fun p => p j < m j) := by
  classical
  by_cases h : m j ≤ o j <;> simp [count, center_apply, directed, h, sub_pos]

lemma center_robust_count {n k : ℕ} (P : Fin n → Pt) (b o : Pt) (j : Fin 2) :
    2*count (fun i => center (cmp P b k) o (P i)) (fun p => 0 < p j) ≤ n+k := by
  classical
  rw [center_count]
  have ha := NormalizeRank.count_above_cmp P b j (k := k)
  have hb := NormalizeRank.count_below_cmp P b j (k := k)
  split_ifs <;> omega

lemma center_consistency_count {n k : ℕ} (P : Fin n → Pt) (o : Pt) (j : Fin 2)
    (hj : 0 < center (cmp P o k) o o j) :
    2*count (fun i => center (cmp P o k) o (P i)) (fun p => 0 < p j)+k ≤ n := by
  classical
  rw [center_count]
  rw [center_apply] at hj
  by_cases h : cmp P o k j ≤ o j
  · rw [if_pos h]
    have hh : cmp P o k j < o j := by simpa [directed, h, sub_pos] using hj
    have ha := NormalizeRank.count_above_cmp P o j (k := k)
    rw [if_pos hh] at ha
    omega
  · rw [if_neg h]
    have hh : o j < cmp P o k j := lt_of_not_ge h
    have hb := NormalizeRank.count_below_cmp P o j (k := k)
    rw [if_pos hh] at hb
    omega

noncomputable def swap (p : Pt) : Pt := !₂[p 1,p 0]

lemma swap_zero : swap 0 = 0 := by ext j; fin_cases j <;> simp [swap]

lemma swap_dist (p q : Pt) : dist (swap p) (swap q) = dist p q := by
  have hsq : dist (swap p) (swap q)^2=dist p q^2 := by
    simp [dist_eq_norm, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, swap, add_comm]
  nlinarith [dist_nonneg (x := swap p) (y := swap q), dist_nonneg (x := p) (y := q)]

end NormalizeAux

lemma normalize_profile {n k : ℕ} (P : Fin n → Pt) (b o : Pt) :
    ∃ (Q : Fin n → Pt) (o' : Pt),
      (∀ j : Fin 2, 0 ≤ o' j) ∧ o' 0 ≤ o' 1 ∧
      total Q 0 = total P (cmp P b k) ∧ total Q o' = total P o ∧
      (∀ j : Fin 2, 2*count Q (fun p => 0 < p j) ≤ n+k) ∧
      (b=o → ∀ j : Fin 2, 0 < o' j → 2*count Q (fun p => 0 < p j)+k ≤ n) := by
  classical
  let m := cmp P b k
  let R := fun i => NormalizeAux.center m o (P i)
  let a := NormalizeAux.center m o o
  have ha : ∀ j, 0 ≤ a j := NormalizeAux.center_nonneg m o
  have h0 : total R 0=total P m := by
    unfold total
    apply Finset.sum_congr rfl
    intro i _
    change dist 0 (NormalizeAux.center m o (P i))=dist m (P i)
    rw [← NormalizeAux.center_zero m o]
    exact NormalizeAux.center_dist m o m (P i)
  have ho : total R a=total P o := by
    unfold total
    apply Finset.sum_congr rfl
    intro i _
    exact NormalizeAux.center_dist m o o (P i)
  have hr (j : Fin 2) : 2*count R (fun p => 0 < p j) ≤ n+k :=
    NormalizeAux.center_robust_count P b o j
  have hc (he : b=o) (j : Fin 2) (hj : 0 < a j) :
      2*count R (fun p => 0 < p j)+k ≤ n := by
    subst b
    exact NormalizeAux.center_consistency_count P o j hj
  by_cases horder : a 0 ≤ a 1
  · exact ⟨R,a,ha,horder,h0,ho,hr,hc⟩
  · refine ⟨fun i => NormalizeAux.swap (R i),NormalizeAux.swap a,?_,?_,?_,?_,?_,?_⟩
    · intro j
      fin_cases j
      · simpa [NormalizeAux.swap] using ha 1
      · simpa [NormalizeAux.swap] using ha 0
    · simpa [NormalizeAux.swap] using (le_of_not_ge horder)
    · calc
        _ = total R 0 := by
          unfold total
          apply Finset.sum_congr rfl
          intro i _
          simpa only [NormalizeAux.swap_zero] using NormalizeAux.swap_dist 0 (R i)
        _ = _ := h0
    · calc
        _ = total R a := by
          unfold total
          exact Finset.sum_congr rfl (fun i _ => NormalizeAux.swap_dist a (R i))
        _ = _ := ho
    · intro j
      fin_cases j
      · simpa [count, NormalizeAux.swap] using hr 1
      · simpa [count, NormalizeAux.swap] using hr 0
    · intro he j hj
      fin_cases j
      · exact hc he 1 hj
      · exact hc he 0 hj

end LearnAugFL.CMP.EqualizeProof


-- Complete inline checked local module: RayReduction.lean

namespace LearnAugFL.CMP.EqualizeProof

lemma ray_crossing_bounds (p o : ℝ) (ho : 0 < o) (hp : p ≤ 0) :
    0 ≤ o/(o-p) ∧ o/(o-p) ≤ 1 ∧ (1-o/(o-p))*o+(o/(o-p))*p = 0 := by
  have hd : 0 < o-p := by linarith
  refine ⟨le_of_lt (div_pos ho hd), (div_le_one hd).mpr (by linarith), ?_⟩
  field_simp
  ring

lemma ray_reduction (p o : Pt) (ho : ∀ j, 0 < o j) :
    ∃ q : Pt, (onX q ∨ onY q ∨ q = o) ∧
      dist o p = dist o q + dist q p ∧ (∀ j, 0 < q j → 0 < p j) := by
  classical
  let d : Fin 2 → ℝ := fun j => if 0 < p j then 0 else o j/(o j-p j)
  have hd : ∀ j, 0 ≤ d j ∧ d j ≤ 1 := by
    intro j
    dsimp [d]
    split_ifs with hj
    · norm_num
    · exact ⟨(ray_crossing_bounds (p j) (o j) (ho j) (le_of_not_gt hj)).1,
        (ray_crossing_bounds (p j) (o j) (ho j) (le_of_not_gt hj)).2.1⟩
  let a := max (d 0) (d 1)
  have ha0 : 0 ≤ a := (hd 0).1.trans (le_max_left _ _)
  have ha1 : a ≤ 1 := max_le (hd 0).2 (hd 1).2
  have hda : ∀ j, d j ≤ a := by
    intro j
    fin_cases j
    · exact le_max_left _ _
    · exact le_max_right _ _
  let q : Pt := (1-a) • o + a • p
  have hqval : ∀ j, q j = (1-a)*o j+a*p j := by
    intro j
    simp [q]
  have hqaxis : onX q ∨ onY q ∨ q = o := by
    rcases le_total (d 0) (d 1) with h | h
    · have ha : a = d 1 := max_eq_right h
      by_cases hp : 0 < p 1
      · have ha' : a = 0 := by simp [ha, d, hp]
        exact Or.inr (Or.inr (by simp [q, ha']))
      · apply Or.inl
        change q 1 = 0
        rw [hqval, ha]
        simp only [d, if_neg hp]
        exact (ray_crossing_bounds (p 1) (o 1) (ho 1) (le_of_not_gt hp)).2.2
    · have ha : a = d 0 := max_eq_left h
      by_cases hp : 0 < p 0
      · have ha' : a = 0 := by simp [ha, d, hp]
        exact Or.inr (Or.inr (by simp [q, ha']))
      · apply Or.inr ∘ Or.inl
        change q 0 = 0
        rw [hqval, ha]
        simp only [d, if_neg hp]
        exact (ray_crossing_bounds (p 0) (o 0) (ho 0) (le_of_not_gt hp)).2.2
  refine ⟨q, hqaxis, ?_, ?_⟩
  · have hqseg : q ∈ segment ℝ o p := by
      exact ⟨1-a, a, by linarith, ha0, by ring, rfl⟩
    exact (dist_add_dist_of_mem_segment hqseg).symm
  · intro j hqj
    by_contra hp
    have hp0 : p j ≤ 0 := le_of_not_gt hp
    have hz : (1-d j)*o j+d j*p j = 0 := by
      simpa only [d, if_neg hp] using (ray_crossing_bounds (p j) (o j) (ho j) hp0).2.2
    have hmul : (a-d j)*(p j-o j) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hda j)) (by linarith [ho j])
    rw [hqval] at hqj
    nlinarith


end LearnAugFL.CMP.EqualizeProof

-- Complete inline checked local module: Assembly.lean

namespace LearnAugFL.CMP.EqualizeProof

def NormalizationProperty : Prop := ∀ {n k : ℕ} (P : Fin n → Pt) (b o : Pt),
  ∃ (Q : Fin n → Pt) (o' : Pt), (∀ j, 0 ≤ o' j) ∧ o' 0 ≤ o' 1 ∧
    total Q 0 = total P (cmp P b k) ∧ total Q o' = total P o ∧
    (∀ j, 2*count Q (fun p => 0 < p j) ≤ n+k) ∧
    (b=o → ∀ j, 0 < o' j → 2*count Q (fun p => 0 < p j)+k ≤ n)

lemma transfer_of_reductions (hRay : RayProperty) (hNorm : NormalizationProperty) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    (∀ α : ℝ,
      (∀ (m k' : ℕ) (Q : Fin m → Pt) (oQ : Pt), (OA_C c m k' Q oQ ∨ CA_C c m k' Q oQ) →
        ucost Q (cmp Q oQ k') ≤ α * ucost Q oQ) →
      ∀ (n k : ℕ), Admissible c n k → ∀ (P : Fin n → Pt) (o : Pt), IsOpt P o →
        ucost P (cmp P o k) ≤ α * ucost P o) ∧
    (∀ β : ℝ,
      (∀ (m k' : ℕ) (Q : Fin m → Pt) (oQ : Pt), (OA_R c m k' Q oQ ∨ CA_R c m k' Q oQ) →
        ucost Q (cmp Q 0 k') ≤ β * ucost Q oQ) →
      ∀ (n k : ℕ), Admissible c n k → ∀ (P : Fin n → Pt) (ô o : Pt), IsOpt P o →
        ucost P (cmp P ô k) ≤ β * ucost P o) := by
  constructor
  · intro α hα n k hnk P o hopt
    have ha := sharp_le_consistency c hc0 hc1 ⟨n,k,hnk⟩ α hα
    obtain ⟨Q,o',ho,ho01,he0,heo,_,hcnt⟩ := hNorm P o o
    have hb := normalized_consistency hRay c hc0 hc1 hnk Q o' ho ho01 (hcnt rfl)
    rw [he0,heo] at hb
    exact (total_cost_bound P (cmp P o k) o _ hb).trans
      (mul_le_mul_of_nonneg_right ha (ucost_nonneg P o))
  · intro β hβ n k hnk P b o hopt
    have ha := sharp_le_robustness c hc0 hc1 ⟨n,k,hnk⟩ β hβ
    obtain ⟨Q,o',ho,ho01,he0,heo,hcnt,_⟩ := hNorm P b o
    have hb := normalized_robustness hRay c hc0 hc1 hnk Q o' ho ho01 hcnt
    rw [he0,heo] at hb
    exact (total_cost_bound P (cmp P b k) o _ hb).trans
      (mul_le_mul_of_nonneg_right ha (ucost_nonneg P o))

end LearnAugFL.CMP.EqualizeProof

-- Complete inline checked local module: Main.lean

open LearnAugFL.CMP LearnAugFL.CMP.EqualizeProof

theorem solution (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    (∀ α : ℝ,
      (∀ (m k' : ℕ) (Q : Fin m → Pt) (oQ : Pt), (OA_C c m k' Q oQ ∨ CA_C c m k' Q oQ) →
        ucost Q (cmp Q oQ k') ≤ α * ucost Q oQ) →
      ∀ (n k : ℕ), Admissible c n k → ∀ (P : Fin n → Pt) (o : Pt), IsOpt P o →
        ucost P (cmp P o k) ≤ α * ucost P o) ∧
    (∀ β : ℝ,
      (∀ (m k' : ℕ) (Q : Fin m → Pt) (oQ : Pt), (OA_R c m k' Q oQ ∨ CA_R c m k' Q oQ) →
        ucost Q (cmp Q 0 k') ≤ β * ucost Q oQ) →
      ∀ (n k : ℕ), Admissible c n k → ∀ (P : Fin n → Pt) (ô o : Pt), IsOpt P o →
        ucost P (cmp P ô k) ≤ β * ucost P o) := by
  exact transfer_of_reductions ray_reduction (@normalize_profile) c hc0 hc1
