-- Prove2me | solution 2 for LodhaMoore.eqOn_two_mul_and_eqOn_neg_inv
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T11:45:29.580295+00:00
-- url     : https://prove2.me/submissions/177df009-4f1f-45c6-9488-ab87e95bda35

import Mathlib
import Definitions.Def_LodhaMoore

set_option autoImplicit false

namespace LodhaMooreAuxc339d893
open LodhaMoore

lemma exists_ext (f : ℝ → ℝ) (hs : Function.Surjective f) (hm : StrictMono f) :
    ∃ e : OnePoint ℝ ≃ₜ OnePoint ℝ, ∀ t : ℝ, e t = ((f t : ℝ) : OnePoint ℝ) :=
  ⟨(StrictMono.orderIsoOfSurjective f hm hs).toHomeomorph.onePointCongr, fun _ => rfl⟩

lemma ofReal_apply (f : ℝ → ℝ) (hs : Function.Surjective f) (hm : StrictMono f) (t : ℝ) :
    ofReal f (t : OnePoint ℝ) = ((f t : ℝ) : OnePoint ℝ) := by
  have h := exists_ext f hs hm
  unfold ofReal
  rw [dif_pos h]
  exact h.choose_spec t

lemma aFun_surj : Function.Surjective aFun := fun r => ⟨r - 1, by simp [aFun]⟩

lemma aFun_mono : StrictMono aFun := by
  intro x y hxy; simp only [aFun]; linarith

lemma L2 (t : ℝ) (h0 : 0 < t) (h1 : t ≤ 1 / 2) : 0 < t / (1 - t) ∧ t / (1 - t) ≤ 1 := by
  constructor
  · apply div_pos h0; linarith
  · rw [div_le_one (by linarith)]; linarith

lemma L3 (t : ℝ) (h0 : 1 / 2 < t) (h1 : t ≤ 1) : 1 < 3 - 1 / t ∧ 3 - 1 / t ≤ 2 := by
  have ht : 0 < t := by linarith
  constructor
  · have : 1 / t < 2 := by rw [div_lt_iff₀ ht]; linarith
    linarith
  · have : 1 ≤ 1 / t := by rw [le_div_iff₀ ht]; linarith
    linarith

lemma M2 (x y : ℝ) (h0 : 0 < x) (hxy : x < y) (h1 : y ≤ 1 / 2) :
    x / (1 - x) < y / (1 - y) := by
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]; nlinarith

lemma M3 (x y : ℝ) (h0 : 1 / 2 < x) (hxy : x < y) :
    3 - 1 / x < 3 - 1 / y := by
  have : 1 / y < 1 / x := one_div_lt_one_div_of_lt (by linarith) hxy
  linarith

lemma bFun_mono : StrictMono bFun := by
  intro x y hxy
  unfold bFun
  split_ifs <;> (try push Not at *) <;>
  first
  | linarith
  | exact M2 x y (by linarith) hxy (by linarith)
  | exact M3 x y (by linarith) hxy
  | (have := L2 y (by linarith) (by linarith); linarith)
  | (have := L3 y (by linarith) (by linarith); linarith)
  | (have := L2 x (by linarith) (by linarith); have := L3 y (by linarith) (by linarith); linarith)
  | (have := L2 x (by linarith) (by linarith); linarith)
  | (have := L3 x (by linarith) (by linarith); linarith)

lemma bFun_surj : Function.Surjective bFun := by
  intro r
  rcases le_or_gt r 0 with h0 | h0
  · exact ⟨r, by simp [bFun, h0]⟩
  rcases le_or_gt r 1 with h1 | h1
  · refine ⟨r / (1 + r), ?_⟩
    have hp : 0 < r / (1 + r) := div_pos h0 (by linarith)
    have hq : r / (1 + r) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    unfold bFun
    rw [if_neg (by linarith), if_pos hq]
    have : (1 : ℝ) + r ≠ 0 := by linarith
    field_simp
    ring
  rcases le_or_gt r 2 with h2 | h2
  · refine ⟨1 / (3 - r), ?_⟩
    have hp : 1 / 2 < 1 / (3 - r) := by
      apply one_div_lt_one_div_of_lt (by linarith); linarith
    have hq : 1 / (3 - r) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    unfold bFun
    rw [if_neg (by linarith), if_neg (by linarith), if_pos hq]
    have : (3 : ℝ) - r ≠ 0 := by linarith
    field_simp
    ring
  · refine ⟨r - 1, ?_⟩
    unfold bFun
    rw [if_neg (by linarith), if_neg (by linarith), if_neg (by linarith)]
    ring

lemma C1 (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : 0 ≤ 2 * t / (1 + t) ∧ 2 * t / (1 + t) ≤ 1 := by
  constructor
  · positivity
  · rw [div_le_one (by linarith)]; linarith

lemma cFun_mono : StrictMono cFun := by
  intro x y hxy
  unfold cFun
  split_ifs with hx hy hy
  · rw [div_lt_div_iff₀ (by linarith) (by linarith)]; nlinarith
  · have := C1 x hx.1 hx.2
    have : 1 < y := by
      by_contra hc; push Not at hc; exact hy ⟨by linarith, hc⟩
    linarith
  · have := C1 y hy.1 hy.2
    have : x < 0 := by
      by_contra hc; push Not at hc; exact hx ⟨hc, by linarith⟩
    linarith
  · exact hxy

lemma cFun_surj : Function.Surjective cFun := by
  intro r
  by_cases hr : 0 ≤ r ∧ r ≤ 1
  · refine ⟨r / (2 - r), ?_⟩
    have hp : 0 ≤ r / (2 - r) := div_nonneg hr.1 (by linarith)
    have hq : r / (2 - r) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    unfold cFun
    rw [if_pos ⟨hp, hq⟩]
    have : (2 : ℝ) - r ≠ 0 := by linarith
    field_simp
    ring
  · exact ⟨r, by simp only [cFun]; rw [if_neg hr]⟩

lemma a_apply (t : ℝ) : a (t : OnePoint ℝ) = ((t + 1 : ℝ) : OnePoint ℝ) :=
  ofReal_apply aFun aFun_surj aFun_mono t

lemma b_apply (t : ℝ) : b (t : OnePoint ℝ) = ((bFun t : ℝ) : OnePoint ℝ) :=
  ofReal_apply bFun bFun_surj bFun_mono t

lemma c_apply (t : ℝ) : c (t : OnePoint ℝ) = ((cFun t : ℝ) : OnePoint ℝ) :=
  ofReal_apply cFun cFun_surj cFun_mono t

lemma inv_apply_of (e : OnePoint ℝ ≃ₜ OnePoint ℝ) (x y : OnePoint ℝ) (h : e x = y) :
    e⁻¹ y = x := by
  rw [Homeomorph.inv_apply, Homeomorph.symm_apply_eq, h]

lemma a_inv_apply (t : ℝ) : a⁻¹ (t : OnePoint ℝ) = ((t - 1 : ℝ) : OnePoint ℝ) := by
  apply inv_apply_of
  rw [a_apply]; congr 1; ring

end LodhaMooreAuxc339d893

open LodhaMoore in
theorem solution :
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      MulOpposite.unop (MulOpposite.op b * MulOpposite.op c * (MulOpposite.op a)⁻¹ * (MulOpposite.op c)⁻¹ * MulOpposite.op a) (t : OnePoint ℝ) = ((2 * t : ℝ) : OnePoint ℝ)) ∧
    (∀ t ∈ Set.Icc (-1 : ℝ) (-1 / 2),
      MulOpposite.unop (MulOpposite.op a * MulOpposite.op b * MulOpposite.op a) (t : OnePoint ℝ) = ((-1 / t : ℝ) : OnePoint ℝ)) ∧
    (∀ t ∈ Set.Icc (1 / 2 : ℝ) 1,
      MulOpposite.unop (MulOpposite.op b * (MulOpposite.op a)⁻¹ ^ (3 : ℕ) : (OnePoint ℝ ≃ₜ OnePoint ℝ)ᵐᵒᵖ) (t : OnePoint ℝ) = ((-1 / t : ℝ) : OnePoint ℝ)) := by
  open LodhaMooreAuxc339d893 in
  refine ⟨?_, ?_, ?_⟩
  · rintro t ⟨h0, h1⟩
    simp only [MulOpposite.unop_mul, MulOpposite.unop_inv, MulOpposite.unop_op,
      Homeomorph.mul_apply]
    rcases le_or_gt t (1 / 2) with hh | hh
    · have hb : bFun t = t / (1 - t) := by
        unfold bFun
        split_ifs with h
        · have : t = 0 := le_antisymm h h0
          subst this; simp
        · rfl
      have hc : cFun (t / (1 - t)) = 2 * t := by
        rcases eq_or_lt_of_le h0 with h | h
        · subst h; simp [cFun]
        have := L2 t h hh
        unfold cFun
        rw [if_pos ⟨this.1.le, this.2⟩]
        have : (1 : ℝ) - t ≠ 0 := by linarith
        field_simp
        ring
      have hc2 : cFun (2 * t - 1) = 2 * t - 1 := by
        unfold cFun
        split_ifs with h
        · have : t = 1 / 2 := by linarith [h.1]
          subst this; norm_num
        · rfl
      rw [b_apply, hb, c_apply, hc, a_inv_apply,
        inv_apply_of c _ _ (by rw [c_apply, hc2]), a_apply]
      congr 1; ring
    · have hb : bFun t = 3 - 1 / t := by
        unfold bFun
        rw [if_neg (by linarith), if_neg (by linarith), if_pos h1]
      have hc : cFun (3 - 1 / t) = 3 - 1 / t := by
        have := L3 t hh h1
        unfold cFun
        rw [if_neg (by intro h; linarith [h.2])]
      have hc2 : cFun (2 * t - 1) = 3 - 1 / t - 1 := by
        have ht : 0 < t := by linarith
        unfold cFun
        rw [if_pos ⟨by linarith, by linarith⟩]
        have : (1 : ℝ) + (2 * t - 1) ≠ 0 := by linarith
        field_simp
        ring
      rw [b_apply, hb, c_apply, hc, a_inv_apply,
        inv_apply_of c _ _ (by rw [c_apply, hc2]), a_apply]
      congr 1; ring
  · rintro t ⟨h0, h1⟩
    simp only [MulOpposite.unop_mul, MulOpposite.unop_op, Homeomorph.mul_apply]
    have hb : bFun (t + 1) = (t + 1) / (1 - (t + 1)) := by
      unfold bFun
      split_ifs with h
      · have : t = -1 := by linarith
        subst this; norm_num
      · rfl
      · exfalso; linarith
      · exfalso; linarith
    rw [a_apply, b_apply, hb, a_apply]
    have : t ≠ 0 := by intro h; linarith
    congr 1
    rw [show (1:ℝ) - (t + 1) = -t by ring, div_add_one (neg_ne_zero.mpr this),
      show t + 1 + -t = 1 by ring, div_neg, neg_div]
  · rintro t ⟨h0, h1⟩
    simp only [MulOpposite.unop_mul, MulOpposite.unop_inv,
      MulOpposite.unop_op, pow_succ, pow_zero, one_mul, Homeomorph.mul_apply]
    have hb : bFun t = 3 - 1 / t := by
      unfold bFun
      split_ifs with h h'
      · exfalso; linarith
      · have : t = 1 / 2 := by linarith
        subst this; norm_num
      · rfl
    rw [b_apply, hb, a_inv_apply, a_inv_apply, a_inv_apply]
    congr 1; ring
