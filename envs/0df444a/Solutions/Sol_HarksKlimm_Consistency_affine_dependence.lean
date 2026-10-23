-- Prove2me | solution 1 for HarksKlimm.Consistency.affine_dependence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T09:06:56.797554+00:00
-- url     : https://prove2.me/submissions/0a55dc57-a534-4867-bfa7-7c6511729eb0

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_IsMonotonic

open scoped NNReal
open HarksKlimm.Consistency

/-- increments of a monotone-or-antitone function have a common weak sign -/
theorem g79j_sign (f : ℝ≥0 → ℝ) (hf : IsMonotonic f) {x y x' y' : ℝ≥0} (h : x ≤ y) (h' : x' ≤ y') :
    0 ≤ (f y - f x) * (f y' - f x') := by
  rcases hf with hm | hm
  · exact mul_nonneg (sub_nonneg.mpr (hm h)) (sub_nonneg.mpr (hm h'))
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hm h)) (sub_nonpos.mpr (hm h'))

theorem solution (c₁ c₂ : ℝ≥0 → ℝ)
    (hc₁ : Continuous c₁) (hc₂ : Continuous c₂)
    (hm₁ : IsMonotonic c₁) (hm₂ : IsMonotonic c₂)
    (hn₁ : ∃ x y, c₁ x ≠ c₁ y) (hn₂ : ∃ x y, c₂ x ≠ c₂ y) :
    (∀ a₁ a₂ : ℤ, IsMonotonic (fun x => (a₁ : ℝ) * c₁ x + (a₂ : ℝ) * c₂ x)) ↔
      ∃ a b : ℝ, ∀ x : ℝ≥0, c₂ x = a * c₁ x + b := by
  constructor
  · intro H
    -- a pair with nonzero c₁-increment
    obtain ⟨x0, y0, hxy0, hD0⟩ : ∃ x0 y0 : ℝ≥0, x0 < y0 ∧ c₁ y0 - c₁ x0 ≠ 0 := by
      obtain ⟨x, y, hne⟩ := hn₁
      rcases lt_trichotomy x y with h | h | h
      · exact ⟨x, y, h, sub_ne_zero.mpr hne.symm⟩
      · exact absurd (h ▸ rfl) hne
      · exact ⟨y, x, h, sub_ne_zero.mpr hne⟩
    set D1 := c₁ y0 - c₁ x0 with hD1
    set k := (c₂ y0 - c₂ x0) / D1 with hk
    have key : ∀ x y : ℝ≥0, x < y → c₂ y - c₂ x = k * (c₁ y - c₁ x) := by
      intro x y hxy
      by_contra hne
      set E1 := c₁ y - c₁ x
      set D := c₂ y - c₂ x - k * E1 with hD
      have hDne : D ≠ 0 := sub_ne_zero.mpr hne
      have hsame : 0 ≤ D1 * E1 := g79j_sign c₁ hm₁ hxy0.le hxy.le
      set ε := |D| / (|E1| + 1) with hε
      have hεpos : 0 < ε := div_pos (abs_pos.mpr hDne) (by positivity)
      -- choose a rational r = k - t with t of the right sign and small
      obtain ⟨r, hr1, hr2⟩ : ∃ r : ℚ, 0 < (k - r) * D1 * D * (-1) ∧ |k - r| < ε := by
        by_cases hs : 0 < D1 * D
        · obtain ⟨r, h1, h2⟩ := exists_rat_btwn (show k < k + ε by linarith)
          refine ⟨r, ?_, ?_⟩
          · have : k - r < 0 := by linarith
            have e : (k - (r:ℝ)) * D1 * D * (-1) = -(k - r) * (D1 * D) := by ring
            rw [e]; exact mul_pos (by linarith) hs
          · rw [abs_lt]; constructor <;> linarith
        · have hneg : D1 * D < 0 := lt_of_le_of_ne (not_lt.mp hs) (mul_ne_zero hD0 hDne)
          obtain ⟨r, h1, h2⟩ := exists_rat_btwn (show k - ε < k by linarith)
          refine ⟨r, ?_, ?_⟩
          · have : 0 < k - r := by linarith
            have e : (k - (r:ℝ)) * D1 * D * (-1) = (k - r) * (-(D1 * D)) := by ring
            rw [e]; exact mul_pos this (by linarith)
          · rw [abs_lt]; constructor <;> linarith
      set t := k - (r : ℝ) with ht
      have hq : (0 : ℝ) < r.den := by exact_mod_cast r.pos
      have hrq : (r.num : ℝ) = r * r.den := by
        rw [Rat.cast_def]; field_simp
      have hmono := H (-r.num) (r.den : ℤ)
      have hs2 := g79j_sign _ hmono hxy0.le hxy.le
      simp only [Int.cast_neg, Int.cast_natCast] at hs2
      -- increments of the combination
      have e0 : (-(r.num : ℝ) * c₁ y0 + (r.den : ℝ) * c₂ y0) - (-(r.num : ℝ) * c₁ x0 + (r.den : ℝ) * c₂ x0)
          = r.den * (D1 * t) := by
        rw [hrq, ht, hk]; field_simp; ring
      have e1 : (-(r.num : ℝ) * c₁ y + (r.den : ℝ) * c₂ y) - (-(r.num : ℝ) * c₁ x + (r.den : ℝ) * c₂ x)
          = r.den * (D + t * E1) := by
        rw [hrq, ht, hD]; ring
      rw [e0, e1] at hs2
      -- sign analysis
      have hE1 : ε * |E1| < |D| := by
        have hDp : 0 < |D| := abs_pos.mpr hDne
        have hf : |E1| / (|E1| + 1) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
        have e : ε * |E1| = |D| * (|E1| / (|E1| + 1)) := by rw [hε]; ring
        rw [e]; exact mul_lt_of_lt_one_right hDp hf
      have habs : |t * E1| < |D| := by
        rw [abs_mul]
        exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hr2.le (abs_nonneg _)) hE1
      have hsignD : 0 < (D + t * E1) * D := by
        rcases lt_or_gt_of_ne hDne with h | h
        · rw [abs_of_neg h] at habs
          have := le_abs_self (t * E1)
          exact mul_pos_of_neg_of_neg (by linarith) h
        · rw [abs_of_pos h] at habs
          have := neg_abs_le (t * E1)
          exact mul_pos (by linarith) h
      have hAD : (D1 * t) * D < 0 := by
        have e : (D1 * t) * D = -((k - r) * D1 * D * (-1)) := by rw [ht]; ring
        rw [e]; linarith
      have hprod : (D1 * t) * (D + t * E1) < 0 := by
        by_contra hc; push Not at hc
        have h1 : 0 ≤ ((D1 * t) * (D + t * E1)) * (D * D) := mul_nonneg hc (mul_self_nonneg D)
        have h2 : ((D1 * t) * D) * ((D + t * E1) * D) < 0 := mul_neg_of_neg_of_pos hAD hsignD
        have e : ((D1 * t) * (D + t * E1)) * (D * D) = ((D1 * t) * D) * ((D + t * E1) * D) := by ring
        linarith
      have e2 : ((r.den : ℝ) * (D1 * t)) * ((r.den : ℝ) * (D + t * E1)) =
          (r.den : ℝ) ^ 2 * ((D1 * t) * (D + t * E1)) := by ring
      rw [e2] at hs2
      have : (r.den : ℝ) ^ 2 * ((D1 * t) * (D + t * E1)) < 0 := mul_neg_of_pos_of_neg (by positivity) hprod
      linarith
    refine ⟨k, c₂ 0 - k * c₁ 0, fun x => ?_⟩
    rcases eq_or_ne x 0 with h | h
    · rw [h]; ring
    · have := key 0 x (pos_iff_ne_zero.mpr h); linarith
  · rintro ⟨a, b, hab⟩ a₁ a₂
    have hf : (fun x => (a₁ : ℝ) * c₁ x + (a₂ : ℝ) * c₂ x) =
        fun x => ((a₁ : ℝ) + a₂ * a) * c₁ x + a₂ * b := by
      funext x; rw [hab]; ring
    rw [hf]
    set m : ℝ := (a₁ : ℝ) + a₂ * a
    rcases le_total 0 m with hm | hm <;> rcases hm₁ with h1 | h1
    · left; intro x y hxy; have := mul_le_mul_of_nonneg_left (h1 hxy) hm; simp only; linarith
    · right; intro x y hxy; have := mul_le_mul_of_nonneg_left (h1 hxy) hm; simp only; linarith
    · right; intro x y hxy; have := mul_le_mul_of_nonpos_left (h1 hxy) hm; simp only; linarith
    · left; intro x y hxy; have := mul_le_mul_of_nonpos_left (h1 hxy) hm; simp only; linarith
