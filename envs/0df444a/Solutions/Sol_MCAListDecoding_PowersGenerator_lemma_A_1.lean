-- Prove2me | solution 1 for MCAListDecoding.PowersGenerator.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-16T16:02:26.998283+00:00
-- url     : https://prove2.me/submissions/4d9a1bab-873b-4027-acc2-592f6eabab5a

import Mathlib

#check pow_lt_pow_left₀
#check Real.rpow_nonneg
#check div_lt_iff₀

theorem solution (δ γ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hγ : 0 ≤ γ)
    (h3 : max ((1 - δ) ^ ((1 : ℝ) / 3)) ((1 + (1 - δ)) / 2) < 1 - γ) :
    ((1 - γ + Real.sqrt (1 - δ)) / 2 - (1 - δ)) /
        (((1 - γ + Real.sqrt (1 - δ)) / 2) ^ 2 - (1 - δ)) < 5 ∧
      ∀ L : ℕ, (L : ℝ) ≤ ((1 - γ + Real.sqrt (1 - δ)) / 2 - (1 - δ)) /
          (((1 - γ + Real.sqrt (1 - δ)) / 2) ^ 2 - (1 - δ)) → L ≤ 4 := by
  have hspos : 0 ≤ 1 - δ := by linarith
  have hslt : 1 - δ < 1 := by linarith
  set s := 1 - δ with hs
  set u := Real.sqrt s with hu
  set r := 1 - γ with hr
  have hu2 : u ^ 2 = s := Real.sq_sqrt hspos
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu1 : u < 1 := by nlinarith [hu2, hu0, hslt]
  have h3' : max (s ^ ((1 : ℝ) / 3)) ((1 + s) / 2) < r := h3
  have hr1 : (1 + s) / 2 < r := lt_of_le_of_lt (le_max_right _ _) h3'
  have hr2 : s ^ ((1 : ℝ) / 3) < r := lt_of_le_of_lt (le_max_left _ _) h3'
  have hr0 : 0 ≤ r := by nlinarith [hr1, hspos]
  have hcube : (s ^ ((1 : ℝ) / 3)) ^ 3 = s := by
    rw [← Real.rpow_natCast (s ^ ((1 : ℝ) / 3)) 3]
    rw [← Real.rpow_mul hspos]
    norm_num
  have hr3 : u ^ 2 < r ^ 3 := by
    rw [hu2, ← hcube]
    exact pow_lt_pow_left₀ hr2 (Real.rpow_nonneg hspos _) (by norm_num : (3 : ℕ) ≠ 0)
  have h1 : 1 + u ^ 2 < 2 * r := by
    rw [hu2]; linarith
  have hnum : 2 * (r + u - 2 * u ^ 2) < 5 * (r - u) * (r + 3 * u) := by
    nlinarith [h1, hr3, sq_nonneg (r - u), sq_nonneg (r + u), sq_nonneg u,
      sq_nonneg (r - 1), mul_nonneg hu0 (le_of_lt (sub_pos.mpr hu1))]
  have hru : 0 < r - u := by
    nlinarith [h1, sq_nonneg (1 - u)]
  have hden : 0 < ((r + u) / 2) ^ 2 - s := by
    have hEq : ((r + u) / 2) ^ 2 - s = ((r - u) * (r + 3 * u)) / 4 := by
      rw [← hu2]; ring
    rw [hEq]
    have : 0 < r + 3 * u := by nlinarith
    positivity
  have hratio : ((r + u) / 2 - s) / (((r + u) / 2) ^ 2 - s) < 5 := by
    rw [div_lt_iff₀ hden, ← hu2]
    nlinarith [hnum]
  constructor
  · exact hratio
  · intro L hL
    have hL5 : (L : ℝ) < 5 := lt_of_le_of_lt hL hratio
    have hL5' : L < 5 := by exact_mod_cast hL5
    omega
