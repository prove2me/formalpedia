-- Prove2me | solution 1 for L0BnB.Relax.omega_value_M_infty
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:29:48.623854+00:00
-- url     : https://prove2.me/submissions/3557eed9-8403-49d1-9654-d300ac0ce868

import Mathlib
import Definitions.Def_L0BnB_Relax_psi1

open L0BnB.Relax in
theorem solution (lam0 lam2 : ℝ) (h0 : 0 < lam0) (h2 : 0 < lam2) (b : ℝ) :
    IsLeast {v | ∃ z s : ℝ, 0 ≤ z ∧ z ≤ 1 ∧ 0 ≤ s ∧ b ^ 2 ≤ s * z ∧ lam0 * z + lam2 * s = v}
      (psi1 lam0 lam2 b) := by
  have hc : 0 < Real.sqrt (lam2 / lam0) := Real.sqrt_pos.mpr (div_pos h2 h0)
  have hc2 : Real.sqrt (lam2 / lam0) ^ 2 = lam2 / lam0 := Real.sq_sqrt (div_pos h2 h0).le
  have hlam2 : lam2 = lam0 * Real.sqrt (lam2 / lam0) ^ 2 := by
    rw [hc2]
    field_simp
  unfold psi1 reverseHuber
  obtain ⟨c, hcdef⟩ : ∃ c, c = Real.sqrt (lam2 / lam0) := ⟨_, rfl⟩
  rw [← hcdef] at hc hlam2 ⊢
  split_ifs with ht
  · rw [abs_mul, abs_of_pos hc] at ht ⊢
    constructor
    · refine ⟨|b| * c, |b| / c, by positivity, ht, by positivity, ?_, ?_⟩
      · have e : |b| / c * (|b| * c) = |b| ^ 2 := by
          field_simp
        rw [e, sq_abs]
      · rw [hlam2]
        field_simp <;> ring
    · rintro v ⟨z, s, hz0, hz1, hs0, hbs, rfl⟩
      rw [hlam2]
      have hb2 : |b| ^ 2 ≤ s * z := by rw [sq_abs]; exact hbs
      have hX : 0 ≤ z + c ^ 2 * s := by positivity
      have hsq : (2 * |b| * c) ^ 2 ≤ (z + c ^ 2 * s) ^ 2 := by
        nlinarith [sq_nonneg (z - c ^ 2 * s), sq_nonneg c]
      have hle : 2 * |b| * c ≤ z + c ^ 2 * s := by
        nlinarith [abs_nonneg b]
      nlinarith [mul_le_mul_of_nonneg_left hle h0.le]
  · rw [abs_mul, abs_of_pos hc] at ht
    push_neg at ht
    have hbc : 1 < b ^ 2 * c ^ 2 := by
      have : 1 < (|b| * c) ^ 2 := by nlinarith
      rwa [mul_pow, sq_abs] at this
    constructor
    · refine ⟨1, b ^ 2, zero_le_one, le_rfl, sq_nonneg b, by rw [mul_one], ?_⟩
      rw [hlam2]
      ring
    · rintro v ⟨z, s, hz0, hz1, hs0, hbs, rfl⟩
      rw [hlam2]
      have hzpos : 0 < z := by
        rcases eq_or_lt_of_le hz0 with h | h
        · rw [← h, mul_zero] at hbs
          nlinarith [sq_nonneg b, sq_nonneg c]
        · exact h
      have key : z * (b ^ 2 * c ^ 2 + 1) ≤ z * (z + c ^ 2 * s) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hz1) (by linarith : 0 ≤ b ^ 2 * c ^ 2 - z),
          mul_nonneg (sq_nonneg c) (sub_nonneg.mpr hbs)]
      have key2 : b ^ 2 * c ^ 2 + 1 ≤ z + c ^ 2 * s := le_of_mul_le_mul_left key hzpos
      have := mul_le_mul_of_nonneg_left key2 h0.le
      nlinarith [this]
