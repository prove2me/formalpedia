-- Prove2me | solution 1 for HighResODE.NAGC.eq_4_7
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:23:36.381849+00:00
-- url     : https://prove2.me/submissions/b5c0730b-dfdb-49ef-8a13-5db70fe05e80

import Mathlib
set_option autoImplicit false

theorem solution (L s : ℝ) (hL : 0 < L) (hs : 0 < s) (hsL : s ≤ 1 / (3 * L)) (k : ℕ) (hk : 2 ≤ k) :
    0 ≤ ((k : ℝ) + 3) * ((k : ℝ) - 1) - L * s * ((k : ℝ) + 3) * ((k : ℝ) + 1) ∧
    s ≤ 1 / L * (((k : ℝ) - 1) / ((k : ℝ) + 1)) := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hLs : L * s ≤ 1 / 3 := by
    have := mul_le_mul_of_nonneg_left hsL hL.le
    have e : L * (1 / (3 * L)) = 1 / 3 := by field_simp
    linarith
  have hLs0 : 0 < L * s := mul_pos hL hs
  constructor
  · have h1 : L * s * ((k : ℝ) + 1) ≤ 1 / 3 * ((k : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right hLs (by linarith)
    have h2 : 0 ≤ ((k : ℝ) + 3) * (((k : ℝ) - 1) - 1 / 3 * ((k : ℝ) + 1)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ (k : ℝ) + 3 by linarith)]
  · have h : s * L ≤ ((k : ℝ) - 1) / ((k : ℝ) + 1) := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith
    calc s = (s * L) / L := by field_simp
      _ ≤ (((k : ℝ) - 1) / ((k : ℝ) + 1)) / L := by gcongr
      _ = 1 / L * (((k : ℝ) - 1) / ((k : ℝ) + 1)) := by ring
