-- Prove2me | solution 1 for Kyprianou.Ch01.geometricFourierTsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T07:31:48.29278+00:00
-- url     : https://prove2.me/submissions/59d935fe-fc7e-4427-9f54-74f63abf4e0c

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Complex
set_option autoImplicit false

/-! Absolute geometric Fourier summation inside the closed unit disc. -/
theorem solution
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    (∑' n : ℕ,
      (p : ℂ) * ((((1 - p : ℝ) : ℂ) * z) ^ n)) =
      (p : ℂ) / (1 - (((1 - p : ℝ) : ℂ) * z)) := by
  have hq0 : 0 ≤ 1 - p := le_of_lt (sub_pos.mpr hp1)
  have hq1 : ‖(((1 - p : ℝ) : ℂ))‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq0]
    exact sub_lt_self 1 hp0
  have hqz : ‖(((1 - p : ℝ) : ℂ) * z)‖ < 1 := by
    calc
      ‖(((1 - p : ℝ) : ℂ) * z)‖ =
          ‖(((1 - p : ℝ) : ℂ))‖ * ‖z‖ := norm_mul _ _
      _ ≤ ‖(((1 - p : ℝ) : ℂ))‖ * 1 :=
        mul_le_mul_of_nonneg_left hz (norm_nonneg _)
      _ < 1 := by simpa using hq1
  calc
    (∑' n : ℕ, (p : ℂ) * ((((1 - p : ℝ) : ℂ) * z) ^ n)) =
      (p : ℂ) * (∑' n : ℕ, ((((1 - p : ℝ) : ℂ) * z) ^ n)) := by
        rw [tsum_mul_left]
    _ = (p : ℂ) * (1 - (((1 - p : ℝ) : ℂ) * z))⁻¹ := by
      rw [tsum_geometric_of_norm_lt_one hqz]
    _ = (p : ℂ) / (1 - (((1 - p : ℝ) : ℂ) * z)) := by
      rw [div_eq_mul_inv]
