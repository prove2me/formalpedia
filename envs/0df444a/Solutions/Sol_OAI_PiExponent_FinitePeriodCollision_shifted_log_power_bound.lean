-- Prove2me | solution 1 for OAI.PiExponent.FinitePeriodCollision.shifted_log_power_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T03:22:11.45198+00:00
-- url     : https://prove2.me/submissions/293e315e-824c-469f-aba2-558010444ce7

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

open OAI.PiExponent.FinitePeriodCollision

theorem solution
    (center : ℂ) (R : ℝ) (hR : 0 < R)
    (hc : ‖center‖ + 3 / 4 ≤ R / 2) (ell d : ℕ) :
    ‖rowTest ell
      (fun t => ((center + Complex.log (1 + t)) / (R : ℂ)) ^ d)‖ ≤
      (2 : ℝ) ^ ell * (1 / 2 : ℝ) ^ d := by
  unfold rowTest
  rw [cauchyPowerSeries_apply]
  have hbd : ∀ z ∈ Metric.sphere (0 : ℂ) (1 / 2),
      ‖(1 / (z - 0)) ^ ell • (z - 0)⁻¹ •
        ((center + Complex.log (1 + z)) / (R : ℂ)) ^ d‖ ≤ 2 ^ ell * 2 * (1 / 2) ^ d := by
    intro z hz
    rw [mem_sphere_zero_iff_norm] at hz
    have hlog : ‖Complex.log (1 + z)‖ ≤ 3 / 4 := by
      have := Complex.norm_log_one_add_half_le_self (z := z) (by rw [hz])
      rw [hz] at this; linarith
    have hnum : ‖(center + Complex.log (1 + z)) / (R : ℂ)‖ ≤ 1 / 2 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR,
        div_le_iff₀ hR]
      calc ‖center + Complex.log (1 + z)‖ ≤ ‖center‖ + ‖Complex.log (1 + z)‖ := norm_add_le _ _
        _ ≤ 1 / 2 * R := by linarith
    simp only [sub_zero, smul_eq_mul, norm_mul, norm_pow, norm_div, norm_one, norm_inv, hz]
    have h1 : ‖(center + Complex.log (1 + z)) / (R : ℂ)‖ ^ d ≤ (1 / 2) ^ d :=
      pow_le_pow_left₀ (norm_nonneg _) hnum d
    rw [norm_div] at h1
    norm_num at h1 ⊢
    nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) ell, pow_nonneg (norm_nonneg center) 0]
  have hI := circleIntegral.norm_integral_le_of_norm_le_const (by norm_num) hbd
  rw [norm_smul]
  have h2 : ‖(2 * ↑Real.pi * Complex.I)⁻¹‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    norm_num
  rw [h2]
  calc (2 * Real.pi)⁻¹ * _ ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * (1 / 2) * (2 ^ ell * 2 * (1 / 2) ^ d)) :=
        mul_le_mul_of_nonneg_left hI (by positivity)
    _ = _ := by field_simp
