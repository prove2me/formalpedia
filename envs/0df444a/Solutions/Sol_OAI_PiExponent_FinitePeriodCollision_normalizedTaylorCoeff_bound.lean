-- Prove2me | solution 1 for OAI.PiExponent.FinitePeriodCollision.normalizedTaylorCoeff_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:54:22.337281+00:00
-- url     : https://prove2.me/submissions/bb8b8b13-042a-46b0-994c-fb806b8dacea

import Mathlib
set_option autoImplicit false

theorem solution (f : ℂ → ℂ) (R : NNReal) (hR : 0 < R) (D : ℝ)
    (hD : ∀ z, z ∈ Metric.sphere (0 : ℂ) (R : ℝ) → ‖f z‖ ≤ D)
    (d : ℕ) :
    ‖cauchyPowerSeries f 0 (R : ℝ) d (fun _ => (R : ℂ))‖ ≤ D := by
  have hRpos : (0:ℝ) < R := hR
  have h1 := norm_cauchyPowerSeries_le f 0 (R : ℝ) d
  have h2 : (2 * Real.pi)⁻¹ * (∫ θ in (0:ℝ)..2 * Real.pi, ‖f (circleMap 0 (R:ℝ) θ)‖) ≤ D := by
    have hD0 : 0 ≤ D := le_trans (norm_nonneg _) (hD _ (circleMap_mem_sphere 0 hRpos.le 0))
    have hint : (∫ θ in (0:ℝ)..2 * Real.pi, ‖f (circleMap 0 (R:ℝ) θ)‖) ≤ ∫ θ in (0:ℝ)..2 * Real.pi, D := by
      by_cases hi : IntervalIntegrable (fun θ => ‖f (circleMap 0 (R:ℝ) θ)‖) MeasureTheory.volume 0 (2 * Real.pi)
      · apply intervalIntegral.integral_mono_on (by positivity) hi intervalIntegrable_const
        intro θ _
        exact hD _ (circleMap_mem_sphere 0 hRpos.le θ)
      · rw [intervalIntegral.integral_undef hi]
        simp only [intervalIntegral.integral_const, smul_eq_mul]
        simp only [sub_zero]
        positivity
    have : (∫ θ in (0:ℝ)..2 * Real.pi, D) = 2 * Real.pi * D := by simp [mul_comm]
    rw [this] at hint
    have hpi : 0 < 2 * Real.pi := by positivity
    calc _ ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * D) := by gcongr
      _ = D := by field_simp
  have h3 := (cauchyPowerSeries f 0 (R:ℝ) d).le_opNorm (fun _ => (R : ℂ))
  have h4 : ∏ _i : Fin d, ‖(R : ℂ)‖ = (R:ℝ) ^ d := by simp
  rw [h4] at h3
  have h5 : ‖cauchyPowerSeries f 0 (R : ℝ) d‖ * (R:ℝ)^d ≤ D := by
    calc _ ≤ ((2 * Real.pi)⁻¹ * (∫ θ in (0:ℝ)..2 * Real.pi, ‖f (circleMap 0 (R:ℝ) θ)‖) * |(R:ℝ)|⁻¹ ^ d) * (R:ℝ)^d := by gcongr
      _ = (2 * Real.pi)⁻¹ * (∫ θ in (0:ℝ)..2 * Real.pi, ‖f (circleMap 0 (R:ℝ) θ)‖) := by
        rw [abs_of_pos hRpos, mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hRpos.ne'), mul_one]
      _ ≤ D := h2
  exact h3.trans h5
