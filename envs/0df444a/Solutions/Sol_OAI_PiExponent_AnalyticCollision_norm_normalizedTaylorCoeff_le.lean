-- Prove2me | solution 1 for OAI.PiExponent.AnalyticCollision.norm_normalizedTaylorCoeff_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T05:23:54.706974+00:00
-- url     : https://prove2.me/submissions/3849134a-38d9-4a0b-9ca4-b48670331712

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Log
open Filter Topology

namespace S105CB

theorem coeff_le {f : ℂ → ℂ} {c : ℂ} {R D : ℝ} (hR : 0 < R)
    (hD : ∀ z, z ∈ Metric.sphere c R → ‖f z‖ ≤ D) (n : ℕ) (w : ℂ) :
    ‖cauchyPowerSeries f c R n (fun _ => w)‖ ≤ D * (‖w‖ / R) ^ n := by
  have hint : (∫ θ : ℝ in (0)..2 * Real.pi, ‖f (circleMap c R θ)‖) ≤ D * (2 * Real.pi) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := 2 * Real.pi) (C := D) (f := fun θ => ‖f (circleMap c R θ)‖)
      (fun θ _ => by
        rw [norm_norm]
        apply hD
        have := circleMap_mem_sphere c hR.le θ
        exact this)
    have hpi : |2 * Real.pi - 0| = 2 * Real.pi := by
      rw [sub_zero, abs_of_pos Real.two_pi_pos]
    rw [hpi] at h
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using h)
  have h1 := (cauchyPowerSeries f c R n).le_opNorm (fun _ => w)
  have h2 := norm_cauchyPowerSeries_le f c R n
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
  rw [abs_of_pos hR] at h2
  calc ‖cauchyPowerSeries f c R n (fun _ => w)‖
      ≤ ‖cauchyPowerSeries f c R n‖ * ‖w‖ ^ n := h1
    _ ≤ (((2 * Real.pi)⁻¹ * ∫ θ : ℝ in (0)..2 * Real.pi, ‖f (circleMap c R θ)‖) * R⁻¹ ^ n)
          * ‖w‖ ^ n := by gcongr
    _ ≤ (((2 * Real.pi)⁻¹ * (D * (2 * Real.pi))) * R⁻¹ ^ n) * ‖w‖ ^ n := by
          gcongr
    _ = D * (‖w‖ / R) ^ n := by
          field_simp; rw [div_pow, one_pow, div_pow]; ring

end S105CB

theorem solution {f : ℂ → ℂ} {R D : ℝ} (hR : 0 < R) (hD : ∀ z, z ∈ Metric.sphere (0 : ℂ) R → ‖f z‖ ≤ D) (d : ℕ) : ‖cauchyPowerSeries f 0 R d (fun _ => (R : ℂ))‖ ≤ D := by
  have := S105CB.coeff_le hR hD d (R : ℂ)
  rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, div_self hR.ne', one_pow, mul_one] at this
