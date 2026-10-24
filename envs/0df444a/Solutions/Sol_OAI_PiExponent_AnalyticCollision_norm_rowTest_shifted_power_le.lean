-- Prove2me | solution 1 for OAI.PiExponent.AnalyticCollision.norm_rowTest_shifted_power_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T05:24:00.104992+00:00
-- url     : https://prove2.me/submissions/ee26d96a-bcfd-4de2-940a-9c2c844a7cc9

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
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

theorem solution {center : ℂ} {R : ℝ} (hR : 0 < R) (hc : ‖center‖ + 3 / 4 ≤ R / 2) (ell d : ℕ) : ‖cauchyPowerSeries (fun t : ℂ => (((center + Complex.log (1 + t)) / (R : ℂ)) ^ d)) 0 (1 / 2) ell (fun _ => (1 : ℂ))‖ ≤ (2 : ℝ) ^ ell * (1 / 2 : ℝ) ^ d := by
  have hb : ∀ z, z ∈ Metric.sphere (0 : ℂ) (1 / 2) →
      ‖((center + Complex.log (1 + z)) / (R : ℂ)) ^ d‖ ≤ (1 / 2 : ℝ) ^ d := by
    intro z hz
    rw [mem_sphere_zero_iff_norm] at hz
    have hl := Complex.norm_log_one_add_half_le_self (z := z) hz.le
    rw [norm_pow]
    apply pow_le_pow_left₀ (norm_nonneg _)
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, div_le_iff₀ hR]
    calc ‖center + Complex.log (1 + z)‖ ≤ ‖center‖ + ‖Complex.log (1 + z)‖ := norm_add_le _ _
      _ ≤ ‖center‖ + 3 / 4 := by rw [hz] at hl; linarith
      _ ≤ 1 / 2 * R := by linarith
  have := S105CB.coeff_le (by norm_num : (0:ℝ) < 1 / 2) hb ell 1
  calc _ ≤ _ := this
    _ = (2 : ℝ) ^ ell * (1 / 2 : ℝ) ^ d := by norm_num; ring
