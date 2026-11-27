-- Prove2me | solution 1 for MasulloRH.finite_zeta_zero_configurations_gaussian_gram_bound
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T01:17:52.42873+00:00
-- url     : https://prove2.me/submissions/8c54a3d5-015d-4712-9859-236452df24ec

import Theorems.Thm_MasulloRH_finite_laplace_evaluations_weighted_energy_bound
import Theorems.Thm_MasulloRH_twenty_five_rational_translates_gaussian_all_windows
import Theorems.Thm_MasulloRH_quarter_shift_gaussian_exterior_energy
import Theorems.Thm_MasulloRH_fixed_gaussian_residual_laplace_at_zeta_zero
import Mathlib.Tactic.Linarith

open MeasureTheory MasulloRH.WindowLaplaceGram MasulloRH.GaussianApproximation
open MasulloRH.ThetaDerivativeCertificate

theorem solution {n : ℕ} (s d : Fin n → ℂ) (hl : ∀ i, 1/2 < (s i).re)
    (hr : ∀ i, (s i).re < 1) (hz : ∀ i, riemannZeta (s i) = 0) :
    ‖∑ i, d i * Complex.exp ((s i)^2/4)‖^2 ≤
      (1/32000000000) * gramValue (3/4) (1/4) s d := by
  have ev (i : Fin n) := MasulloRH.fixed_gaussian_residual_laplace_at_zeta_zero
    (fun i : Fin 25 => (coeff i:ℂ)) (fun i => (shift i:ℝ)) (s i)
    (by linarith [hl i]) (hr i) (hz i)
  have he := (MasulloRH.quarter_shift_gaussian_exterior_energy (3/4) (1/4) (by norm_num) (by norm_num)).1
  have energy_lt := MasulloRH.twenty_five_rational_translates_gaussian_all_windows.1 (3/4) (1/4)
    (by norm_num) (by norm_num)
  have hw (i : Fin n) : |(s i).re-3/4|<1/4 := abs_lt.mpr ⟨by linarith [hl i],by linarith [hr i]⟩
  have h := MasulloRH.finite_laplace_evaluations_weighted_energy_bound (3/4) (1/4) err s d hw he (fun i => (ev i).1)
  have hv (i : Fin n) : moment err (s i) = Complex.exp ((s i)^2/4) := (ev i).2
  have hG : 0 ≤ gramValue (3/4) (1/4) s d := h.1 ▸ integral_nonneg (fun _ => sq_nonneg _)
  exact (by simpa only [hv] using h.2 : ‖∑ i, d i * Complex.exp ((s i)^2/4)‖^2 ≤
      energy (3/4) (1/4) err * gramValue (3/4) (1/4) s d).trans (mul_le_mul_of_nonneg_right energy_lt.le hG)
