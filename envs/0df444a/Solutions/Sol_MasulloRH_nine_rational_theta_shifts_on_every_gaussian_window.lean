-- Prove2me | solution 1 for MasulloRH.nine_rational_theta_shifts_on_every_gaussian_window
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T21:50:20.875965+00:00
-- url     : https://prove2.me/submissions/5280cc49-563f-426d-a02a-2c3cda1c6959

import Theorems.Thm_MasulloRH_nine_shift_residual_uniform_exterior
import Theorems.Thm_MasulloRH_nine_shift_residual_central_integral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open MeasureTheory MasulloRH MasulloRH.NineShift MasulloRH.GaussianApproximation MasulloRH.FixedGaussianTest

theorem solution :
    (∀ c b : ℝ, 1/2 ≤ c-b → c+b ≤ 1 → energy c b err < 1/16384) ∧
    (∀ k : ℕ, energy (fullCenter k) (fullWidth k) err < 1/16384) := by
  have h (c b : ℝ) (hl : 1/2 ≤ c-b) (hr : c+b ≤ 1) : energy c b err < 1/16384 := by
    have he := MasulloRH.nine_shift_residual_uniform_exterior c b hl hr
    have hc := MasulloRH.nine_shift_residual_central_integral c b hl hr he.1
    linarith only [he.2,hc]
  refine ⟨h,?_⟩
  intro k
  apply h
  · have e : fullCenter k - fullWidth k = left k := by unfold fullCenter fullWidth;ring
    rw [e];unfold left; have : 0≤(12287/32768:ℝ)/((k:ℝ)+1) := by positivity
    linarith
  · have e : fullCenter k + fullWidth k = upper k := by unfold fullCenter fullWidth;ring
    rw [e];apply max_le (by norm_num [right]);exact sub_le_self _ (by positivity)
