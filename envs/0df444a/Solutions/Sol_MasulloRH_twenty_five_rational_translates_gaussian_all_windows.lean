-- Prove2me | solution 1 for MasulloRH.twenty_five_rational_translates_gaussian_all_windows
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T00:15:24.985591+00:00
-- url     : https://prove2.me/submissions/4c58f9c5-89da-4573-9c5b-1e5f9e539050

import Theorems.Thm_MasulloRH_quarter_shift_gaussian_exterior_energy
import Theorems.Thm_MasulloRH_quarter_shift_gaussian_central_energy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open MeasureTheory MasulloRH MasulloRH.ThetaDerivativeCertificate MasulloRH.GaussianApproximation MasulloRH.FixedGaussianTest

theorem solution :
    (∀ c b : ℝ, 1/2 ≤ c-b → c+b ≤ 1 → energy c b err < 1/32000000000) ∧
    (∀ k : ℕ, energy (fullCenter k) (fullWidth k) err < 1/32000000000) := by
  have h (c b : ℝ) (hl : 1/2 ≤ c-b) (hr : c+b ≤ 1) : energy c b err < 1/32000000000 := by
    have he := MasulloRH.quarter_shift_gaussian_exterior_energy c b hl hr
    have hc := MasulloRH.quarter_shift_gaussian_central_energy c b hl hr he.1
    linarith only [he.2,hc]
  refine ⟨h,?_⟩
  intro k
  apply h
  · have e : fullCenter k - fullWidth k = left k := by unfold fullCenter fullWidth;ring
    rw [e];unfold left; have : 0≤(12287/32768:ℝ)/((k:ℝ)+1) := by positivity
    linarith
  · have e : fullCenter k + fullWidth k = upper k := by unfold fullCenter fullWidth;ring
    rw [e];apply max_le (by norm_num [right]);exact sub_le_self _ (by positivity)
