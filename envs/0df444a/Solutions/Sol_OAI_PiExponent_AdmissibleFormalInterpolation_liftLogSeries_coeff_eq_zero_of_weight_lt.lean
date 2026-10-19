-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries_coeff_eq_zero_of_weight_lt
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T07:19:07.071471+00:00
-- url     : https://prove2.me/submissions/42e165f4-4a13-4f5f-b51c-3fda28af4029

import Definitions.Def_OAI_PiExponent_WeightedJetShear
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_liftLogSeries_coeff_eq_zero_of_nonzero_tail
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_liftLogSeries_coeff_eq_coeff_of_zero_tail
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_liftLogSeries_coord_zero_lt_of_weight_lt

open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem solution
    {m : ℕ} (v0 : ℝ) (u : Fin m → ℝ)
    (N : Fin m → ℕ) (D : Fin m → PowerSeries ℂ)
    (hv0 : 0 < v0)
    (hN : ∀ i, u i ≤ (N i : ℝ) * v0)
    (hD : ∀ i n, n < N i → PowerSeries.coeff n (D i) = 0)
    (i : Fin m) (α : Fin (m + 1) →₀ ℕ)
    (hα : (∑ j, Fin.cases v0 u j * (α j : ℝ)) < u i) :
    MvPowerSeries.coeff α (liftLogSeries m (D i)) = 0 := by
  classical
  by_cases htail : ∀ j : Fin m, α j.succ = 0
  · rw [OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries_coeff_eq_coeff_of_zero_tail
      m (D i) α htail]
    exact hD i (α 0)
      (OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries_coord_zero_lt_of_weight_lt
        v0 u N hv0 hN i α htail hα)
  · have hnonzero : ∃ j : Fin m, α j.succ ≠ 0 := by
      by_contra h
      push_neg at h
      exact htail h
    exact OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries_coeff_eq_zero_of_nonzero_tail
      m (D i) α hnonzero
