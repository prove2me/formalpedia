-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.liftPowerSeries_succ_support
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T17:55:25.013559+00:00
-- url     : https://prove2.me/submissions/e1bb7fde-8c82-403a-9a00-0cb0017508f4

import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_liftPowerSeries_coeff_formula

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} (f : PowerSeries ℂ)
    (d : Fin (m + 1) →₀ ℕ) (j : Fin m) (h : d j.succ ≠ 0) :
    MvPowerSeries.coeff d
      (((MvPowerSeries.finSuccEquiv ℂ m).symm.toRingHom.comp
        (PowerSeries.map MvPowerSeries.C)) f) = 0 := by
  have hn : ¬ ∀ k : Fin m, d k.succ = 0 := by
    intro hall
    exact h (hall j)
  rw [OAI.PiExponent.AdmissibleFormalInterpolation.liftPowerSeries_coeff_formula]
  simp [hn]