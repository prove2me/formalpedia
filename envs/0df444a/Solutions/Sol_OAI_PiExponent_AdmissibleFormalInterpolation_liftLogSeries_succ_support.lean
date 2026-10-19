-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries_succ_support
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T17:48:37.004969+00:00
-- url     : https://prove2.me/submissions/57946f40-2f7e-4d55-b4b0-c01ce03e2506

import Definitions.Def_OAI_PiExponent_FormalJetShear
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_liftPowerSeries_succ_support

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} (delta : Fin m → PowerSeries ℂ) (i : Fin m)
    (d : Fin (m + 1) →₀ ℕ) (j : Fin m) (h : d j.succ ≠ 0) :
    MvPowerSeries.coeff d (liftLogSeries m (delta i)) = 0 := by
  simpa [liftLogSeries] using
    OAI.PiExponent.AdmissibleFormalInterpolation.liftPowerSeries_succ_support
      (f := delta i) d j h