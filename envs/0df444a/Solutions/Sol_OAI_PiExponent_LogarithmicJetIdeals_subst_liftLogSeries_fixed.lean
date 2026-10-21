-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.subst_liftLogSeries_fixed
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T18:41:30.134207+00:00
-- url     : https://prove2.me/submissions/15c00759-5c57-424b-a66c-1e7bac935570

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_subst_liftLogSeries_of_X_zero

open OAI.PiExponent.AdmissibleFormalInterpolation

/-- A substitution that fixes the distinguished variable leaves lifted series unchanged.
This is the assertion of `subst_liftLogSeries_of_X_zero`, restated in the binder order of the
target so that its type is syntactically identical. -/
theorem solution {m : ℕ} (a : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ)
    (ha : MvPowerSeries.HasSubst a) (ha0 : a 0 = MvPowerSeries.X 0)
    (f : PowerSeries ℂ) :
    MvPowerSeries.subst a
      (OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries m f) =
        OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries m f :=
  OAI.PiExponent.AdmissibleFormalInterpolation.subst_liftLogSeries_of_X_zero
    (m := m) f a ha ha0
