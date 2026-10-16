-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.hasSubst_logTailCoordinates
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T06:44:13.220775+00:00
-- url     : https://prove2.me/submissions/b25781ff-ed4d-440c-8102-76d256de9d48

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Mathlib.RingTheory.MvPowerSeries.Substitution

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution {m : ℕ} (T : Fin m → ℕ) :
    MvPowerSeries.HasSubst
      (Fin.cases (MvPowerSeries.X 0)
        (fun i : Fin m => MvPowerSeries.X i.succ +
          OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries m
            ((InterpolationMatrix.truncatedLog (T i) : PowerSeries ℂ) - PowerSeries.log ℂ))) := by
  have htrunc (i : Fin m) :
      PowerSeries.constantCoeff (InterpolationMatrix.truncatedLog (T i) : PowerSeries ℂ) = 0 := by
    rw [Polynomial.constantCoeff_coe]
    simp [InterpolationMatrix.truncatedLog, PowerSeries.coeff_trunc]
  have htail (i : Fin m) :
      PowerSeries.constantCoeff
        ((InterpolationMatrix.truncatedLog (T i) : PowerSeries ℂ) - PowerSeries.log ℂ) = 0 := by
    rw [map_sub, htrunc i, PowerSeries.constantCoeff_log, sub_self]
  have hlift (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f = 0) :
      MvPowerSeries.constantCoeff (liftLogSeries m f) = 0 := by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    change MvPowerSeries.coeff 0
      ((MvPowerSeries.finSuccEquiv ℂ m).symm (PowerSeries.map MvPowerSeries.C f)) = 0
    have hc := MvPowerSeries.coeff_coeff_finSuccEquiv
      (p := (MvPowerSeries.finSuccEquiv ℂ m).symm (PowerSeries.map MvPowerSeries.C f))
      (k := 0) (x := 0)
    rw [AlgEquiv.apply_symm_apply, Finsupp.cons_zero_zero,
      PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, hf,
      map_zero, map_zero] at hc
    exact hc.symm
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · change MvPowerSeries.constantCoeff (MvPowerSeries.X 0 :
      MvPowerSeries (Fin (m + 1)) ℂ) = 0
    exact MvPowerSeries.constantCoeff_X 0
  · change MvPowerSeries.constantCoeff
      (MvPowerSeries.X i.succ + liftLogSeries m
        ((InterpolationMatrix.truncatedLog (T i) : PowerSeries ℂ) - PowerSeries.log ℂ)) = 0
    rw [map_add, MvPowerSeries.constantCoeff_X, zero_add]
    exact hlift _ (htail i)
