-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries_constantCoeff
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T06:19:22.036294+00:00
-- url     : https://prove2.me/submissions/877f80df-aa13-4807-b1c1-f77fd7ac905d

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.MvPowerSeries.Substitution

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution {m : ℕ} (F : PowerSeries ℂ) :
    MvPowerSeries.constantCoeff (liftLogSeries m F) = PowerSeries.coeff 0 F := by
  change MvPowerSeries.coeff (0 : Fin (m + 1) →₀ ℕ) (liftLogSeries m F) = _
  have hzero : Finsupp.cons 0 (0 : Fin m →₀ ℕ) = (0 : Fin (m + 1) →₀ ℕ) := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  rw [← hzero]
  rw [← MvPowerSeries.coeff_coeff_finSuccEquiv
    (p := liftLogSeries m F) (k := 0) (x := 0)]
  simp [liftLogSeries]