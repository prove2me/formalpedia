-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.coeff_X_first_coordinate_power_vanish
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T11:30:27.067275+00:00
-- url     : https://prove2.me/submissions/f2d91c8b-137f-4a43-97d6-cb70d7cd69a8

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem solution
    {m : ℕ} (b : Fin (m + 1) → ℕ) (n : ℕ)
    (hbn : b (0 : Fin (m + 1)) < n) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
      ((MvPowerSeries.X (0 : Fin (m + 1)) :
        MvPowerSeries (Fin (m + 1)) ℂ) ^ n) = 0 := by
  classical
  have hne : InterpolationMatrix.exponentVector b ≠
      Finsupp.single (0 : Fin (m + 1)) n := by
    intro heq
    have hcoord : b (0 : Fin (m + 1)) = n := by
      simpa [InterpolationMatrix.exponentVector] using
        congrArg (fun f : Fin (m + 1) →₀ ℕ => f (0 : Fin (m + 1))) heq
    omega
  simp [MvPowerSeries.coeff_X_pow, hne]