-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.formalJet_first_coordinate_power_eq_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T11:34:00.321841+00:00
-- url     : https://prove2.me/submissions/022d0f6e-0a1b-4d77-baaa-c01f5aca109f

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem solution
    {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ)
    (n : ℕ) :
    AdmissibleFormalInterpolation.formalJet c
      (jetCoordinate c T (0 : Fin (m + 1)) ^ n) =
        MvPowerSeries.X (0 : Fin (m + 1)) ^ n := by
  simp [AdmissibleFormalInterpolation.formalJet, jetCoordinate] <;> ring