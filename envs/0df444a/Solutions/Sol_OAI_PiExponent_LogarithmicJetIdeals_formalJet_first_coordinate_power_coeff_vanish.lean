-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.formalJet_first_coordinate_power_coeff_vanish
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T10:57:32.856981+00:00
-- url     : https://prove2.me/submissions/0a711ab1-f2b8-41ff-81bb-1e0159b55502

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_first_coordinate_power_eq_X_pow
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_coeff_X_first_coordinate_power_vanish

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem solution
    {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ)
    (b : Fin (m + 1) → ℕ) (n : ℕ)
    (hbn : b (0 : Fin (m + 1)) < n) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
      (AdmissibleFormalInterpolation.formalJet c
        (jetCoordinate c T (0 : Fin (m + 1)) ^ n)) = 0 := by
  rw [OAI.PiExponent.LogarithmicJetIdeals.formalJet_first_coordinate_power_eq_X_pow]
  exact OAI.PiExponent.LogarithmicJetIdeals.coeff_X_first_coordinate_power_vanish b n hbn