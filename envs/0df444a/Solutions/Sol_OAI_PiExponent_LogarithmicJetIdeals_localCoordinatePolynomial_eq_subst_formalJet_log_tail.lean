-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.localCoordinatePolynomial_eq_subst_formalJet_log_tail
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T05:49:23.298573+00:00
-- url     : https://prove2.me/submissions/db51e696-9c24-4d61-87a6-49feb7e183d3

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinates
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_subst_formalJet_log_tail_eq_truncatedCoordinate_aeval
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_localCoordinatePolynomial_eq_truncatedCoordinate_aeval

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem solution
    {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ)
    (P : MvPolynomial (Fin (m + 1)) ℂ) :
    (localCoordinatePolynomial c T P : MvPowerSeries (Fin (m + 1)) ℂ) =
      MvPowerSeries.subst
        (Fin.cases (MvPowerSeries.X 0)
          (fun i : Fin m => MvPowerSeries.X i.succ + liftLogSeries m
            ((InterpolationMatrix.truncatedLog (T i) : PowerSeries ℂ) -
              PowerSeries.log ℂ)))
        (formalJet c P) := by
  exact (OAI.PiExponent.LogarithmicJetIdeals.localCoordinatePolynomial_eq_truncatedCoordinate_aeval c T P).trans
    (OAI.PiExponent.LogarithmicJetIdeals.subst_formalJet_log_tail_eq_truncatedCoordinate_aeval c T P).symm