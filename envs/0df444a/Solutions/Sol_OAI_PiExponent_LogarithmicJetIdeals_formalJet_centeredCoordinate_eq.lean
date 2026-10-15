-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.formalJet_centeredCoordinate_eq
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T06:30:01.755548+00:00
-- url     : https://prove2.me/submissions/faa6ab7a-2a1e-45f7-9ff2-ef34d00cdd29

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_CenteredCoordinate
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.Tactic.Ring

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : Nat} (center : Fin m -> Complex) (i : Fin (m + 1)) :
    formalJet center (OAI.PiExponent.LogarithmicJetIdeals.centeredCoordinate center i) =
      (if i = 0 then MvPowerSeries.X 0 else
        MvPowerSeries.X i + liftLogSeries m (PowerSeries.log Complex) - MvPowerSeries.X 0) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [formalJet, OAI.PiExponent.LogarithmicJetIdeals.centeredCoordinate,
      MvPolynomial.aeval_def]
  · simp [formalJet, OAI.PiExponent.LogarithmicJetIdeals.centeredCoordinate,
      MvPolynomial.aeval_def, ← MvPowerSeries.c_eq_algebraMap] <;> ring