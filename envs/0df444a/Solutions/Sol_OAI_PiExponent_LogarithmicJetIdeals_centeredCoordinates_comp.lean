-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.centeredCoordinates_comp
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T06:22:35.492432+00:00
-- url     : https://prove2.me/submissions/5ed644d6-e1be-4ae2-a227-627fba8b999b

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_CenteredCoordinate
import Mathlib.RingTheory.MvPowerSeries.Equiv

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : Nat} (center : Fin m → Complex)
    (Q : MvPolynomial (Fin (m + 1)) Complex) :
    formalJet center
        (MvPolynomial.aeval
          (OAI.PiExponent.LogarithmicJetIdeals.centeredCoordinate center) Q) =
      MvPolynomial.aeval
        (fun i => formalJet center
          (OAI.PiExponent.LogarithmicJetIdeals.centeredCoordinate center i)) Q := by
  exact MvPolynomial.comp_aeval_apply
    (OAI.PiExponent.LogarithmicJetIdeals.centeredCoordinate center)
    (formalJet center) Q