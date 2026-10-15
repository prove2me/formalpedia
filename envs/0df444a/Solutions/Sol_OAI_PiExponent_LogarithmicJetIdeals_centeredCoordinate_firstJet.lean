-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.centeredCoordinate_firstJet
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T06:19:51.472237+00:00
-- url     : https://prove2.me/submissions/58e0e00f-290d-41ff-9912-94eafbabf48b

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_CenteredCoordinate
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_centeredCoordinate_eq
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_explicitCenteredExpression_firstJet

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : Nat} (center : Fin m → Complex) :
    (∀ i, MvPowerSeries.coeff 0
      (formalJet center (OAI.PiExponent.LogarithmicJetIdeals.centeredCoordinate center i)) = 0) ∧
    (∀ i j, MvPowerSeries.coeff (Finsupp.single j 1)
      (formalJet center (OAI.PiExponent.LogarithmicJetIdeals.centeredCoordinate center i)) =
        (if i = j then 1 else 0)) := by
  have h := OAI.PiExponent.LogarithmicJetIdeals.explicitCenteredExpression_firstJet (m := m)
  constructor
  · intro i
    rw [OAI.PiExponent.LogarithmicJetIdeals.formalJet_centeredCoordinate_eq center i]
    exact h.1 i
  · intro i j
    rw [OAI.PiExponent.LogarithmicJetIdeals.formalJet_centeredCoordinate_eq center i]
    exact h.2 i j