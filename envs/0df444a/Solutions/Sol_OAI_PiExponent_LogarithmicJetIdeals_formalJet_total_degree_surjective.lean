-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.formalJet_total_degree_surjective
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T06:10:12.225125+00:00
-- url     : https://prove2.me/submissions/cd8cef5e-5fa8-4500-bc6a-a0aae98cf3fc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_PlainJet
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_CenteredCoordinate
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_finiteJet_comp_surjective
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_centeredCoordinate_firstJet
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_centeredCoordinates_comp
import Mathlib.RingTheory.Ideal.Operations

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : Nat}
    (center : Fin m → Complex)
    (N : Nat)
    (value : (Fin (m + 1) → Nat) → Complex) :
    Exists fun P : MvPolynomial (Fin (m + 1)) Complex =>
      (e : Fin (m + 1) → Nat) →
        (∑ k, e k) ≤ N →
          MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
            (formalJet center P) = value e := by
  let phi : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) Complex :=
    fun i => formalJet center (OAI.PiExponent.LogarithmicJetIdeals.centeredCoordinate center i)
  obtain ⟨hzero, hlinear⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.centeredCoordinate_firstJet center
  obtain ⟨Q, hQ⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.finiteJet_comp_surjective
      phi hzero hlinear N value
  refine ⟨MvPolynomial.aeval (OAI.PiExponent.LogarithmicJetIdeals.centeredCoordinate center) Q, ?_⟩
  intro e he
  rw [OAI.PiExponent.LogarithmicJetIdeals.centeredCoordinates_comp center Q]
  exact hQ e he