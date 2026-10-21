-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.total_degree_series_jet_interpolation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T05:44:25.012327+00:00
-- url     : https://prove2.me/submissions/146dc44b-0df3-451d-aa5a-51f13bd29e9a

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.Ideal.Operations
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_finite_total_degree_truncation
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_finite_support_jet_realization

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : Nat}
    (center : Fin m -> Complex)
    (N : Nat)
    (S : MvPowerSeries (Fin (m + 1)) Complex) :
    Exists fun P : MvPolynomial (Fin (m + 1)) Complex =>
      (e : Fin (m + 1) -> Nat) ->
        (∑ k : Fin (m + 1), e k) <= N ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (formalJet center P) =
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) S := by
  obtain ⟨T, hTsupport, hTcoeff⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.finite_total_degree_truncation N S
  obtain ⟨P, hP⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.finite_support_jet_realization
      center N T hTsupport
  refine ⟨P, ?_⟩
  intro e he
  exact (hP e he).trans (hTcoeff e he)