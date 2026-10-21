-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.finite_support_jet_realization
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T05:49:33.062102+00:00
-- url     : https://prove2.me/submissions/af30d93a-4e88-4ddc-8a3a-4ca781848e7c

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.Ideal.Operations
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_finite_support_series_has_polynomial_jet
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_jet_surjective_on_polynomials

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : Nat}
    (center : Fin m -> Complex)
    (N : Nat)
    (S : MvPowerSeries (Fin (m + 1)) Complex)
    (hS : (e : Fin (m + 1) -> Nat) -> N < (∑ k : Fin (m + 1), e k) ->
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) S = 0) :
    Exists fun P : MvPolynomial (Fin (m + 1)) Complex =>
      (e : Fin (m + 1) -> Nat) ->
        (∑ k : Fin (m + 1), e k) <= N ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (formalJet center P) =
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) S := by
  obtain ⟨Q, hQ⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.finite_support_series_has_polynomial_jet N S hS
  obtain ⟨P, hP⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.formalJet_jet_surjective_on_polynomials
      center N Q
  refine ⟨P, fun e he => ?_⟩
  rw [hP e he, hQ e he]