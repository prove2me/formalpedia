-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.finite_support_series_has_polynomial_jet
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T05:56:10.841194+00:00
-- url     : https://prove2.me/submissions/f767499f-2dda-446f-9373-1df3ebc009a1

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.Ideal.Operations

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : Nat}
    (N : Nat)
    (S : MvPowerSeries (Fin (m + 1)) Complex)
    (hS : (e : Fin (m + 1) -> Nat) -> N < (∑ k : Fin (m + 1), e k) ->
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) S = 0) :
    Exists fun Q : MvPolynomial (Fin (m + 1)) Complex =>
      (e : Fin (m + 1) -> Nat) ->
        (∑ k : Fin (m + 1), e k) <= N ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) Q =
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) S := by
  classical
  refine ⟨MvPowerSeries.truncTotal (N + 1) S, ?_⟩
  intro e he
  have hd : Finsupp.degree (Finsupp.equivFunOnFinite.symm e) < N + 1 := by
    rw [Finsupp.degree_eq_sum]
    exact Nat.lt_succ_of_le (by simpa using he)
  simpa only [MvPolynomial.coeff_coe] using
    (MvPowerSeries.coeff_truncTotal S hd)