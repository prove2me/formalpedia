-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.finite_total_degree_truncation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T05:50:01.975584+00:00
-- url     : https://prove2.me/submissions/21ccd492-2dbc-40e5-abd1-b50c02532cdb

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.MvPowerSeries.Trunc

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : Nat}
    (N : Nat)
    (S : MvPowerSeries (Fin (m + 1)) Complex) :
    Exists fun T : MvPowerSeries (Fin (m + 1)) Complex =>
      ((e : Fin (m + 1) -> Nat) -> N < (∑ k : Fin (m + 1), e k) ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) T = 0) ∧
      ((e : Fin (m + 1) -> Nat) -> (∑ k : Fin (m + 1), e k) <= N ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) T =
          MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) S) := by
  classical
  let T : MvPowerSeries (Fin (m + 1)) Complex :=
    (MvPowerSeries.truncTotal (N + 1) S : MvPolynomial (Fin (m + 1)) Complex)
  have hdegree (e : Fin (m + 1) -> Nat) :
      (Finsupp.equivFunOnFinite.symm e).degree = ∑ k : Fin (m + 1), e k := by
    rw [Finsupp.degree_eq_sum]
    simp
  refine ⟨T, ?_, ?_⟩
  · intro e he
    change MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e)
      (MvPowerSeries.truncTotal (N + 1) S) = 0
    apply MvPowerSeries.coeff_truncTotal_eq_zero
    rw [hdegree]
    omega
  · intro e he
    change MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e)
      (MvPowerSeries.truncTotal (N + 1) S) =
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) S
    apply MvPowerSeries.coeff_truncTotal
    rw [hdegree]
    omega
