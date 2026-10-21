-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.plainJet_shifted_monomial_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T21:52:06.502254+00:00
-- url     : https://prove2.me/submissions/9f7813a0-5eff-4796-aa32-63ba7739e690

import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_plainJet_shifted_monomial_eq_monomial
import Mathlib.Data.Fintype.Pi

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : Nat} (c : Fin m -> Complex) (a : Complex)
    (d e : Fin (m + 1) -> Nat) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (OAI.PiExponent.LogarithmicJetIdeals.plainJet c
        (MvPolynomial.C a *
          Finset.prod Finset.univ (fun k : Fin (m + 1) =>
            (MvPolynomial.X k -
              MvPolynomial.C ((Fin.cases (1 : Complex) c : Fin (m + 1) -> Complex) k)) ^ d k))) =
      if d = e then a else 0 := by
  rw [OAI.PiExponent.LogarithmicJetIdeals.plainJet_shifted_monomial_eq_monomial]
  rw [MvPowerSeries.coeff_monomial]
  simp [eq_comm]