-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.plain_jet_shifted_monomial_sum_coeff
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T21:45:14.707442+00:00
-- url     : https://prove2.me/submissions/45c6b464-3a93-4b8a-8653-204ac85b037d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_PlainJet
import Mathlib.Data.Fintype.Pi
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_plainJet_shifted_monomial_coeff

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : Nat} (c : Fin m -> Complex)
    (s : Finset (Fin (m + 1) -> Nat))
    (a : (Fin (m + 1) -> Nat) -> Complex)
    (e : Fin (m + 1) -> Nat) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (OAI.PiExponent.LogarithmicJetIdeals.plainJet c
        (Finset.sum s (fun d => MvPolynomial.C (a d) *
          Finset.prod Finset.univ (fun k : Fin (m + 1) => (MvPolynomial.X k -
            MvPolynomial.C ((Fin.cases (1 : Complex) c : Fin (m + 1) -> Complex) k))
              ^ d k)))) =
      if e ∈ s then a e else 0 := by
  classical
  simp only [map_sum]
  simp_rw [OAI.PiExponent.LogarithmicJetIdeals.plainJet_shifted_monomial_coeff]
  simp [Finset.sum_ite_eq', eq_comm]