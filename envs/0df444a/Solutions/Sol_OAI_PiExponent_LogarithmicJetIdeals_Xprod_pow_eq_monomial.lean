-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.Xprod_pow_eq_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T03:01:58.309044+00:00
-- url     : https://prove2.me/submissions/c5852983-2e88-42e5-b24e-2f273c337c53

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_PlainJet
import Mathlib.Data.Fintype.Pi

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : Nat} (a : Complex) (d : Fin (m + 1) -> Nat) :
    MvPowerSeries.C a *
        Finset.prod Finset.univ (fun k : Fin (m + 1) =>
          (MvPowerSeries.X k) ^ d k) =
      MvPowerSeries.monomial (Finsupp.equivFunOnFinite.symm d) a := by
  classical
  rw [MvPowerSeries.monomial_eq']
  congr 1
  exact (Finsupp.prod_fintype
    (Finsupp.equivFunOnFinite.symm d)
    (fun k n => (MvPowerSeries.X k : MvPowerSeries (Fin (m + 1)) Complex) ^ n)
    (fun _ => pow_zero _)).symm