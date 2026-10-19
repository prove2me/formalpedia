-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.plainJet_shifted_monomial_eq_monomial
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T22:00:07.700711+00:00
-- url     : https://prove2.me/submissions/12b773d6-c32d-4943-a7f9-661def2377ec
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_PlainJet
import Mathlib.Data.Fintype.Pi
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_plainJet_shifted_product_eq_Xprod
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_Xprod_pow_eq_monomial

open OAI.PiExponent.AdmissibleFormalInterpolation

 theorem solution
    {m : Nat} (c : Fin m -> Complex) (a : Complex)
    (d : Fin (m + 1) -> Nat) :
    OAI.PiExponent.LogarithmicJetIdeals.plainJet c
        (MvPolynomial.C a *
          Finset.prod Finset.univ (fun k : Fin (m + 1) =>
            (MvPolynomial.X k -
              MvPolynomial.C ((Fin.cases (1 : Complex) c : Fin (m + 1) -> Complex) k)) ^ d k)) =
      MvPowerSeries.monomial (Finsupp.equivFunOnFinite.symm d) a := by
  exact (OAI.PiExponent.LogarithmicJetIdeals.plainJet_shifted_product_eq_Xprod
    c a d).trans (OAI.PiExponent.LogarithmicJetIdeals.Xprod_pow_eq_monomial a d)