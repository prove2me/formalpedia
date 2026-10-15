-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.finiteJet_comp_surjective
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T06:21:38.596487+00:00
-- url     : https://prove2.me/submissions/efa2ff0b-e2d1-403b-82de-9c05ee451e53
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_finiteJet_monomial_coefficients
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_finiteJet_interpolation_from_triangular

open scoped BigOperators

theorem solution
    {n : Nat}
    (phi : Fin n → MvPowerSeries (Fin n) Complex)
    (hzero : ∀ i, MvPowerSeries.coeff 0 (phi i) = 0)
    (hlinear : ∀ i j, MvPowerSeries.coeff (Finsupp.single j 1) (phi i) =
      (if i = j then 1 else 0))
    (N : Nat)
    (value : (Fin n → Nat) → Complex) :
    Exists fun Q : MvPolynomial (Fin n) Complex =>
      (e : Fin n → Nat) →
        (∑ k, e k) ≤ N →
          MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
            (MvPolynomial.aeval phi Q) = value e := by
  apply OAI.PiExponent.LogarithmicJetIdeals.finiteJet_interpolation_from_triangular phi N
  · intro d e hd he hlt
    exact (OAI.PiExponent.LogarithmicJetIdeals.finiteJet_monomial_coefficients
      phi hzero hlinear d e).1 hlt
  · intro d e hd he heq
    exact (OAI.PiExponent.LogarithmicJetIdeals.finiteJet_monomial_coefficients
      phi hzero hlinear d e).2 heq