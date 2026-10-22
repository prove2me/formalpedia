-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.monomial_coeff_below_degree
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:15:23.48664+00:00
-- url     : https://prove2.me/submissions/b5979248-7b6e-40b4-a936-f135f54bb46e

import Mathlib
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
set_option autoImplicit false
open scoped BigOperators

theorem solution
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [CommSemiring K]
    (a : Finsupp ι Nat)
    (e : ι -> Nat)
    (he : (∑ k : ι, e k) < (∑ k : ι, a k)) :
    MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e)
      (MvPolynomial.monomial a (1 : K)) = 0 := by
  rw [MvPolynomial.coeff_monomial, if_neg]
  intro h
  have : ∀ k, a k = e k := by
    intro k
    rw [h]
    simp
  have h2 : (∑ k : ι, a k) = ∑ k : ι, e k := Finset.sum_congr rfl (fun k _ => this k)
  omega
