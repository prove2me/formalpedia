-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.truncatedPolynomialJet_coeff_sum_e43f5331
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:12:42.692297+00:00
-- url     : https://prove2.me/submissions/cb981636-734d-437f-9ad5-b40ed6006049

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem solution
    {α : Type*} [Fintype α] (m : Nat)
    (c : Fin m → Complex) (T : Fin m → Nat)
    (e : Fin (m + 1) →₀ Nat)
    (f : α → MvPolynomial (Fin (m + 1)) Complex) :
    (truncatedPolynomialJet c T (∑ x, f x)).coeff e =
      ∑ x, (truncatedPolynomialJet c T (f x)).coeff e := by
  simp only [truncatedPolynomialJet, map_sum, MvPolynomial.coeff_sum]