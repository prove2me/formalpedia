-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.bounded_representatives_of_monic_relations
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T12:39:34.922259+00:00
-- url     : https://prove2.me/submissions/e61a00c7-8523-4bda-9e98-46917d9dbd9f

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_quotient_finiteDimensional_from_monic_coordinate_relations
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_monomial_representatives_bounded_of_finiteDimensional

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat}
    (J : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (hrel : ∀ i : Fin (m + 1),
      ∃ p : Polynomial Complex,
        p.Monic ∧ Polynomial.aeval (Ideal.Quotient.mk J (MvPolynomial.X i)) p = 0) :
    ∃ N : Nat, ∀ a : Fin (m + 1) →₀ Nat,
      ∃ R : MvPolynomial (Fin (m + 1)) Complex,
        (∀ b ∈ R.support, ∀ i : Fin (m + 1), b i < N) ∧
          MvPolynomial.monomial a (1 : Complex) - R ∈ J := by
  exact OAI.PiExponent.FormalInterpolation.monomial_representatives_bounded_of_finiteDimensional
    J (OAI.PiExponent.FormalInterpolation.quotient_finiteDimensional_from_monic_coordinate_relations
      J hrel)
