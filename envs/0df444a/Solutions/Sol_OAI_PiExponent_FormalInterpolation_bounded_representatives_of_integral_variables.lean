-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.bounded_representatives_of_integral_variables
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T12:20:53.84422+00:00
-- url     : https://prove2.me/submissions/20620bca-d49f-4619-a6e9-0a3bed8ee7f7

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_integral_class_has_monic_relation
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_representatives_of_monic_relations

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat}
    (J : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (hvars : ∀ i : Fin (m + 1),
      IsIntegral Complex (Ideal.Quotient.mk J (MvPolynomial.X i))) :
    ∃ N : Nat, ∀ a : Fin (m + 1) →₀ Nat,
      ∃ R : MvPolynomial (Fin (m + 1)) Complex,
        (∀ b ∈ R.support, ∀ i : Fin (m + 1), b i < N) ∧
          MvPolynomial.monomial a (1 : Complex) - R ∈ J := by
  apply bounded_representatives_of_monic_relations J
  intro i
  exact integral_class_has_monic_relation J (hvars i)