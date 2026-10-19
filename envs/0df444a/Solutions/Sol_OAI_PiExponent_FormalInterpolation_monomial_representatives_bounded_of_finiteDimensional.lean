-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.monomial_representatives_bounded_of_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T13:30:48.980669+00:00
-- url     : https://prove2.me/submissions/d24e096c-88e0-49ce-9562-37b3d8d46f39

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinate_relations_of_finiteDimensional
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_representatives_of_coordinate_relations

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat}
    (J : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (hfd : FiniteDimensional Complex ((MvPolynomial (Fin (m + 1)) Complex) ⧸ J)) :
    ∃ N : Nat, ∀ a : Fin (m + 1) →₀ Nat,
      ∃ R : MvPolynomial (Fin (m + 1)) Complex,
        (∀ b ∈ R.support, ∀ i : Fin (m + 1), b i < N) ∧
          MvPolynomial.monomial a (1 : Complex) - R ∈ J := by
  obtain ⟨N, hN, hrel⟩ :=
    OAI.PiExponent.FormalInterpolation.coordinate_relations_of_finiteDimensional J hfd
  refine ⟨N, ?_⟩
  exact OAI.PiExponent.FormalInterpolation.bounded_representatives_of_coordinate_relations
    J N hN hrel