-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.monomial_has_bounded_support_representatives
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T12:16:31.104008+00:00
-- url     : https://prove2.me/submissions/ef7c2b79-260c-4060-8d5f-d1d7a02b3202

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_variables_integral_of_finiteDimensional
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_representatives_of_integral_variables
open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
theorem solution
    {m : Nat}
    (J : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (hfinite : FiniteDimensional Complex (MvPolynomial (Fin (m + 1)) Complex ⧸ J)) :
    ∃ N : Nat, ∀ a : Fin (m + 1) →₀ Nat,
      ∃ R : MvPolynomial (Fin (m + 1)) Complex,
        (∀ b ∈ R.support, ∀ i : Fin (m + 1), b i < N) ∧
          MvPolynomial.monomial a (1 : Complex) - R ∈ J := by
  exact OAI.PiExponent.FormalInterpolation.bounded_representatives_of_integral_variables
    J (OAI.PiExponent.FormalInterpolation.variables_integral_of_finiteDimensional J hfinite)