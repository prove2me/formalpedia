-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finiteDimensional_quotient_has_bounded_support_representatives
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T12:10:46.001139+00:00
-- url     : https://prove2.me/submissions/9a579b20-3d88-4d47-88a0-d156f9fc9a19

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_monomial_has_bounded_support_representatives
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_support_representatives_of_monomials

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat}
    (J : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (hfinite : FiniteDimensional Complex (MvPolynomial (Fin (m + 1)) Complex ⧸ J)) :
    ∃ N : Nat, ∀ P : MvPolynomial (Fin (m + 1)) Complex,
      ∃ R : MvPolynomial (Fin (m + 1)) Complex,
        (∀ a ∈ R.support, ∀ i : Fin (m + 1), a i < N) ∧ P - R ∈ J := by
  obtain ⟨N, hmono⟩ :=
    OAI.PiExponent.FormalInterpolation.monomial_has_bounded_support_representatives
      (m := m) J hfinite
  refine ⟨N, ?_⟩
  exact
    OAI.PiExponent.FormalInterpolation.bounded_support_representatives_of_monomials
      (m := m) J N hmono