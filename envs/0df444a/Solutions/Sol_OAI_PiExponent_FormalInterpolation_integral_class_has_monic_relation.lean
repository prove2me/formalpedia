-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.integral_class_has_monic_relation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T12:24:32.140681+00:00
-- url     : https://prove2.me/submissions/49969665-b9bb-48a8-8f6e-e77f8a0c6485

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat}
    (J : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    {i : Fin (m + 1)}
    (h : IsIntegral Complex (Ideal.Quotient.mk J (MvPolynomial.X i))) :
    ∃ p : Polynomial Complex,
      p.Monic ∧ Polynomial.aeval (Ideal.Quotient.mk J (MvPolynomial.X i)) p = 0 := by
  rcases h with ⟨p, hp, he⟩
  exact ⟨p, hp, by simpa only [Polynomial.aeval_def] using he⟩