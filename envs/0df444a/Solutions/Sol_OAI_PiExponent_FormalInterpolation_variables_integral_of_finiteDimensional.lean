-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.variables_integral_of_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T12:54:49.405264+00:00
-- url     : https://prove2.me/submissions/209a625f-9ca3-439c-8021-10358ce95eb0

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat}
    (J : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (hfinite : FiniteDimensional Complex (MvPolynomial (Fin (m + 1)) Complex ⧸ J)) :
    ∀ i : Fin (m + 1),
      IsIntegral Complex (Ideal.Quotient.mk J (MvPolynomial.X i)) := by
  letI : Module.Finite Complex (MvPolynomial (Fin (m + 1)) Complex ⧸ J) := hfinite
  intro i
  exact IsIntegral.of_finite Complex (Ideal.Quotient.mk J (MvPolynomial.X i))