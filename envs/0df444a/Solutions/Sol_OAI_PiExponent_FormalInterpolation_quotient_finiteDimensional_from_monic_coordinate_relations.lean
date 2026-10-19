-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.quotient_finiteDimensional_from_monic_coordinate_relations
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T17:22:24.925853+00:00
-- url     : https://prove2.me/submissions/749d6d5c-2c76-4cf3-b18d-cfb28ac7d191

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat}
    (J : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (hrel : ∀ i : Fin (m + 1),
      ∃ p : Polynomial Complex,
        p.Monic ∧ Polynomial.aeval (Ideal.Quotient.mk J (MvPolynomial.X i)) p = 0) :
    FiniteDimensional Complex ((MvPolynomial (Fin (m + 1)) Complex) ⧸ J) := by
  have hcoord :
      ∀ i : Fin (m + 1),
        IsIntegral Complex (Ideal.Quotient.mk J (MvPolynomial.X i)) := by
    intro i
    rcases hrel i with ⟨p, hp, he⟩
    exact ⟨p, hp, he⟩
  have hall : ∀ x : (MvPolynomial (Fin (m + 1)) Complex) ⧸ J,
      IsIntegral Complex x := by
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    induction p using MvPolynomial.induction_on with
    | C a =>
        change IsIntegral Complex
          (algebraMap Complex ((MvPolynomial (Fin (m + 1)) Complex) ⧸ J) a)
        exact isIntegral_algebraMap
    | add p q hp hq =>
        rw [map_add]
        exact hp.add hq
    | mul_X p i hp =>
        rw [map_mul]
        exact hp.mul (hcoord i)
  letI : Algebra.IsIntegral Complex ((MvPolynomial (Fin (m + 1)) Complex) ⧸ J) :=
    ⟨hall⟩
  exact Algebra.IsIntegral.finite
