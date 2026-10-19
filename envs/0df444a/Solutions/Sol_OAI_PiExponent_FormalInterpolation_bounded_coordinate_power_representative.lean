-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.bounded_coordinate_power_representative
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T17:12:55.452557+00:00
-- url     : https://prove2.me/submissions/1ee14251-b34a-40f2-97a4-b5b152ede077

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_coordinate_power_representative_step

open scoped BigOperators

theorem solution
    {m : Nat}
    (J : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (N : Nat)
    (hN : 0 < N)
    (i : Fin (m + 1))
    (n : Nat)
    (c : Fin N → Complex)
    (hpow : MvPolynomial.X i ^ N -
      ∑ k : Fin N, MvPolynomial.C (c k) * MvPolynomial.X i ^ k.val ∈ J) :
    ∃ R : MvPolynomial (Fin (m + 1)) Complex,
      (∀ b ∈ R.support, b i < N ∧ ∀ j : Fin (m + 1), j ≠ i → b j = 0) ∧
        MvPolynomial.monomial (Finsupp.single i n) (1 : Complex) - R ∈ J := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      exact OAI.PiExponent.FormalInterpolation.bounded_coordinate_power_representative_step
        J N hN i n c hpow ih