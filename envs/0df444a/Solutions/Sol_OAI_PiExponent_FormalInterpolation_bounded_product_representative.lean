-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.bounded_product_representative
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T13:40:08.22968+00:00
-- url     : https://prove2.me/submissions/5fa59674-d8cf-4634-b5dc-f97026dddaf8

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_product_support
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_product_congruence

open scoped BigOperators
theorem solution
    {m : Nat}
    (J : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (N : Nat)
    (a : Fin (m + 1) →₀ Nat)
    (hcoord : ∀ i : Fin (m + 1),
      ∃ R : MvPolynomial (Fin (m + 1)) Complex,
        (∀ b ∈ R.support, b i < N ∧ ∀ j : Fin (m + 1), j ≠ i → b j = 0) ∧
          MvPolynomial.monomial (Finsupp.single i (a i)) (1 : Complex) - R ∈ J) :
    ∃ R : MvPolynomial (Fin (m + 1)) Complex,
      (∀ b ∈ R.support, ∀ i : Fin (m + 1), b i < N) ∧
        MvPolynomial.monomial a (1 : Complex) - R ∈ J := by
  classical
  choose R hR using hcoord
  refine ⟨∏ i : Fin (m + 1), R i, ?_, ?_⟩
  · exact OAI.PiExponent.FormalInterpolation.bounded_product_support N R
      (fun i => (hR i).1)
  · exact OAI.PiExponent.FormalInterpolation.bounded_product_congruence J a R
      (fun i => (hR i).2)