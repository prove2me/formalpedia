-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.bounded_product_congruence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:45:08.63483+00:00
-- url     : https://prove2.me/submissions/61b1f4e3-d0f6-4176-bfb0-3c54c943a442

import Mathlib
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

open scoped BigOperators
theorem solution
    {m : Nat}
    (J : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (a : Fin (m + 1) →₀ Nat)
    (R : Fin (m + 1) → MvPolynomial (Fin (m + 1)) Complex)
    (hR : ∀ i : Fin (m + 1),
      MvPolynomial.monomial (Finsupp.single i (a i)) (1 : Complex) - R i ∈ J) :
    MvPolynomial.monomial a (1 : Complex) - (∏ i : Fin (m + 1), R i) ∈ J := by
  have hmon : MvPolynomial.monomial a (1 : Complex) =
      ∏ i : Fin (m + 1), MvPolynomial.monomial (Finsupp.single i (a i)) (1 : Complex) := by
    rw [← MvPolynomial.monomial_sum_one, Finsupp.univ_sum_single]
  rw [hmon, ← Ideal.Quotient.eq, map_prod, map_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact Ideal.Quotient.eq.mpr (hR i)
