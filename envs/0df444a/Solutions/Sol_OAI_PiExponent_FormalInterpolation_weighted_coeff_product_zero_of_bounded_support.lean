-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_coeff_product_zero_of_bounded_support
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T08:19:38.385019+00:00
-- url     : https://prove2.me/submissions/9896c23c-3690-4a41-a488-5f268ee77f87

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_product_coeff_nonzero_has_bounded_factor_allocation
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_allocation_contradicts_strict_gap

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem solution
    {m : Nat} {n : Nat} (v : Fin (m + 1) → Real) (R : Fin n → Real)
    (a : Fin (m + 1) → Nat)
    (F : Fin n → MvPolynomial (Fin (m + 1)) Complex)
    (hcoeff : ∀ i b, b ≤ a →
      MvPolynomial.coeff (InterpolationMatrix.exponentVector b) (F i) ≠ 0 →
        R i ≤ ∑ j, v j * (b j : Real))
    (hweight : ∑ j, v j * (a j : Real) < ∑ i, R i) :
    MvPolynomial.coeff (InterpolationMatrix.exponentVector a) (∏ i, F i) = 0 := by
  by_contra hzero
  have hprod : MvPolynomial.coeff (InterpolationMatrix.exponentVector a) (∏ i, F i) ≠ 0 := by
    simpa using hzero
  obtain ⟨b, hbound, hsum, hnz⟩ :=
    OAI.PiExponent.FormalInterpolation.product_coeff_nonzero_has_bounded_factor_allocation
      a F hprod
  exact (OAI.PiExponent.FormalInterpolation.weighted_allocation_contradicts_strict_gap
    v R a F hcoeff hweight b hbound hsum hnz).elim
