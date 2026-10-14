-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.coeff_vanishes_for_product_on_weighted_simplex
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T07:41:58.837028+00:00
-- url     : https://prove2.me/submissions/2d80cbb7-cbc9-4479-a796-69b81e364963

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_coeff_product_zero_of_bounded_support
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_simplex_downward_cutoff

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem solution
    {m : Nat} {n : Nat} (v : Fin (m + 1) → Real) (R : Fin n → Real)
    (hR : ∀ i, 0 < R i)
    (F : Fin n → MvPolynomial (Fin (m + 1)) Complex)
    (hF : ∀ i a, a ∈ OAI.PiExponent.strictWeightedSimplex v (R i) →
      MvPolynomial.coeff (InterpolationMatrix.exponentVector a) (F i) = 0) :
    ∀ a, a ∈ OAI.PiExponent.strictWeightedSimplex v (∑ i, R i) →
      MvPolynomial.coeff (InterpolationMatrix.exponentVector a) (∏ i, F i) = 0 := by
  intro a ha
  apply OAI.PiExponent.FormalInterpolation.weighted_coeff_product_zero_of_bounded_support
    v R a F
  · intro i b hba hne
    by_contra hnot
    have hb : ∑ j, v j * (b j : Real) < R i := lt_of_not_ge hnot
    have hmem := OAI.PiExponent.FormalInterpolation.weighted_simplex_downward_cutoff
      v R hR a ha i b hba hb
    exact hne (hF i b hmem)
  · simp only [OAI.PiExponent.strictWeightedSimplex, Finset.mem_filter] at ha
    exact ha.2
