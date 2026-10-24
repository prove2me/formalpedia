-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weighted_coefficient_support_sum_eq_column_sum
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:28:11.827431+00:00
-- url     : https://prove2.me/submissions/4781b005-0bd8-4373-a5dd-b760803435f1

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_support_sum_eq_simplex_sum
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_finset_sum_eq_subtype_sum
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Classical
open scoped BigOperators
noncomputable section

theorem solution
    (nu : Real) (d : FixedData nu) (H : Real)
    (P : WeightedPolynomial d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) H)
    (f : (Fin (d.m + 1) →₀ Nat) → Complex) :
    (∑ a ∈ P.1.support, f a * P.1.coeff a) =
      ∑ c : Column d H,
        f (InterpolationMatrix.exponentVector c.1) *
          P.1.coeff (InterpolationMatrix.exponentVector c.1) := by
  let s := realWeightedSimplex
    (InterpolationMatrix.columnWeights d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d))) H
  calc
    (∑ a ∈ P.1.support, f a * P.1.coeff a) =
        ∑ a ∈ s,
          f (InterpolationMatrix.exponentVector a) *
            P.1.coeff (InterpolationMatrix.exponentVector a) := by
      simpa [s] using
        (weighted_support_sum_eq_simplex_sum nu d H P f)
    _ = ∑ c : {a // a ∈ s},
          f (InterpolationMatrix.exponentVector c.1) *
            P.1.coeff (InterpolationMatrix.exponentVector c.1) := by
      exact finset_sum_eq_subtype_sum s
        (fun a => f (InterpolationMatrix.exponentVector a) *
          P.1.coeff (InterpolationMatrix.exponentVector a))
    _ = ∑ c : Column d H,
          f (InterpolationMatrix.exponentVector c.1) *
            P.1.coeff (InterpolationMatrix.exponentVector c.1) := by
      rfl