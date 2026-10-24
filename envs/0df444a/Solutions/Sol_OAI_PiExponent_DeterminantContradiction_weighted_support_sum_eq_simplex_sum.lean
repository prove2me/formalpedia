-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weighted_support_sum_eq_simplex_sum
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:32:42.511988+00:00
-- url     : https://prove2.me/submissions/ffb37bb5-c455-4c92-aef3-d6620a43a385

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_support_sum_reindex
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_support_subset_simplex
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_encoded_not_support_coeff_zero
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
      ∑ a ∈ realWeightedSimplex
        (InterpolationMatrix.columnWeights d.w0
          (MatrixArithmetic.logWeights (finiteDenominators d))) H,
        f (InterpolationMatrix.exponentVector a) *
          P.1.coeff (InterpolationMatrix.exponentVector a) := by
  classical
  let S : Finset (Fin (d.m + 1) → Nat) :=
    P.1.support.map Finsupp.equivFunOnFinite.toEmbedding
  have hS : S ⊆ realWeightedSimplex
      (InterpolationMatrix.columnWeights d.w0
        (MatrixArithmetic.logWeights (finiteDenominators d))) H := by
    simpa [S] using
      weighted_support_subset_simplex nu d H P
  calc
    (∑ a ∈ P.1.support, f a * P.1.coeff a) =
        ∑ a ∈ S,
          f (InterpolationMatrix.exponentVector a) *
            P.1.coeff (InterpolationMatrix.exponentVector a) := by
      simpa [S] using support_sum_reindex (d.m + 1) P.1 f
    _ = ∑ a ∈ realWeightedSimplex
          (InterpolationMatrix.columnWeights d.w0
            (MatrixArithmetic.logWeights (finiteDenominators d))) H,
          f (InterpolationMatrix.exponentVector a) *
            P.1.coeff (InterpolationMatrix.exponentVector a) :=
      Finset.sum_subset hS (by
        intro a ha hnot
        have hz := encoded_not_support_coeff_zero (d.m + 1) P.1 a hnot
        simp [hz])