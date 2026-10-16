-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncated_packet_canonical_coefficients_of_positive_weights_weighted_support_columns
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T20:54:31.018892+00:00
-- url     : https://prove2.me/submissions/a85ca982-f078-4fd8-87ad-2847c6b85593

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_coordinates_mem_realWeightedSimplex

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open scoped BigOperators

noncomputable section

theorem solution
    {m : Nat} (w0 : Real) (w : Fin m → Real) (H : Real)
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i)
    (P : WeightedPolynomial w0 w H) :
    ∀ a ∈ P.val.support,
      ∃ c : InterpolationMatrix.Column w0 w H,
        InterpolationMatrix.exponentVector c.1 = a := by
  classical
  intro a ha
  let b : Fin (m + 1) → Nat := Finsupp.equivFunOnFinite a
  have hbound := P.property a ha
  have hsum :
      ∑ i : Fin (m + 1), InterpolationMatrix.columnWeights w0 w i * (b i : Real) ≤ H := by
    simpa [b] using hbound
  have hw' : ∀ i : Fin (m + 1), 0 < InterpolationMatrix.columnWeights w0 w i := by
    intro i
    exact Fin.cases hw0 hw i
  have hb : b ∈ realWeightedSimplex (InterpolationMatrix.columnWeights w0 w) H :=
    OAI.PiExponent.FormalInterpolation.weighted_coordinates_mem_realWeightedSimplex
      (InterpolationMatrix.columnWeights w0 w) H hw' b hsum
  refine ⟨⟨b, hb⟩, ?_⟩
  simp [b, InterpolationMatrix.exponentVector]