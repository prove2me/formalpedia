-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncated_image_support_is_weight_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T09:00:18.36678+00:00
-- url     : https://prove2.me/submissions/817ae56a-e094-492b-b655-3a3101893a04

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (w0 : Real) (w : Fin m → Real) (H : Real)
    (P : MvPolynomial (Fin (m + 1)) Complex)
    (hP : P.support ⊆ Finset.univ.image
      (fun c : InterpolationMatrix.Column w0 w H =>
        InterpolationMatrix.exponentVector c.1)) :
    ∀ a ∈ P.support,
      ∑ i, InterpolationMatrix.columnWeights w0 w i * (a i : Real) ≤ H := by
  classical
  intro a ha
  obtain ⟨c, -, hc⟩ := Finset.mem_image.mp (hP ha)
  have hsimplex : c.1 ∈ OAI.PiExponent.realWeightedSimplex
      (InterpolationMatrix.columnWeights w0 w) H := c.2
  have hbound := (Finset.mem_filter.mp hsimplex).2
  have hbound' : ∑ i, InterpolationMatrix.columnWeights w0 w i *
      ((InterpolationMatrix.exponentVector c.1 i : Nat) : Real) ≤ H := by
    simpa [InterpolationMatrix.exponentVector] using hbound
  simpa [hc] using hbound'
