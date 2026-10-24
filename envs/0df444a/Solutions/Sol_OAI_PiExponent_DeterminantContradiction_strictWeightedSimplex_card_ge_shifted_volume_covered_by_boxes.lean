-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.strictWeightedSimplex_card_ge_shifted_volume_covered_by_boxes
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T11:55:13.392523+00:00
-- url     : https://prove2.me/submissions/d8aaddaa-743d-4d36-b2d4-09e92d789740

import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_strictWeightedSimplex_card_ge_shifted_volume_covered_by_boxes_pointwise_cover
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_shifted_boxes_volume_ne_top
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_volume_toReal_mono_of_subset
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem solution
    (n : Nat) (w : Fin n → Real) (hw : ∀ i, 0 < w i)
    (T : Real) (hT : 0 < T) :
    ENNReal.toReal
      (MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, w i * x i) < T})
      ≤ ENNReal.toReal
        (MeasureTheory.volume
          (⋃ a ∈ (strictWeightedSimplex w (T + Finset.univ.sum w) : Set (Fin n → Nat)),
            {x : Fin n → Real | ∀ i, (a i : Real) ≤ x i ∧ x i < (a i : Real) + 1})) := by
  apply OAI.PiExponent.DeterminantContradiction.volume_toReal_mono_of_subset
  · intro x hx
    obtain ⟨a, ha, hbox⟩ :=
      OAI.PiExponent.DeterminantContradiction.strictWeightedSimplex_card_ge_shifted_volume_covered_by_boxes_pointwise_cover
        n w hw T hT x hx
    exact Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨ha, hbox⟩⟩
  · exact OAI.PiExponent.DeterminantContradiction.shifted_boxes_volume_ne_top
      n w hw T hT