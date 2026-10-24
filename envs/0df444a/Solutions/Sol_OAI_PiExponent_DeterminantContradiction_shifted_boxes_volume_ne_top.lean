-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.shifted_boxes_volume_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:02:08.926974+00:00
-- url     : https://prove2.me/submissions/df0cdc92-5815-482d-af6a-caa8f8364278

import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_shifted_boxes_isBounded
import Theorems.Thm_bounded_set_volume_ne_top
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem solution
    (n : Nat) (w : Fin n → Real) (hw : ∀ i, 0 < w i)
    (T : Real) (hT : 0 < T) :
    MeasureTheory.volume
      (⋃ a ∈ (strictWeightedSimplex w (T + Finset.univ.sum w) : Set (Fin n → Nat)),
        {x : Fin n → Real | ∀ i, (a i : Real) ≤ x i ∧ x i < (a i : Real) + 1}) ≠ ⊤ := by
  exact bounded_set_volume_ne_top _ (shifted_boxes_isBounded n w hw T hT)