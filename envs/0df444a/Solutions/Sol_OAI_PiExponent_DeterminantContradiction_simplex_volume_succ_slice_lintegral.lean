-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_volume_succ_slice_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:28:21.936758+00:00
-- url     : https://prove2.me/submissions/f992baea-d265-44dd-92e3-5e6c7128320a

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_volume_succ_product_reindex
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_product_lintegral
open scoped BigOperators
open MeasureTheory

theorem solution (m : Nat) (T : Real) (hT : 0 < T) :
    MeasureTheory.volume {x : Fin (m + 1) → Real |
      (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < T} =
      MeasureTheory.lintegral MeasureTheory.volume (fun t : Real =>
        if 0 ≤ t ∧ t < T then
          MeasureTheory.volume {x : Fin m → Real |
            (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < T - t}
        else 0) := by
  rw [OAI.PiExponent.DeterminantContradiction.simplex_volume_succ_product_reindex]
  exact OAI.PiExponent.DeterminantContradiction.simplex_product_lintegral m T