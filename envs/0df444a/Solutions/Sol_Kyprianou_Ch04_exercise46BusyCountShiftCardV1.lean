-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46BusyCountShiftCardV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:20:17.146911+00:00
-- url     : https://prove2.me/submissions/71939c10-111c-4af0-b2da-427a3e74daac

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (S T : Set NNReal) (a b : NNReal)
    (hab : a ≤ b) (hpos : ∀ u ∈ T, 0 < u)
    (hEq : S = insert a ((fun u : NNReal => b+u) '' T)) :
    (S.encard : ENNReal) = 1 + (T.encard : ENNReal) := by
  rw [hEq, Set.encard_insert_of_notMem]
  · rw [(show Function.Injective (fun u : NNReal => b+u) from
      fun x y h => add_left_cancel h).encard_image]
    simp [add_comm]
  · rintro ⟨u, hu, he⟩
    exact (not_lt_of_ge hab) (he ▸ lt_add_of_pos_right b (hpos u hu))
