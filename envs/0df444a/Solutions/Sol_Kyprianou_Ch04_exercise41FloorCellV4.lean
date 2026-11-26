-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41FloorCellV4
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:23:44.245598+00:00
-- url     : https://prove2.me/submissions/2cd6648e-92a3-41e7-a19d-41467362bbab

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false
theorem solution
    (a h s : ℝ) (n : ℕ) (hh : 0 < h)
    (ha : a ≤ s) (hb : s < a + (n : ℝ) * h) :
    let i := Nat.floor ((s - a) / h)
    i ∈ Finset.range n ∧ a + (i : ℝ) * h ≤ s ∧
      s < a + ((i : ℝ) + 1) * h := by
  dsimp only
  have hz : 0 ≤ (s - a) / h := div_nonneg (sub_nonneg.mpr ha) hh.le
  have hl := Nat.floor_le hz
  have hu := Nat.lt_floor_add_one ((s - a) / h)
  refine ⟨Finset.mem_range.mpr ((Nat.floor_lt hz).mpr ?_), ?_, ?_⟩
  · exact (div_lt_iff₀ hh).2 (by linarith)
  · have := (le_div_iff₀ hh).mp hl
    linarith
  · have := (div_lt_iff₀ hh).mp hu
    linarith
