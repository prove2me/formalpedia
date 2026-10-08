-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.exists_nat_unit_interval
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T21:50:27.965824+00:00
-- url     : https://prove2.me/submissions/2d0d425b-d39f-43f0-8d90-688a312eddde

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution {s : ℝ} (hs : 0 ≤ s) :
    ∃ m : ℕ, s ∈ Set.Icc (m : ℝ) (m + 1) := by
  refine ⟨⌊s⌋₊, ?_⟩
  constructor
  · exact Nat.floor_le hs
  · have hlt : s < (⌊s⌋₊ : ℝ) + 1 := by
      exact_mod_cast Nat.lt_floor_add_one s
    exact hlt.le
