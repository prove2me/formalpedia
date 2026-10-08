-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.exists_pos_left_unit_interval
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T21:59:05.937545+00:00
-- url     : https://prove2.me/submissions/e04d3655-fc8f-47b9-9084-a81faaabc542

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution {s : ℝ} (hs : 0 < s) :
    ∃ m : ℕ, 0 < m ∧ s ∈ Set.Icc ((m : ℝ) - 1) (m : ℝ) := by
  let n : ℕ := ⌊s⌋₊
  by_cases hint : s = (n : ℝ)
  · have hn : 0 < n := by
      exact_mod_cast (show (0 : ℝ) < (n : ℝ) by simpa [hint] using hs)
    refine ⟨n, hn, ?_⟩
    constructor
    · simpa [hint] using (sub_le_self (n : ℝ) (by norm_num : (0 : ℝ) ≤ 1))
    · simpa [hint]
  · refine ⟨n + 1, Nat.succ_pos n, ?_⟩
    constructor
    · have hfloor : (n : ℝ) ≤ s := by
        exact Nat.floor_le hs.le
      simpa [n, Nat.cast_add, Nat.cast_one] using hfloor
    · have hlt : s < (n : ℝ) + 1 := by
        exact_mod_cast Nat.lt_floor_add_one s
      simpa [Nat.cast_add, Nat.cast_one] using hlt.le
