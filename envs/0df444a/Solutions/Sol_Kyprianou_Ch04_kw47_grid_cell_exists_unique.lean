-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_grid_cell_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:05:35.371383+00:00
-- url     : https://prove2.me/submissions/ea576598-120e-41d4-a192-d6c3b6124b77

import Mathlib
open Set
set_option autoImplicit false

/-- A finite increasing grid covers its half-open endpoint interval
with exactly one nonempty cell containing each point. -/
theorem solution
    (u : Nat → Real) (hu : Monotone u) (N : Nat)
    (x : Real) (hx : x ∈ Ioc (u 0) (u N)) :
    ∃ i ∈ Finset.range N, x ∈ Ioc (u i) (u (i+1)) ∧
      ∀ j ∈ Finset.range N, x ∈ Ioc (u j) (u (j+1)) → j = i := by
  have hex : ∃ i < N, x ∈ Ioc (u i) (u (i+1)) := by
    induction N with
    | zero => exact (not_lt_of_ge hx.2 hx.1).elim
    | succ N ih =>
      by_cases h : x ≤ u N
      · obtain ⟨i, hi, hcell⟩ := ih ⟨hx.1, h⟩
        exact ⟨i, Nat.lt_succ_of_lt hi, hcell⟩
      · exact ⟨N, Nat.lt_succ_self N, lt_of_not_ge h, hx.2⟩
  obtain ⟨i, hi, hcell⟩ := hex
  refine ⟨i, Finset.mem_range.mpr hi, hcell, ?_⟩
  intro j hj hjcell
  rcases lt_trichotomy j i with h | h | h
  · have hle := hu (Nat.succ_le_of_lt h)
    exact (not_lt_of_ge (hjcell.2.trans hle) hcell.1).elim
  · exact h
  · have hle := hu (Nat.succ_le_of_lt h)
    exact (not_lt_of_ge (hcell.2.trans hle) hjcell.1).elim
