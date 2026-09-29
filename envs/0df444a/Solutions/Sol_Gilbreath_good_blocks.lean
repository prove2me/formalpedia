-- Prove2me | solution 1 for Gilbreath.good_blocks
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-15T20:07:27.037974+00:00
-- url     : https://prove2.me/submissions/a2f023ab-a7f6-4c12-903b-d6652be2102b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_gilbreath_triangle
import Theorems.Thm_Gilbreath_second_column
import Theorems.Thm_Gilbreath_small_rows
import Theorems.Thm_Gilbreath_head_odd_tail_even

open Gilbreath

theorem solution (K : ℕ) : ∃ k m : ℕ, 1 ≤ k ∧ k + m = K + 1 ∧ d k 0 = 1 ∧
    ∀ n, 1 ≤ n → n ≤ m → d k n = 0 ∨ d k n = 2 := by
  -- Every row `j + 1` begins with `1`: the head of a row is `|d j 1 - d j 0|`,
  -- and `d j 1` is even and at most `2`, hence `0` or `2`.
  have head : ∀ j : ℕ, d (j + 1) 0 = 1 := by
    intro j
    induction j with
    | zero => exact small_rows 1 le_rfl (by norm_num)
    | succ j ih =>
      have heven : Even (d (j + 1) 1) := (head_odd_tail_even j).2 0
      have heven' := Nat.even_iff.1 heven
      have hle := second_column j
      have h2 : d (j + 1) 1 = 0 ∨ d (j + 1) 1 = 2 := by omega
      rw [d_succ_apply, ih]
      rcases h2 with h2 | h2 <;> rw [h2] <;> decide
  -- The good block can then be taken at the row `K + 1` itself, with `m = 0`.
  exact ⟨K + 1, 0, Nat.le_add_left 1 K, rfl, head K, by omega⟩
