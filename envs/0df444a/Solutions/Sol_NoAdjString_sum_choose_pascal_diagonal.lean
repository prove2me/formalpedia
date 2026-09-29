-- Prove2me | solution 1 for NoAdjString.sum_choose_pascal_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-25T17:34:16.861074+00:00
-- url     : https://prove2.me/submissions/ed080f3a-b130-4595-8234-e46cfd6c4d0c

import Theorems.Thm_NoAdjString_card_noAdjacentStrings_eq_sum
import Theorems.Thm_NoAdjString_card_noAdjacentStrings
import Definitions.Def_NoAdjacentBinaryStrings
import Mathlib.Data.Nat.Fib.Basic

open Finset Function NoAdjString

theorem solution (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), Nat.choose (n + 1 - k) k = Nat.fib (n + 2) := by
  rw [←card_noAdjacentStrings_eq_sum, card_noAdjacentStrings]
