-- Prove2me | solution 2 for NoAdjString.card_noAdjacentStringsCard_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-25T17:33:10.398924+00:00
-- url     : https://prove2.me/submissions/a7385595-3384-4071-8720-5ed284ce749d

import Theorems.Thm_NoAdjString_card_noAdjacentStringsCard
import Definitions.Def_NoAdjacentBinaryStrings

open Finset Function NoAdjString

theorem solution (n k : ℕ) (h : n + 1 < 2 * k) :
    (noAdjacentStringsCard n k).card = 0 := by
  rw [card_noAdjacentStringsCard]
  exact Nat.choose_eq_zero_of_lt (by omega)
