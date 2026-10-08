-- Prove2me | solution 1 for GoldbachComet.orderedReprCount_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T05:29:48.448419+00:00
-- url     : https://prove2.me/submissions/f3191f8e-53e5-47a4-8cf4-6d8d2b058752

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Prime.Defs
import Definitions.Def_GoldbachComet

set_option autoImplicit false

open GoldbachComet

theorem solution (n : ℕ) : orderedReprCount n = (primeLeftSummand n).card := by
  unfold orderedReprCount orderedReprPairs
  exact Finset.card_map (pairEmbedding n)

#print axioms solution
