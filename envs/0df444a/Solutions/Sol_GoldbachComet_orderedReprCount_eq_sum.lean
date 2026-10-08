-- Prove2me | solution 1 for GoldbachComet.orderedReprCount_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T04:49:27.269493+00:00
-- url     : https://prove2.me/submissions/b9dc86df-c613-4577-9e09-42c48ab581ea

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_GoldbachComet

open scoped BigOperators

set_option autoImplicit false

open GoldbachComet

theorem solution (n : ℕ) :
    orderedReprCount n =
      (primeLeftSummand n).sum (fun _ => 1) := by
  unfold orderedReprCount orderedReprPairs
  rw [Finset.card_map, Finset.card_eq_sum_ones]

#print axioms solution
