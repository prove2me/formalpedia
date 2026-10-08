-- Prove2me | solution 1 for GoldbachCometImprint.normalized_from_sum
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T23:50:59.774382+00:00
-- url     : https://prove2.me/submissions/9a934d20-ceb9-42ba-b87a-969523c3a505

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Rat.Defs
import Mathlib.Data.List.Basic
import Definitions.Def_GoldbachComet
import Definitions.Def_GoldbachCometImprint
import Definitions.Def_GoldbachCometRace
import Theorems.Thm_GoldbachComet_orderedReprCount_eq_sum

open scoped BigOperators

set_option autoImplicit false

open GoldbachComet GoldbachCometImprint

theorem solution (n : ℕ) :
    normalizedOrderedCount n =
      ((primeLeftSummand n).sum (fun _ => 1) : ℚ) / singularSeriesPrimes n := by
  unfold normalizedOrderedCount
  congr 1
  exact_mod_cast GoldbachComet.orderedReprCount_eq_sum n

#print axioms solution
