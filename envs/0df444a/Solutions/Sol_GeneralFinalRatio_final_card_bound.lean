-- Prove2me | solution 1 for GeneralFinalRatio.final_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:11:38.609384+00:00
-- url     : https://prove2.me/submissions/541667b1-7853-4957-9ca6-44d2f911433a

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
public import Theorems.Thm_GeneralFinalRatio_cutoff_mul_k_le

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
set_option linter.unusedSectionVars false
set_option linter.unusedSectionVars false
set_option linter.unusedSectionVars false
open GeneralFinalRatio
namespace GeneralFinalRatio
theorem _root_.solution
    (d n k good plans : ℕ) (hd : 3 ≤ d) (hkn : k < n)
    (hinc : (d - 2) * k * good ≤
      8 * (d - 1) * cutoff d n k * plans) :
    good * k ^ 2 ≤ K d * n * plans := by
  have hq : 1 ≤ d - 2 := by omega
  have hdrop : k * good ≤ (d - 2) * k * good := by
    calc
      k * good = 1 * (k * good) := by ring
      _ ≤ (d - 2) * (k * good) := Nat.mul_le_mul_right (k * good) hq
      _ = (d - 2) * k * good := by ring
  have hswitch : k * good ≤ 8 * (d - 1) * cutoff d n k * plans :=
    hdrop.trans hinc
  have hcut := cutoff_mul_k_le d n k hkn
  have hcoef : 8 * (d - 1) * (64 * d + 1) ≤ K d := by
    calc
      8 * (d - 1) * (64 * d + 1) ≤ 8 * d * (65 * d) := by
        gcongr <;> omega
      _ = 520 * d ^ 2 := by ring
      _ ≤ 1048576 * d ^ 2 := Nat.mul_le_mul_right _ (by omega)
      _ = K d := by rfl
  calc
    good * k ^ 2 = (k * good) * k := by ring
    _ ≤ (8 * (d - 1) * cutoff d n k * plans) * k :=
      Nat.mul_le_mul_right k hswitch
    _ = 8 * (d - 1) * (cutoff d n k * k) * plans := by ring
    _ ≤ 8 * (d - 1) * ((64 * d + 1) * n) * plans := by
      gcongr
    _ = (8 * (d - 1) * (64 * d + 1)) * n * plans := by ring
    _ ≤ K d * n * plans := by
      gcongr
end GeneralFinalRatio
