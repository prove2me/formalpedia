-- Prove2me | solution 1 for GeneralFinalRatio.cutoff_mul_k_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:05:57.47322+00:00
-- url     : https://prove2.me/submissions/df105886-5cf9-4564-848e-73ec9e060fd8

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution

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
theorem _root_.solution (d n k : ℕ) (hkn : k < n) :
    cutoff d n k * k ≤ (64 * d + 1) * n := by
  have hdiv : (64 * d * n / k) * k ≤ 64 * d * n := Nat.div_mul_le_self _ _
  calc
    cutoff d n k * k = (64 * d * n / k) * k + k := by
      simp [cutoff]
      ring
    _ ≤ 64 * d * n + n := Nat.add_le_add hdiv hkn.le
    _ = (64 * d + 1) * n := by ring
end GeneralFinalRatio
