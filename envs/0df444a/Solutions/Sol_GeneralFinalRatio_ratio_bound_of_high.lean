-- Prove2me | solution 1 for GeneralFinalRatio.ratio_bound_of_high
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:10:07.834401+00:00
-- url     : https://prove2.me/submissions/6533f654-cdc9-470e-be79-47b10054f920

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
theorem _root_.solution
    (d n k : ℕ) (p : ℝ) (hk : 0 < k) (hp_one : p ≤ 1)
    (hhigh : K d * n ≤ k ^ 2 →
      p ≤ (K d : ℝ) * (n : ℝ) / (k : ℝ) ^ 2) :
    p ≤ (K d : ℝ) * (n : ℝ) / (k : ℝ) ^ 2 := by
  by_cases h : K d * n ≤ k ^ 2
  · exact hhigh h
  · calc
      p ≤ 1 := hp_one
      _ ≤ (K d : ℝ) * (n : ℝ) / (k : ℝ) ^ 2 := by
        have hnat : k ^ 2 ≤ K d * n := by omega
        have hk' : (0 : ℝ) < k := by exact_mod_cast hk
        apply (le_div_iff₀ (sq_pos_of_pos hk')).2
        norm_num
        exact_mod_cast hnat
end GeneralFinalRatio
