-- Prove2me | solution 1 for GeneralFinalRatio.ratio_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:09:58.39097+00:00
-- url     : https://prove2.me/submissions/432a968b-466e-44d3-a1b5-95bdced4366d

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
    (d n k good plans : ℕ) (hk : 0 < k) (hplans : 0 < plans)
    (hcard : good * k ^ 2 ≤ K d * n * plans) :
    (good : ℝ) / (plans : ℝ) ≤
      (K d : ℝ) * (n : ℝ) / (k : ℝ) ^ 2 := by
  have hp : (0 : ℝ) < plans := by exact_mod_cast hplans
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  apply (div_le_iff₀ hp).2
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sq_pos_of_pos hk')).2
  exact_mod_cast hcard
end GeneralFinalRatio
