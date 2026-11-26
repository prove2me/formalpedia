-- Prove2me | solution 1 for GeneralFinalRatio.quantitative_to_epsilon
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:10:22.547278+00:00
-- url     : https://prove2.me/submissions/799f7529-b2c5-4944-ba86-dc74cd47f3f3

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
theorem _root_.solution (d : ℕ) (hd : 3 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n k : ℕ) (p : ℝ),
        p ≤ (K d : ℝ) * (n : ℝ) / (k : ℝ) ^ 2 →
        C * Real.sqrt (n : ℝ) < (k : ℝ) → p < ε := by
  let a : ℝ := (K d : ℝ) / ε
  let C : ℝ := a + 1
  have hKpos : (0 : ℝ) < K d := by
    simp [K]
    positivity
  have ha : 0 < a := div_pos hKpos hε
  have hC : 0 < C := by simp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro n k p hp hthreshold
  have hsqrt : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hleft : 0 ≤ C * Real.sqrt (n : ℝ) := mul_nonneg hC.le hsqrt
  have hkreal : (0 : ℝ) < k := lt_of_le_of_lt hleft hthreshold
  have hsqrt_sq : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := by
    rw [Real.sq_sqrt]
    positivity
  have hsq : C ^ 2 * (n : ℝ) < (k : ℝ) ^ 2 := by
    have : (C * Real.sqrt (n : ℝ)) ^ 2 < (k : ℝ) ^ 2 := by
      nlinarith
    nlinarith [hsqrt_sq]
  have haC : a ≤ C ^ 2 := by
    dsimp [C]
    nlinarith
  have han : a * (n : ℝ) ≤ C ^ 2 * (n : ℝ) := by
    gcongr
  have hnum : (K d : ℝ) * (n : ℝ) < ε * (k : ℝ) ^ 2 := by
    have hmain : a * (n : ℝ) < (k : ℝ) ^ 2 := han.trans_lt hsq
    have haeq : ε * a = (K d : ℝ) := by
      dsimp [a]
      field_simp
    nlinarith
  have hquant : (K d : ℝ) * (n : ℝ) / (k : ℝ) ^ 2 < ε := by
    apply (div_lt_iff₀ (sq_pos_of_pos hkreal)).2
    nlinarith
  exact hp.trans_lt hquant
end GeneralFinalRatio
