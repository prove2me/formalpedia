-- Prove2me | solution 1 for MiniFirstReturn.intervalPoint_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:07:05.487311+00:00
-- url     : https://prove2.me/submissions/ba524160-f44b-40d2-b39e-54a7bba94247

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
noncomputable section
variable {V : Type*} [Fintype V]
variable (d : ℕ) [NeZero d]
variable (G : SimpleGraph V) (hG : IsRegularOfDegree G d)
attribute [local instance] graphAdjDecidable
attribute [local instance] vertexDecidableEq
open MiniFirstReturn
open scoped BigOperators
variable {X : Type*} [Fintype X] [DecidableEq X]
namespace MiniFirstReturn
theorem _root_.solution {I : Type*} [Fintype I]
    (p : Equiv.Perm X) (B : Finset X) (bases : I → B)
    (hbases : Function.Injective bases) :
    Function.Injective (intervalPoint p B bases) := by
  rintro ⟨i,t⟩ ⟨j,u⟩ heq
  rcases le_total (t : ℕ) (u : ℕ) with hle | hle
  · obtain ⟨q,hq⟩ := Nat.exists_eq_add_of_le hle
    have hbase : (bases i : X) = (p ^ q) (bases j : X) := by
      apply (p ^ (t : ℕ)).injective
      simpa [intervalPoint, hq, pow_add] using heq
    have hqzero : q = 0 := by
      by_contra hne
      have hqpos : 0 < q := Nat.pos_of_ne_zero hne
      have hqlt : q < time p B (bases j) := by
        have hqu : q ≤ (u : ℕ) := by omega
        exact lt_of_le_of_lt hqu u.isLt
      exact pow_not_mem_of_lt_time p B (bases j) hqpos hqlt (hbase ▸ (bases i).property)
    have hij : i = j := hbases <| by
      apply Subtype.ext
      simpa [hqzero] using hbase
    subst j
    have htu : (t : ℕ) = (u : ℕ) := by omega
    cases Fin.ext htu
    rfl
  · obtain ⟨q,hq⟩ := Nat.exists_eq_add_of_le hle
    have hbase : (bases j : X) = (p ^ q) (bases i : X) := by
      apply (p ^ (u : ℕ)).injective
      simpa [intervalPoint, hq, pow_add] using heq.symm
    have hqzero : q = 0 := by
      by_contra hne
      have hqpos : 0 < q := Nat.pos_of_ne_zero hne
      have hqlt : q < time p B (bases i) := by
        have hqt : q ≤ (t : ℕ) := by omega
        exact lt_of_le_of_lt hqt t.isLt
      exact pow_not_mem_of_lt_time p B (bases i) hqpos hqlt (hbase ▸ (bases j).property)
    have hji : j = i := hbases <| by
      apply Subtype.ext
      simpa [hqzero] using hbase
    subst j
    have htu : (t : ℕ) = (u : ℕ) := by omega
    cases Fin.ext htu
    rfl
end MiniFirstReturn
