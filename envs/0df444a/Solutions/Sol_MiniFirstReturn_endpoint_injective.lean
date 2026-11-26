-- Prove2me | solution 1 for MiniFirstReturn.endpoint_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:07:02.370044+00:00
-- url     : https://prove2.me/submissions/c7b25924-beb6-45ca-be83-2f18abb98657

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
theorem _root_.solution (p : Equiv.Perm X) (B : Finset X) :
    Function.Injective (endpoint p B) := by
  intro b b' hend
  have hend' :
      (p ^ time p B b) (b : X) = (p ^ time p B b') (b' : X) :=
    congrArg Subtype.val hend
  rcases le_total (time p B b) (time p B b') with hle | hle
  · obtain ⟨q,hq⟩ := Nat.exists_eq_add_of_le hle
    have hbase : (b : X) = (p ^ q) (b' : X) := by
      apply (p ^ time p B b).injective
      simpa [hq, pow_add] using hend'
    have hqzero : q = 0 := by
      by_contra hne
      have hqpos : 0 < q := Nat.pos_of_ne_zero hne
      have hqlt : q < time p B b' := by
        rw [hq]
        exact Nat.lt_add_of_pos_left (time_pos p B b)
      exact pow_not_mem_of_lt_time p B b' hqpos hqlt (hbase ▸ b.property)
    apply Subtype.ext
    simpa [hqzero] using hbase
  · obtain ⟨q,hq⟩ := Nat.exists_eq_add_of_le hle
    have hbase : (b' : X) = (p ^ q) (b : X) := by
      apply (p ^ time p B b').injective
      simpa [hq, pow_add] using hend'.symm
    have hqzero : q = 0 := by
      by_contra hne
      have hqpos : 0 < q := Nat.pos_of_ne_zero hne
      have hqlt : q < time p B b := by
        rw [hq]
        exact Nat.lt_add_of_pos_left (time_pos p B b')
      exact pow_not_mem_of_lt_time p B b hqpos hqlt (hbase ▸ b'.property)
    apply Subtype.ext
    simpa [hqzero] using hbase.symm
end MiniFirstReturn
