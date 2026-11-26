-- Prove2me | solution 1 for NonbacktrackingWalk.card_walks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:11:24.382158+00:00
-- url     : https://prove2.me/submissions/5d11f7b6-b91e-4bf4-8f68-cfe165e493d4

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
public import Theorems.Thm_NonbacktrackingWalk_card_one
public import Theorems.Thm_NonbacktrackingWalk_card_step

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
noncomputable section
variable {V : Type*} [Fintype V]
open NonbacktrackingWalk
variable {G : SimpleGraph V} {start : OrientedEdge G}
namespace NonbacktrackingWalk
theorem _root_.solution {d : ℕ} (hG : IsRegularOfDegree G d) (k : ℕ) (hk : 1 ≤ k) :
    Nat.card (NonbacktrackingWalk G start k) = (d - 1) ^ (k - 1) := by
  have aux : ∀ m : ℕ, Nat.card (NonbacktrackingWalk G start (m + 1)) = (d - 1) ^ m := by
    intro m
    induction m with
    | zero => simpa using (card_one (G := G) (start := start))
    | succ m ih =>
        change Nat.card (NonbacktrackingWalk G start (m + 2)) = (d - 1) ^ (m + 1)
        rw [card_step hG m, ih, pow_succ]
        ac_rfl
  have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
  rw [← hk']
  simpa using aux (k - 1)
end NonbacktrackingWalk
