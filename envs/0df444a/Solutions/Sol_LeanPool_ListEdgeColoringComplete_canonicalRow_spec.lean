-- Prove2me | solution 1 for LeanPool.ListEdgeColoringComplete.canonicalRow_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:27:37.353288+00:00
-- url     : https://prove2.me/submissions/a2ed0022-a853-4858-853d-53cc66257f33

module
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Fin
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Certificate
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_localRank_add
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_canonicalRow_injective

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.ListEdgeColoringComplete
variable {n : ℕ}
namespace LeanPool.ListEdgeColoringComplete
theorem _root_.solution :
    (∀ i : Fin n, Function.Injective (canonicalRow i)) ∧
    (∀ i : Fin n, (canonicalRow i i : ℕ) = blockedRank n i) ∧
    (∀ i j : Fin n, i ≠ j →
      (canonicalRow i j : ℕ) + canonicalRow j i = targetDegree n i j) := by
  refine ⟨canonicalRow_injective, fun i => by simp [canonicalRow, fullRank], ?_⟩
  intro i j hij
  have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  simp only [canonicalRow, fullRank, hij', (Ne.symm hij'), ite_false]
  exact localRank_add i.isLt j.isLt hij'
end LeanPool.ListEdgeColoringComplete
