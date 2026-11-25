-- Prove2me | solution 1 for LeanPool.Vizing.PEC.kempe_degree_le_one_of_isFree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:29:22.299337+00:00
-- url     : https://prove2.me/submissions/762a96a0-1918-46c7-b299-39c09f07f843

module
public import Definitions.Def_LeanPool_Vizing_Endpoints
public import Definitions.Def_LeanPool_Vizing_Kempe
public import Theorems.Thm_LeanPool_Vizing_PEC_kempeGraph_adj

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open LeanPool LeanPool.Vizing
open LeanPool.Vizing.PEC
variable {V : Type*} [Fintype V] [DecidableEq V] {C : Type*} [DecidableEq C]
  {G : SimpleGraph V}
omit [DecidableEq V] [DecidableEq C]
namespace LeanPool.Vizing.PEC
theorem _root_.solution (c : PEC G C) {a b : C} [DecidableRel (c.kempeGraph a b).Adj]
    {v : V} {γ : C} (hγ : γ = a ∨ γ = b) (hfree : c.IsFree v γ) :
    (c.kempeGraph a b).degree v ≤ 1 := by
  classical
  rw [← card_neighborFinset_eq_degree, Finset.card_le_one]
  intro p hp q hq
  rw [mem_neighborFinset, kempeGraph_adj] at hp hq
  rcases hγ with rfl | rfl
  · rcases hp.2 with h | h
    · exact absurd h (hfree p)
    · rcases hq.2 with h' | h'
      · exact absurd h' (hfree q)
      · exact c.col_proper h h'
  · rcases hp.2 with h | h
    · rcases hq.2 with h' | h'
      · exact c.col_proper h h'
      · exact absurd h' (hfree q)
    · exact absurd h (hfree p)
end LeanPool.Vizing.PEC
