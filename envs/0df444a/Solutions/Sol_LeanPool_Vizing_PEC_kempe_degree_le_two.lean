-- Prove2me | solution 1 for LeanPool.Vizing.PEC.kempe_degree_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:28:55.994807+00:00
-- url     : https://prove2.me/submissions/1a16ad83-c044-4794-928f-3bea41c99bf8

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
theorem _root_.solution (c : PEC G C) (a b : C) [DecidableRel (c.kempeGraph a b).Adj] (v : V) :
    (c.kempeGraph a b).degree v ≤ 2 := by
  classical
  rw [← card_neighborFinset_eq_degree]
  have hsub : (c.kempeGraph a b).neighborFinset v ⊆
      ((c.kempeGraph a b).neighborFinset v).filter (fun u => c.col v u = some a) ∪
      ((c.kempeGraph a b).neighborFinset v).filter (fun u => c.col v u = some b) := by
    intro u hu
    have hu' := hu
    rw [mem_neighborFinset, kempeGraph_adj] at hu'
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases hu'.2 with h | h
    · exact Or.inl ⟨hu, h⟩
    · exact Or.inr ⟨hu, h⟩
  have hcarda : (((c.kempeGraph a b).neighborFinset v).filter
      (fun u => c.col v u = some a)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro p hp q hq
    rw [Finset.mem_filter] at hp hq
    exact c.col_proper hp.2 hq.2
  have hcardb : (((c.kempeGraph a b).neighborFinset v).filter
      (fun u => c.col v u = some b)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro p hp q hq
    rw [Finset.mem_filter] at hp hq
    exact c.col_proper hp.2 hq.2
  calc ((c.kempeGraph a b).neighborFinset v).card
      ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ 2 := by omega
end LeanPool.Vizing.PEC
