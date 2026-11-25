-- Prove2me | solution 1 for LeanPool.Vizing.PEC.exists_total
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:43:30.557193+00:00
-- url     : https://prove2.me/submissions/30301aad-e90c-4cd5-aa05-777d38418381

module
public import Definitions.Def_LeanPool_Vizing_Step
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Definitions.Def_LeanPool_Vizing_Main
public import Theorems.Thm_LeanPool_Vizing_PEC_mem_uncoloured
public import Theorems.Thm_LeanPool_Vizing_PEC_kempeSwap_col
public import Theorems.Thm_LeanPool_Vizing_PEC_setEdge_col
public import Theorems.Thm_LeanPool_Vizing_PEC_updFun_left
public import Theorems.Thm_LeanPool_Vizing_PEC_updFun_right
public import Theorems.Thm_LeanPool_Vizing_PEC_vizing_step
attribute [local simp] LeanPool.Vizing.PEC.kempeSwap_col
attribute [local simp] LeanPool.Vizing.PEC.setEdge_col
attribute [local simp] LeanPool.Vizing.PEC.updFun_left
attribute [local simp] LeanPool.Vizing.PEC.updFun_right



set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open LeanPool LeanPool.Vizing
open LeanPool.Vizing.PEC
variable {V : Type*} [Fintype V] [DecidableEq V] {C : Type*} [Fintype C] [DecidableEq C]
  {G : SimpleGraph V}
omit [DecidableEq V] [DecidableEq C]
namespace LeanPool.Vizing.PEC
theorem _root_.solution [DecidableRel G.Adj] (hcard : G.maxDegree < Fintype.card C) :
    ∃ c : PEC G C, ∀ u v, G.Adj u v → c.col u v ≠ none := by
  classical
  suffices H : ∀ (k : ℕ) (c : PEC G C), c.uncoloured.card ≤ k →
      ∃ c' : PEC G C, ∀ u v, G.Adj u v → c'.col u v ≠ none by
    exact H (empty G C).uncoloured.card (empty G C) le_rfl
  intro k
  induction k with
  | zero =>
    intro c hk
    refine ⟨c, fun u v huv hcol => ?_⟩
    have hmem : (u, v) ∈ c.uncoloured := (c.mem_uncoloured (u, v)).2 ⟨huv, hcol⟩
    have := Finset.card_pos.2 ⟨_, hmem⟩
    omega
  | succ k ih =>
    intro c hk
    by_cases hall : ∀ u v, G.Adj u v → c.col u v ≠ none
    · exact ⟨c, hall⟩
    · push Not at hall
      obtain ⟨x, y, hadj, hnone⟩ := hall
      obtain ⟨c1, hext, hc1⟩ := vizing_step c hcard hadj (by simpa using hnone)
      refine ih c1 ?_
      have hsub : c1.uncoloured ⊆ c.uncoloured := by
        intro p hp
        rw [mem_uncoloured] at hp ⊢
        refine ⟨hp.1, ?_⟩
        by_contra hcon
        exact (hext p.1 p.2 hcon) hp.2
      have hxy : (x, y) ∈ c.uncoloured := (c.mem_uncoloured (x, y)).2 ⟨hadj, by simpa using hnone⟩
      have hxy' : (x, y) ∉ c1.uncoloured := by
        rw [mem_uncoloured]
        rintro ⟨-, h⟩
        exact hc1 h
      have hlt : c1.uncoloured.card < c.uncoloured.card :=
        Finset.card_lt_card ⟨hsub, fun hcon => hxy' (hcon hxy)⟩
      omega
end LeanPool.Vizing.PEC
