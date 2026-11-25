-- Prove2me | solution 1 for Konig.exists_total_of_bipartite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:44:33.175803+00:00
-- url     : https://prove2.me/submissions/252bec62-1946-4487-a888-601e4c6acdd0

module
public import Definitions.Def_LeanPool_Vizing_Main
public import Definitions.Def_Konig_Basic
public import Theorems.Thm_Konig_konig_step
public import Theorems.Thm_LeanPool_Vizing_PEC_mem_uncoloured


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open Konig
open LeanPool.Vizing LeanPool.Vizing.PEC
variable {V : Type*} {C : Type*} {G : SimpleGraph V}
namespace Konig
theorem _root_.solution [Fintype V] [Fintype C] [DecidableRel G.Adj]
    (s : G.Coloring (Fin 2))
    (hcard : G.maxDegree ≤ Fintype.card C) :
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
      obtain ⟨c1, hext, hc1⟩ := konig_step s c hcard hadj hnone
      refine ih c1 ?_
      have hsub : c1.uncoloured ⊆ c.uncoloured := by
        intro p hp
        rw [mem_uncoloured] at hp ⊢
        refine ⟨hp.1, ?_⟩
        by_contra hcon
        exact (hext p.1 p.2 hcon) hp.2
      have hxy : (x, y) ∈ c.uncoloured := (c.mem_uncoloured (x, y)).2 ⟨hadj, hnone⟩
      have hxy' : (x, y) ∉ c1.uncoloured := by
        rw [mem_uncoloured]
        rintro ⟨-, h⟩
        exact hc1 h
      have hlt : c1.uncoloured.card < c.uncoloured.card :=
        Finset.card_lt_card ⟨hsub, fun hcon => hxy' (hcon hxy)⟩
      omega
end Konig
