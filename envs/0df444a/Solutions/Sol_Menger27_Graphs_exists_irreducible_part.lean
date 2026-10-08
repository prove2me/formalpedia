-- Prove2me | solution 1 for Menger27.Graphs.exists_irreducible_part
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T05:56:21.662169+00:00
-- url     : https://prove2.me/submissions/21f8933d-0112-4033-879c-d10a701da76e

import Mathlib
import Definitions.Def_Menger27_Graphs_Separation
import Definitions.Def_Menger27_Graphs_Parts



namespace Menger27.Graphs

theorem exists_irreducible_part_core {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (P Q : Finset V) (hPQ : Disjoint P Q) (n : ℕ) (hG : NPointConnected G P Q n) :
    ∃ K : SimpleGraph V, K ≤ G ∧ IrreduciblyNPointConnected K P Q n := by
  classical
  let S : Set (SimpleGraph V) := {K | K ≤ G ∧ NPointConnected K P Q n}
  obtain ⟨K, hK, hmin⟩ := WellFounded.has_min wellFounded_lt S ⟨G, le_rfl, hG⟩
  refine ⟨K, hK.1, hK.2, fun H hH hH' => hmin H ⟨hH.le.trans hK.1, hH'⟩ hH⟩

theorem exists_separator_through_core {V : Type*} [Fintype V] [DecidableEq V] (K : SimpleGraph V)
    [DecidableRel K.Adj] (P Q : Finset V) (hPQ : Disjoint P Q) (n : ℕ)
    (hK : IrreduciblyNPointConnected K P Q n) (hgrad : n < K.edgeFinset.card)
    (s : V) (hsP : s ∉ P) (hsQ : s ∉ Q) (t : V) (hst : K.Adj s t) :
    ∃ S : Finset V, s ∈ S ∧ S.card = n ∧ Separates K P Q S := by
  classical
  have hlt : K.deleteEdges {s(s, t)} < K := by
    refine lt_of_le_of_ne (SimpleGraph.deleteEdges_le _) ?_
    intro h
    have h2 : (K.deleteEdges {s(s, t)}).Adj s t := by rw [h]; exact hst
    simp [SimpleGraph.deleteEdges_adj] at h2
  obtain ⟨T, hT, hTc⟩ : ∃ T, Separates (K.deleteEdges {s(s, t)}) P Q T ∧ T.card < n := by
    have := hK.2 _ hlt
    unfold NPointConnected at this
    push_neg at this
    exact this
  have hsep : Separates K P Q (insert s T) := by
    intro x hx y hy w
    by_cases hs : s ∈ w.support
    · exact ⟨s, hs, Finset.mem_insert_self _ _⟩
    · have hw : ∀ e ∈ w.edges, e ∉ ({s(s, t)} : Set (Sym2 V)) := by
        intro e he hmem
        have : e = s(s, t) := hmem
        subst this
        exact hs (w.fst_mem_support_of_mem_edges he)
      have hE : ∀ e ∈ w.edges, e ∈ (K.deleteEdges {s(s, t)}).edgeSet := by
        intro e he
        rw [SimpleGraph.edgeSet_deleteEdges]
        exact ⟨w.edges_subset_edgeSet he, hw e he⟩
      obtain ⟨v, hv, hvT⟩ := hT x hx y hy (w.transfer _ hE)
      rw [SimpleGraph.Walk.support_transfer] at hv
      exact ⟨v, hv, Finset.mem_insert_of_mem hvT⟩
  have hc := hK.1 _ hsep
  have hc2 : (insert s T).card ≤ n := (Finset.card_insert_le _ _).trans (by omega)
  exact ⟨insert s T, Finset.mem_insert_self _ _, le_antisymm hc2 hc, hsep⟩

end Menger27.Graphs

open Menger27.Graphs


theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (P Q : Finset V) (hPQ : Disjoint P Q) (n : ℕ) (hG : NPointConnected G P Q n) :
    ∃ K : SimpleGraph V, K ≤ G ∧ IrreduciblyNPointConnected K P Q n := by
  exact exists_irreducible_part_core G P Q hPQ n hG
