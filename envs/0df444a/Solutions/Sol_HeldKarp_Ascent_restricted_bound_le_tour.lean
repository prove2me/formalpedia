-- Prove2me | solution 1 for HeldKarp.Ascent.restricted_bound_le_tour
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:04:04.580585+00:00
-- url     : https://prove2.me/submissions/eb15cc2c-4e60-4b5b-b82a-96627bc2fc4d

import Definitions.Def_HeldKarp_Ascent_IsOneTree
import Definitions.Def_HeldKarp_Ascent_oneTreeBound
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Tactic
open Classical
open scoped BigOperators
namespace HeldKarp.Ascent
private lemma tour_oneTree {n : ℕ} [NeZero n] (G : SimpleGraph (Fin n))
    (hG : IsTour G) : IsOneTree G := by
  classical
  have hc : G.IsCycles := by
    intro v _
    rw [Set.ncard_eq_toFinset_card']
    exact (G.card_neighborFinset_eq_degree v).trans (hG.2 v)
  obtain ⟨w, hw⟩ := (G.degree_pos_iff_exists_adj 0).mp (by rw [hG.2]; norm_num)
  let T := G.deleteEdges {s(0,w)}
  have hconn : T.Connected := hG.1.connected_delete_edge_of_not_isBridge
    (by simpa only [SimpleGraph.isBridge_iff, not_not] using hc.reachable_deleteEdges hw)
  have hcard : G.edgeFinset.card = n := by
    have hh := G.sum_degrees_eq_twice_card_edges
    simp only [hG.2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hh
    omega
  have he : s(0,w) ∈ G.edgeFinset := by simpa using hw
  have htcard : T.edgeFinset.card = n-1 := by
    have heq : T = G.deleteEdges (↑({s(0,w)} : Finset _) : Set _) := by simp [T]
    have hed : T.edgeFinset = G.edgeFinset.erase s(0,w) := by
      ext e
      simp [T, and_comm]
    rw [hed, Finset.card_erase_of_mem he, hcard]
  have htree : T.IsTree := by
    apply SimpleGraph.isTree_iff_connected_and_card.mpr
    refine ⟨hconn, ?_⟩
    rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, htcard, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    have := NeZero.ne n
    omega
  have hdeg : T.degree 0 = 1 := by
    rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
    obtain ⟨u, ⟨hu, hadj⟩, huniq⟩ := hc.existsUnique_ne_adj hw
    refine ⟨u, ?_, ?_⟩
    · simp only [T, SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_iff]
      exact ⟨hadj, by aesop⟩
    · intro v hv
      simp only [T, SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_iff] at hv
      exact huniq v ⟨by aesop, hv.1⟩
  have hind : T.induce {v : Fin n | v ≠ 0} = G.induce {v : Fin n | v ≠ 0} := by
    ext u v
    simp only [SimpleGraph.induce_adj, T, SimpleGraph.deleteEdges_adj,
      Set.mem_singleton_iff, Sym2.eq_iff, and_iff_left_iff_imp]
    intro _
    have hu := u.property
    have hv := v.property
    aesop
  refine ⟨?_, hG.2 0⟩
  rw [← hind]
  exact ⟨by
      have hs : {v : Fin n | v ≠ 0} = ({0} : Set (Fin n))ᶜ := by ext; simp
      rw [hs]
      exact hconn.induce_compl_singleton_of_degree_eq_one hdeg,
    htree.isAcyclic.induce _⟩


private lemma tour_lagr {n : ℕ} [NeZero n] (c : Sym2 (Fin n) → ℝ) (π : Fin n → ℝ)
    (H : SimpleGraph (Fin n)) (hH : IsTour H) : lagrWeight c π H = weight c H := by
  simp [lagrWeight, degExcess, hH.2]

theorem _root_.solution {n : ℕ} [NeZero n] (hn : 3 ≤ n) (c : Sym2 (Fin n) → ℝ)
    (X Y : Set (Sym2 (Fin n))) (π : Fin n → ℝ) (H : SimpleGraph (Fin n)) (hH : IsTour H)
    (hX : X ⊆ H.edgeSet) (hY : Disjoint Y H.edgeSet) :
    restrictedBound c X Y π ≤ weight c H := by
  rw [← tour_lagr c π H hH]
  apply csInf_le
  · apply (Set.finite_range (lagrWeight c π)).bddBelow.mono
    rintro x ⟨G, hG, hx, hy, rfl⟩
    exact ⟨G, rfl⟩
  · exact ⟨H, tour_oneTree H hH, hX, hY, rfl⟩
end HeldKarp.Ascent
