-- Prove2me | solution 1 for NashWilliams.arboricity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:29:24.086663+00:00
-- url     : https://prove2.me/submissions/f3d1a861-2bc0-4bd3-91f1-4d21cc470834

module
public import Mathlib
public import Definitions.Def_TreePackingLib_NashWilliamsAux
public import Definitions.Def_TreePackingLib_NashWilliams
public import Theorems.Thm_NashWilliams_IsAcyclic_ncard_edgeSet_add_one_le
public import Theorems.Thm_NashWilliams_exists_forests_core
public import Theorems.Thm_NashWilliams_sum_ncard_le_of_pairwise_disjoint


set_option autoImplicit true
@[expose] public section
public section
open Finset Fintype SimpleGraph
open NashWilliams
namespace NashWilliams
theorem _root_.solution {V : Type*} [Finite V] (G : SimpleGraph V) (k : ℕ) :
    (∃ F : Fin k → SimpleGraph V, (∀ i, F i ≤ G ∧ (F i).IsAcyclic) ∧ G = ⨆ i, F i) ↔
      ∀ S : Finset V, S.Nonempty → (G.induce (S : Set V)).edgeSet.ncard ≤ k * (#S - 1) := by
  constructor
  · rintro ⟨F, hF, hG⟩ S hS
    have : Nonempty (S : Set V) := ⟨⟨hS.choose, hS.choose_spec⟩⟩
    have hcardS : Nat.card (S : Set V) = #S := by
      rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
    have hsub : (G.induce (S : Set V)).edgeSet ⊆ ⋃ i, ((F i).induce (S : Set V)).edgeSet := by
      intro e he
      induction e using Sym2.ind with
      | _ a b =>
        have hab : G.Adj a b := he
        rw [hG, iSup_adj] at hab
        obtain ⟨i, hi⟩ := hab
        exact Set.mem_iUnion.2 ⟨i, hi⟩
    calc (G.induce (S : Set V)).edgeSet.ncard
        ≤ ∑ i, ((F i).induce (S : Set V)).edgeSet.ncard :=
          (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_iUnion_le_of_fintype _)
      _ ≤ ∑ _i : Fin k, (#S - 1) := sum_le_sum fun i _ ↦ by
          have := (IsAcyclic.ncard_edgeSet_add_one_le ((hF i).2.induce (S : Set V))).1
          omega
      _ = k * (#S - 1) := by simp
  · intro hcond
    have := Fintype.ofFinite V
    classical
    obtain ⟨F, H, hF, hdisj, -, hreach, hcov⟩ := exists_forests_core G k
    refine ⟨F, hF, le_antisymm (fun u v huv ↦ ?_) (iSup_le fun i ↦ (hF i).1)⟩
    rw [iSup_adj]
    by_contra hnot
    have hH : H.Adj u v := by
      by_contra h
      exact hnot (hcov u v huv h)
    let S : Finset V := univ.filter fun w ↦ H.Reachable u w
    have hu : u ∈ S := by simp [S]
    have hv : v ∈ S := by simpa [S] using hH.reachable
    have hcardS : Nat.card (S : Set V) = #S := by
      rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
    have hconn : ∀ i, ((F i ⊓ H).induce (S : Set V)).Connected := by
      intro i
      have hS : (S : Set V) = ((F i ⊓ H).connectedComponentMk u).supp := by
        ext w
        simp only [S, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq,
          ConnectedComponent.mem_supp_iff, ConnectedComponent.eq]
        exact ⟨fun h ↦ (hreach i u w h).symm, fun h ↦ (h.mono inf_le_right).symm⟩
      rw [hS]
      exact ((F i ⊓ H).connectedComponentMk u).connected_toSimpleGraph
    let e : Sym2 (S : Set V) := s(⟨u, hu⟩, ⟨v, hv⟩)
    have he : e ∈ (G.induce (S : Set V)).edgeSet := huv
    have h1 := sum_ncard_le_of_pairwise_disjoint
      (fun i ↦ ((F i ⊓ H).induce (S : Set V)).edgeSet) ((G.induce (S : Set V)).edgeSet \ {e})
      (fun i x hx ↦ by
        induction x using Sym2.ind with
        | _ a b =>
          have hab : (F i ⊓ H).Adj a b := hx
          refine ⟨(hF i).1 hab.1, fun h ↦ ?_⟩
          rcases Sym2.eq_iff.1 (Set.mem_singleton_iff.1 h) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hnot ⟨i, hab.1⟩
          · exact hnot ⟨i, hab.1.symm⟩)
      (fun i j hij ↦ by
        rw [Function.onFun, disjoint_edgeSet, disjoint_iff_adj]
        intro a b hi hj
        exact disjoint_iff_adj.1 (hdisj hij) a b hi.1 hj.1)
    have h2 := Set.ncard_sdiff_singleton_add_one he (Set.toFinite _)
    have h3 := hcond S ⟨u, hu⟩
    have h4 : ∑ _i : Fin k, (#S - 1) ≤ ∑ i, ((F i ⊓ H).induce (S : Set V)).edgeSet.ncard :=
      sum_le_sum fun i _ ↦ by
        have := (hconn i).card_vert_le_card_edgeSet_add_one
        rw [Nat.card_coe_set_eq (((F i ⊓ H).induce (S : Set V)).edgeSet), hcardS] at this
        omega
    simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h4
    omega
end NashWilliams
