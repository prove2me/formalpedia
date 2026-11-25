-- Prove2me | solution 1 for NashWilliams.card_le_ncard_edgeSet_add_card_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:51:15.832277+00:00
-- url     : https://prove2.me/submissions/ea86e4a2-88b8-47c2-8e97-554234478bd0

module
public import Mathlib
public import Definitions.Def_TreePackingLib_NashWilliamsAux

set_option autoImplicit true
@[expose] public section
public section
open Finset Fintype SimpleGraph Function
open NashWilliams
variable {V : Type*}
namespace NashWilliams
theorem _root_.solution [Fintype V] [DecidableEq V] [Nonempty V]
    (K : SimpleGraph V) (f : V → V) (hf : ∀ v, K.Reachable v (f v)) :
    Nat.card V ≤ K.edgeSet.ncard + #(univ.image f) := by
  set r₀ := f (Classical.arbitrary V)
  have hr₀ : r₀ ∈ univ.image f := mem_image_of_mem _ (mem_univ _)
  set St : Set (Sym2 V) := (fun r ↦ s(r₀, r)) '' ↑((univ.image f).erase r₀)
  set L := K ⊔ fromEdgeSet St
  have hreach : ∀ a, L.Reachable a r₀ := by
    intro a
    refine ((hf a).mono le_sup_left).trans ?_
    by_cases ha : f a = r₀
    · rw [ha]
    · refine Adj.reachable (Or.inr ?_)
      refine ⟨⟨f a, ?_, ?_⟩, ha⟩
      · simp [ha]
      · exact Sym2.eq_swap
  have hL : L.Connected := by
    have : Nonempty V := inferInstance
    exact Connected.mk fun a b ↦ (hreach a).trans (hreach b).symm
  have h1 := hL.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_coe_set_eq] at h1
  have h2 : L.edgeSet.ncard ≤ K.edgeSet.ncard + St.ncard := by
    refine (Set.ncard_le_ncard (t := K.edgeSet ∪ St) ?_).trans (Set.ncard_union_le _ _)
    rw [edgeSet_sup, edgeSet_fromEdgeSet]
    exact Set.union_subset_union_right _ Set.sdiff_subset
  have h3 : St.ncard ≤ #(univ.image f) - 1 := by
    refine (Set.ncard_image_le (Set.toFinite _)).trans ?_
    rw [Set.ncard_coe_finset, card_erase_of_mem hr₀]
  have h4 : 1 ≤ #(univ.image f) := card_pos.2 ⟨_, hr₀⟩
  omega
end NashWilliams
