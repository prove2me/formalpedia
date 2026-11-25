-- Prove2me | solution 1 for NashWilliams.IsAcyclic.ncard_edgeSet_add_one_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:45:53.20505+00:00
-- url     : https://prove2.me/submissions/168affb9-d6c3-4bca-9fe6-db76d1db5d0b

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
namespace IsAcyclic
theorem _root_.solution [Finite V] [Nonempty V] {F : SimpleGraph V}
    (hF : F.IsAcyclic) :
    F.edgeSet.ncard + 1 ≤ Nat.card V ∧ (Nat.card V ≤ F.edgeSet.ncard + 1 → F.IsTree) := by
  obtain ⟨T, hFT, hT⟩ := exists_maximal_isAcyclic_of_le_isAcyclic (le_top : F ≤ ⊤) hF
  have hT' : T.IsTree := by
    rw [← maximal_isAcyclic_iff_isTree]
    exact ⟨hT.1.2, fun H hH hle ↦ hT.2 ⟨le_top, hH⟩ hle⟩
  have hcard := (isTree_iff_connected_and_card.1 hT').2
  rw [Nat.card_coe_set_eq] at hcard
  have hsub : F.edgeSet ⊆ T.edgeSet := edgeSet_mono hFT
  have hle : F.edgeSet.ncard ≤ T.edgeSet.ncard := Set.ncard_le_ncard hsub
  refine ⟨by omega, fun h ↦ ?_⟩
  have heq : F.edgeSet = T.edgeSet := Set.eq_of_subset_of_ncard_le hsub (by omega)
  rwa [edgeSet_inj.1 heq]
end IsAcyclic
end NashWilliams
