-- Prove2me | solution 1 for NashWilliams.sum_ncard_le_of_pairwise_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:45:45.689967+00:00
-- url     : https://prove2.me/submissions/c9248206-c653-434d-9abf-489ab052034e

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
theorem _root_.solution {ι α : Type*} [Fintype ι] [Finite α] (A : ι → Set α)
    (B : Set α) (hAB : ∀ i, A i ⊆ B) (hd : Pairwise (Disjoint on A)) :
    ∑ i, (A i).ncard ≤ B.ncard := by
  have h := Set.ncard_iUnion_of_finite (s := A) (fun i ↦ Set.toFinite _) hd
  rw [finsum_eq_sum_of_fintype] at h
  rw [← h]
  exact Set.ncard_le_ncard (Set.iUnion_subset hAB)
end NashWilliams
