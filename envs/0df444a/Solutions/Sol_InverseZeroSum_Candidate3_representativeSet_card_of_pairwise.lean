-- Prove2me | solution 1 for InverseZeroSum.Candidate3.representativeSet_card_of_pairwise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:25:57.651094+00:00
-- url     : https://prove2.me/submissions/1d1171da-b8ad-4e88-9fb3-a85a5e7e6571

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
attribute [local simp] InverseZeroSum.Candidate3.baseIndex_val
attribute [local simp] InverseZeroSum.Candidate3.mem_s039AllBlocks

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution {s : ℕ}
    {blocks : Fin s → Finset (Fin 24)} {rep : Fin s → Fin 24}
    (hBlocks : ∀ i j, i ≠ j → Disjoint (blocks i) (blocks j))
    (hRep : ∀ j, rep j ∈ blocks j) :
    (representativeSet rep).card = s := by
  classical
  have hInj : Function.Injective rep := by
    intro i j hij
    by_contra hne
    have hDisj := hBlocks i j hne
    have hmemj : rep i ∈ blocks j := by
      rw [hij]
      exact hRep j
    exact (Finset.disjoint_left.mp hDisj) (hRep i) hmemj
  simpa [representativeSet] using
    Finset.card_image_of_injective (Finset.univ : Finset (Fin s)) hInj
end InverseZeroSum.Candidate3
