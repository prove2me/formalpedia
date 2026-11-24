-- Prove2me | solution 1 for InverseZeroSum.Candidate3.tupleSupportT_card_eq_eight_length15
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:45:35.194165+00:00
-- url     : https://prove2.me/submissions/882504ad-b2de-4528-b214-c581e68f76aa

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
public import Theorems.Thm_InverseZeroSum_Candidate3_tupleFiberT_card_le_two
public import Theorems.Thm_InverseZeroSum_Candidate3_tupleSupportT_card_le_eight
attribute [local simp] InverseZeroSum.Candidate3.baseIndex_val
attribute [local simp] InverseZeroSum.Candidate3.mem_s039AllBlocks
attribute [local simp] InverseZeroSum.Candidate3.planeSetT_card

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution (R : PosSeq 15)
    (hFree : ShortFree R) :
    (tupleSupportT R).card = 8 := by
  classical
  have hMaps :
      ∀ i ∈ (Finset.univ : Finset (Fin 15)),
        tupleValueT R i ∈ tupleSupportT R := by
    intro i hi
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  have hBound :=
    Finset.card_le_mul_card_image_of_maps_to hMaps 2
      (tupleFiberT_card_le_two R hFree)
  have hBound' : 15 ≤ 2 * (tupleSupportT R).card := by
    simpa using hBound
  have hLe := tupleSupportT_card_le_eight R hFree
  omega
end InverseZeroSum.Candidate3
