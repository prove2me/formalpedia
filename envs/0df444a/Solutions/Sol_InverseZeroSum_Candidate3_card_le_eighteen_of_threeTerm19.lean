-- Prove2me | solution 1 for InverseZeroSum.Candidate3.card_le_eighteen_of_threeTerm19
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:37:42.069801+00:00
-- url     : https://prove2.me/submissions/53a36311-3d2b-4b01-aaac-8ab7dae9ed2a

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_shortZero_map_pullSeq
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
attribute [local simp] InverseZeroSum.Candidate3.baseIndex_val
attribute [local simp] InverseZeroSum.Candidate3.mem_s039AllBlocks
attribute [local simp] InverseZeroSum.Candidate3.planeSetT_card

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution (h19 : ThreeTerm19Input)
    (S : PosSeq 24) {A : Finset (Fin 24)}
    (hNoThree :
      ∀ I : Finset (Fin 24), I ⊆ A → I.card = 3 → posSum S I ≠ 0) :
    A.card ≤ 18 := by
  classical
  by_contra h
  have h19le : 19 ≤ A.card := by omega
  let eOrder : Fin 19 ↪o Fin 24 := A.orderEmbOfCardLe h19le
  let e : Fin 19 ↪ Fin 24 := eOrder.toEmbedding
  let R : PosSeq 19 := pullSeq S e
  obtain ⟨I, hCard, hZero⟩ := h19 R
  have hShort : ShortZero R I := by
    refine ⟨Finset.card_pos.mp (by omega), by omega, hZero⟩
  have hMap : ShortZero S (I.map e) :=
    shortZero_map_pullSeq S e hShort
  have hSub : I.map e ⊆ A := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    simpa [e, eOrder] using Finset.orderEmbOfCardLe_mem A h19le i
  have hMapCard : (I.map e).card = 3 := by
    simpa using hCard
  exact (hNoThree (I.map e) hSub hMapCard) hMap.2.2
end InverseZeroSum.Candidate3
