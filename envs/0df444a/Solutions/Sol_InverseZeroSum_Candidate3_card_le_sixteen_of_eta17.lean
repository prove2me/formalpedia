-- Prove2me | solution 1 for InverseZeroSum.Candidate3.card_le_sixteen_of_eta17
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:37:40.811611+00:00
-- url     : https://prove2.me/submissions/a8f13618-6cc8-4b11-8dfe-914a30db9d0f

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
theorem _root_.solution (hEta : Eta17Input)
    (S : PosSeq 24) {A : Finset (Fin 24)} (hFree : ShortFreeOn S A) :
    A.card ≤ 16 := by
  classical
  by_contra h
  have h17 : 17 ≤ A.card := by omega
  let eOrder : Fin 17 ↪o Fin 24 := A.orderEmbOfCardLe h17
  let e : Fin 17 ↪ Fin 24 := eOrder.toEmbedding
  let R : PosSeq 17 := pullSeq S e
  obtain ⟨I, hI⟩ := hEta R
  have hMap : ShortZero S (I.map e) :=
    shortZero_map_pullSeq S e hI
  have hSub : I.map e ⊆ A := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    simpa [e, eOrder] using Finset.orderEmbOfCardLe_mem A h17 i
  exact (hFree (I.map e) hSub) hMap
end InverseZeroSum.Candidate3
