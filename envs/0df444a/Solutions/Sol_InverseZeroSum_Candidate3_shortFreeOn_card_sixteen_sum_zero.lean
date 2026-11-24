-- Prove2me | solution 1 for InverseZeroSum.Candidate3.shortFreeOn_card_sixteen_sum_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:39:06.763566+00:00
-- url     : https://prove2.me/submissions/4737ce94-0efd-401a-bcd4-9d5a709e55ab

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
theorem _root_.solution
    (h16 : Length16SumZeroInput) (S : PosSeq 24)
    {A : Finset (Fin 24)} (hCard : A.card = 16)
    (hFree : ShortFreeOn S A) :
    posSum S A = 0 := by
  classical
  have h16le : 16 ≤ A.card := by omega
  let eOrder : Fin 16 ↪o Fin 24 := A.orderEmbOfCardLe h16le
  let e : Fin 16 ↪ Fin 24 := eOrder.toEmbedding
  let R : PosSeq 16 := pullSeq S e
  have hRFree : ShortFree R := by
    intro I hShort
    have hMap : ShortZero S (I.map e) :=
      shortZero_map_pullSeq S e hShort
    have hSub : I.map e ⊆ A := by
      intro x hx
      obtain ⟨i, _hi, rfl⟩ := Finset.mem_map.mp hx
      simpa [e, eOrder] using Finset.orderEmbOfCardLe_mem A h16le i
    exact (hFree (I.map e) hSub) hMap
  have hRZero : totalSum R = 0 :=
    h16 R hRFree
  have hMapSub : Finset.univ.map e ⊆ A := by
    intro x hx
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_map.mp hx
    simpa [e, eOrder] using Finset.orderEmbOfCardLe_mem A h16le i
  have hMapCard : (Finset.univ.map e).card = 16 := by
    simp
  have hMapEq : Finset.univ.map e = A := by
    apply Finset.eq_of_subset_of_card_le hMapSub
    rw [hCard, hMapCard]
  have hMapZero : posSum S (Finset.univ.map e) = 0 := by
    simpa [R, totalSum, posSum, pullSeq] using hRZero
  simpa [hMapEq] using hMapZero
end InverseZeroSum.Candidate3
