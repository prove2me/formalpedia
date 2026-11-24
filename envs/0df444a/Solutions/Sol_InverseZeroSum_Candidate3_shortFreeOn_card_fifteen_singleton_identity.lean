-- Prove2me | solution 1 for InverseZeroSum.Candidate3.shortFreeOn_card_fifteen_singleton_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:49:52.228143+00:00
-- url     : https://prove2.me/submissions/21dc65e5-5c04-4802-b3f7-9f07861a66cc

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_shortZero_map_pullSeq
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
public import Theorems.Thm_InverseZeroSum_Candidate3_tupleFiberT_card_le_two
public import Theorems.Thm_InverseZeroSum_Candidate3_exists_tupleFiberT_card_eq_one_length15
public import Theorems.Thm_InverseZeroSum_Candidate3_length15_singleton_sum_identity
public import Theorems.Thm_InverseZeroSum_Candidate3_length15_singleton_unique
attribute [local simp] InverseZeroSum.Candidate3.baseIndex_val
attribute [local simp] InverseZeroSum.Candidate3.mem_s039AllBlocks
attribute [local simp] InverseZeroSum.Candidate3.planeSetT_card

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000
namespace InverseZeroSum.Candidate3
theorem _root_.solution
    (S : PosSeq 24) {A : Finset (Fin 24)}
    (hCard : A.card = 15) (hFree : ShortFreeOn S A) :
    ∃ u : F3T,
      (A.filter (fun i => finiteModelEquiv (S i : G) = u)).card = 1 ∧
      (∀ v : F3T,
        (A.filter (fun i => finiteModelEquiv (S i : G) = v)).card ≤ 2) ∧
      (∀ v : F3T,
        (A.filter (fun i => finiteModelEquiv (S i : G) = v)).card = 1 →
          v = u) ∧
      (∑ i ∈ A, finiteModelEquiv (S i : G)) + u = 0 := by
  classical
  have h15le : 15 ≤ A.card := by omega
  let eOrder : Fin 15 ↪o Fin 24 := A.orderEmbOfCardLe h15le
  let e : Fin 15 ↪ Fin 24 := eOrder.toEmbedding
  let R : PosSeq 15 := pullSeq S e
  have hRFree : ShortFree R := by
    intro I hShort
    have hMap : ShortZero S (I.map e) :=
      shortZero_map_pullSeq S e hShort
    have hSub : I.map e ⊆ A := by
      intro x hx
      obtain ⟨i, _hi, rfl⟩ := Finset.mem_map.mp hx
      simpa [e, eOrder] using Finset.orderEmbOfCardLe_mem A h15le i
    exact (hFree (I.map e) hSub) hMap
  have hMapSub : Finset.univ.map e ⊆ A := by
    intro x hx
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_map.mp hx
    simpa [e, eOrder] using Finset.orderEmbOfCardLe_mem A h15le i
  have hMapCard : (Finset.univ.map e).card = 15 := by simp
  have hMapEq : Finset.univ.map e = A := by
    apply Finset.eq_of_subset_of_card_le hMapSub
    rw [hCard, hMapCard]
  have hFilterMap (v : F3T) :
      ((Finset.univ : Finset (Fin 15)).filter
        (fun i => tupleValueT R i = v)).map e =
      A.filter (fun k => finiteModelEquiv (S k : G) = v) := by
    rw [← hMapEq]
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
      have hiEq : finiteModelEquiv (S (e i) : G) = v := by
        simpa [R, tupleValueT, pullSeq] using (Finset.mem_filter.mp hi).2
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩, hiEq⟩
    · intro hx
      obtain ⟨hxMap, hxEq⟩ := Finset.mem_filter.mp hx
      obtain ⟨i, _hi, rfl⟩ := Finset.mem_map.mp hxMap
      have hiEq : tupleValueT R i = v := by
        simpa [R, tupleValueT, pullSeq] using hxEq
      exact Finset.mem_map.mpr
        ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiEq⟩, rfl⟩
  have hFiberEq (v : F3T) :
      (A.filter (fun k => finiteModelEquiv (S k : G) = v)).card =
        ((Finset.univ : Finset (Fin 15)).filter
          (fun i => tupleValueT R i = v)).card := by
    rw [← hFilterMap v]
    simp
  have hSumEq :
      (∑ i ∈ A, finiteModelEquiv (S i : G)) =
        ∑ i ∈ (Finset.univ : Finset (Fin 15)), tupleValueT R i := by
    rw [← hMapEq]
    simp [R, tupleValueT, pullSeq]
  obtain ⟨u, hu, huOne⟩ :=
    exists_tupleFiberT_card_eq_one_length15 R hRFree
  refine ⟨u, ?_, ?_, ?_, ?_⟩
  · rw [hFiberEq]
    exact huOne
  · intro v
    rw [hFiberEq]
    by_cases hv : v ∈ tupleSupportT R
    · exact tupleFiberT_card_le_two R hRFree v hv
    · have hEmpty :
          ((Finset.univ : Finset (Fin 15)).filter
            (fun i => tupleValueT R i = v)) = ∅ := by
        ext i
        constructor
        · intro hi
          exact (hv (Finset.mem_image.mpr
            ⟨i, Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩)).elim
        · intro hi
          simp at hi
      simp [hEmpty]
  · intro v hvOne
    have hvOneR :
        ((Finset.univ : Finset (Fin 15)).filter
          (fun i => tupleValueT R i = v)).card = 1 := by
      rw [hFiberEq] at hvOne
      exact hvOne
    have hvSupport : v ∈ tupleSupportT R := by
      have hPos :
          0 < ((Finset.univ : Finset (Fin 15)).filter
            (fun i => tupleValueT R i = v)).card := by omega
      obtain ⟨i, hi⟩ := Finset.card_pos.mp hPos
      exact Finset.mem_image.mpr
        ⟨i, Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
    exact length15_singleton_unique R hRFree hu huOne hvSupport hvOneR
  · rw [hSumEq]
    exact length15_singleton_sum_identity R hRFree hu huOne
end InverseZeroSum.Candidate3
