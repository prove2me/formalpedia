-- Prove2me | solution 1 for InverseZeroSum.Candidate3.exists_tupleFiberT_card_eq_one_length15
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:46:59.4818+00:00
-- url     : https://prove2.me/submissions/c2cd68f9-c7d6-4eca-8572-d28e8fc4a842

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
public import Theorems.Thm_InverseZeroSum_Candidate3_tupleFiberT_card_le_two
public import Theorems.Thm_InverseZeroSum_Candidate3_tupleSupportT_card_eq_eight_length15
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
    ∃ u ∈ tupleSupportT R,
      ((Finset.univ : Finset (Fin 15)).filter
        (fun i => tupleValueT R i = u)).card = 1 := by
  classical
  have hSupportCard := tupleSupportT_card_eq_eight_length15 R hFree
  have hMaps :
      ∀ i ∈ (Finset.univ : Finset (Fin 15)),
        tupleValueT R i ∈ tupleSupportT R := by
    intro i hi
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  have hFiberSum0 :=
    Finset.card_eq_sum_card_fiberwise
      (f := tupleValueT R) (s := (Finset.univ : Finset (Fin 15)))
      (t := tupleSupportT R) hMaps
  have hFiberSum :
      15 =
        ∑ x ∈ tupleSupportT R,
          ((Finset.univ : Finset (Fin 15)).filter
            (fun i => tupleValueT R i = x)).card := by
    simpa using hFiberSum0
  by_contra hNo
  have hNotOne :
      ∀ x ∈ tupleSupportT R,
        ((Finset.univ : Finset (Fin 15)).filter
          (fun i => tupleValueT R i = x)).card ≠ 1 := by
    intro x hx hOne
    exact hNo ⟨x, hx, hOne⟩
  have hAllTwo :
      ∀ x ∈ tupleSupportT R,
        ((Finset.univ : Finset (Fin 15)).filter
          (fun i => tupleValueT R i = x)).card = 2 := by
    intro x hx
    have hLe := tupleFiberT_card_le_two R hFree x hx
    have hNeOne := hNotOne x hx
    have hPos :
        0 <
          ((Finset.univ : Finset (Fin 15)).filter
            (fun i => tupleValueT R i = x)).card := by
      obtain ⟨i, _hi, hiEq⟩ := Finset.mem_image.mp hx
      apply Finset.card_pos.mpr
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiEq⟩⟩
    omega
  have hSixteen :
      (∑ x ∈ tupleSupportT R,
        ((Finset.univ : Finset (Fin 15)).filter
          (fun i => tupleValueT R i = x)).card) = 16 := by
    calc
      (∑ x ∈ tupleSupportT R,
        ((Finset.univ : Finset (Fin 15)).filter
          (fun i => tupleValueT R i = x)).card) =
          ∑ _x ∈ tupleSupportT R, 2 := by
            exact Finset.sum_congr rfl (fun x hx => hAllTwo x hx)
      _ = 16 := by simp [hSupportCard]
  omega
end InverseZeroSum.Candidate3
