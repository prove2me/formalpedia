-- Prove2me | solution 1 for InverseZeroSum.Candidate3.tupleFiberT_card_eq_two_length16
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:46:36.083024+00:00
-- url     : https://prove2.me/submissions/0275e5c8-8b58-48c1-a235-e0751be7d973

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
public import Theorems.Thm_InverseZeroSum_Candidate3_tupleFiberT_card_le_two
public import Theorems.Thm_InverseZeroSum_Candidate3_tupleSupportT_card_eq_eight_length16
attribute [local simp] InverseZeroSum.Candidate3.baseIndex_val
attribute [local simp] InverseZeroSum.Candidate3.mem_s039AllBlocks
attribute [local simp] InverseZeroSum.Candidate3.planeSetT_card

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution (R : PosSeq 16)
    (hFree : ShortFree R) :
    ∀ x ∈ tupleSupportT R,
      ((Finset.univ : Finset (Fin 16)).filter
        (fun i => tupleValueT R i = x)).card = 2 := by
  classical
  intro x hx
  have hxle := tupleFiberT_card_le_two R hFree x hx
  by_contra hne
  have hxle1 :
      ((Finset.univ : Finset (Fin 16)).filter
        (fun i => tupleValueT R i = x)).card ≤ 1 := by
    omega
  have hSupportCard := tupleSupportT_card_eq_eight_length16 R hFree
  have hMaps :
      ∀ i ∈ (Finset.univ : Finset (Fin 16)),
        tupleValueT R i ∈ tupleSupportT R := by
    intro i hi
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  have hFiberSum0 :=
    Finset.card_eq_sum_card_fiberwise
      (f := tupleValueT R) (s := (Finset.univ : Finset (Fin 16)))
      (t := tupleSupportT R) hMaps
  have hFiberSum :
      16 =
        ∑ y ∈ tupleSupportT R,
          ((Finset.univ : Finset (Fin 16)).filter
            (fun i => tupleValueT R i = y)).card := by
    simpa using hFiberSum0
  have hEraseCard : ((tupleSupportT R).erase x).card = 7 := by
    rw [Finset.card_erase_of_mem hx, hSupportCard]
  have hOther :
      (∑ y ∈ (tupleSupportT R).erase x,
        ((Finset.univ : Finset (Fin 16)).filter
          (fun i => tupleValueT R i = y)).card) ≤ 14 := by
    calc
      (∑ y ∈ (tupleSupportT R).erase x,
        ((Finset.univ : Finset (Fin 16)).filter
          (fun i => tupleValueT R i = y)).card)
          ≤ ∑ _y ∈ (tupleSupportT R).erase x, 2 := by
            exact Finset.sum_le_sum
              (fun y hy =>
                tupleFiberT_card_le_two R hFree y
                  (Finset.mem_of_mem_erase hy))
      _ = 14 := by simp [hEraseCard]
  have hSplit :
      (∑ y ∈ tupleSupportT R,
        ((Finset.univ : Finset (Fin 16)).filter
          (fun i => tupleValueT R i = y)).card) =
        (∑ y ∈ (tupleSupportT R).erase x,
          ((Finset.univ : Finset (Fin 16)).filter
            (fun i => tupleValueT R i = y)).card) +
        ((Finset.univ : Finset (Fin 16)).filter
          (fun i => tupleValueT R i = x)).card := by
    exact
      (Finset.sum_erase_add (tupleSupportT R)
        (fun y =>
          ((Finset.univ : Finset (Fin 16)).filter
            (fun i => tupleValueT R i = y)).card) hx).symm
  rw [hSplit] at hFiberSum
  omega
end InverseZeroSum.Candidate3
