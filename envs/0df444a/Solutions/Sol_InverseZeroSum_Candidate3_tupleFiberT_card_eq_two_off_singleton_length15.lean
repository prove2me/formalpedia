-- Prove2me | solution 1 for InverseZeroSum.Candidate3.tupleFiberT_card_eq_two_off_singleton_length15
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:46:58.795965+00:00
-- url     : https://prove2.me/submissions/b30c6ea8-68e4-487c-a0c1-f009b720d231

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
theorem _root_.solution
    (R : PosSeq 15) (hFree : ShortFree R)
    {u : F3T} (hu : u ∈ tupleSupportT R)
    (huOne :
      ((Finset.univ : Finset (Fin 15)).filter
        (fun i => tupleValueT R i = u)).card = 1) :
    ∀ x ∈ (tupleSupportT R).erase u,
      ((Finset.univ : Finset (Fin 15)).filter
        (fun i => tupleValueT R i = x)).card = 2 := by
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
        ∑ y ∈ tupleSupportT R,
          ((Finset.univ : Finset (Fin 15)).filter
            (fun i => tupleValueT R i = y)).card := by
    simpa using hFiberSum0
  have hSplitU :
      (∑ y ∈ tupleSupportT R,
        ((Finset.univ : Finset (Fin 15)).filter
          (fun i => tupleValueT R i = y)).card) =
        (∑ y ∈ (tupleSupportT R).erase u,
          ((Finset.univ : Finset (Fin 15)).filter
            (fun i => tupleValueT R i = y)).card) +
        ((Finset.univ : Finset (Fin 15)).filter
          (fun i => tupleValueT R i = u)).card := by
    exact
      (Finset.sum_erase_add (tupleSupportT R)
        (fun y =>
          ((Finset.univ : Finset (Fin 15)).filter
            (fun i => tupleValueT R i = y)).card) hu).symm
  have hOtherSum :
      (∑ y ∈ (tupleSupportT R).erase u,
        ((Finset.univ : Finset (Fin 15)).filter
          (fun i => tupleValueT R i = y)).card) = 14 := by
    rw [hSplitU, huOne] at hFiberSum
    omega
  have hEraseCard : ((tupleSupportT R).erase u).card = 7 := by
    rw [Finset.card_erase_of_mem hu, hSupportCard]
  intro x hx
  have hxSupport : x ∈ tupleSupportT R := Finset.mem_of_mem_erase hx
  have hxLe := tupleFiberT_card_le_two R hFree x hxSupport
  by_contra hxNe
  have hxLeOne :
      ((Finset.univ : Finset (Fin 15)).filter
        (fun i => tupleValueT R i = x)).card ≤ 1 := by
    omega
  have hRestCard : (((tupleSupportT R).erase u).erase x).card = 6 := by
    rw [Finset.card_erase_of_mem hx, hEraseCard]
  have hRestLe :
      (∑ y ∈ ((tupleSupportT R).erase u).erase x,
        ((Finset.univ : Finset (Fin 15)).filter
          (fun i => tupleValueT R i = y)).card) ≤ 12 := by
    calc
      (∑ y ∈ ((tupleSupportT R).erase u).erase x,
        ((Finset.univ : Finset (Fin 15)).filter
          (fun i => tupleValueT R i = y)).card)
          ≤ ∑ _y ∈ ((tupleSupportT R).erase u).erase x, 2 := by
            exact Finset.sum_le_sum
              (fun y hy =>
                tupleFiberT_card_le_two R hFree y
                  (Finset.mem_of_mem_erase
                    (Finset.mem_of_mem_erase hy)))
      _ = 12 := by simp [hRestCard]
  have hSplitX :
      (∑ y ∈ (tupleSupportT R).erase u,
        ((Finset.univ : Finset (Fin 15)).filter
          (fun i => tupleValueT R i = y)).card) =
        (∑ y ∈ ((tupleSupportT R).erase u).erase x,
          ((Finset.univ : Finset (Fin 15)).filter
            (fun i => tupleValueT R i = y)).card) +
        ((Finset.univ : Finset (Fin 15)).filter
          (fun i => tupleValueT R i = x)).card := by
    exact
      (Finset.sum_erase_add ((tupleSupportT R).erase u)
        (fun y =>
          ((Finset.univ : Finset (Fin 15)).filter
            (fun i => tupleValueT R i = y)).card) hx).symm
  rw [hSplitX] at hOtherSum
  omega
end InverseZeroSum.Candidate3
