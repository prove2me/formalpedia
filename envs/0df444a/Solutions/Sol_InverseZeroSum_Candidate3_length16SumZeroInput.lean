-- Prove2me | solution 1 for InverseZeroSum.Candidate3.length16SumZeroInput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:47:57.408286+00:00
-- url     : https://prove2.me/submissions/ec4594dd-6d17-4884-9350-0499d01ffd76

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
public import Theorems.Thm_InverseZeroSum_Candidate3_zero_not_mem_tupleSupportT
public import Theorems.Thm_InverseZeroSum_Candidate3_insert_zero_tupleSupportT_isCap
public import Theorems.Thm_InverseZeroSum_Candidate3_eight_nonzero_cap_sum_zero
public import Theorems.Thm_InverseZeroSum_Candidate3_tupleSupportT_card_eq_eight_length16
public import Theorems.Thm_InverseZeroSum_Candidate3_tupleFiberT_card_eq_two_length16
attribute [local simp] InverseZeroSum.Candidate3.baseIndex_val
attribute [local simp] InverseZeroSum.Candidate3.mem_s039AllBlocks
attribute [local simp] InverseZeroSum.Candidate3.planeSetT_card

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution : Length16SumZeroInput := by
  classical
  intro R hFree
  have hSupportCard := tupleSupportT_card_eq_eight_length16 R hFree
  have hSupportSum :
      (∑ x ∈ tupleSupportT R, x) = 0 :=
    eight_nonzero_cap_sum_zero hSupportCard
      (zero_not_mem_tupleSupportT R)
      (insert_zero_tupleSupportT_isCap R hFree)
  have hFiberEq := tupleFiberT_card_eq_two_length16 R hFree
  have hMaps :
      ∀ i ∈ (Finset.univ : Finset (Fin 16)),
        tupleValueT R i ∈ tupleSupportT R := by
    intro i hi
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  have hFiberwise :=
    Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset (Fin 16))) (t := tupleSupportT R)
      (g := tupleValueT R) hMaps (tupleValueT R)
  have hGrouped :
      (∑ i ∈ (Finset.univ : Finset (Fin 16)), tupleValueT R i) =
        ∑ x ∈ tupleSupportT R, (2 : ℕ) • x := by
    calc
      (∑ i ∈ (Finset.univ : Finset (Fin 16)), tupleValueT R i) =
          ∑ x ∈ tupleSupportT R,
            ∑ i ∈ (Finset.univ : Finset (Fin 16)) with
              tupleValueT R i = x, tupleValueT R i := by
                simpa using hFiberwise.symm
      _ = ∑ x ∈ tupleSupportT R, (2 : ℕ) • x := by
        apply Finset.sum_congr rfl
        intro x hx
        calc
          (∑ i ∈ (Finset.univ : Finset (Fin 16)) with
              tupleValueT R i = x, tupleValueT R i) =
              ∑ _i ∈ (Finset.univ : Finset (Fin 16)).filter
                (fun i => tupleValueT R i = x), x := by
                  exact Finset.sum_congr rfl
                    (fun i hi => (Finset.mem_filter.mp hi).2)
          _ =
              ((Finset.univ : Finset (Fin 16)).filter
                (fun i => tupleValueT R i = x)).card • x := by
                  simp
          _ = (2 : ℕ) • x := by rw [hFiberEq x hx]
  have hDouble :
      (∑ x ∈ tupleSupportT R, (2 : ℕ) • x) = 0 := by
    rw [Finset.sum_nsmul, hSupportSum]
    simp
  have hTupleTotal :
      (∑ i ∈ (Finset.univ : Finset (Fin 16)), tupleValueT R i) = 0 := by
    calc
      (∑ i ∈ (Finset.univ : Finset (Fin 16)), tupleValueT R i) =
          ∑ x ∈ tupleSupportT R, (2 : ℕ) • x := hGrouped
      _ = 0 := hDouble
  apply finiteModelEquiv.injective
  simpa [totalSum, posSum, tupleValueT] using hTupleTotal
end InverseZeroSum.Candidate3
