-- Prove2me | solution 1 for InverseZeroSum.Candidate3.length15NonzeroInput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:48:19.01946+00:00
-- url     : https://prove2.me/submissions/18a64bbe-dc38-4511-be31-b63c8446b1df

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
public import Theorems.Thm_InverseZeroSum_Candidate3_zero_not_mem_tupleSupportT
public import Theorems.Thm_InverseZeroSum_Candidate3_insert_zero_tupleSupportT_isCap
public import Theorems.Thm_InverseZeroSum_Candidate3_eight_nonzero_cap_sum_zero
public import Theorems.Thm_InverseZeroSum_Candidate3_tupleSupportT_card_eq_eight_length15
public import Theorems.Thm_InverseZeroSum_Candidate3_exists_tupleFiberT_card_eq_one_length15
public import Theorems.Thm_InverseZeroSum_Candidate3_tupleFiberT_card_eq_two_off_singleton_length15
public import Theorems.Thm_InverseZeroSum_Candidate3_tupleValueT_sum_eq_support_weight
attribute [local simp] InverseZeroSum.Candidate3.baseIndex_val
attribute [local simp] InverseZeroSum.Candidate3.mem_s039AllBlocks
attribute [local simp] InverseZeroSum.Candidate3.planeSetT_card

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000
namespace InverseZeroSum.Candidate3
theorem _root_.solution : Length15NonzeroInput := by
  classical
  intro R hFree
  obtain ⟨u, hu, huOne⟩ :=
    exists_tupleFiberT_card_eq_one_length15 R hFree
  let w : F3T → ℕ := fun x =>
    ((Finset.univ : Finset (Fin 15)).filter
      (fun i => tupleValueT R i = x)).card
  have huOneW : w u = 1 := by
    simpa [w] using huOne
  have hOtherW :
      ∀ x ∈ (tupleSupportT R).erase u, w x = 2 := by
    intro x hx
    simpa [w] using
      (tupleFiberT_card_eq_two_off_singleton_length15
        R hFree hu huOne x hx)
  have hSupportCard := tupleSupportT_card_eq_eight_length15 R hFree
  have hSupportSum :
      (∑ x ∈ tupleSupportT R, x) = 0 :=
    eight_nonzero_cap_sum_zero hSupportCard
      (zero_not_mem_tupleSupportT R)
      (insert_zero_tupleSupportT_isCap R hFree)
  have hGrouped :
      (∑ i ∈ (Finset.univ : Finset (Fin 15)), tupleValueT R i) =
        ∑ x ∈ tupleSupportT R, w x • x := by
    simpa [w] using tupleValueT_sum_eq_support_weight R
  have hWeightedPlus :
      (∑ x ∈ tupleSupportT R, w x • x) + u =
        ∑ x ∈ tupleSupportT R, (2 : ℕ) • x := by
    have hErase :
        (∑ x ∈ (tupleSupportT R).erase u, w x • x) =
          ∑ x ∈ (tupleSupportT R).erase u, (2 : ℕ) • x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hOtherW x hx]
    rw [← Finset.sum_erase_add (tupleSupportT R)
      (fun x => w x • x) hu]
    rw [← Finset.sum_erase_add (tupleSupportT R)
      (fun x => (2 : ℕ) • x) hu]
    rw [hErase, huOneW]
    simp [two_nsmul, add_assoc]
  have hDouble :
      (∑ x ∈ tupleSupportT R, (2 : ℕ) • x) = 0 := by
    rw [Finset.sum_nsmul, hSupportSum]
    simp
  intro hTotal
  have hTupleTotal :
      (∑ i ∈ (Finset.univ : Finset (Fin 15)), tupleValueT R i) = 0 := by
    have hMapped :=
      congrArg (fun z : G => finiteModelEquiv z) hTotal
    simpa [totalSum, posSum, tupleValueT] using hMapped
  have hTuplePlus :
      (∑ i ∈ (Finset.univ : Finset (Fin 15)), tupleValueT R i) + u = 0 := by
    calc
      (∑ i ∈ (Finset.univ : Finset (Fin 15)), tupleValueT R i) + u =
          (∑ x ∈ tupleSupportT R, w x • x) + u := by
            rw [hGrouped]
      _ = ∑ x ∈ tupleSupportT R, (2 : ℕ) • x := hWeightedPlus
      _ = 0 := hDouble
  have huZero : u = 0 := by
    simpa [hTupleTotal] using hTuplePlus
  apply zero_not_mem_tupleSupportT R
  simpa [huZero] using hu
end InverseZeroSum.Candidate3
