-- Prove2me | solution 1 for InverseZeroSum.Candidate3.nine_cap_sum_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:43:56.976606+00:00
-- url     : https://prove2.me/submissions/4aa1c822-42ef-4ca9-8fa2-a2bccdc1c239

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
public import Theorems.Thm_InverseZeroSum_Candidate3_nine_cap_direction_value_sum_zero
public import Theorems.Thm_InverseZeroSum_Candidate3_planeValueT_sum
attribute [local simp] InverseZeroSum.Candidate3.baseIndex_val
attribute [local simp] InverseZeroSum.Candidate3.mem_s039AllBlocks
attribute [local simp] InverseZeroSum.Candidate3.planeSetT_card

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution {A : Finset F3T} (hA : IsCapT A)
    (hcard : A.card = 9) :
    (∑ x ∈ A, x) = 0 := by
  let d0 : Fin 13 := ⟨0, by omega⟩
  let d1 : Fin 13 := ⟨9, by omega⟩
  let d2 : Fin 13 := ⟨12, by omega⟩
  have h0 : planeValueT d0 (∑ x ∈ A, x) = 0 := by
    rw [planeValueT_sum]
    exact nine_cap_direction_value_sum_zero hA hcard d0
  have h1 : planeValueT d1 (∑ x ∈ A, x) = 0 := by
    rw [planeValueT_sum]
    exact nine_cap_direction_value_sum_zero hA hcard d1
  have h2 : planeValueT d2 (∑ x ∈ A, x) = 0 := by
    rw [planeValueT_sum]
    exact nine_cap_direction_value_sum_zero hA hcard d2
  have hc0 : (∑ x ∈ A, x).1 = 0 := by
    simpa [d0, planeValueT] using h0
  have hc1 : (∑ x ∈ A, x).2.1 = 0 := by
    simpa [d1, planeValueT] using h1
  have hc2 : (∑ x ∈ A, x).2.2 = 0 := by
    simpa [d2, planeValueT] using h2
  apply Prod.ext
  · exact hc0
  · apply Prod.ext
    · exact hc1
    · exact hc2
end InverseZeroSum.Candidate3
