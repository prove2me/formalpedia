-- Prove2me | solution 1 for InverseZeroSum.Candidate3.nine_cap_direction_slice_pattern
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:40:12.424066+00:00
-- url     : https://prove2.me/submissions/ea66c877-4ba5-4f86-a675-21183ab60c72

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
public import Theorems.Thm_InverseZeroSum_Candidate3_nine_cap_plane_card_ne_two
public import Theorems.Thm_InverseZeroSum_Candidate3_directionSliceT_eq_inter
public import Theorems.Thm_InverseZeroSum_Candidate3_directionSliceT_card_le_four
public import Theorems.Thm_InverseZeroSum_Candidate3_card_eq_sum_directionSliceT
attribute [local simp] InverseZeroSum.Candidate3.baseIndex_val
attribute [local simp] InverseZeroSum.Candidate3.mem_s039AllBlocks
attribute [local simp] InverseZeroSum.Candidate3.planeSetT_card

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution {A : Finset F3T} (hA : IsCapT A)
    (hcard : A.card = 9) (d : Fin 13) :
    ((directionSliceT A d 0).card = 3 ∧
      (directionSliceT A d 1).card = 3 ∧
      (directionSliceT A d 2).card = 3) ∨
    ((directionSliceT A d 0).card = 1 ∧
      (directionSliceT A d 1).card = 4 ∧
      (directionSliceT A d 2).card = 4) ∨
    ((directionSliceT A d 0).card = 4 ∧
      (directionSliceT A d 1).card = 1 ∧
      (directionSliceT A d 2).card = 4) ∨
    ((directionSliceT A d 0).card = 4 ∧
      (directionSliceT A d 1).card = 4 ∧
      (directionSliceT A d 2).card = 1) := by
  have h0le := directionSliceT_card_le_four hA d 0
  have h1le := directionSliceT_card_le_four hA d 1
  have h2le := directionSliceT_card_le_four hA d 2
  have h0ne : (directionSliceT A d 0).card ≠ 2 := by
    rw [directionSliceT_eq_inter]
    exact nine_cap_plane_card_ne_two hA hcard (d, 0)
  have h1ne : (directionSliceT A d 1).card ≠ 2 := by
    rw [directionSliceT_eq_inter]
    exact nine_cap_plane_card_ne_two hA hcard (d, 1)
  have h2ne : (directionSliceT A d 2).card ≠ 2 := by
    rw [directionSliceT_eq_inter]
    exact nine_cap_plane_card_ne_two hA hcard (d, 2)
  have hsum := card_eq_sum_directionSliceT A d
  rw [hcard] at hsum
  have hsum' :
      (directionSliceT A d 0).card +
        (directionSliceT A d 1).card +
        (directionSliceT A d 2).card = 9 := by
    simpa [Fin.sum_univ_succ, Nat.add_assoc] using hsum.symm
  omega
end InverseZeroSum.Candidate3
