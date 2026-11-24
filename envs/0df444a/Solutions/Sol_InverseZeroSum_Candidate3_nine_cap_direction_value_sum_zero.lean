-- Prove2me | solution 1 for InverseZeroSum.Candidate3.nine_cap_direction_value_sum_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:41:32.311789+00:00
-- url     : https://prove2.me/submissions/7a1858ed-d0b5-4a7e-9989-83a02a5dca84

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
public import Theorems.Thm_InverseZeroSum_Candidate3_nine_cap_direction_slice_pattern
public import Theorems.Thm_InverseZeroSum_Candidate3_sum_planeValueT_directionSliceT
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
    (∑ x ∈ A, planeValueT d x) = 0 := by
  classical
  have hFiberwise :=
    Finset.sum_fiberwise_of_maps_to
      (s := A) (t := (Finset.univ : Finset (Fin 3))) (g := planeValueT d)
      (fun x _hx => Finset.mem_univ (planeValueT d x)) (planeValueT d)
  calc
    (∑ x ∈ A, planeValueT d x) =
        ∑ c : Fin 3, ∑ x ∈ directionSliceT A d c, planeValueT d x := by
          simpa [directionSliceT] using hFiberwise.symm
    _ = ∑ c : Fin 3, (directionSliceT A d c).card • c := by
      apply Finset.sum_congr rfl
      intro c _hc
      exact sum_planeValueT_directionSliceT A d c
    _ = 0 := by
      rcases nine_cap_direction_slice_pattern hA hcard d with
        h333 | h144 | h414 | h441
      · rcases h333 with ⟨h0, h1, h2⟩
        simp [Fin.sum_univ_succ, h0, h1, h2]
        all_goals decide
      · rcases h144 with ⟨h0, h1, h2⟩
        simp [Fin.sum_univ_succ, h0, h1, h2]
        all_goals decide
      · rcases h414 with ⟨h0, h1, h2⟩
        simp [Fin.sum_univ_succ, h0, h1, h2]
        all_goals decide
      · rcases h441 with ⟨h0, h1, h2⟩
        simp [Fin.sum_univ_succ, h0, h1, h2]
        all_goals decide
end InverseZeroSum.Candidate3
