-- Prove2me | solution 1 for InverseZeroSum.Candidate3.card_eq_sum_directionSliceT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:39:05.163934+00:00
-- url     : https://prove2.me/submissions/a7a277d2-4416-4b3e-8d65-f336750f289e

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
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
theorem _root_.solution (A : Finset F3T) (d : Fin 13) :
    A.card = ∑ c : Fin 3, (directionSliceT A d c).card := by
  classical
  simpa [directionSliceT] using
    (Finset.card_eq_sum_card_fiberwise
      (f := planeValueT d) (s := A) (t := (Finset.univ : Finset (Fin 3)))
      (fun x _hx => Finset.mem_univ (planeValueT d x)))
end InverseZeroSum.Candidate3
