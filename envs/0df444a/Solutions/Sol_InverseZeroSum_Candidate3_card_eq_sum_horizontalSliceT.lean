-- Prove2me | solution 1 for InverseZeroSum.Candidate3.card_eq_sum_horizontalSliceT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:37:29.586626+00:00
-- url     : https://prove2.me/submissions/4349eaaa-fcb8-4923-87a6-facd412c2b1e

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
theorem _root_.solution (A : Finset F3T) :
    A.card = ∑ c : Fin 3, (horizontalSliceT A c).card := by
  classical
  simpa [horizontalSliceT, thirdCoordT] using
    (Finset.card_eq_sum_card_fiberwise
      (f := thirdCoordT) (s := A) (t := (Finset.univ : Finset (Fin 3)))
      (fun x _hx => Finset.mem_univ (thirdCoordT x)))
end InverseZeroSum.Candidate3
