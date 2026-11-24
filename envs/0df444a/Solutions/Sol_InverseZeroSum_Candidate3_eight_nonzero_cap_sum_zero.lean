-- Prove2me | solution 1 for InverseZeroSum.Candidate3.eight_nonzero_cap_sum_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:46:42.197491+00:00
-- url     : https://prove2.me/submissions/87519012-f387-4b14-9d33-3e91cc8fcaa0

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
public import Theorems.Thm_InverseZeroSum_Candidate3_nine_cap_sum_zero
attribute [local simp] InverseZeroSum.Candidate3.baseIndex_val
attribute [local simp] InverseZeroSum.Candidate3.mem_s039AllBlocks
attribute [local simp] InverseZeroSum.Candidate3.planeSetT_card

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution {A : Finset F3T}
    (hcard : A.card = 8) (hzero : (0 : F3T) ∉ A)
    (hcap : IsCapT (insert 0 A)) :
    (∑ x ∈ A, x) = 0 := by
  have hcard9 : (insert 0 A).card = 9 := by
    simp [hzero, hcard]
  have hsum := nine_cap_sum_zero hcap hcard9
  simpa [hzero] using hsum
end InverseZeroSum.Candidate3
