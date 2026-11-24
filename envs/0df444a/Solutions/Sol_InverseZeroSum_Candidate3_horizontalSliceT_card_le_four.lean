-- Prove2me | solution 1 for InverseZeroSum.Candidate3.horizontalSliceT_card_le_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:37:39.856029+00:00
-- url     : https://prove2.me/submissions/7aeffca3-0ea5-4c07-b7d8-5074c6d74d9c

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_cap_inter_plane_le_four
public import Theorems.Thm_InverseZeroSum_Candidate3_horizontalSliceT_eq_inter

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution {A : Finset F3T} (hA : IsCapT A) (c : Fin 3) :
    (horizontalSliceT A c).card ≤ 4 := by
  rw [horizontalSliceT_eq_inter]
  exact cap_inter_plane_le_four hA (horizontalPlaneT c)
end InverseZeroSum.Candidate3
