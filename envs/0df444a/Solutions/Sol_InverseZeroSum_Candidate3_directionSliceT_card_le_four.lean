-- Prove2me | solution 1 for InverseZeroSum.Candidate3.directionSliceT_card_le_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:37:49.777291+00:00
-- url     : https://prove2.me/submissions/c94e29a5-4fe6-4e65-8d64-86c98c950c8c

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_cap_inter_plane_le_four
public import Theorems.Thm_InverseZeroSum_Candidate3_directionSliceT_eq_inter

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution {A : Finset F3T} (hA : IsCapT A)
    (d : Fin 13) (c : Fin 3) :
    (directionSliceT A d c).card ≤ 4 := by
  rw [directionSliceT_eq_inter]
  exact cap_inter_plane_le_four hA (d, c)
end InverseZeroSum.Candidate3
