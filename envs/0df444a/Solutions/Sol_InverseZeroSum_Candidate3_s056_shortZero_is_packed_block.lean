-- Prove2me | solution 1 for InverseZeroSum.Candidate3.s056_shortZero_is_packed_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:43:51.143426+00:00
-- url     : https://prove2.me/submissions/cf5a54da-99ad-48ea-9d46-5acb1c8ccbc3

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_shortZero_disjoint_of_ne
public import Theorems.Thm_InverseZeroSum_Candidate3_s056_eight_constant_blocks_cover

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000
namespace InverseZeroSum.Candidate3
theorem _root_.solution {S : PosSeq 24}
    (hAvoid : AvoidsInnerJointPair S)
    (c : S039PackingCertificate S)
    (h : S8RepresentativeSwapOutput S c)
    {I : Finset (Fin 24)} (hI : ShortZero S I) :
    ∃ j : Fin c.s, I = c.blocks j := by
  classical
  have hCover := s056_eight_constant_blocks_cover c h
  obtain ⟨x, hx⟩ := hI.1
  have hxUnion : x ∈ blockUnion c.blocks := by
    rw [hCover]
    exact Finset.mem_univ x
  obtain ⟨j, _hj, hxBlock⟩ := Finset.mem_biUnion.mp hxUnion
  refine ⟨j, ?_⟩
  by_contra hNe
  have hDisj :=
    shortZero_disjoint_of_ne hAvoid hI (c.block_shortZero j) hNe
  exact (Finset.disjoint_left.mp hDisj) hx hxBlock
end InverseZeroSum.Candidate3
