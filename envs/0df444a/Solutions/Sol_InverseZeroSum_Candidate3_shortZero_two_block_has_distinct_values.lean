-- Prove2me | solution 1 for InverseZeroSum.Candidate3.shortZero_two_block_has_distinct_values
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:40:45.212073+00:00
-- url     : https://prove2.me/submissions/6db65a10-1a6e-45ed-9df4-73207748b672

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_constant_shortZero_block_ne_two

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000
namespace InverseZeroSum.Candidate3
theorem _root_.solution
    {S : PosSeq 24} {B : Finset (Fin 24)}
    (hShort : ShortZero S B) (hCard : B.card = 2) :
    ∃ x ∈ B, ∃ y ∈ B, S x ≠ S y := by
  classical
  by_contra hNo
  have hConst : ∀ x ∈ B, ∀ y ∈ B, S x = S y := by
    intro x hx y hy
    by_contra hne
    exact hNo ⟨x, hx, y, hy, hne⟩
  exact (constant_shortZero_block_ne_two hShort hConst) hCard
end InverseZeroSum.Candidate3
