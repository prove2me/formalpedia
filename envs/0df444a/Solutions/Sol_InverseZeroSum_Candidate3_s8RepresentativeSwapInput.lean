-- Prove2me | solution 1 for InverseZeroSum.Candidate3.s8RepresentativeSwapInput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:49:25.745831+00:00
-- url     : https://prove2.me/submissions/8def3696-b6bb-423a-b9b7-90ea3301b0c3

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
public import Theorems.Thm_InverseZeroSum_Candidate3_length16SumZeroInput
public import Theorems.Thm_InverseZeroSum_Candidate3_s8_packed_blocks_constant
public import Theorems.Thm_InverseZeroSum_Candidate3_constant_shortZero_block_ne_two
attribute [local simp] InverseZeroSum.Candidate3.baseIndex_val
attribute [local simp] InverseZeroSum.Candidate3.mem_s039AllBlocks
attribute [local simp] InverseZeroSum.Candidate3.planeSetT_card

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution : S8RepresentativeSwapInput := by
  intro S c hs
  have hConst :=
    s8_packed_blocks_constant length16SumZeroInput c hs
  have hLR : c.l = 8 ∧ c.r = 0 := by
    rcases c.signature with h682 | h781 | h880 | h690
    · let j : Fin c.s := ⟨6, by omega⟩
      have hCardTwo : (c.blocks j).card = 2 := by
        rw [c.block_card]
        simp [j, h682.1]
      exact False.elim
        ((constant_shortZero_block_ne_two (c.block_shortZero j) (hConst j))
          hCardTwo)
    · let j : Fin c.s := ⟨7, by omega⟩
      have hCardTwo : (c.blocks j).card = 2 := by
        rw [c.block_card]
        simp [j, h781.1]
      exact False.elim
        ((constant_shortZero_block_ne_two (c.block_shortZero j) (hConst j))
          hCardTwo)
    · exact ⟨h880.1, h880.2.2⟩
    · omega
  exact ⟨hLR.1, hLR.2, hConst⟩
end InverseZeroSum.Candidate3
