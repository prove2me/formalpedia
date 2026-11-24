-- Prove2me | solution 1 for InverseZeroSum.Candidate3.tupleSupportT_card_le_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:43:07.431055+00:00
-- url     : https://prove2.me/submissions/a2eb2010-5c73-437a-8079-6c6b0926f3ff

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
public import Theorems.Thm_InverseZeroSum_Candidate3_capT_card_le_nine
public import Theorems.Thm_InverseZeroSum_Candidate3_zero_not_mem_tupleSupportT
public import Theorems.Thm_InverseZeroSum_Candidate3_insert_zero_tupleSupportT_isCap
attribute [local simp] InverseZeroSum.Candidate3.baseIndex_val
attribute [local simp] InverseZeroSum.Candidate3.mem_s039AllBlocks
attribute [local simp] InverseZeroSum.Candidate3.planeSetT_card

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution {n : ℕ} (R : PosSeq n)
    (hFree : ShortFree R) :
    (tupleSupportT R).card ≤ 8 := by
  have hCap0 := insert_zero_tupleSupportT_isCap R hFree
  have hCap0Card : (insert 0 (tupleSupportT R)).card ≤ 9 :=
    capT_card_le_nine hCap0
  have hZeroNot := zero_not_mem_tupleSupportT R
  have hCard :
      (insert 0 (tupleSupportT R)).card = (tupleSupportT R).card + 1 := by
    simp [hZeroNot, Nat.add_comm]
  rw [hCard] at hCap0Card
  omega
end InverseZeroSum.Candidate3
