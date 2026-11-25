-- Prove2me | solution 1 for GlobalTheory.BadShare.SqCount.card_zero_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:30:18.888296+00:00
-- url     : https://prove2.me/submissions/a41a6587-0b9a-4809-8740-cc4d7fed5af0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardMonicSquarefreeUnitConstPolysGe
import Theorems.Thm_GlobalTheory_BadShare_SqCount_mem_monicSet
import Theorems.Thm_GlobalTheory_BadShare_SqCount_card_monicSet
import Theorems.Thm_GlobalTheory_BadShare_SqCount_monic_divX

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare GlobalTheory.BadShare.SqCount
variable (g : ℕ) [Fact g.Prime]
variable {g}
namespace GlobalTheory.BadShare.SqCount
theorem _root_.solution (n : ℕ) : ((monicSet g (n + 1)).filter fun f => f.coeff 0 = 0).card ≤ g ^ n := by
  rw [← card_monicSet]
  refine Finset.card_le_card_of_injOn divX ?_ ?_
  · intro f hf
    simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_monicSet, Finset.mem_coe] at hf ⊢
    refine ⟨monic_divX hf.1.1 (by omega), ?_⟩
    rw [natDegree_divX_eq_natDegree_tsub_one]; omega
  · intro f hf f' hf' h
    simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_monicSet] at hf hf'
    rw [← divX_mul_X_add f, ← divX_mul_X_add f', h, hf.2, hf'.2]
end GlobalTheory.BadShare.SqCount
