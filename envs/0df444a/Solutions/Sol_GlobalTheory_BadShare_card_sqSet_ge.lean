-- Prove2me | solution 1 for GlobalTheory.BadShare.card_sqSet_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:38:00.596657+00:00
-- url     : https://prove2.me/submissions/dd009fdb-52a8-4323-879d-c7bb176e9392

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardMonicSquarefreeUnitConstPolysGe
import Theorems.Thm_GlobalTheory_BadShare_SqCount_mem_monicSet
import Theorems.Thm_GlobalTheory_BadShare_SqCount_card_monicSet
import Theorems.Thm_GlobalTheory_BadShare_SqCount_card_zero_const
import Theorems.Thm_GlobalTheory_BadShare_SqCount_card_not_squarefree
import Theorems.Thm_GlobalTheory_BadShare_mem_sqSet


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory.BadShare.SqCount
namespace GlobalTheory.BadShare
theorem _root_.solution : ∀ (g : ℕ) [Fact g.Prime], ∀ N : ℕ, 1 ≤ N →
    (g : ℝ) ^ N - 2 * (g : ℝ) ^ (N - 1) ≤ ((sqSet g N).card : ℝ) := by
  intro g _ N hN
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hsub : monicSet g (n + 1) ⊆ sqSet g (n + 1) ∪ (((monicSet g (n + 1)).filter fun f => f.coeff 0 = 0) ∪
      ((monicSet g (n + 1)).filter fun f => ¬ Squarefree f)) := by
    intro f hf
    simp only [Finset.mem_union, Finset.mem_filter, mem_sqSet]
    have := mem_monicSet.1 hf
    tauto
  have h1 := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_left ((Finset.card_union_le _ _).trans
      (Nat.add_le_add (card_zero_const n) (card_not_squarefree n))) _))
  rw [card_monicSet] at h1
  have h2 : ((g : ℝ)) ^ (n + 1) ≤ ((sqSet g (n + 1)).card : ℝ) + ((g : ℝ) ^ n + (g : ℝ) ^ n) := by exact_mod_cast h1
  rw [Nat.add_sub_cancel]
  linarith
end GlobalTheory.BadShare
