-- Prove2me | solution 1 for GlobalTheory.T.card_monicSquarefreeUnitConstPolys_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:36:26.335012+00:00
-- url     : https://prove2.me/submissions/d1155724-7e5a-4dad-be8a-e9a2cb198cc1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardMonicSquarefreeUnitConstPolysGe
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardMonicSquarefreeUnitConstPolysGeStatement
import Theorems.Thm_GlobalTheory_BadShare_card_sqSet_ge


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (g : ℕ) [Fact g.Prime], ∀ N : ℕ, 1 ≤ N → (g : ℝ) ^ N - 2 * (g : ℝ) ^ (N - 1) ≤ ((sqSet g N).card : ℝ) := by
  first | exact @GlobalTheory.BadShare.card_sqSet_ge | exact GlobalTheory.BadShare.card_sqSet_ge | (intros; apply GlobalTheory.BadShare.card_sqSet_ge <;> assumption)
end _root_.GlobalTheory.T
