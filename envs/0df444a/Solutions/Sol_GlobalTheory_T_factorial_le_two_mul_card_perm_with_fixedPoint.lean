-- Prove2me | solution 1 for GlobalTheory.T.factorial_le_two_mul_card_perm_with_fixedPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:19:31.218263+00:00
-- url     : https://prove2.me/submissions/b5fd2632-3ce4-4504-aacb-a77c60f20958

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FactorialLeTwoMulCardPermWithFixedPoint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FactorialLeTwoMulCardPermWithFixedPointStatement
import Theorems.Thm_GlobalTheory_BadShare_factorial_le_two_mul_card_perm_fixed


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
theorem _root_.solution : ∀ (α : Type) [Fintype α] [DecidableEq α], Nonempty α → (Fintype.card α).factorial ≤ 2 * (Finset.univ.filter fun σ : Equiv.Perm α => ∃ i, σ i = i).card := by
  first | exact @GlobalTheory.BadShare.factorial_le_two_mul_card_perm_fixed | exact GlobalTheory.BadShare.factorial_le_two_mul_card_perm_fixed | (intros; apply GlobalTheory.BadShare.factorial_le_two_mul_card_perm_fixed <;> assumption)
end _root_.GlobalTheory.T
