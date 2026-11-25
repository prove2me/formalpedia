-- Prove2me | solution 1 for GlobalTheory.T.squarefreeLabelTorusMass_no_large_prime_factor_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:03:29.973476+00:00
-- url     : https://prove2.me/submissions/7994fdf0-e690-42b4-9c42-eeb9d8dbd653

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassNoLargePrimeFactorLe
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassNoLargePrimeFactorLeStatement
import Theorems.Thm_GlobalTheory_BadShare_mass_not_hasPrimeFactor_le


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
theorem _root_.solution : ∀ (g : ℕ) [Fact g.Prime], ∀ N : ℕ, 100000 ≤ N → (mass g N fun f => ¬ HasPrimeFactor g N f) ≤ 1 - 1 / (10 * Real.log N) := by
  first | exact @GlobalTheory.BadShare.mass_not_hasPrimeFactor_le | exact GlobalTheory.BadShare.mass_not_hasPrimeFactor_le | (intros; apply GlobalTheory.BadShare.mass_not_hasPrimeFactor_le <;> assumption)
end _root_.GlobalTheory.T
