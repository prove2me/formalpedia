-- Prove2me | solution 1 for GlobalTheory.T.squarefreeLabelTorusMass_hasDivisorOfDegree_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:17:52.080328+00:00
-- url     : https://prove2.me/submissions/62f4ae1c-3478-4788-a46c-5996aa073398

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassHasDivisorOfDegreeLe
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassHasDivisorOfDegreeLeStatement
import Theorems.Thm_GlobalTheory_BadShare_mass_hasDiv_le


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
theorem _root_.solution : ∀ (g : ℕ) [Fact g.Prime], ∀ N a : ℕ, 0 < a → a < N → mass g N (HasDiv g a) ≤ 7 / 8 := by
  first | exact @GlobalTheory.BadShare.mass_hasDiv_le | exact GlobalTheory.BadShare.mass_hasDiv_le | (intros; apply GlobalTheory.BadShare.mass_hasDiv_le <;> assumption)
end _root_.GlobalTheory.T
