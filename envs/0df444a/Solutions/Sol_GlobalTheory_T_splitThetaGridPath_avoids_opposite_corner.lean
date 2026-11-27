-- Prove2me | solution 1 for GlobalTheory.T.splitThetaGridPath_avoids_opposite_corner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:34:03.381277+00:00
-- url     : https://prove2.me/submissions/79ecfb05-fa5c-436a-82ee-c51c09f80983

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SplitThetaGridPathAvoidsOppositeCorner
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SplitThetaGridPathAvoidsOppositeCornerStatement
import Theorems.Thm_GlobalTheory_SplitFlip_pathAvoid


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SplitFlip
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {γ : List Edge} {i j : ℕ}, IsPath γ → PassesThrough i j γ → ∀ b ∈ γ, b.src ≠ (i + 1, j + 1) ∧ b.tgt ≠ (i + 1, j + 1) := by
  first | exact @GlobalTheory.SplitFlip.pathAvoid | exact GlobalTheory.SplitFlip.pathAvoid | (intros; apply GlobalTheory.SplitFlip.pathAvoid <;> assumption)
end _root_.GlobalTheory.T
