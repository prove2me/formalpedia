-- Prove2me | solution 1 for GlobalTheory.T.isSplitThetaGridPath_flipGridPathAtSquare
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:23:39.065512+00:00
-- url     : https://prove2.me/submissions/3b536e6b-34bd-48a7-bd82-a842520fa5df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSplitThetaGridPathFlipGridPathAtSquare
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSplitThetaGridPathFlipGridPathAtSquareStatement
import Theorems.Thm_GlobalTheory_SplitFlip_isPath_flipPath


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
theorem _root_.solution : ∀ {γ : List Edge} {i j : ℕ}, IsPath γ → PassesThrough i j γ → IsPath (flipPath i j γ) := by
  first | exact @GlobalTheory.SplitFlip.isPath_flipPath | exact GlobalTheory.SplitFlip.isPath_flipPath | (intros; apply GlobalTheory.SplitFlip.isPath_flipPath <;> assumption)
end _root_.GlobalTheory.T
