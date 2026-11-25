-- Prove2me | solution 1 for GlobalTheory.LocAsm.exOne_ex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:02:20.418298+00:00
-- url     : https://prove2.me/submissions/d75c3776-2b2e-4bb0-8ee2-780448eb948e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExOneEqSelf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LocAsm
namespace GlobalTheory.LocAsm
theorem _root_.solution {X : GlobalTheory.SplitFlip.Edge → Type} (φ : ∀ b, X b → ℂ) (i j : ℕ) (x : X (.ex i j)) :
    exOne φ (.ex i j) x = 1 := rfl
end GlobalTheory.LocAsm
