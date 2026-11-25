-- Prove2me | solution 1 for GlobalTheory.LocAsm.exOne_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:02:24.927458+00:00
-- url     : https://prove2.me/submissions/a93311b8-eadb-42ab-a7df-d093c93604cb

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
theorem _root_.solution {X : GlobalTheory.SplitFlip.Edge → Type} (φ : ∀ b, X b → ℂ) (i j : ℕ) (x : X (.theta i j)) :
    exOne φ (.theta i j) x = φ (.theta i j) x := rfl
end GlobalTheory.LocAsm
