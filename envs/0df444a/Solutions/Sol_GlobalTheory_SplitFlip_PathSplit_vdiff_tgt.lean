-- Prove2me | solution 1 for GlobalTheory.SplitFlip.PathSplit.vdiff_tgt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:54:54.818523+00:00
-- url     : https://prove2.me/submissions/10084bf0-e685-4b37-95b0-8079b07cd4f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlipGridPathAtSquareSplit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SplitFlip GlobalTheory.SplitFlip.PathSplit
open GlobalTheory.SplitFlip
namespace GlobalTheory.SplitFlip.PathSplit
theorem _root_.solution (e : Edge) : vdiff e.tgt = vdiff e.src + 1 := by
  cases e <;> simp [vdiff] <;> push_cast <;> ring
end GlobalTheory.SplitFlip.PathSplit
