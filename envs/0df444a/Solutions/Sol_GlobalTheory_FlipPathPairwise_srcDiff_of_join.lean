-- Prove2me | solution 1 for GlobalTheory.FlipPathPairwise.srcDiff_of_join
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:27:11.175102+00:00
-- url     : https://prove2.me/submissions/396042be-81a5-417a-84d5-9f3f23b5e926

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSplitThetaGridPathFlipGridPathAtSquare

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SplitFlip
open GlobalTheory GlobalTheory.FlipPathPairwise
namespace GlobalTheory.FlipPathPairwise
theorem _root_.solution {e e' : Edge} (h : e.tgt = e'.src) : srcDiff e' = srcDiff e + 1 := by
  cases e <;> cases e' <;> simp only [Edge.src, Edge.tgt, Prod.mk.injEq] at h <;>
    simp only [srcDiff, Edge.src] <;> omega
end GlobalTheory.FlipPathPairwise
