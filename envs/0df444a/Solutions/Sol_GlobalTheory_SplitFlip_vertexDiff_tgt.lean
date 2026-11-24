-- Prove2me | solution 1 for GlobalTheory.SplitFlip.vertexDiff_tgt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:17.344327+00:00
-- url     : https://prove2.me/submissions/74ba412d-34e8-4464-a0b2-21e8a9f4c700

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SplitThetaGridPathAvoidsOppositeCorner

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SplitFlip
namespace GlobalTheory.SplitFlip
theorem _root_.solution (e : Edge) : vertexDiff e.tgt = vertexDiff e.src + 1 := by
  cases e <;> simp [vertexDiff, Edge.src, Edge.tgt] <;> omega
end GlobalTheory.SplitFlip
