-- Prove2me | solution 1 for GlobalTheory.SplitFlip.pathInnerDiff_tgt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:54:56.533483+00:00
-- url     : https://prove2.me/submissions/20e8fdf5-db6d-4427-9d3d-30d7bfa443e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemGridPathInnerVerticesFlipGridPathAtSquare

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
theorem _root_.solution (e : Edge) : pathInnerDiff e.tgt = pathInnerDiff e.src + 1 := by
  cases e <;> simp [pathInnerDiff, Edge.tgt, Edge.src] <;> push_cast <;> ring
end GlobalTheory.SplitFlip
