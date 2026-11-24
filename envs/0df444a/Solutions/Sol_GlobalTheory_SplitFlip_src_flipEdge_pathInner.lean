-- Prove2me | solution 1 for GlobalTheory.SplitFlip.src_flipEdge_pathInner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:54:58.597059+00:00
-- url     : https://prove2.me/submissions/e86c278a-2ae2-4cdb-84c6-22e47815d59e

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
theorem _root_.solution (i j : ℕ) (e : Edge) :
    (if e = .theta i j then Edge.ex i (j + 1) else if e = .ex i j then .theta (i + 1) j else e).src =
      if e = .ex i j then (i + 1, j + 1) else e.src := by
  by_cases h1 : e = .theta i j
  · subst h1; simp
  · by_cases h2 : e = .ex i j
    · subst h2; simp
    · simp [h1, h2]
end GlobalTheory.SplitFlip
