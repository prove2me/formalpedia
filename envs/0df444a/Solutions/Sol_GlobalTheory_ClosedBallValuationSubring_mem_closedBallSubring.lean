-- Prove2me | solution 1 for GlobalTheory.ClosedBallValuationSubring.mem_closedBallSubring
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:58.54692+00:00
-- url     : https://prove2.me/submissions/fb55e2cc-e3df-487a-9603-7d66a9f574f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ClosedBallValuationSubringToSubring

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ClosedBallValuationSubring
variable (K : Type*) [NormedField K] [IsUltrametricDist K]
variable {K}
namespace GlobalTheory.ClosedBallValuationSubring
theorem _root_.solution {x : K} : x ∈ closedBallSubring K ↔ ‖x‖ ≤ 1 := Iff.rfl
end GlobalTheory.ClosedBallValuationSubring
