-- Prove2me | solution 1 for GlobalTheory.ClosedBallValuationSubring.mem_openBallIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:06.302985+00:00
-- url     : https://prove2.me/submissions/4a062fe5-f3a7-4730-929d-b7471c802135

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
theorem _root_.solution {x : closedBallSubring K} :
    x ∈ openBallIdeal K ↔ ‖(x : K)‖ < 1 := Iff.rfl
end GlobalTheory.ClosedBallValuationSubring
