-- Prove2me | solution 1 for GlobalTheory.ClosedBallValuationSubring.mem_openBallIdeal_iff_not_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:29:46.893221+00:00
-- url     : https://prove2.me/submissions/93fbd7c9-3dfc-4ee8-aa63-e74de8bd92b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ClosedBallValuationSubringToSubring
import Theorems.Thm_GlobalTheory_ClosedBallValuationSubring_mem_closedBallSubring
import Theorems.Thm_GlobalTheory_ClosedBallValuationSubring_mem_openBallIdeal
import Theorems.Thm_GlobalTheory_ClosedBallValuationSubring_isUnit_iff_norm_eq_one

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
    x ∈ openBallIdeal K ↔ ¬ IsUnit x := by
  rw [mem_openBallIdeal, isUnit_iff_norm_eq_one]
  have hle : ‖(x : K)‖ ≤ 1 := mem_closedBallSubring.mp x.2
  exact ⟨fun h he => (ne_of_lt h) he, fun h => lt_of_le_of_ne hle h⟩
end GlobalTheory.ClosedBallValuationSubring
