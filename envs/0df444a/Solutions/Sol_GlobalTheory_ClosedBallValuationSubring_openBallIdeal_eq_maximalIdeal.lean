-- Prove2me | solution 1 for GlobalTheory.ClosedBallValuationSubring.openBallIdeal_eq_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:47:12.693358+00:00
-- url     : https://prove2.me/submissions/18704766-e7b4-4ccb-ac16-0fb62d4966c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ClosedBallValuationSubringToSubring
import Theorems.Thm_GlobalTheory_ClosedBallValuationSubring_mem_openBallIdeal_iff_not_isUnit

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
variable (K)
namespace GlobalTheory.ClosedBallValuationSubring
theorem _root_.solution :
    openBallIdeal K = IsLocalRing.maximalIdeal (closedBallSubring K) := by
  ext x
  rw [mem_openBallIdeal_iff_not_isUnit, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
end GlobalTheory.ClosedBallValuationSubring
