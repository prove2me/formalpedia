-- Prove2me | solution 1 for GlobalTheory.ClosedBallValuationSubring.openBallIdeal_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:01:28.712853+00:00
-- url     : https://prove2.me/submissions/f8de0362-e3a3-4afd-ba88-f128527ed599

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ClosedBallValuationSubringToSubring
import Theorems.Thm_GlobalTheory_ClosedBallValuationSubring_openBallIdeal_eq_maximalIdeal

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
theorem _root_.solution : (openBallIdeal K).IsMaximal := by
  rw [openBallIdeal_eq_maximalIdeal]
  exact IsLocalRing.maximalIdeal.isMaximal _
end GlobalTheory.ClosedBallValuationSubring
