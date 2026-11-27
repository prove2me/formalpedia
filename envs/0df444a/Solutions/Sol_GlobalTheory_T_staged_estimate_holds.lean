-- Prove2me | solution 1 for GlobalTheory.T.staged_estimate_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:33:37.573798+00:00
-- url     : https://prove2.me/submissions/e6821ec4-bf14-48d4-9677-a3e8bed65619

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_StagedEstimateHolds
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_StagedEstimateHoldsStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_stage


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : PositivityTheory.RgEis.PiLocalization₂ := by
  first | exact @GlobalTheory.CompanionTheory.RgEis.stage | exact GlobalTheory.CompanionTheory.RgEis.stage | (intros; apply GlobalTheory.CompanionTheory.RgEis.stage <;> assumption)
end _root_.GlobalTheory.T
