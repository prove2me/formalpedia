-- Prove2me | solution 1 for GlobalTheory.T.height_lipschitz_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:22:27.194143+00:00
-- url     : https://prove2.me/submissions/917a6161-d68d-4d14-9226-6043bcd71721

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HeightLipschitzHolds
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HeightLipschitzHoldsStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_htLip


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
theorem _root_.solution : PositivityTheory.RgEis.HtLip := by
  first | exact @GlobalTheory.CompanionTheory.RgEis.htLip | exact GlobalTheory.CompanionTheory.RgEis.htLip | (intros; apply GlobalTheory.CompanionTheory.RgEis.htLip <;> assumption)
end _root_.GlobalTheory.T
