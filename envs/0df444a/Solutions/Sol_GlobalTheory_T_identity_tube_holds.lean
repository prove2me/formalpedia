-- Prove2me | solution 1 for GlobalTheory.T.identity_tube_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:23:22.726902+00:00
-- url     : https://prove2.me/submissions/dd5d20f9-1141-48ab-be49-c7e0e490c6db

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IdentityTubeHolds
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IdentityTubeHoldsStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Eis_idTube


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
theorem _root_.solution : PositivityTheory.RgEis.IdTube := by
  first | exact @GlobalTheory.CompanionTheory.Eis.idTube | exact GlobalTheory.CompanionTheory.Eis.idTube | (intros; apply GlobalTheory.CompanionTheory.Eis.idTube <;> assumption)
end _root_.GlobalTheory.T
