-- Prove2me | solution 1 for GlobalTheory.T.extension_law
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:17:05.626476+00:00
-- url     : https://prove2.me/submissions/898ad3b9-c16f-471d-a093-69ed6d84c2e6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExtensionLaw
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExtensionLawStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisExt_extLaw


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
theorem _root_.solution : PositivityTheory.RgEis.ExtLaw := by
  first | exact @GlobalTheory.CompanionTheory.RgEisExt.extLaw | exact GlobalTheory.CompanionTheory.RgEisExt.extLaw | (intros; apply GlobalTheory.CompanionTheory.RgEisExt.extLaw <;> assumption)
end _root_.GlobalTheory.T
