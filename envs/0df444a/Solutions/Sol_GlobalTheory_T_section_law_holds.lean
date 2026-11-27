-- Prove2me | solution 1 for GlobalTheory.T.section_law_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:34:03.38291+00:00
-- url     : https://prove2.me/submissions/d2fcaa6a-5f7d-4960-9832-bede685533f1

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SectionLawHolds
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SectionLawHoldsStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisSec_secLaw


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
theorem _root_.solution : PositivityTheory.RgEis.SecLaw := by
  first | exact @GlobalTheory.CompanionTheory.RgEisSec.secLaw | exact GlobalTheory.CompanionTheory.RgEisSec.secLaw | (intros; apply GlobalTheory.CompanionTheory.RgEisSec.secLaw <;> assumption)
end _root_.GlobalTheory.T
