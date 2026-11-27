-- Prove2me | solution 1 for GlobalTheory.T.twist_of_section_law
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:33:58.936537+00:00
-- url     : https://prove2.me/submissions/922cd19f-21e3-4db6-b661-bfdb75728a86

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TwistOfSectionLaw
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_Descend
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TwistOfSectionLawStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisTwist_twist


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
theorem _root_.solution : PositivityTheory.RgEis.SecLaw → PositivityTheory.RgEis.Twist := by
  first | exact @GlobalTheory.CompanionTheory.RgEisTwist.twist | exact GlobalTheory.CompanionTheory.RgEisTwist.twist | (intros; apply GlobalTheory.CompanionTheory.RgEisTwist.twist <;> assumption)
end _root_.GlobalTheory.T
