-- Prove2me | solution 1 for GlobalTheory.T.wall_law_of_section_law
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:26:17.158802+00:00
-- url     : https://prove2.me/submissions/a9415e73-7c3c-4203-b6d6-13b55a0a8e4d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WallLawOfSectionLaw
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WallLawOfSectionLawStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_wallLaw_of_secLaw


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
theorem _root_.solution : PositivityTheory.RgEis.SecLaw → PositivityTheory.RgEis.WallLaw := by
  first | exact @GlobalTheory.CompanionTheory.RgEis.wallLaw_of_secLaw | exact GlobalTheory.CompanionTheory.RgEis.wallLaw_of_secLaw | (intros; apply GlobalTheory.CompanionTheory.RgEis.wallLaw_of_secLaw <;> assumption)
end _root_.GlobalTheory.T
