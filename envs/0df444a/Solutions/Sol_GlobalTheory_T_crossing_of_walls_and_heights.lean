-- Prove2me | solution 1 for GlobalTheory.T.crossing_of_walls_and_heights
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:16:09.307344+00:00
-- url     : https://prove2.me/submissions/bdf56b88-18ce-4e43-81da-f51e07e829c5

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CrossingOfWallsAndHeights
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CrossingOfWallsAndHeightsStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisCross_cross


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
theorem _root_.solution : PositivityTheory.RgEis.SecLaw → PositivityTheory.RgEis.HtLip → PositivityTheory.RgEis.PiLocalization₂ → PositivityTheory.RgEis.WallLaw → PositivityTheory.RgEis.Cross := by
  first | exact @GlobalTheory.CompanionTheory.RgEisCross.cross | exact GlobalTheory.CompanionTheory.RgEisCross.cross | (intros; apply GlobalTheory.CompanionTheory.RgEisCross.cross <;> assumption)
end _root_.GlobalTheory.T
