-- Prove2me | solution 1 for GlobalTheory.T.siegel_induction_from_gallery
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:33:27.346549+00:00
-- url     : https://prove2.me/submissions/b86f97c3-06e0-4c82-a64e-d9eaac0b4254

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SiegelInductionFromGallery
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SiegelInductionFromGalleryStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_sgStep


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
theorem _root_.solution : PositivityTheory.RgEis.Gallery → PositivityTheory.RgEis.Transfer → PositivityTheory.RgEis.Twist → PositivityTheory.RgEis.GrpTop → PositivityTheory.RgEis.ParLaw → PositivityTheory.RgEis.LeviS → PositivityTheory.RgEis.LeviQ → PositivityTheory.RgEis.ConvGrOf → PositivityTheory.RgEis.ConvU → PositivityTheory.RgEis.SgStep := by
  first | exact @GlobalTheory.CompanionTheory.RgEis.sgStep | exact GlobalTheory.CompanionTheory.RgEis.sgStep | (intros; apply GlobalTheory.CompanionTheory.RgEis.sgStep <;> assumption)
end _root_.GlobalTheory.T
