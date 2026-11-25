-- Prove2me | solution 1 for GlobalTheory.T.block_determinant_law
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:13:33.17449+00:00
-- url     : https://prove2.me/submissions/522bdc4c-70aa-4fe2-9ed0-1cb27e4ad354

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BlockDeterminantLaw
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BlockDeterminantLawStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_bdetLaw


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
theorem _root_.solution : PositivityTheory.RgEis.BdetLaw := by
  first | exact @GlobalTheory.CompanionTheory.RgEis.bdetLaw | exact GlobalTheory.CompanionTheory.RgEis.bdetLaw | (intros; apply GlobalTheory.CompanionTheory.RgEis.bdetLaw <;> assumption)
end _root_.GlobalTheory.T
