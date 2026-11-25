-- Prove2me | solution 1 for GlobalTheory.T.parabolic_law_of_block_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:24:29.427971+00:00
-- url     : https://prove2.me/submissions/5d5e2127-6231-4cc7-92d5-6cec8b2047f6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ParabolicLawOfBlockDet
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ParabolicLawOfBlockDetStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisPar_parLaw


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
theorem _root_.solution : PositivityTheory.RgEis.BdetLaw → PositivityTheory.RgEis.ExtLaw → PositivityTheory.RgEis.GrpTop → PositivityTheory.RgEis.ParLaw := by
  first | exact @GlobalTheory.CompanionTheory.RgEisPar.parLaw | exact GlobalTheory.CompanionTheory.RgEisPar.parLaw | (intros; apply GlobalTheory.CompanionTheory.RgEisPar.parLaw <;> assumption)
end _root_.GlobalTheory.T
