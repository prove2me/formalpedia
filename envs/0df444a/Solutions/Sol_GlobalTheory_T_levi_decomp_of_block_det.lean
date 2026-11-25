-- Prove2me | solution 1 for GlobalTheory.T.levi_decomp_of_block_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:22:17.249808+00:00
-- url     : https://prove2.me/submissions/0eb9e476-7490-43d4-9fd8-a18e6b879f50

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviDecompOfBlockDet
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviDecompOfBlockDetStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLevi_leviS


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
theorem _root_.solution : PositivityTheory.RgEis.BdetLaw → PositivityTheory.RgEis.ExtLaw → PositivityTheory.RgEis.GrpTop → PositivityTheory.RgEis.LeviS := by
  first | exact @GlobalTheory.CompanionTheory.RgEisLevi.leviS | exact GlobalTheory.CompanionTheory.RgEisLevi.leviS | (intros; apply GlobalTheory.CompanionTheory.RgEisLevi.leviS <;> assumption)
end _root_.GlobalTheory.T
