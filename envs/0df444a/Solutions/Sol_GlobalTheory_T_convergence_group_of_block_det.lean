-- Prove2me | solution 1 for GlobalTheory.T.convergence_group_of_block_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:19:50.932964+00:00
-- url     : https://prove2.me/submissions/b2aee084-ac47-4baf-85f9-bd045d7c1333

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConvergenceGroupOfBlockDet
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConvergenceGroupOfBlockDetStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_convGrOf


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
theorem _root_.solution : PositivityTheory.RgEis.BdetLaw → PositivityTheory.RgEis.ExtLaw → PositivityTheory.RgEis.ConvGrOf := by
  first | exact @GlobalTheory.CompanionTheory.Plucker.convGrOf | exact GlobalTheory.CompanionTheory.Plucker.convGrOf | (intros; apply GlobalTheory.CompanionTheory.Plucker.convGrOf <;> assumption)
end _root_.GlobalTheory.T
