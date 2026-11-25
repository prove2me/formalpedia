-- Prove2me | solution 1 for GlobalTheory.T.general_linear_topological_group
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:21:43.847752+00:00
-- url     : https://prove2.me/submissions/7521d444-a9b5-4088-9af4-40079fa3c0cb

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GeneralLinearTopologicalGroup
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GeneralLinearTopologicalGroupStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisTop_grpTop


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
theorem _root_.solution : PositivityTheory.RgEis.GrpTop := by
  first | exact @GlobalTheory.CompanionTheory.RgEisTop.grpTop | exact GlobalTheory.CompanionTheory.RgEisTop.grpTop | (intros; apply GlobalTheory.CompanionTheory.RgEisTop.grpTop <;> assumption)
end _root_.GlobalTheory.T
