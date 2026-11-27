-- Prove2me | solution 1 for GlobalTheory.T.unipotent_convergence_of_parabolic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:34:10.11078+00:00
-- url     : https://prove2.me/submissions/15fcfe12-d642-4798-83ca-b4fc26ea6b2e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnipotentConvergenceOfParabolic
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnipotentConvergenceOfParabolicStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_UnitaryConv_convU_of_parLaw


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
theorem _root_.solution : PositivityTheory.RgEis.ParLaw → PositivityTheory.RgEis.ConvU := by
  first | exact @GlobalTheory.CompanionTheory.RgEis.UnitaryConv.convU_of_parLaw | exact GlobalTheory.CompanionTheory.RgEis.UnitaryConv.convU_of_parLaw | (intros; apply GlobalTheory.CompanionTheory.RgEis.UnitaryConv.convU_of_parLaw <;> assumption)
end _root_.GlobalTheory.T
