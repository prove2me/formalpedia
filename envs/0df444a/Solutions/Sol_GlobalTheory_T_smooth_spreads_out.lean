-- Prove2me | solution 1 for GlobalTheory.T.smooth_spreads_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:26:44.356937+00:00
-- url     : https://prove2.me/submissions/040070fb-d6fe-4d35-934e-2240830bed74

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SmoothSpreadsOut
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_CubeTheorem_SchemeModels
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SmoothSpreadsOutStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothSpread_smooth_spreads


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GlobalTheory.SpreadingModels
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : GlobalTheory.SpreadingModels.Spreads (fun _ _ f => Smooth f) := by
  first | exact @GlobalTheory.CompanionTheory.SmoothSpread.smooth_spreads | exact GlobalTheory.CompanionTheory.SmoothSpread.smooth_spreads | (intros; apply GlobalTheory.CompanionTheory.SmoothSpread.smooth_spreads <;> assumption)
end _root_.GlobalTheory.T
