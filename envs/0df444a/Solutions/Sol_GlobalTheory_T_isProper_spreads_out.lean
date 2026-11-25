-- Prove2me | solution 1 for GlobalTheory.T.isProper_spreads_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:24:48.360496+00:00
-- url     : https://prove2.me/submissions/f34307d2-7217-44ca-88a4-932b6aa1ac76

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsProperSpreadsOut
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_CubeTheorem_SchemeModels
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsProperSpreadsOutStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SpreadingModels_properSpreads


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
theorem _root_.solution : GlobalTheory.SpreadingModels.Spreads (fun _ _ f => IsProper f) := by
  first | exact @GlobalTheory.CompanionTheory.SpreadingModels.properSpreads | exact GlobalTheory.CompanionTheory.SpreadingModels.properSpreads | (intros; apply GlobalTheory.CompanionTheory.SpreadingModels.properSpreads <;> assumption)
end _root_.GlobalTheory.T
