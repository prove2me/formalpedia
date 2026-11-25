-- Prove2me | solution 1 for GlobalTheory.T.scheme_models_spread
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:24:33.93134+00:00
-- url     : https://prove2.me/submissions/92e20493-a87b-4216-9d14-43dc82f3ca1e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SchemeModelsSpread
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_CubeTheorem_SchemeModels
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SchemeModelsSpreadStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_NoethApprox_schemeModels


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
theorem _root_.solution : GlobalTheory.SpreadingModels.SchemeModels := by
  first | exact @GlobalTheory.CompanionTheory.NoethApprox.schemeModels | exact GlobalTheory.CompanionTheory.NoethApprox.schemeModels | (intros; apply GlobalTheory.CompanionTheory.NoethApprox.schemeModels <;> assumption)
end _root_.GlobalTheory.T
