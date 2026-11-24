-- Prove2me | solution 1 for GlobalTheory.T.unitary_levi_summation_geometric_series
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:26:06.216801+00:00
-- url     : https://prove2.me/submissions/b3c6bb73-efa0-4d31-8176-134ffd318b3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryLeviSummationGeometricSeries
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryLeviSummationGeometricSeriesStatement
import Theorems.Thm_GlobalTheory_InertZeta_step


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : Step := by
  first | exact @GlobalTheory.InertZeta.step | exact GlobalTheory.InertZeta.step | (intros; apply GlobalTheory.InertZeta.step <;> assumption)
end _root_.GlobalTheory.T
