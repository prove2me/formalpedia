-- Prove2me | solution 1 for GlobalTheory.T.unitaryRankTwoRootIndex_of_traceZeroCard
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:19:38.551476+00:00
-- url     : https://prove2.me/submissions/cb144003-ed33-43d1-b3b9-9229b4d2ad8a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryRankTwoRootIndexOfTraceZeroCard
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryRankTwoRootIndexOfTraceZeroCardStatement
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_SatakeWeyl_indexTwo_of_traceZeroIndex


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : GlobalTheory.SatakeWeyl.TraceZeroIndex → GlobalTheory.SatakeWeyl.IndexTwo := by
  first | exact @GlobalTheory.SatakeWeyl.indexTwo_of_traceZeroIndex | exact GlobalTheory.SatakeWeyl.indexTwo_of_traceZeroIndex | (intros; apply GlobalTheory.SatakeWeyl.indexTwo_of_traceZeroIndex <;> assumption)
end _root_.GlobalTheory.T
