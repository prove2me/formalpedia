-- Prove2me | solution 1 for GlobalTheory.T.cellSumRankOneReflectionSymmetry_of_steps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:49:14.626662+00:00
-- url     : https://prove2.me/submissions/9f94cc8b-7937-4e97-bec9-bd08c1a87340

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CellSumRankOneReflectionSymmetryOfSteps
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CellSumRankOneReflectionSymmetryOfStepsStatement
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_SatakeWeyl_rankOne_of_steps


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
theorem _root_.solution : GlobalTheory.SatakeWeyl.Descent → GlobalTheory.SatakeWeyl.CellInv → GlobalTheory.SatakeWeyl.ChainSum → GlobalTheory.SatakeWeyl.RankOne := by
  first | exact @GlobalTheory.SatakeWeyl.rankOne_of_steps | exact GlobalTheory.SatakeWeyl.rankOne_of_steps | (intros; apply GlobalTheory.SatakeWeyl.rankOne_of_steps <;> assumption)
end _root_.GlobalTheory.T
