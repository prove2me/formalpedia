-- Prove2me | solution 1 for GlobalTheory.T.unitaryCellSumLeviReduction_of_steps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:05:25.484278+00:00
-- url     : https://prove2.me/submissions/d4b231e2-47e8-410c-a7ea-f8ab8e489f9d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryCellSumLeviReductionOfSteps
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryCellSumLeviReductionOfStepsStatement
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_SatakeWeyl_leviStep_of_steps


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
theorem _root_.solution : GlobalTheory.SatakeWeyl.RankOne → GlobalTheory.SatakeWeyl.EmbExists → GlobalTheory.SatakeWeyl.EmbMem → GlobalTheory.SatakeWeyl.EmbTorus → GlobalTheory.SatakeWeyl.LeviRad → GlobalTheory.SatakeWeyl.UnipSplit → GlobalTheory.SatakeWeyl.Contract → GlobalTheory.SatakeWeyl.TorusConj → GlobalTheory.SatakeWeyl.LeviStep := by
  first | exact @GlobalTheory.SatakeWeyl.leviStep_of_steps | exact GlobalTheory.SatakeWeyl.leviStep_of_steps | (intros; apply GlobalTheory.SatakeWeyl.leviStep_of_steps <;> assumption)
end _root_.GlobalTheory.T
