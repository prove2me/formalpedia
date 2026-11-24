-- Prove2me | solution 1 for GlobalTheory.T.unitarySatakeCoeff_lastSignChange_of_leviReduction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:25:48.325751+00:00
-- url     : https://prove2.me/submissions/4ad75b07-78f7-4dbf-af3d-a505a09433c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitarySatakeCoeffLastSignChangeOfLeviReduction
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitarySatakeCoeffLastSignChangeOfLeviReductionStatement
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_SatakeWeyl_coeffNeg_of_leviStep


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
theorem _root_.solution : GlobalTheory.SatakeWeyl.LeviStep → GlobalTheory.SatakeWeyl.IndexTwo → GlobalTheory.SatakeWeyl.IndexThree → GlobalTheory.SatakeWeyl.CoeffNeg := by
  first | exact @GlobalTheory.SatakeWeyl.coeffNeg_of_leviStep | exact GlobalTheory.SatakeWeyl.coeffNeg_of_leviStep | (intros; apply GlobalTheory.SatakeWeyl.coeffNeg_of_leviStep <;> assumption)
end _root_.GlobalTheory.T
