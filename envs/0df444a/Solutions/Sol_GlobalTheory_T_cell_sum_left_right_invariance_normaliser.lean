-- Prove2me | solution 1 for GlobalTheory.T.cell_sum_left_right_invariance_normaliser
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:51:51.838802+00:00
-- url     : https://prove2.me/submissions/47677b1c-aba2-44f6-9df4-5ec2ac4e1555

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CellSumLeftRightInvarianceNormaliser
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CellSumLeftRightInvarianceNormaliserStatement
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_SatakeWeyl_cellInv_holds


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
theorem _root_.solution : GlobalTheory.SatakeWeyl.CellInv := by
  first | exact @GlobalTheory.SatakeWeyl.cellInv_holds | exact GlobalTheory.SatakeWeyl.cellInv_holds | (intros; apply GlobalTheory.SatakeWeyl.cellInv_holds <;> assumption)
end _root_.GlobalTheory.T
