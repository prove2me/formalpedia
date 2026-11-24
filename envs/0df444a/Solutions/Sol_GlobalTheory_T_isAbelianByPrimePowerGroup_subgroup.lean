-- Prove2me | solution 1 for GlobalTheory.T.isAbelianByPrimePowerGroup_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:15:02.209528+00:00
-- url     : https://prove2.me/submissions/56ccb158-7653-4b9f-9e16-49607c553d46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsAbelianByPrimePowerGroupSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsAbelianByPrimePowerGroupSubgroupStatement
import Theorems.Thm_GlobalTheory_BI_AbByP_subgroup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (G : Type) [Group G] (T : Subgroup G), AbByP G → AbByP T := by
  first | exact @GlobalTheory.BI.AbByP.subgroup | exact GlobalTheory.BI.AbByP.subgroup | (intros; apply GlobalTheory.BI.AbByP.subgroup <;> assumption)
end _root_.GlobalTheory.T
