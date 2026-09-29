-- Prove2me | solution 1 for ModularCurve.coeffEmb_jq_mem_laurentBaseChange_x1FunctionField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/be1f0add-0b31-5ee7-a7c5-bf6a8cb22e8b

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coeffEmb_jq_mem_laurentBaseChange_x1FunctionField

set_option autoImplicit false

theorem solution
    (L : Type) [Field L] [CharZero L] (N : ℕ) [NeZero N] :
    ModularCurve.coeffEmb L ModularCurve.jq ∈ ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N) := by
  apply ModularCurve.coeffEmb_mem_laurentBaseChange
  rw [← ModularCurve.jqModC_rat]
  show ModularCurve.jqModC ℚ ∈
    IntermediateField.adjoin ℚ (ModularCurve.intFormRatiosC ℚ (CongruenceSubgroup.Gamma1 N))
  exact IntermediateField.subset_adjoin ℚ _
    (ModularCurve.jqModC_mem_intFormRatiosC ℚ (CongruenceSubgroup.Gamma1 N))

end S_ModularCurve_coeffEmb_jq_mem_laurentBaseChange_x1FunctionField
end P2MW
export P2MW.S_ModularCurve_coeffEmb_jq_mem_laurentBaseChange_x1FunctionField (solution)
