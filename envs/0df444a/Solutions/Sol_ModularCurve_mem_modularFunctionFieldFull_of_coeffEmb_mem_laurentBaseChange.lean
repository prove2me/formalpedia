-- Prove2me | solution 1 for ModularCurve.mem_modularFunctionFieldFull_of_coeffEmb_mem_laurentBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/1fa80862-913f-5658-810c-2ba6d925ece1

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_mem_of_coeffEmb_mem_laurentBaseChange
import Mathlib.Data.Complex.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_mem_modularFunctionFieldFull_of_coeffEmb_mem_laurentBaseChange

theorem solution (N : ℕ) [NeZero N]
    (x : LaurentSeries ℚ)
    (hx : ModularCurve.coeffEmb ℂ x ∈
      ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) :
    x ∈ ModularCurve.modularFunctionFieldFull N :=
  ModularCurve.mem_of_coeffEmb_mem_laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N) x hx

end S_ModularCurve_mem_modularFunctionFieldFull_of_coeffEmb_mem_laurentBaseChange
end P2MW
export P2MW.S_ModularCurve_mem_modularFunctionFieldFull_of_coeffEmb_mem_laurentBaseChange (solution)
