-- Prove2me | solution 1 for ModularCurve.full_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/c1865caa-8549-52e8-ba93-1a9ad7cbded7

import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_functionFieldGeneration_iff_full_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_full_one_eq

open ModularCurve IntermediateField

noncomputable section

theorem solution : modularFunctionFieldFull 1 = modularFunctionField 1 :=
  (ModularCurve.functionFieldGeneration_iff_full_eq 1).mp functionFieldGeneration_one

end

end S_ModularCurve_full_one_eq
end P2MW
export P2MW.S_ModularCurve_full_one_eq (solution)
