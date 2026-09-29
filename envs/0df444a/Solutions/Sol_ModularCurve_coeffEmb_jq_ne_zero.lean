-- Prove2me | solution 1 for ModularCurve.coeffEmb_jq_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/a3c68cd0-c219-5759-882d-f144dfd1c746

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coeffEmb_jq_ne_zero

set_option autoImplicit false

theorem solution
    (L : Type) [Field L] [CharZero L] : ModularCurve.coeffEmb L ModularCurve.jq ≠ 0 :=
  (map_ne_zero (ModularCurve.coeffEmb L)).mpr ModularCurve.jq_ne_zero

end S_ModularCurve_coeffEmb_jq_ne_zero
end P2MW
export P2MW.S_ModularCurve_coeffEmb_jq_ne_zero (solution)
