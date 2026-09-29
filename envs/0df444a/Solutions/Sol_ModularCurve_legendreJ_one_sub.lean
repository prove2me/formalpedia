-- Prove2me | solution 1 for ModularCurve.legendreJ_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/661838b9-27b9-5353-b37a-65bfe6125622

import Mathlib
import Definitions.Def_ModularCurve_LegendreJ
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_legendreJ_one_sub

set_option autoImplicit false

namespace ModularCurve
p2m_export "ModularCurve" "legendreJ"
p2m_open "ModularCurve"

end ModularCurve

p2m_open "ModularCurve P2MW.S_ModularCurve_legendreJ_one_sub.ModularCurve"

theorem solution {K : Type*} [Field K] (t : K) : legendreJ (1 - t) = legendreJ t := by
  simp only [legendreJ]
  ring

end S_ModularCurve_legendreJ_one_sub
end P2MW
export P2MW.S_ModularCurve_legendreJ_one_sub (solution)
