-- Prove2me | solution 1 for ModularCurve.coeffEmb_qExpand
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/9d7acf02-2ba9-5f6a-96e7-487ba04adacc

import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coeffEmb_qExpand

open ModularCurve IntermediateField HahnSeries

theorem solution (L : Type*) [Field L] [Algebra ℚ L] (n : ℕ) [NeZero n] (x : LaurentSeries ℚ) : ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ n x) = ModularCurve.qExpand L n (ModularCurve.coeffEmb L x) :=
  coeffMap_qExpand _ n x

end S_ModularCurve_coeffEmb_qExpand
end P2MW
export P2MW.S_ModularCurve_coeffEmb_qExpand (solution)
