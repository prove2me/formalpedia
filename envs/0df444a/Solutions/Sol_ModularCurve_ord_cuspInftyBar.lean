-- Prove2me | solution 1 for ModularCurve.ord_cuspInftyBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/110fbe58-b8e6-5d21-9b21-574cbec2ab2f

import Definitions.Def_ModularCurve_AtkinLehner
import Theorems.Thm_ModularCurve_ord_qInftyPlaceBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_cuspInftyBar

open ModularCurve AlgebraicCurve
open scoped Pointwise

theorem solution (N : ℕ) [NeZero N] (f : modularFunctionFieldBar N) :
    (cuspInftyBar N).ord f = (f : LaurentSeries (AlgebraicClosure ℚ)).order :=
  ModularCurve.ord_qInftyPlaceBar (AlgebraicClosure ℚ) _ f

end S_ModularCurve_ord_cuspInftyBar
end P2MW
export P2MW.S_ModularCurve_ord_cuspInftyBar (solution)
