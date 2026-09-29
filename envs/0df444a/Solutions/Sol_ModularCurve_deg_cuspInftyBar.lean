-- Prove2me | solution 1 for ModularCurve.deg_cuspInftyBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/e0363130-4057-57ec-bd88-1a630a929c66

import Definitions.Def_ModularCurve_AtkinLehner
import Theorems.Thm_ModularCurve_deg_qInftyPlaceBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_deg_cuspInftyBar

open ModularCurve AlgebraicCurve
open scoped Pointwise

theorem solution (N : ℕ) [NeZero N] :
    (cuspInftyBar N).deg = 1 :=
  ModularCurve.deg_qInftyPlaceBar (AlgebraicClosure ℚ) _

end S_ModularCurve_deg_cuspInftyBar
end P2MW
export P2MW.S_ModularCurve_deg_cuspInftyBar (solution)
