-- Prove2me | solution 1 for ModularCurve.monic_fibrePoly
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/f61f5c5f-634a-5a84-8647-cfd0482becdf

import Mathlib
import Definitions.Def_ModularCurve_FibrePoly
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_monic_fibrePoly

open Polynomial ModularCurve

theorem solution {K : Type*} [Field K] {Φ : Polynomial (Polynomial ℤ)} (hΦ : Φ.Monic)
    (a : K) : (fibrePoly Φ a).Monic := by
  exact hΦ.map _

end S_ModularCurve_monic_fibrePoly
end P2MW
export P2MW.S_ModularCurve_monic_fibrePoly (solution)
