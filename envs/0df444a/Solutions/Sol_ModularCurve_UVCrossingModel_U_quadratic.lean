-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.U_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/c5e677bf-2004-5aca-8afa-e79dab1da078

import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_U_mul_V
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_U_quadratic

open ModularCurve ModularCurve.UVCrossingModel in
theorem solution {W : Type*} [CommRing W] (π : W) :
    U π ^ 2 - S π * U π + const π π = 0 :=
  by
  rw [← ModularCurve.UVCrossingModel.U_mul_V, S_def]; ring

end S_ModularCurve_UVCrossingModel_U_quadratic
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_U_quadratic (solution)
