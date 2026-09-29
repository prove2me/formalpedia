-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.chartHom_X
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/e0ee5179-f468-57c1-b6fd-fb2ddb3e43b0

import Definitions.Def_ModularCurve_UVCrossingChart
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_chartHom_X

open ModularCurve ModularCurve.UVCrossingModel in
theorem solution {W : Type*} [CommRing W] (π : W) :
    chartHom π PowerSeries.X = S π :=
  by
  rw [chartHom_apply, PowerSeries.subst_X (hasSubst_sAmbient W), sAmbient, map_add, S_def]
  rfl

end S_ModularCurve_UVCrossingModel_chartHom_X
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_chartHom_X (solution)
