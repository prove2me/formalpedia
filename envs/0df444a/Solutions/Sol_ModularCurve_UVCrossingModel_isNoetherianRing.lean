-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.isNoetherianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/3b73f31a-9b47-539c-b9d3-ea8b3c3f3f8a

import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_MvPowerSeries_isNoetherianRing_of_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_isNoetherianRing

open ModularCurve ModularCurve.UVCrossingModel in
theorem solution {W : Type*} [CommRing W] [IsNoetherianRing W] (π : W) :
    IsNoetherianRing (UVCrossingModel W π) :=
  by
  haveI : IsNoetherianRing (MvPowerSeries (Fin 2) W) := MvPowerSeries.isNoetherianRing_of_finite
  exact isNoetherianRing_of_surjective (MvPowerSeries (Fin 2) W) (UVCrossingModel W π)
    (UVCrossingModel.mk π) (UVCrossingModel.mk_surjective π)

end S_ModularCurve_UVCrossingModel_isNoetherianRing
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_isNoetherianRing (solution)
