-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.map_crossingSwap_span_U
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/13ca1ff5-63dd-5563-be54-0f4814a7b525

import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_crossingSwap_U
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_map_crossingSwap_span_U

open ModularCurve ModularCurve.UVCrossingModel in
theorem solution {W : Type*} [CommRing W] (π : W) :
    Ideal.map (crossingSwap π) (Ideal.span {U π}) = Ideal.span {V π} :=
  by
  rw [Ideal.map_span, Set.image_singleton, ModularCurve.UVCrossingModel.crossingSwap_U]

end S_ModularCurve_UVCrossingModel_map_crossingSwap_span_U
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_map_crossingSwap_span_U (solution)
