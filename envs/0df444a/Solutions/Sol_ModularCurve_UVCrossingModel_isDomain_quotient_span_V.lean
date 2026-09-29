-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.isDomain_quotient_span_V
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/77f97dfb-0828-5bbb-b431-5645b25bd1e5

import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_ringEquiv_quotient_span_V_powerSeries
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_isDomain_quotient_span_V

open ModularCurve ModularCurve.UVCrossingModel in
theorem solution {W : Type*} [CommRing W] (π : W) [IsDomain (W ⧸ Ideal.span {π})] :
    IsDomain (UVCrossingModel W π ⧸ Ideal.span {V π}) :=
  by
  obtain ⟨e, -, -, -⟩ := ModularCurve.UVCrossingModel.exists_ringEquiv_quotient_span_V_powerSeries π
  exact MulEquiv.isDomain (PowerSeries (W ⧸ Ideal.span {π})) e.toMulEquiv

end S_ModularCurve_UVCrossingModel_isDomain_quotient_span_V
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_isDomain_quotient_span_V (solution)
