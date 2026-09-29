-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.U_mul_V
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/7be730f0-fc87-5e2c-ba2e-65b427023c51

import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_U_mul_V

open ModularCurve ModularCurve.UVCrossingModel

theorem solution {W : Type*} [CommRing W] (π : W) :
    U π * V π = const π π :=
  by
  show Ideal.Quotient.mk _ _ * Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
  rw [← map_mul, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact Ideal.subset_span rfl

end S_ModularCurve_UVCrossingModel_U_mul_V
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_U_mul_V (solution)
