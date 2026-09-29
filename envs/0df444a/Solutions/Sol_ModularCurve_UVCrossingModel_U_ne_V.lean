-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.U_ne_V
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/3c3cd333-c9f1-5729-ba21-177628b1da77

import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_U_notMem_span_V
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_U_ne_V

open ModularCurve ModularCurve.UVCrossingModel in
theorem solution {W : Type*} [CommRing W] (π : W) [Nontrivial (W ⧸ Ideal.span {π})] :
    U π ≠ V π :=
  by
  intro h
  apply ModularCurve.UVCrossingModel.U_notMem_span_V π
  rw [h]
  exact Ideal.mem_span_singleton_self _

end S_ModularCurve_UVCrossingModel_U_ne_V
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_U_ne_V (solution)
