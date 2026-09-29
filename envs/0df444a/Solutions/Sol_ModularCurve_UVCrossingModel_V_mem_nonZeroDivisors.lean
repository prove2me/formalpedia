-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.V_mem_nonZeroDivisors
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/b3d327b3-3e7b-58a1-b068-8002c724db34

import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_const_mem_nonZeroDivisors
import Theorems.Thm_ModularCurve_UVCrossingModel_U_mul_V
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_V_mem_nonZeroDivisors

open ModularCurve ModularCurve.UVCrossingModel in
theorem solution {W : Type*} [CommRing W] {π : W} (hπ : π ∈ nonZeroDivisors W) :
    V π ∈ nonZeroDivisors (UVCrossingModel W π) :=
  by
  have h := ModularCurve.UVCrossingModel.const_mem_nonZeroDivisors hπ
  rw [← ModularCurve.UVCrossingModel.U_mul_V] at h
  exact (mul_mem_nonZeroDivisors.mp h).2

end S_ModularCurve_UVCrossingModel_V_mem_nonZeroDivisors
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_V_mem_nonZeroDivisors (solution)
