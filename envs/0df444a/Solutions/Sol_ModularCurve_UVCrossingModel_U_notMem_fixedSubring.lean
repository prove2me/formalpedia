-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.U_notMem_fixedSubring
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/5849b155-6d0d-5618-9c74-b5df362f66f9

import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_crossingSwap_U
import Theorems.Thm_ModularCurve_UVCrossingModel_U_ne_V
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_U_notMem_fixedSubring

open ModularCurve ModularCurve.UVCrossingModel in
theorem solution {W : Type*} [CommRing W] (π : W) [Nontrivial (W ⧸ Ideal.span {π})] :
    U π ∉ fixedSubring π :=
  by
  intro hmem
  rw [mem_fixedSubring_iff, ModularCurve.UVCrossingModel.crossingSwap_U] at hmem
  exact ModularCurve.UVCrossingModel.U_ne_V π hmem.symm

end S_ModularCurve_UVCrossingModel_U_notMem_fixedSubring
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_U_notMem_fixedSubring (solution)
