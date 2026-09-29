-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.range_chartHom_le_fixedSubring
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/55e6e2d9-f316-574e-8ded-e754e5643f55

import Definitions.Def_ModularCurve_UVCrossingChart
import Theorems.Thm_ModularCurve_UVCrossingModel_crossingSwap_chartHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_range_chartHom_le_fixedSubring

open ModularCurve ModularCurve.UVCrossingModel in
theorem solution {W : Type*} [CommRing W] (π : W) :
    (chartHom π).range ≤ fixedSubring π :=
  by
  intro x hx
  obtain ⟨f, rfl⟩ := RingHom.mem_range.mp hx
  exact mem_fixedSubring_iff.mpr (ModularCurve.UVCrossingModel.crossingSwap_chartHom π f)

end S_ModularCurve_UVCrossingModel_range_chartHom_le_fixedSubring
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_range_chartHom_le_fixedSubring (solution)
