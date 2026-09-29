-- Prove2me | solution 1 for ModularCurve.laurentBaseChange_mono
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/4bf38222-df92-50f9-89db-71cff8f8e801

import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_laurentBaseChange_mono

open ModularCurve IntermediateField HahnSeries

theorem solution (L : Type*) [Field L] [Algebra ℚ L] {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)} (h : F₀ ≤ F₁) : ModularCurve.laurentBaseChange L F₀ ≤ ModularCurve.laurentBaseChange L F₁ :=
  by
  rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, hy, rfl⟩
  exact coeffEmb_mem_laurentBaseChange L (h hy)

end S_ModularCurve_laurentBaseChange_mono
end P2MW
export P2MW.S_ModularCurve_laurentBaseChange_mono (solution)
