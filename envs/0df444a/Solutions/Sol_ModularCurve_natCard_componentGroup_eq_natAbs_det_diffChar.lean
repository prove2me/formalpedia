-- Prove2me | solution 1 for ModularCurve.natCard_componentGroup_eq_natAbs_det_diffChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/118639b8-0631-5e37-98f7-a8b3fbbefeb2

import Definitions.Def_ModularCurve_ComponentGroupKirchhoff
import Theorems.Thm_ModularCurve_natCard_componentGroup_eq_natAbs_det
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_natCard_componentGroup_eq_natAbs_det_diffChar

open ModularCurve Module

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ] [DecidableEq κ]
    {e : ι → ℕ} (he : ∀ x, 0 < e x) (σ : Option κ ≃ ι) :
    Nat.card (componentGroup e) = ((gramMatrixOf e (diffChar σ)).det).natAbs := by
  have h : gramMatrixOf e ⇑(diffBasisOf σ) = gramMatrixOf e (diffChar σ) := by
    ext i j
    rw [gramMatrixOf_apply, gramMatrixOf_apply, diffBasisOf_apply, diffBasisOf_apply]
  rw [← h]
  exact ModularCurve.natCard_componentGroup_eq_natAbs_det he (diffBasisOf σ)

end S_ModularCurve_natCard_componentGroup_eq_natAbs_det_diffChar
end P2MW
export P2MW.S_ModularCurve_natCard_componentGroup_eq_natAbs_det_diffChar (solution)
