-- Prove2me | solution 1 for ModularCurve.heckeBetaBar_coeffEmb
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/0c982981-762a-5bf2-8de4-76398ce584d3

import Definitions.Def_ModularCurve_HeckeOperator
import Theorems.Thm_ModularCurve_coeffEmb_qExpand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_heckeBetaBar_coeffEmb

open ModularCurve AlgebraicCurve AlgebraicCurve.SemilinearAut IntermediateField HahnSeries

theorem solution {L : Type*} [Field L] [Algebra ℚ L] (N ℓ : ℕ) [NeZero ℓ] {x : LaurentSeries ℚ} (hx : x ∈ ModularCurve.modularFunctionFieldFull N) : ((ModularCurve.heckeBetaBar L N ℓ ⟨ModularCurve.coeffEmb L x, ModularCurve.coeffEmb_mem_laurentBaseChange L hx⟩ : ModularCurve.laurentBaseChange L (ModularCurve.modularFunctionFieldFull (N * ℓ))) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ ℓ x) :=
  by
  rw [coe_heckeBetaBar, coeffEmb_qExpand]

end S_ModularCurve_heckeBetaBar_coeffEmb
end P2MW
export P2MW.S_ModularCurve_heckeBetaBar_coeffEmb (solution)
