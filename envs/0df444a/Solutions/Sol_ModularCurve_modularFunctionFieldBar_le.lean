-- Prove2me | solution 1 for ModularCurve.modularFunctionFieldBar_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/1ba5b0fa-72be-567b-aa37-97ddb21da189

import Definitions.Def_ModularCurve_ArithmeticGalois
import Theorems.Thm_ModularCurve_laurentBaseChange_mono
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_modularFunctionFieldBar_le

open ModularCurve AlgebraicCurve IntermediateField HahnSeries

theorem solution (N : ℕ) [NeZero N] {M : ℕ} [NeZero M] (h : N ∣ M) : ModularCurve.modularFunctionFieldBar N ≤ ModularCurve.modularFunctionFieldBar M :=
  laurentBaseChange_mono _ (full_degeneracy_le h)

end S_ModularCurve_modularFunctionFieldBar_le
end P2MW
export P2MW.S_ModularCurve_modularFunctionFieldBar_le (solution)
