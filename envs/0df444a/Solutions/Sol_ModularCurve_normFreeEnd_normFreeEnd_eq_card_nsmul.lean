-- Prove2me | solution 1 for ModularCurve.normFreeEnd_normFreeEnd_eq_card_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/6b8df4cd-0799-581f-bf64-2a7e6f5d7e1b

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_ModularCurve_X1PrimitiveSpecializationAtP

import Theorems.Thm_ModularCurve_sum_diamondOneBar_normFreeEnd_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_normFreeEnd_normFreeEnd_eq_card_nsmul

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem solution
    (M p : ℕ) [NeZero M] [Fact p.Prime] (hpM : p ∣ M)
    (hIn : ModularCurve.HeckeDiamondInputsAll M) (x : JOne M) :
    normFreeEnd M (normFreeRepsAt M p) (normFreeEnd M (normFreeRepsAt M p) x) =
      (normFreeRepsAt M p).card • normFreeEnd M (normFreeRepsAt M p) x := by

  rw [normFreeEnd_apply M (normFreeRepsAt M p) (normFreeEnd M (normFreeRepsAt M p) x),
    (ModularCurve.sum_diamondOneBar_normFreeEnd_eq_zero M p hpM hIn x).1, sub_zero]

end S_ModularCurve_normFreeEnd_normFreeEnd_eq_card_nsmul
end P2MW
export P2MW.S_ModularCurve_normFreeEnd_normFreeEnd_eq_card_nsmul (solution)
