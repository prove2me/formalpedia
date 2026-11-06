-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.RBox.scale_check_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:15:45.766109+00:00
-- url     : https://prove2.me/submissions/28d0e6d3-51d9-4e84-b41d-d1ac78ec9ac0

import Mathlib
import Definitions.Def_OAIQ098E030
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_floor_mul_le_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_le_ceil_mul_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Intervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integer interval arithmetic for a planar Fourier certificate

Real and complex interval operations with precision `10^30`, including checked
Taylor bounds for the complex exponential and rational Fourier kernels.
-/

namespace SharpPlanar.IntegerIntervals

lemma RBox.scale_check_e_oai (a : RBox) (m n : ℤ) (hn : 0 < n) : a.ScaleCheck (a.scale m n) m n :=
  ⟨hn,floor_mul_le_e _ hn,le_ceil_mul_e _ hn⟩

end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.RBox.scale_check_e_oai := @OAI.SharpPlanar.IntegerIntervals.RBox.scale_check_e_oai
