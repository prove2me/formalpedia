-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.RBox.rat_check_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:14:39.719825+00:00
-- url     : https://prove2.me/submissions/62366bb9-7b64-4be2-839f-9f6e054f80b0

import Mathlib
import Definitions.Def_OAIQ098E026
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

lemma RBox.rat_check_e_oai (m n : ℤ) (hn : 0 < n) : (RBox.rat m n).RatCheck m n := by
  exact ⟨hn,floor_mul_le_e _ hn,by simpa only [RBox.rat, neg_mul] using le_ceil_mul_e (precision*m) hn⟩

end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.RBox.rat_check_e_oai := @OAI.SharpPlanar.IntegerIntervals.RBox.rat_check_e_oai
