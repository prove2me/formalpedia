-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.RBox.rat_check_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:40:21.505249+00:00
-- url     : https://prove2.me/submissions/c0a47aaa-c460-41ae-854d-e6fbdaf24cfb

import Mathlib
import Definitions.Def_OAIQ098G047
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_floor_mul_le_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_le_ceil_mul_g

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

lemma RBox.rat_check_g_oai (m n : ℤ) (hn : 0 < n) : (RBox.rat m n).RatCheck m n := by
  exact ⟨hn,floor_mul_le_g _ hn,by simpa only [RBox.rat, neg_mul] using le_ceil_mul_g (precision*m) hn⟩

end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.RBox.rat_check_g_oai := @OAI.SharpPlanar.IntegerIntervals.RBox.rat_check_g_oai
