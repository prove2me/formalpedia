-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.RBox.mul_check_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:37:47.042217+00:00
-- url     : https://prove2.me/submissions/2cb18afe-93b9-4549-82b3-1631baaff699

import Mathlib
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

lemma RBox.mul_check_g_oai (a b : RBox) : a.MulCheck b (a.mul b) :=
  ⟨floor_mul_le_g _ (by norm_num [precision]),le_ceil_mul_g _ (by norm_num [precision])⟩

end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.RBox.mul_check_g_oai := @OAI.SharpPlanar.IntegerIntervals.RBox.mul_check_g_oai
