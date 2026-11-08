-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.CBox.mul_check_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:09:49.179584+00:00
-- url     : https://prove2.me/submissions/08b7dd76-1070-4550-a206-78a6636a7e42

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

lemma CBox.mul_check_g_oai (a b : CBox) : a.MulCheck b (a.mul b) :=
  ⟨floor_mul_le_g _ (by norm_num [precision]),le_ceil_mul_g _ (by norm_num [precision]),
   floor_mul_le_g _ (by norm_num [precision]),le_ceil_mul_g _ (by norm_num [precision])⟩

end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.CBox.mul_check_g_oai := @OAI.SharpPlanar.IntegerIntervals.CBox.mul_check_g_oai
