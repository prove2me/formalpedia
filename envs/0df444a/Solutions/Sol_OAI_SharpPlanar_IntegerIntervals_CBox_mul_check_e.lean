-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.CBox.mul_check_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:12:48.3373+00:00
-- url     : https://prove2.me/submissions/e74bbd63-80dd-41a5-933d-ef14f35175b6

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

lemma CBox.mul_check_e_oai (a b : CBox) : a.MulCheck b (a.mul b) :=
  ⟨floor_mul_le_e _ (by norm_num [precision]),le_ceil_mul_e _ (by norm_num [precision]),
   floor_mul_le_e _ (by norm_num [precision]),le_ceil_mul_e _ (by norm_num [precision])⟩

end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.CBox.mul_check_e_oai := @OAI.SharpPlanar.IntegerIntervals.CBox.mul_check_e_oai
