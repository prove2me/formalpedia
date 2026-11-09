-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.quarterArgBox_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:34:43.567979+00:00
-- url     : https://prove2.me/submissions/1e3cfcc4-9748-40a3-9aae-21f4f0658e63

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G089
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_scale_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_piI_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_zBox_contains_g

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

lemma quarterArgBox_contains_g_oai {a : RBox} {x : ℝ} (hx : a.Contains x)
    (hi : (denBox a).GoodInv) :
    (quarterArgBox a).Contains (Complex.I*Real.pi*pointZ x/4) := by
  have hh := CBox.contains_scale_g (CBox.contains_mul_g piI_contains_g (zBox_contains_g hx hi)) 1 4 (by norm_num)
  unfold quarterArgBox
  convert hh using 1 <;> first | rfl | ring

end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.quarterArgBox_contains_g_oai := @OAI.SharpPlanar.IntegerIntervals.quarterArgBox_contains_g_oai
