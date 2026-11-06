-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.quarterArgBox_contains_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T03:30:51.870204+00:00
-- url     : https://prove2.me/submissions/3d70b5ca-ddea-41f5-bd76-6744edd3de06

import Mathlib
import Definitions.Def_OAIQ098E031
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_scale_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_piI_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_zBox_contains_e

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

lemma quarterArgBox_contains_e_oai {a : RBox} {x : ℝ} (hx : a.Contains x)
    (hi : (denBox a).GoodInv) :
    (quarterArgBox a).Contains (Complex.I*Real.pi*pointZ x/4) := by
  have hh := CBox.contains_scale_e (CBox.contains_mul_e piI_contains_e (zBox_contains_e hx hi)) 1 4 (by norm_num)
  unfold quarterArgBox
  convert hh using 1 <;> first | rfl | ring

end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.quarterArgBox_contains_e_oai := @OAI.SharpPlanar.IntegerIntervals.quarterArgBox_contains_e_oai
