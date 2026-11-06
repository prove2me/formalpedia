-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.CBox.contains_scale_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T03:23:06.986805+00:00
-- url     : https://prove2.me/submissions/7e4122f3-3409-4347-9f97-bc5f25f2410c

import Mathlib
import Definitions.Def_OAIQ098E031
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_scale_check_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_scale_contains_e

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

lemma CBox.contains_scale_e_oai {a : CBox} {z : ℂ} (hz : a.Contains z) (m n : ℤ) (hn : 0 < n) :
    (a.scale m n).Contains (((m:ℂ)/n)*z) := CBox.scale_contains_e hz (CBox.scale_check_e _ _ _ hn)

end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.CBox.contains_scale_e_oai := @OAI.SharpPlanar.IntegerIntervals.CBox.contains_scale_e_oai
