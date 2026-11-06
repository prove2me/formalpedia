-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.CBox.scale_check_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:13:33.434602+00:00
-- url     : https://prove2.me/submissions/8293cfbd-3d69-47bd-95af-5d9318019dc0

import Mathlib
import Definitions.Def_OAIQ098E030
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_scale_check_e

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

lemma CBox.scale_check_e_oai (a : CBox) (m n : ℤ) (hn : 0 < n) : a.ScaleCheck (a.scale m n) m n :=
  ⟨RBox.scale_check_e _ _ _ hn,RBox.scale_check_e _ _ _ hn⟩

end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.CBox.scale_check_e_oai := @OAI.SharpPlanar.IntegerIntervals.CBox.scale_check_e_oai
