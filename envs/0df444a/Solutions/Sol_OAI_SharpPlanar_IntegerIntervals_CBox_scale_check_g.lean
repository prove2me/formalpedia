-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.CBox.scale_check_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:44:35.644525+00:00
-- url     : https://prove2.me/submissions/c0931eeb-f531-41a1-a4f9-acb33466f57e

import Mathlib
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_scale_check_g

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

lemma CBox.scale_check_g_oai (a : CBox) (m n : ℤ) (hn : 0 < n) : a.ScaleCheck (a.scale m n) m n :=
  ⟨RBox.scale_check_g _ _ _ hn,RBox.scale_check_g _ _ _ hn⟩

end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.CBox.scale_check_g_oai := @OAI.SharpPlanar.IntegerIntervals.CBox.scale_check_g_oai
