-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.piI_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:53:54.180395+00:00
-- url     : https://prove2.me/submissions/c9d8ad53-531b-41a9-84de-763a2cd91ccb

import Mathlib
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_piBounds_contains_g

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

lemma piI_contains_g_oai : piI.Contains (Complex.I*Real.pi) := by
  constructor
  · norm_num [CBox.Contains,RBox.Contains,piI]
  · simpa [piI] using piBounds_contains_g

end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.piI_contains_g_oai := @OAI.SharpPlanar.IntegerIntervals.piI_contains_g_oai
