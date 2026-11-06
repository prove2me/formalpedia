-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.piI_contains_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T03:30:50.6625+00:00
-- url     : https://prove2.me/submissions/77bef9d1-b22b-4cae-beed-4c2797d1f833

import Mathlib
import Definitions.Def_OAIQ098E031
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_piBounds_contains_e

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

lemma piI_contains_e_oai : piI.Contains (Complex.I*Real.pi) := by
  constructor
  · norm_num [CBox.Contains,RBox.Contains,piI]
  · simpa [piI] using piBounds_contains_e

end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.piI_contains_e_oai := @OAI.SharpPlanar.IntegerIntervals.piI_contains_e_oai
