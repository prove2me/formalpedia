-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.b8_4_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:45:38.943914+00:00
-- url     : https://prove2.me/submissions/faeb69c1-0018-4092-8ac8-8e0072e5a7ba

import Mathlib
import Definitions.Def_OAIQ098G080
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_betaBox_contains_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerAlpha
open IntegerIntervals IntegerBasis
lemma b8_4_contains_g_oai : b8_4.Contains (basisBeta 8 4) := by
  have he : betaBox 8 4 = b8_4 := by decide +kernel
  rw [← he]
  exact betaBox_contains_g 8 4
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.b8_4_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.b8_4_contains_g_oai
