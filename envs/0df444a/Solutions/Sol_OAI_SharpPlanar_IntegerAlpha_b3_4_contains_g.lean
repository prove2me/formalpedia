-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.b3_4_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:43:17.154655+00:00
-- url     : https://prove2.me/submissions/fedf4741-659d-4812-b46f-c412c0903147

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
lemma b3_4_contains_g_oai : b3_4.Contains (basisBeta 3 4) := by
  have he : betaBox 3 4 = b3_4 := by decide +kernel
  rw [← he]
  exact betaBox_contains_g 3 4
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.b3_4_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.b3_4_contains_g_oai
