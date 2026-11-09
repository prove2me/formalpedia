-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.b0_3_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:38:39.907391+00:00
-- url     : https://prove2.me/submissions/4b87d2bb-2af4-4984-a35f-1ba58bd40dc2

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
lemma b0_3_contains_g_oai : b0_3.Contains (basisBeta 0 3) := by
  have he : betaBox 0 3 = b0_3 := by decide +kernel
  rw [← he]
  exact betaBox_contains_g 0 3
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.b0_3_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.b0_3_contains_g_oai
