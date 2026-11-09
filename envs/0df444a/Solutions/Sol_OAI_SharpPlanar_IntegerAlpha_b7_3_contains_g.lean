-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.b7_3_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:45:25.165267+00:00
-- url     : https://prove2.me/submissions/7285cdd0-3331-4ac1-afdc-81b7c2a927a3

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
lemma b7_3_contains_g_oai : b7_3.Contains (basisBeta 7 3) := by
  have he : betaBox 7 3 = b7_3 := by decide +kernel
  rw [← he]
  exact betaBox_contains_g 7 3
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.b7_3_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.b7_3_contains_g_oai
