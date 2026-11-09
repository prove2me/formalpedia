-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.b8_3_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:45:34.245213+00:00
-- url     : https://prove2.me/submissions/5704ed88-c66c-4c38-b9c5-a34bd466cf01

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
lemma b8_3_contains_g_oai : b8_3.Contains (basisBeta 8 3) := by
  have he : betaBox 8 3 = b8_3 := by decide +kernel
  rw [← he]
  exact betaBox_contains_g 8 3
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.b8_3_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.b8_3_contains_g_oai
