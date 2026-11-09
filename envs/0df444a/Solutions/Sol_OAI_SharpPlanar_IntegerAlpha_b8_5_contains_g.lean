-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.b8_5_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:46:12.86927+00:00
-- url     : https://prove2.me/submissions/1c3cbe6d-0e6b-4ac5-9fc3-bc4ddb7085bb

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
lemma b8_5_contains_g_oai : b8_5.Contains (basisBeta 8 5) := by
  have he : betaBox 8 5 = b8_5 := by decide +kernel
  rw [← he]
  exact betaBox_contains_g 8 5
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.b8_5_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.b8_5_contains_g_oai
