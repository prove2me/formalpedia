-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.b5_3_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:44:07.090207+00:00
-- url     : https://prove2.me/submissions/9a10e32d-48c8-4fb1-b4c3-b3af1425c62b

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
lemma b5_3_contains_g_oai : b5_3.Contains (basisBeta 5 3) := by
  have he : betaBox 5 3 = b5_3 := by decide +kernel
  rw [← he]
  exact betaBox_contains_g 5 3
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.b5_3_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.b5_3_contains_g_oai
