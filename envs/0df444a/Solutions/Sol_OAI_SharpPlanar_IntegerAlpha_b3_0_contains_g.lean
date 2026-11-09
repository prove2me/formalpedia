-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.b3_0_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:43:12.474208+00:00
-- url     : https://prove2.me/submissions/573c9449-55b8-42a7-b7d6-03ad18aaf63f

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
lemma b3_0_contains_g_oai : b3_0.Contains (basisBeta 3 0) := by
  have he : betaBox 3 0 = b3_0 := by decide +kernel
  rw [← he]
  exact betaBox_contains_g 3 0
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.b3_0_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.b3_0_contains_g_oai
