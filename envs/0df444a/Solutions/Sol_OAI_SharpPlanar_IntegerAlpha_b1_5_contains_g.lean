-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.b1_5_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:41:59.000214+00:00
-- url     : https://prove2.me/submissions/9392550e-4ce8-4c76-96f4-57bf8a7df313

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
lemma b1_5_contains_g_oai : b1_5.Contains (basisBeta 1 5) := by
  have he : betaBox 1 5 = b1_5 := by decide +kernel
  rw [← he]
  exact betaBox_contains_g 1 5
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.b1_5_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.b1_5_contains_g_oai
