-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.b8_0_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:45:28.945649+00:00
-- url     : https://prove2.me/submissions/5fa341c1-5350-4866-b71a-5b55c5d78d46

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
lemma b8_0_contains_g_oai : b8_0.Contains (basisBeta 8 0) := by
  have he : betaBox 8 0 = b8_0 := by decide +kernel
  rw [← he]
  exact betaBox_contains_g 8 0
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.b8_0_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.b8_0_contains_g_oai
