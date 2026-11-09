-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.b4_0_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:43:19.411189+00:00
-- url     : https://prove2.me/submissions/0886e5f7-47fa-442b-adf3-9bc07dd285f7

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
lemma b4_0_contains_g_oai : b4_0.Contains (basisBeta 4 0) := by
  have he : betaBox 4 0 = b4_0 := by decide +kernel
  rw [← he]
  exact betaBox_contains_g 4 0
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.b4_0_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.b4_0_contains_g_oai
