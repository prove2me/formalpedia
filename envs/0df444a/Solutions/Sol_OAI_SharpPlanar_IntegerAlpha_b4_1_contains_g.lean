-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.b4_1_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:43:52.399756+00:00
-- url     : https://prove2.me/submissions/a45434aa-5759-47bf-976b-418b33ac3af3

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
lemma b4_1_contains_g_oai : b4_1.Contains (basisBeta 4 1) := by
  have he : betaBox 4 1 = b4_1 := by decide +kernel
  rw [← he]
  exact betaBox_contains_g 4 1
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.b4_1_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.b4_1_contains_g_oai
