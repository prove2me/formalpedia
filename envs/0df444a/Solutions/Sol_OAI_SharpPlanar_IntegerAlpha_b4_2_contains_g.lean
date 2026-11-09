-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.b4_2_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:43:53.508488+00:00
-- url     : https://prove2.me/submissions/f978776b-9cab-47ec-9505-68af7847564a

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
lemma b4_2_contains_g_oai : b4_2.Contains (basisBeta 4 2) := by
  have he : betaBox 4 2 = b4_2 := by decide +kernel
  rw [← he]
  exact betaBox_contains_g 4 2
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.b4_2_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.b4_2_contains_g_oai
