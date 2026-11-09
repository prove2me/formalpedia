-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.b10_5_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:40:33.353197+00:00
-- url     : https://prove2.me/submissions/345cea77-8ab6-4625-89fc-d93f62a7a483

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
lemma b10_5_contains_g_oai : b10_5.Contains (basisBeta 10 5) := by
  have he : betaBox 10 5 = b10_5 := by decide +kernel
  rw [← he]
  exact betaBox_contains_g 10 5
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.b10_5_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.b10_5_contains_g_oai
