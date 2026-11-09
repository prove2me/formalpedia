-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.b5_5_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:44:40.75364+00:00
-- url     : https://prove2.me/submissions/83cd992b-b0ed-4891-933c-3b9113e11109

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
lemma b5_5_contains_g_oai : b5_5.Contains (basisBeta 5 5) := by
  have he : betaBox 5 5 = b5_5 := by decide +kernel
  rw [← he]
  exact betaBox_contains_g 5 5
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.b5_5_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.b5_5_contains_g_oai
