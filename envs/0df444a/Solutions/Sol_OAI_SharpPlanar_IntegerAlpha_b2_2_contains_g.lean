-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.b2_2_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:42:33.747209+00:00
-- url     : https://prove2.me/submissions/4e4cf86c-8e6d-464e-983b-5fb03506cf09

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
lemma b2_2_contains_g_oai : b2_2.Contains (basisBeta 2 2) := by
  have he : betaBox 2 2 = b2_2 := by decide +kernel
  rw [← he]
  exact betaBox_contains_g 2 2
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.b2_2_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.b2_2_contains_g_oai
