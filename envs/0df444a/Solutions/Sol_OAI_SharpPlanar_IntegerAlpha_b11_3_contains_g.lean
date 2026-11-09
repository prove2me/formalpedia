-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.b11_3_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:40:38.305018+00:00
-- url     : https://prove2.me/submissions/c7cd407f-807b-4020-b11b-2bfa457c8140

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
lemma b11_3_contains_g_oai : b11_3.Contains (basisBeta 11 3) := by
  have he : betaBox 11 3 = b11_3 := by decide +kernel
  rw [← he]
  exact betaBox_contains_g 11 3
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.b11_3_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.b11_3_contains_g_oai
