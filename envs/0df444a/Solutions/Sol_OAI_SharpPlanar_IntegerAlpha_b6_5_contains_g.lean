-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.b6_5_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:45:20.322663+00:00
-- url     : https://prove2.me/submissions/4ac0c502-9943-4337-a71f-26c41fcce0dc

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
lemma b6_5_contains_g_oai : b6_5.Contains (basisBeta 6 5) := by
  have he : betaBox 6 5 = b6_5 := by decide +kernel
  rw [← he]
  exact betaBox_contains_g 6 5
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.b6_5_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.b6_5_contains_g_oai
