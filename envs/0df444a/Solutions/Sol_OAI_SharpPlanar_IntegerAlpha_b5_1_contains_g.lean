-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.b5_1_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:43:59.419204+00:00
-- url     : https://prove2.me/submissions/9c6a5172-391d-450b-a540-a0f4b7a5676c

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
lemma b5_1_contains_g_oai : b5_1.Contains (basisBeta 5 1) := by
  have he : betaBox 5 1 = b5_1 := by decide +kernel
  rw [← he]
  exact betaBox_contains_g 5 1
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.b5_1_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.b5_1_contains_g_oai
