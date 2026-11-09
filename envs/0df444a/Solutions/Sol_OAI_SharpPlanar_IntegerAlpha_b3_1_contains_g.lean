-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.b3_1_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:43:13.686204+00:00
-- url     : https://prove2.me/submissions/0c64a0fa-39a3-4aa1-8c6d-a993f78e359a

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
lemma b3_1_contains_g_oai : b3_1.Contains (basisBeta 3 1) := by
  have he : betaBox 3 1 = b3_1 := by decide +kernel
  rw [← he]
  exact betaBox_contains_g 3 1
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.b3_1_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.b3_1_contains_g_oai
