-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.b9_1_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:46:17.467388+00:00
-- url     : https://prove2.me/submissions/7f1654af-9980-4f70-808e-8ad0e2b20c31

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
lemma b9_1_contains_g_oai : b9_1.Contains (basisBeta 9 1) := by
  have he : betaBox 9 1 = b9_1 := by decide +kernel
  rw [← he]
  exact betaBox_contains_g 9 1
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.b9_1_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.b9_1_contains_g_oai
