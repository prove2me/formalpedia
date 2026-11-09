-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.b11_1_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:40:35.789204+00:00
-- url     : https://prove2.me/submissions/ef3fca22-35c1-4f50-be14-2c9c8973adb2

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
lemma b11_1_contains_g_oai : b11_1.Contains (basisBeta 11 1) := by
  have he : betaBox 11 1 = b11_1 := by decide +kernel
  rw [← he]
  exact betaBox_contains_g 11 1
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.b11_1_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.b11_1_contains_g_oai
