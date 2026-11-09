-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.b11_2_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:40:37.115208+00:00
-- url     : https://prove2.me/submissions/a14639f0-06e6-45a0-b51a-bb7f5337954a

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
lemma b11_2_contains_g_oai : b11_2.Contains (basisBeta 11 2) := by
  have he : betaBox 11 2 = b11_2 := by decide +kernel
  rw [← he]
  exact betaBox_contains_g 11 2
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.b11_2_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.b11_2_contains_g_oai
