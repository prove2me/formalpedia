-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.b9_2_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:46:18.753904+00:00
-- url     : https://prove2.me/submissions/0c8ae211-1f75-4a44-bcb7-b390888f0b21

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
lemma b9_2_contains_g_oai : b9_2.Contains (basisBeta 9 2) := by
  have he : betaBox 9 2 = b9_2 := by decide +kernel
  rw [← he]
  exact betaBox_contains_g 9 2
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.b9_2_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.b9_2_contains_g_oai
