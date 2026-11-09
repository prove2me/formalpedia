-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.b0_4_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:38:42.759194+00:00
-- url     : https://prove2.me/submissions/fadf9c05-76e2-4d64-aa50-36a9889825f1

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
lemma b0_4_contains_g_oai : b0_4.Contains (basisBeta 0 4) := by
  have he : betaBox 0 4 = b0_4 := by decide +kernel
  rw [← he]
  exact betaBox_contains_g 0 4
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.b0_4_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.b0_4_contains_g_oai
