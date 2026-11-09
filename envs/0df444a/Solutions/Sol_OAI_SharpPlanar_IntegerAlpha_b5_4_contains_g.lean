-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.b5_4_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:44:39.563477+00:00
-- url     : https://prove2.me/submissions/10fad58f-0abb-4562-91a6-5fa6482cc6c6

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
lemma b5_4_contains_g_oai : b5_4.Contains (basisBeta 5 4) := by
  have he : betaBox 5 4 = b5_4 := by decide +kernel
  rw [← he]
  exact betaBox_contains_g 5 4
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.b5_4_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.b5_4_contains_g_oai
