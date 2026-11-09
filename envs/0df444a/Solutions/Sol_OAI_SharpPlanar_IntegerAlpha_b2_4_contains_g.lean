-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.b2_4_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:42:36.426232+00:00
-- url     : https://prove2.me/submissions/37d479a4-c346-4654-9d9c-2e810b1374c3

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
lemma b2_4_contains_g_oai : b2_4.Contains (basisBeta 2 4) := by
  have he : betaBox 2 4 = b2_4 := by decide +kernel
  rw [← he]
  exact betaBox_contains_g 2 4
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.b2_4_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.b2_4_contains_g_oai
