-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.b2_5_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:43:11.237216+00:00
-- url     : https://prove2.me/submissions/6d663a17-3e5c-4022-b4e3-08357687e969

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
lemma b2_5_contains_g_oai : b2_5.Contains (basisBeta 2 5) := by
  have he : betaBox 2 5 = b2_5 := by decide +kernel
  rw [← he]
  exact betaBox_contains_g 2 5
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.b2_5_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.b2_5_contains_g_oai
