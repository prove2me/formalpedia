-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.b9_0_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:46:14.22196+00:00
-- url     : https://prove2.me/submissions/2eea6581-a97a-488d-8f33-9f77efb613de

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
lemma b9_0_contains_g_oai : b9_0.Contains (basisBeta 9 0) := by
  have he : betaBox 9 0 = b9_0 := by decide +kernel
  rw [← he]
  exact betaBox_contains_g 9 0
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.b9_0_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.b9_0_contains_g_oai
