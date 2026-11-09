-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.b9_4_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:46:21.440658+00:00
-- url     : https://prove2.me/submissions/5015e91d-9008-4dd4-b368-a15b292291cb

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
lemma b9_4_contains_g_oai : b9_4.Contains (basisBeta 9 4) := by
  have he : betaBox 9 4 = b9_4 := by decide +kernel
  rw [← he]
  exact betaBox_contains_g 9 4
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.b9_4_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.b9_4_contains_g_oai
