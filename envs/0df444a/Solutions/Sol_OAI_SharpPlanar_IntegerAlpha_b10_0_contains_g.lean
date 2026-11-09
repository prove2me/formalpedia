-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.b10_0_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:39:21.445776+00:00
-- url     : https://prove2.me/submissions/c47eea80-0931-4fef-949b-791ec2e63374

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
lemma b10_0_contains_g_oai : b10_0.Contains (basisBeta 10 0) := by
  have he : betaBox 10 0 = b10_0 := by decide +kernel
  rw [← he]
  exact betaBox_contains_g 10 0
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.b10_0_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.b10_0_contains_g_oai
