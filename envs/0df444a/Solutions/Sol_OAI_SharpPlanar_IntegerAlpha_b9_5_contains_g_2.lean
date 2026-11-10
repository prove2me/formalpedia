-- Prove2me | solution 2 for OAI.SharpPlanar.IntegerAlpha.b9_5_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T19:03:59.011835+00:00
-- url     : https://prove2.me/submissions/705fcc0b-b481-4077-be36-c8a21f38a981

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
lemma b9_5_contains_g_oai : b9_5.Contains (basisBeta 9 5) := by
  have he : betaBox 9 5 = b9_5 := by decide +kernel
  rw [← he]
  exact betaBox_contains_g 9 5
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.b9_5_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.b9_5_contains_g_oai
