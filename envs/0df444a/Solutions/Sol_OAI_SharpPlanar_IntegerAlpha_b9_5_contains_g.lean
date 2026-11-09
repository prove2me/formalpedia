-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.b9_5_contains_g
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:46:52.438913+00:00
-- url     : https://prove2.me/submissions/b98eb98b-de85-48ce-8e85-b17cd1931b2e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

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
