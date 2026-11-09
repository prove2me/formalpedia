-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.bRow10_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:01:26.430725+00:00
-- url     : https://prove2.me/submissions/22c9cc06-9419-4f9f-85e3-a613bfdba4e1

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b10_0_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b10_1_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b10_2_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b10_3_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b10_4_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b10_5_contains_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerAlpha
open IntegerIntervals IntegerBasis
lemma bRow10_contains_g_oai (j : Fin 6) : (bRow10 j).Contains (basisBeta 10 j.val) := by
  fin_cases j
  · exact b10_0_contains_g
  · exact b10_1_contains_g
  · exact b10_2_contains_g
  · exact b10_3_contains_g
  · exact b10_4_contains_g
  · exact b10_5_contains_g
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.bRow10_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.bRow10_contains_g_oai
