-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.bRow6_contains_g
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:03:40.904747+00:00
-- url     : https://prove2.me/submissions/1f4ac60c-0c34-4579-a490-47b189909336
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b6_0_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b6_1_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b6_2_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b6_3_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b6_4_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b6_5_contains_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerAlpha
open IntegerIntervals IntegerBasis
lemma bRow6_contains_g_oai (j : Fin 6) : (bRow6 j).Contains (basisBeta 6 j.val) := by
  fin_cases j
  · exact b6_0_contains_g
  · exact b6_1_contains_g
  · exact b6_2_contains_g
  · exact b6_3_contains_g
  · exact b6_4_contains_g
  · exact b6_5_contains_g
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.bRow6_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.bRow6_contains_g_oai
