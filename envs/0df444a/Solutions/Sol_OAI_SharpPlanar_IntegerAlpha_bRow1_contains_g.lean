-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.bRow1_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:00:14.266311+00:00
-- url     : https://prove2.me/submissions/70929413-8e32-4938-a271-5cab2541d669

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b1_0_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b1_1_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b1_2_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b1_3_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b1_4_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b1_5_contains_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerAlpha
open IntegerIntervals IntegerBasis
lemma bRow1_contains_g_oai (j : Fin 6) : (bRow1 j).Contains (basisBeta 1 j.val) := by
  fin_cases j
  · exact b1_0_contains_g
  · exact b1_1_contains_g
  · exact b1_2_contains_g
  · exact b1_3_contains_g
  · exact b1_4_contains_g
  · exact b1_5_contains_g
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.bRow1_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.bRow1_contains_g_oai
