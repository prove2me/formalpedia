-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.bRow2_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:00:17.149118+00:00
-- url     : https://prove2.me/submissions/425afd42-2b52-4641-8c5e-d41b1c2cd5ec

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b2_0_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b2_1_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b2_2_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b2_3_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b2_4_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b2_5_contains_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerAlpha
open IntegerIntervals IntegerBasis
lemma bRow2_contains_g_oai (j : Fin 6) : (bRow2 j).Contains (basisBeta 2 j.val) := by
  fin_cases j
  · exact b2_0_contains_g
  · exact b2_1_contains_g
  · exact b2_2_contains_g
  · exact b2_3_contains_g
  · exact b2_4_contains_g
  · exact b2_5_contains_g
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.bRow2_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.bRow2_contains_g_oai
