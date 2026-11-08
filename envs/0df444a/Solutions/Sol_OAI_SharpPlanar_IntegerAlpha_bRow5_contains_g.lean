-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.bRow5_contains_g
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:03:26.629194+00:00
-- url     : https://prove2.me/submissions/7deac01d-0afb-42c6-befe-7e6b190e833e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b5_0_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b5_1_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b5_2_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b5_3_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b5_4_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b5_5_contains_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerAlpha
open IntegerIntervals IntegerBasis
lemma bRow5_contains_g_oai (j : Fin 6) : (bRow5 j).Contains (basisBeta 5 j.val) := by
  fin_cases j
  · exact b5_0_contains_g
  · exact b5_1_contains_g
  · exact b5_2_contains_g
  · exact b5_3_contains_g
  · exact b5_4_contains_g
  · exact b5_5_contains_g
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.bRow5_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.bRow5_contains_g_oai
