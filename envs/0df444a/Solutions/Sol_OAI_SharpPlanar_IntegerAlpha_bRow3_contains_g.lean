-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.bRow3_contains_g
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:03:21.31231+00:00
-- url     : https://prove2.me/submissions/f8521750-b227-4b76-a54c-8df644c5fcfe
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b3_0_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b3_1_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b3_2_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b3_3_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b3_4_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b3_5_contains_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerAlpha
open IntegerIntervals IntegerBasis
lemma bRow3_contains_g_oai (j : Fin 6) : (bRow3 j).Contains (basisBeta 3 j.val) := by
  fin_cases j
  · exact b3_0_contains_g
  · exact b3_1_contains_g
  · exact b3_2_contains_g
  · exact b3_3_contains_g
  · exact b3_4_contains_g
  · exact b3_5_contains_g
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.bRow3_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.bRow3_contains_g_oai
