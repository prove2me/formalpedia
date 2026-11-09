-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.aRow11_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T22:51:39.612641+00:00
-- url     : https://prove2.me/submissions/fca6bf3c-0b43-417e-9a13-0e2608ab6cac

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a11_0_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a11_1_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a11_2_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a11_3_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a11_4_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a11_5_contains_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerAlpha
open IntegerIntervals IntegerBasis
lemma aRow11_contains_g_oai (j : Fin 6) : (aRow11 j).Contains (basisAlpha 11 j.val) := by
  fin_cases j
  · exact a11_0_contains_g
  · exact a11_1_contains_g
  · exact a11_2_contains_g
  · exact a11_3_contains_g
  · exact a11_4_contains_g
  · exact a11_5_contains_g
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.aRow11_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.aRow11_contains_g_oai
