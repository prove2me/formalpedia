-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.bRow9_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:03:47.644149+00:00
-- url     : https://prove2.me/submissions/f2bbd269-e200-4d26-861c-7569a85f1291

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b9_0_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b9_1_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b9_2_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b9_3_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b9_4_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b9_5_contains_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerAlpha
open IntegerIntervals IntegerBasis
lemma bRow9_contains_g_oai (j : Fin 6) : (bRow9 j).Contains (basisBeta 9 j.val) := by
  fin_cases j
  · exact b9_0_contains_g
  · exact b9_1_contains_g
  · exact b9_2_contains_g
  · exact b9_3_contains_g
  · exact b9_4_contains_g
  · exact b9_5_contains_g
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.bRow9_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.bRow9_contains_g_oai
