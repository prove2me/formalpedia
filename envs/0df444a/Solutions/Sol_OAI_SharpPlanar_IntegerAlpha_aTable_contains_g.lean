-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.aTable_contains_g
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T22:53:17.652108+00:00
-- url     : https://prove2.me/submissions/a50e2ce2-c3a3-4bff-9cc8-61b7b1e872ce
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_aRow0_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_aRow10_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_aRow11_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_aRow1_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_aRow2_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_aRow3_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_aRow4_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_aRow5_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_aRow6_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_aRow7_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_aRow8_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_aRow9_contains_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerAlpha
open IntegerIntervals IntegerBasis
lemma aTable_contains_g_oai (n : Fin 12) (j : Fin 6) : (aTable n j).Contains (basisAlpha n.val j.val) := by
  fin_cases n
  · exact aRow0_contains_g j
  · exact aRow1_contains_g j
  · exact aRow2_contains_g j
  · exact aRow3_contains_g j
  · exact aRow4_contains_g j
  · exact aRow5_contains_g j
  · exact aRow6_contains_g j
  · exact aRow7_contains_g j
  · exact aRow8_contains_g j
  · exact aRow9_contains_g j
  · exact aRow10_contains_g j
  · exact aRow11_contains_g j
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.aTable_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.aTable_contains_g_oai
