-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.bTable_contains_g
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:03:54.004222+00:00
-- url     : https://prove2.me/submissions/9fd882bb-125e-4834-959a-8600f3dc3c90
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_bRow0_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_bRow10_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_bRow11_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_bRow1_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_bRow2_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_bRow3_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_bRow4_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_bRow5_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_bRow6_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_bRow7_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_bRow8_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_bRow9_contains_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerAlpha
open IntegerIntervals IntegerBasis
lemma bTable_contains_g_oai (n : Fin 12) (j : Fin 6) : (bTable n j).Contains (basisBeta n.val j.val) := by
  fin_cases n
  · exact bRow0_contains_g j
  · exact bRow1_contains_g j
  · exact bRow2_contains_g j
  · exact bRow3_contains_g j
  · exact bRow4_contains_g j
  · exact bRow5_contains_g j
  · exact bRow6_contains_g j
  · exact bRow7_contains_g j
  · exact bRow8_contains_g j
  · exact bRow9_contains_g j
  · exact bRow10_contains_g j
  · exact bRow11_contains_g j
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.bTable_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.bTable_contains_g_oai
