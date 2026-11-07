-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.aTable_contains_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T17:00:08.437196+00:00
-- url     : https://prove2.me/submissions/c8c2bfb8-d420-4895-8b36-4c9cf38ebbf8

import Mathlib
import Definitions.Def_OAIQ098E031
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a0_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a0_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a0_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a0_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a0_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a0_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a10_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a10_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a10_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a10_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a10_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a10_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a11_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a11_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a11_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a11_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a11_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a11_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a1_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a1_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a1_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a1_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a1_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a1_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a2_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a2_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a2_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a2_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a2_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a2_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a3_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a3_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a3_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a3_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a3_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a3_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a4_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a4_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a4_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a4_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a4_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a4_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a5_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a5_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a5_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a5_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a5_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a5_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a6_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a6_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a6_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a6_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a6_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a6_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a7_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a7_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a7_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a7_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a7_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a7_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a8_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a8_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a8_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a8_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a8_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a8_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a9_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a9_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a9_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a9_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a9_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a9_5_contains_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerAlpha
open IntegerIntervals IntegerBasis
lemma aRow0_contains (j : Fin 6) : (aRow0 j).Contains (basisAlpha 0 j.val) := by
  fin_cases j
  · exact a0_0_contains_e
  · exact a0_1_contains_e
  · exact a0_2_contains_e
  · exact a0_3_contains_e
  · exact a0_4_contains_e
  · exact a0_5_contains_e
lemma aRow1_contains (j : Fin 6) : (aRow1 j).Contains (basisAlpha 1 j.val) := by
  fin_cases j
  · exact a1_0_contains_e
  · exact a1_1_contains_e
  · exact a1_2_contains_e
  · exact a1_3_contains_e
  · exact a1_4_contains_e
  · exact a1_5_contains_e
lemma aRow2_contains (j : Fin 6) : (aRow2 j).Contains (basisAlpha 2 j.val) := by
  fin_cases j
  · exact a2_0_contains_e
  · exact a2_1_contains_e
  · exact a2_2_contains_e
  · exact a2_3_contains_e
  · exact a2_4_contains_e
  · exact a2_5_contains_e
lemma aRow3_contains (j : Fin 6) : (aRow3 j).Contains (basisAlpha 3 j.val) := by
  fin_cases j
  · exact a3_0_contains_e
  · exact a3_1_contains_e
  · exact a3_2_contains_e
  · exact a3_3_contains_e
  · exact a3_4_contains_e
  · exact a3_5_contains_e
lemma aRow4_contains (j : Fin 6) : (aRow4 j).Contains (basisAlpha 4 j.val) := by
  fin_cases j
  · exact a4_0_contains_e
  · exact a4_1_contains_e
  · exact a4_2_contains_e
  · exact a4_3_contains_e
  · exact a4_4_contains_e
  · exact a4_5_contains_e
lemma aRow5_contains (j : Fin 6) : (aRow5 j).Contains (basisAlpha 5 j.val) := by
  fin_cases j
  · exact a5_0_contains_e
  · exact a5_1_contains_e
  · exact a5_2_contains_e
  · exact a5_3_contains_e
  · exact a5_4_contains_e
  · exact a5_5_contains_e
lemma aRow6_contains (j : Fin 6) : (aRow6 j).Contains (basisAlpha 6 j.val) := by
  fin_cases j
  · exact a6_0_contains_e
  · exact a6_1_contains_e
  · exact a6_2_contains_e
  · exact a6_3_contains_e
  · exact a6_4_contains_e
  · exact a6_5_contains_e
lemma aRow7_contains (j : Fin 6) : (aRow7 j).Contains (basisAlpha 7 j.val) := by
  fin_cases j
  · exact a7_0_contains_e
  · exact a7_1_contains_e
  · exact a7_2_contains_e
  · exact a7_3_contains_e
  · exact a7_4_contains_e
  · exact a7_5_contains_e
lemma aRow8_contains (j : Fin 6) : (aRow8 j).Contains (basisAlpha 8 j.val) := by
  fin_cases j
  · exact a8_0_contains_e
  · exact a8_1_contains_e
  · exact a8_2_contains_e
  · exact a8_3_contains_e
  · exact a8_4_contains_e
  · exact a8_5_contains_e
lemma aRow9_contains (j : Fin 6) : (aRow9 j).Contains (basisAlpha 9 j.val) := by
  fin_cases j
  · exact a9_0_contains_e
  · exact a9_1_contains_e
  · exact a9_2_contains_e
  · exact a9_3_contains_e
  · exact a9_4_contains_e
  · exact a9_5_contains_e
lemma aRow10_contains (j : Fin 6) : (aRow10 j).Contains (basisAlpha 10 j.val) := by
  fin_cases j
  · exact a10_0_contains_e
  · exact a10_1_contains_e
  · exact a10_2_contains_e
  · exact a10_3_contains_e
  · exact a10_4_contains_e
  · exact a10_5_contains_e
lemma aRow11_contains (j : Fin 6) : (aRow11 j).Contains (basisAlpha 11 j.val) := by
  fin_cases j
  · exact a11_0_contains_e
  · exact a11_1_contains_e
  · exact a11_2_contains_e
  · exact a11_3_contains_e
  · exact a11_4_contains_e
  · exact a11_5_contains_e
lemma aTable_contains_e_oai (n : Fin 12) (j : Fin 6) : (aTable n j).Contains (basisAlpha n.val j.val) := by
  fin_cases n
  · exact aRow0_contains j
  · exact aRow1_contains j
  · exact aRow2_contains j
  · exact aRow3_contains j
  · exact aRow4_contains j
  · exact aRow5_contains j
  · exact aRow6_contains j
  · exact aRow7_contains j
  · exact aRow8_contains j
  · exact aRow9_contains j
  · exact aRow10_contains j
  · exact aRow11_contains j
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.aTable_contains_e_oai := @OAI.SharpPlanar.IntegerAlpha.aTable_contains_e_oai
