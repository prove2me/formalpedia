-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.bTable_contains_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T17:01:14.966557+00:00
-- url     : https://prove2.me/submissions/23d15270-50a1-4355-8392-b2ffc046fb05

import Mathlib
import Definitions.Def_OAIQ098E031
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b0_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b0_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b0_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b0_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b0_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b0_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b10_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b10_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b10_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b10_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b10_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b10_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b11_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b11_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b11_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b11_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b11_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b11_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b1_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b1_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b1_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b1_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b1_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b1_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b2_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b2_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b2_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b2_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b2_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b2_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b3_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b3_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b3_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b3_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b3_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b3_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b4_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b4_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b4_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b4_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b4_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b4_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b5_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b5_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b5_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b5_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b5_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b5_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b6_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b6_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b6_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b6_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b6_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b6_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b7_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b7_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b7_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b7_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b7_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b7_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b8_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b8_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b8_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b8_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b8_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b8_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b9_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b9_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b9_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b9_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b9_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b9_5_contains_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerAlpha
open IntegerIntervals IntegerBasis
lemma bRow0_contains (j : Fin 6) : (bRow0 j).Contains (basisBeta 0 j.val) := by
  fin_cases j
  · exact b0_0_contains_e
  · exact b0_1_contains_e
  · exact b0_2_contains_e
  · exact b0_3_contains_e
  · exact b0_4_contains_e
  · exact b0_5_contains_e
lemma bRow1_contains (j : Fin 6) : (bRow1 j).Contains (basisBeta 1 j.val) := by
  fin_cases j
  · exact b1_0_contains_e
  · exact b1_1_contains_e
  · exact b1_2_contains_e
  · exact b1_3_contains_e
  · exact b1_4_contains_e
  · exact b1_5_contains_e
lemma bRow2_contains (j : Fin 6) : (bRow2 j).Contains (basisBeta 2 j.val) := by
  fin_cases j
  · exact b2_0_contains_e
  · exact b2_1_contains_e
  · exact b2_2_contains_e
  · exact b2_3_contains_e
  · exact b2_4_contains_e
  · exact b2_5_contains_e
lemma bRow3_contains (j : Fin 6) : (bRow3 j).Contains (basisBeta 3 j.val) := by
  fin_cases j
  · exact b3_0_contains_e
  · exact b3_1_contains_e
  · exact b3_2_contains_e
  · exact b3_3_contains_e
  · exact b3_4_contains_e
  · exact b3_5_contains_e
lemma bRow4_contains (j : Fin 6) : (bRow4 j).Contains (basisBeta 4 j.val) := by
  fin_cases j
  · exact b4_0_contains_e
  · exact b4_1_contains_e
  · exact b4_2_contains_e
  · exact b4_3_contains_e
  · exact b4_4_contains_e
  · exact b4_5_contains_e
lemma bRow5_contains (j : Fin 6) : (bRow5 j).Contains (basisBeta 5 j.val) := by
  fin_cases j
  · exact b5_0_contains_e
  · exact b5_1_contains_e
  · exact b5_2_contains_e
  · exact b5_3_contains_e
  · exact b5_4_contains_e
  · exact b5_5_contains_e
lemma bRow6_contains (j : Fin 6) : (bRow6 j).Contains (basisBeta 6 j.val) := by
  fin_cases j
  · exact b6_0_contains_e
  · exact b6_1_contains_e
  · exact b6_2_contains_e
  · exact b6_3_contains_e
  · exact b6_4_contains_e
  · exact b6_5_contains_e
lemma bRow7_contains (j : Fin 6) : (bRow7 j).Contains (basisBeta 7 j.val) := by
  fin_cases j
  · exact b7_0_contains_e
  · exact b7_1_contains_e
  · exact b7_2_contains_e
  · exact b7_3_contains_e
  · exact b7_4_contains_e
  · exact b7_5_contains_e
lemma bRow8_contains (j : Fin 6) : (bRow8 j).Contains (basisBeta 8 j.val) := by
  fin_cases j
  · exact b8_0_contains_e
  · exact b8_1_contains_e
  · exact b8_2_contains_e
  · exact b8_3_contains_e
  · exact b8_4_contains_e
  · exact b8_5_contains_e
lemma bRow9_contains (j : Fin 6) : (bRow9 j).Contains (basisBeta 9 j.val) := by
  fin_cases j
  · exact b9_0_contains_e
  · exact b9_1_contains_e
  · exact b9_2_contains_e
  · exact b9_3_contains_e
  · exact b9_4_contains_e
  · exact b9_5_contains_e
lemma bRow10_contains (j : Fin 6) : (bRow10 j).Contains (basisBeta 10 j.val) := by
  fin_cases j
  · exact b10_0_contains_e
  · exact b10_1_contains_e
  · exact b10_2_contains_e
  · exact b10_3_contains_e
  · exact b10_4_contains_e
  · exact b10_5_contains_e
lemma bRow11_contains (j : Fin 6) : (bRow11 j).Contains (basisBeta 11 j.val) := by
  fin_cases j
  · exact b11_0_contains_e
  · exact b11_1_contains_e
  · exact b11_2_contains_e
  · exact b11_3_contains_e
  · exact b11_4_contains_e
  · exact b11_5_contains_e
lemma bTable_contains_e_oai (n : Fin 12) (j : Fin 6) : (bTable n j).Contains (basisBeta n.val j.val) := by
  fin_cases n
  · exact bRow0_contains j
  · exact bRow1_contains j
  · exact bRow2_contains j
  · exact bRow3_contains j
  · exact bRow4_contains j
  · exact bRow5_contains j
  · exact bRow6_contains j
  · exact bRow7_contains j
  · exact bRow8_contains j
  · exact bRow9_contains j
  · exact bRow10_contains j
  · exact bRow11_contains j
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.bTable_contains_e_oai := @OAI.SharpPlanar.IntegerAlpha.bTable_contains_e_oai
