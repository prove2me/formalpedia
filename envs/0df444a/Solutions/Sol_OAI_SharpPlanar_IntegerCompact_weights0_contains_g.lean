-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerCompact.weights0_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T00:51:50.007791+00:00
-- url     : https://prove2.me/submissions/74e01580-cb2c-486a-abee-89028cdc08ce

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G086
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_weightBoxCalc_contains_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Fejer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fejér quadrature enclosures

Certified nodes and weights for the 256-node cosine quadrature rule.
-/

namespace SharpPlanar.IntegerCompact
open IntegerIntervals
lemma weight0_contains : weight0.Contains (fejerWeight 0) := by
  have he : weightBoxCalc 0 = weight0 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 0
lemma weight1_contains : weight1.Contains (fejerWeight 1) := by
  have he : weightBoxCalc 1 = weight1 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 1
lemma weight2_contains : weight2.Contains (fejerWeight 2) := by
  have he : weightBoxCalc 2 = weight2 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 2
lemma weight3_contains : weight3.Contains (fejerWeight 3) := by
  have he : weightBoxCalc 3 = weight3 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 3
lemma weight4_contains : weight4.Contains (fejerWeight 4) := by
  have he : weightBoxCalc 4 = weight4 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 4
lemma weight5_contains : weight5.Contains (fejerWeight 5) := by
  have he : weightBoxCalc 5 = weight5 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 5
lemma weight6_contains : weight6.Contains (fejerWeight 6) := by
  have he : weightBoxCalc 6 = weight6 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 6
lemma weight7_contains : weight7.Contains (fejerWeight 7) := by
  have he : weightBoxCalc 7 = weight7 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 7
lemma weight8_contains : weight8.Contains (fejerWeight 8) := by
  have he : weightBoxCalc 8 = weight8 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 8
lemma weight9_contains : weight9.Contains (fejerWeight 9) := by
  have he : weightBoxCalc 9 = weight9 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 9
lemma weight10_contains : weight10.Contains (fejerWeight 10) := by
  have he : weightBoxCalc 10 = weight10 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 10
lemma weight11_contains : weight11.Contains (fejerWeight 11) := by
  have he : weightBoxCalc 11 = weight11 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 11
lemma weight12_contains : weight12.Contains (fejerWeight 12) := by
  have he : weightBoxCalc 12 = weight12 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 12
lemma weight13_contains : weight13.Contains (fejerWeight 13) := by
  have he : weightBoxCalc 13 = weight13 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 13
lemma weight14_contains : weight14.Contains (fejerWeight 14) := by
  have he : weightBoxCalc 14 = weight14 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 14
lemma weight15_contains : weight15.Contains (fejerWeight 15) := by
  have he : weightBoxCalc 15 = weight15 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 15
lemma weights0_contains_g_oai (j : Fin 16) : (weights0 j).Contains (fejerWeight (0+j.val)) := by
  fin_cases j
  · exact weight0_contains
  · exact weight1_contains
  · exact weight2_contains
  · exact weight3_contains
  · exact weight4_contains
  · exact weight5_contains
  · exact weight6_contains
  · exact weight7_contains
  · exact weight8_contains
  · exact weight9_contains
  · exact weight10_contains
  · exact weight11_contains
  · exact weight12_contains
  · exact weight13_contains
  · exact weight14_contains
  · exact weight15_contains
end SharpPlanar.IntegerCompact


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerCompact.weights0_contains_g_oai := @OAI.SharpPlanar.IntegerCompact.weights0_contains_g_oai
