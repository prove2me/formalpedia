-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerCompact.weights7_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T00:52:27.028021+00:00
-- url     : https://prove2.me/submissions/e8af0168-fe64-4c07-8106-3dc6c7c986ed

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
lemma weight112_contains : weight112.Contains (fejerWeight 112) := by
  have he : weightBoxCalc 112 = weight112 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 112
lemma weight113_contains : weight113.Contains (fejerWeight 113) := by
  have he : weightBoxCalc 113 = weight113 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 113
lemma weight114_contains : weight114.Contains (fejerWeight 114) := by
  have he : weightBoxCalc 114 = weight114 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 114
lemma weight115_contains : weight115.Contains (fejerWeight 115) := by
  have he : weightBoxCalc 115 = weight115 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 115
lemma weight116_contains : weight116.Contains (fejerWeight 116) := by
  have he : weightBoxCalc 116 = weight116 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 116
lemma weight117_contains : weight117.Contains (fejerWeight 117) := by
  have he : weightBoxCalc 117 = weight117 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 117
lemma weight118_contains : weight118.Contains (fejerWeight 118) := by
  have he : weightBoxCalc 118 = weight118 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 118
lemma weight119_contains : weight119.Contains (fejerWeight 119) := by
  have he : weightBoxCalc 119 = weight119 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 119
lemma weight120_contains : weight120.Contains (fejerWeight 120) := by
  have he : weightBoxCalc 120 = weight120 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 120
lemma weight121_contains : weight121.Contains (fejerWeight 121) := by
  have he : weightBoxCalc 121 = weight121 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 121
lemma weight122_contains : weight122.Contains (fejerWeight 122) := by
  have he : weightBoxCalc 122 = weight122 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 122
lemma weight123_contains : weight123.Contains (fejerWeight 123) := by
  have he : weightBoxCalc 123 = weight123 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 123
lemma weight124_contains : weight124.Contains (fejerWeight 124) := by
  have he : weightBoxCalc 124 = weight124 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 124
lemma weight125_contains : weight125.Contains (fejerWeight 125) := by
  have he : weightBoxCalc 125 = weight125 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 125
lemma weight126_contains : weight126.Contains (fejerWeight 126) := by
  have he : weightBoxCalc 126 = weight126 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 126
lemma weight127_contains : weight127.Contains (fejerWeight 127) := by
  have he : weightBoxCalc 127 = weight127 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 127
lemma weights7_contains_g_oai (j : Fin 16) : (weights7 j).Contains (fejerWeight (112+j.val)) := by
  fin_cases j
  · exact weight112_contains
  · exact weight113_contains
  · exact weight114_contains
  · exact weight115_contains
  · exact weight116_contains
  · exact weight117_contains
  · exact weight118_contains
  · exact weight119_contains
  · exact weight120_contains
  · exact weight121_contains
  · exact weight122_contains
  · exact weight123_contains
  · exact weight124_contains
  · exact weight125_contains
  · exact weight126_contains
  · exact weight127_contains
end SharpPlanar.IntegerCompact


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerCompact.weights7_contains_g_oai := @OAI.SharpPlanar.IntegerCompact.weights7_contains_g_oai
