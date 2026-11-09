-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerCompact.weights8_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T00:52:28.081023+00:00
-- url     : https://prove2.me/submissions/8278d6cb-adb6-4708-a7e2-add2148eab83

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

namespace SharpPlanar
open IntegerIntervals

lemma fejerWeight_reverse (v : ℕ) (hv : v < 256) : fejerWeight (255-v) = fejerWeight v := by
  have hv' : v ≤ 255 := by omega
  have ha : fejerAngle (255-v) = Real.pi-fejerAngle v := by
    unfold fejerAngle
    rw [Nat.cast_sub hv']
    push_cast
    ring
  unfold fejerWeight
  rw [ha]
  congr 3
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  rw [show 2*(a:ℝ)*(Real.pi-fejerAngle v)=(a:ℝ)*(2*Real.pi)-2*(a:ℝ)*fejerAngle v by ring]
  exact Real.cos_nat_mul_two_pi_sub _ a

end SharpPlanar

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
lemma weight128_contains : weight128.Contains (fejerWeight 128) := by
  rw [← fejerWeight_reverse 128 (by decide)]
  exact weight127_contains
lemma weight129_contains : weight129.Contains (fejerWeight 129) := by
  rw [← fejerWeight_reverse 129 (by decide)]
  exact weight126_contains
lemma weight130_contains : weight130.Contains (fejerWeight 130) := by
  rw [← fejerWeight_reverse 130 (by decide)]
  exact weight125_contains
lemma weight131_contains : weight131.Contains (fejerWeight 131) := by
  rw [← fejerWeight_reverse 131 (by decide)]
  exact weight124_contains
lemma weight132_contains : weight132.Contains (fejerWeight 132) := by
  rw [← fejerWeight_reverse 132 (by decide)]
  exact weight123_contains
lemma weight133_contains : weight133.Contains (fejerWeight 133) := by
  rw [← fejerWeight_reverse 133 (by decide)]
  exact weight122_contains
lemma weight134_contains : weight134.Contains (fejerWeight 134) := by
  rw [← fejerWeight_reverse 134 (by decide)]
  exact weight121_contains
lemma weight135_contains : weight135.Contains (fejerWeight 135) := by
  rw [← fejerWeight_reverse 135 (by decide)]
  exact weight120_contains
lemma weight136_contains : weight136.Contains (fejerWeight 136) := by
  rw [← fejerWeight_reverse 136 (by decide)]
  exact weight119_contains
lemma weight137_contains : weight137.Contains (fejerWeight 137) := by
  rw [← fejerWeight_reverse 137 (by decide)]
  exact weight118_contains
lemma weight138_contains : weight138.Contains (fejerWeight 138) := by
  rw [← fejerWeight_reverse 138 (by decide)]
  exact weight117_contains
lemma weight139_contains : weight139.Contains (fejerWeight 139) := by
  rw [← fejerWeight_reverse 139 (by decide)]
  exact weight116_contains
lemma weight140_contains : weight140.Contains (fejerWeight 140) := by
  rw [← fejerWeight_reverse 140 (by decide)]
  exact weight115_contains
lemma weight141_contains : weight141.Contains (fejerWeight 141) := by
  rw [← fejerWeight_reverse 141 (by decide)]
  exact weight114_contains
lemma weight142_contains : weight142.Contains (fejerWeight 142) := by
  rw [← fejerWeight_reverse 142 (by decide)]
  exact weight113_contains
lemma weight143_contains : weight143.Contains (fejerWeight 143) := by
  rw [← fejerWeight_reverse 143 (by decide)]
  exact weight112_contains
lemma weights8_contains_g_oai (j : Fin 16) : (weights8 j).Contains (fejerWeight (128+j.val)) := by
  fin_cases j
  · exact weight128_contains
  · exact weight129_contains
  · exact weight130_contains
  · exact weight131_contains
  · exact weight132_contains
  · exact weight133_contains
  · exact weight134_contains
  · exact weight135_contains
  · exact weight136_contains
  · exact weight137_contains
  · exact weight138_contains
  · exact weight139_contains
  · exact weight140_contains
  · exact weight141_contains
  · exact weight142_contains
  · exact weight143_contains
end SharpPlanar.IntegerCompact


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerCompact.weights8_contains_g_oai := @OAI.SharpPlanar.IntegerCompact.weights8_contains_g_oai
