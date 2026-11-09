-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerCompact.weights15_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T00:52:25.982194+00:00
-- url     : https://prove2.me/submissions/c212f0b3-afa4-4bf8-acfa-760c99207565

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
lemma weight240_contains : weight240.Contains (fejerWeight 240) := by
  rw [← fejerWeight_reverse 240 (by decide)]
  exact weight15_contains
lemma weight241_contains : weight241.Contains (fejerWeight 241) := by
  rw [← fejerWeight_reverse 241 (by decide)]
  exact weight14_contains
lemma weight242_contains : weight242.Contains (fejerWeight 242) := by
  rw [← fejerWeight_reverse 242 (by decide)]
  exact weight13_contains
lemma weight243_contains : weight243.Contains (fejerWeight 243) := by
  rw [← fejerWeight_reverse 243 (by decide)]
  exact weight12_contains
lemma weight244_contains : weight244.Contains (fejerWeight 244) := by
  rw [← fejerWeight_reverse 244 (by decide)]
  exact weight11_contains
lemma weight245_contains : weight245.Contains (fejerWeight 245) := by
  rw [← fejerWeight_reverse 245 (by decide)]
  exact weight10_contains
lemma weight246_contains : weight246.Contains (fejerWeight 246) := by
  rw [← fejerWeight_reverse 246 (by decide)]
  exact weight9_contains
lemma weight247_contains : weight247.Contains (fejerWeight 247) := by
  rw [← fejerWeight_reverse 247 (by decide)]
  exact weight8_contains
lemma weight248_contains : weight248.Contains (fejerWeight 248) := by
  rw [← fejerWeight_reverse 248 (by decide)]
  exact weight7_contains
lemma weight249_contains : weight249.Contains (fejerWeight 249) := by
  rw [← fejerWeight_reverse 249 (by decide)]
  exact weight6_contains
lemma weight250_contains : weight250.Contains (fejerWeight 250) := by
  rw [← fejerWeight_reverse 250 (by decide)]
  exact weight5_contains
lemma weight251_contains : weight251.Contains (fejerWeight 251) := by
  rw [← fejerWeight_reverse 251 (by decide)]
  exact weight4_contains
lemma weight252_contains : weight252.Contains (fejerWeight 252) := by
  rw [← fejerWeight_reverse 252 (by decide)]
  exact weight3_contains
lemma weight253_contains : weight253.Contains (fejerWeight 253) := by
  rw [← fejerWeight_reverse 253 (by decide)]
  exact weight2_contains
lemma weight254_contains : weight254.Contains (fejerWeight 254) := by
  rw [← fejerWeight_reverse 254 (by decide)]
  exact weight1_contains
lemma weight255_contains : weight255.Contains (fejerWeight 255) := by
  rw [← fejerWeight_reverse 255 (by decide)]
  exact weight0_contains
lemma weights15_contains_g_oai (j : Fin 16) : (weights15 j).Contains (fejerWeight (240+j.val)) := by
  fin_cases j
  · exact weight240_contains
  · exact weight241_contains
  · exact weight242_contains
  · exact weight243_contains
  · exact weight244_contains
  · exact weight245_contains
  · exact weight246_contains
  · exact weight247_contains
  · exact weight248_contains
  · exact weight249_contains
  · exact weight250_contains
  · exact weight251_contains
  · exact weight252_contains
  · exact weight253_contains
  · exact weight254_contains
  · exact weight255_contains
end SharpPlanar.IntegerCompact


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerCompact.weights15_contains_g_oai := @OAI.SharpPlanar.IntegerCompact.weights15_contains_g_oai
