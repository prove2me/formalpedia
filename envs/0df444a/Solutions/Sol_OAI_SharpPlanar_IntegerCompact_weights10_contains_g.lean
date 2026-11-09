-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerCompact.weights10_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T00:52:24.666448+00:00
-- url     : https://prove2.me/submissions/367204fa-386d-4870-9213-238b21024999

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
lemma weight80_contains : weight80.Contains (fejerWeight 80) := by
  have he : weightBoxCalc 80 = weight80 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 80
lemma weight81_contains : weight81.Contains (fejerWeight 81) := by
  have he : weightBoxCalc 81 = weight81 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 81
lemma weight82_contains : weight82.Contains (fejerWeight 82) := by
  have he : weightBoxCalc 82 = weight82 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 82
lemma weight83_contains : weight83.Contains (fejerWeight 83) := by
  have he : weightBoxCalc 83 = weight83 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 83
lemma weight84_contains : weight84.Contains (fejerWeight 84) := by
  have he : weightBoxCalc 84 = weight84 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 84
lemma weight85_contains : weight85.Contains (fejerWeight 85) := by
  have he : weightBoxCalc 85 = weight85 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 85
lemma weight86_contains : weight86.Contains (fejerWeight 86) := by
  have he : weightBoxCalc 86 = weight86 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 86
lemma weight87_contains : weight87.Contains (fejerWeight 87) := by
  have he : weightBoxCalc 87 = weight87 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 87
lemma weight88_contains : weight88.Contains (fejerWeight 88) := by
  have he : weightBoxCalc 88 = weight88 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 88
lemma weight89_contains : weight89.Contains (fejerWeight 89) := by
  have he : weightBoxCalc 89 = weight89 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 89
lemma weight90_contains : weight90.Contains (fejerWeight 90) := by
  have he : weightBoxCalc 90 = weight90 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 90
lemma weight91_contains : weight91.Contains (fejerWeight 91) := by
  have he : weightBoxCalc 91 = weight91 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 91
lemma weight92_contains : weight92.Contains (fejerWeight 92) := by
  have he : weightBoxCalc 92 = weight92 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 92
lemma weight93_contains : weight93.Contains (fejerWeight 93) := by
  have he : weightBoxCalc 93 = weight93 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 93
lemma weight94_contains : weight94.Contains (fejerWeight 94) := by
  have he : weightBoxCalc 94 = weight94 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 94
lemma weight95_contains : weight95.Contains (fejerWeight 95) := by
  have he : weightBoxCalc 95 = weight95 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 95
lemma weight160_contains : weight160.Contains (fejerWeight 160) := by
  rw [← fejerWeight_reverse 160 (by decide)]
  exact weight95_contains
lemma weight161_contains : weight161.Contains (fejerWeight 161) := by
  rw [← fejerWeight_reverse 161 (by decide)]
  exact weight94_contains
lemma weight162_contains : weight162.Contains (fejerWeight 162) := by
  rw [← fejerWeight_reverse 162 (by decide)]
  exact weight93_contains
lemma weight163_contains : weight163.Contains (fejerWeight 163) := by
  rw [← fejerWeight_reverse 163 (by decide)]
  exact weight92_contains
lemma weight164_contains : weight164.Contains (fejerWeight 164) := by
  rw [← fejerWeight_reverse 164 (by decide)]
  exact weight91_contains
lemma weight165_contains : weight165.Contains (fejerWeight 165) := by
  rw [← fejerWeight_reverse 165 (by decide)]
  exact weight90_contains
lemma weight166_contains : weight166.Contains (fejerWeight 166) := by
  rw [← fejerWeight_reverse 166 (by decide)]
  exact weight89_contains
lemma weight167_contains : weight167.Contains (fejerWeight 167) := by
  rw [← fejerWeight_reverse 167 (by decide)]
  exact weight88_contains
lemma weight168_contains : weight168.Contains (fejerWeight 168) := by
  rw [← fejerWeight_reverse 168 (by decide)]
  exact weight87_contains
lemma weight169_contains : weight169.Contains (fejerWeight 169) := by
  rw [← fejerWeight_reverse 169 (by decide)]
  exact weight86_contains
lemma weight170_contains : weight170.Contains (fejerWeight 170) := by
  rw [← fejerWeight_reverse 170 (by decide)]
  exact weight85_contains
lemma weight171_contains : weight171.Contains (fejerWeight 171) := by
  rw [← fejerWeight_reverse 171 (by decide)]
  exact weight84_contains
lemma weight172_contains : weight172.Contains (fejerWeight 172) := by
  rw [← fejerWeight_reverse 172 (by decide)]
  exact weight83_contains
lemma weight173_contains : weight173.Contains (fejerWeight 173) := by
  rw [← fejerWeight_reverse 173 (by decide)]
  exact weight82_contains
lemma weight174_contains : weight174.Contains (fejerWeight 174) := by
  rw [← fejerWeight_reverse 174 (by decide)]
  exact weight81_contains
lemma weight175_contains : weight175.Contains (fejerWeight 175) := by
  rw [← fejerWeight_reverse 175 (by decide)]
  exact weight80_contains
lemma weights10_contains_g_oai (j : Fin 16) : (weights10 j).Contains (fejerWeight (160+j.val)) := by
  fin_cases j
  · exact weight160_contains
  · exact weight161_contains
  · exact weight162_contains
  · exact weight163_contains
  · exact weight164_contains
  · exact weight165_contains
  · exact weight166_contains
  · exact weight167_contains
  · exact weight168_contains
  · exact weight169_contains
  · exact weight170_contains
  · exact weight171_contains
  · exact weight172_contains
  · exact weight173_contains
  · exact weight174_contains
  · exact weight175_contains
end SharpPlanar.IntegerCompact


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerCompact.weights10_contains_g_oai := @OAI.SharpPlanar.IntegerCompact.weights10_contains_g_oai
