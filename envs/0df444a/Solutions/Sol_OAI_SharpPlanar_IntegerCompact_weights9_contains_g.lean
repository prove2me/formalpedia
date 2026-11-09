-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerCompact.weights9_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T00:52:29.324104+00:00
-- url     : https://prove2.me/submissions/172c998d-aeee-4eed-959b-5e4fea5ccd87

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G086
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_weight100_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_weight101_contains_g
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
lemma weight96_contains : weight96.Contains (fejerWeight 96) := by
  have he : weightBoxCalc 96 = weight96 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 96
lemma weight97_contains : weight97.Contains (fejerWeight 97) := by
  have he : weightBoxCalc 97 = weight97 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 97
lemma weight98_contains : weight98.Contains (fejerWeight 98) := by
  have he : weightBoxCalc 98 = weight98 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 98
lemma weight99_contains : weight99.Contains (fejerWeight 99) := by
  have he : weightBoxCalc 99 = weight99 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 99
lemma weight102_contains : weight102.Contains (fejerWeight 102) := by
  have he : weightBoxCalc 102 = weight102 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 102
lemma weight103_contains : weight103.Contains (fejerWeight 103) := by
  have he : weightBoxCalc 103 = weight103 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 103
lemma weight104_contains : weight104.Contains (fejerWeight 104) := by
  have he : weightBoxCalc 104 = weight104 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 104
lemma weight105_contains : weight105.Contains (fejerWeight 105) := by
  have he : weightBoxCalc 105 = weight105 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 105
lemma weight106_contains : weight106.Contains (fejerWeight 106) := by
  have he : weightBoxCalc 106 = weight106 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 106
lemma weight107_contains : weight107.Contains (fejerWeight 107) := by
  have he : weightBoxCalc 107 = weight107 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 107
lemma weight108_contains : weight108.Contains (fejerWeight 108) := by
  have he : weightBoxCalc 108 = weight108 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 108
lemma weight109_contains : weight109.Contains (fejerWeight 109) := by
  have he : weightBoxCalc 109 = weight109 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 109
lemma weight110_contains : weight110.Contains (fejerWeight 110) := by
  have he : weightBoxCalc 110 = weight110 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 110
lemma weight111_contains : weight111.Contains (fejerWeight 111) := by
  have he : weightBoxCalc 111 = weight111 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 111
lemma weight144_contains : weight144.Contains (fejerWeight 144) := by
  rw [← fejerWeight_reverse 144 (by decide)]
  exact weight111_contains
lemma weight145_contains : weight145.Contains (fejerWeight 145) := by
  rw [← fejerWeight_reverse 145 (by decide)]
  exact weight110_contains
lemma weight146_contains : weight146.Contains (fejerWeight 146) := by
  rw [← fejerWeight_reverse 146 (by decide)]
  exact weight109_contains
lemma weight147_contains : weight147.Contains (fejerWeight 147) := by
  rw [← fejerWeight_reverse 147 (by decide)]
  exact weight108_contains
lemma weight148_contains : weight148.Contains (fejerWeight 148) := by
  rw [← fejerWeight_reverse 148 (by decide)]
  exact weight107_contains
lemma weight149_contains : weight149.Contains (fejerWeight 149) := by
  rw [← fejerWeight_reverse 149 (by decide)]
  exact weight106_contains
lemma weight150_contains : weight150.Contains (fejerWeight 150) := by
  rw [← fejerWeight_reverse 150 (by decide)]
  exact weight105_contains
lemma weight151_contains : weight151.Contains (fejerWeight 151) := by
  rw [← fejerWeight_reverse 151 (by decide)]
  exact weight104_contains
lemma weight152_contains : weight152.Contains (fejerWeight 152) := by
  rw [← fejerWeight_reverse 152 (by decide)]
  exact weight103_contains
lemma weight153_contains : weight153.Contains (fejerWeight 153) := by
  rw [← fejerWeight_reverse 153 (by decide)]
  exact weight102_contains
lemma weight154_contains : weight154.Contains (fejerWeight 154) := by
  rw [← fejerWeight_reverse 154 (by decide)]
  exact weight101_contains_g
lemma weight155_contains : weight155.Contains (fejerWeight 155) := by
  rw [← fejerWeight_reverse 155 (by decide)]
  exact weight100_contains_g
lemma weight156_contains : weight156.Contains (fejerWeight 156) := by
  rw [← fejerWeight_reverse 156 (by decide)]
  exact weight99_contains
lemma weight157_contains : weight157.Contains (fejerWeight 157) := by
  rw [← fejerWeight_reverse 157 (by decide)]
  exact weight98_contains
lemma weight158_contains : weight158.Contains (fejerWeight 158) := by
  rw [← fejerWeight_reverse 158 (by decide)]
  exact weight97_contains
lemma weight159_contains : weight159.Contains (fejerWeight 159) := by
  rw [← fejerWeight_reverse 159 (by decide)]
  exact weight96_contains
lemma weights9_contains_g_oai (j : Fin 16) : (weights9 j).Contains (fejerWeight (144+j.val)) := by
  fin_cases j
  · exact weight144_contains
  · exact weight145_contains
  · exact weight146_contains
  · exact weight147_contains
  · exact weight148_contains
  · exact weight149_contains
  · exact weight150_contains
  · exact weight151_contains
  · exact weight152_contains
  · exact weight153_contains
  · exact weight154_contains
  · exact weight155_contains
  · exact weight156_contains
  · exact weight157_contains
  · exact weight158_contains
  · exact weight159_contains
end SharpPlanar.IntegerCompact


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerCompact.weights9_contains_g_oai := @OAI.SharpPlanar.IntegerCompact.weights9_contains_g_oai
