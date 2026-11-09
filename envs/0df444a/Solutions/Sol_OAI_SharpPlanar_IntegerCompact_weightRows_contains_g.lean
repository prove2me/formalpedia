-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerCompact.weightRows_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T00:51:48.847666+00:00
-- url     : https://prove2.me/submissions/f71da773-2d37-47a8-baed-84f317cdc5de

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G086
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_weight100_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_weight101_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_weight16_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_weight176_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_weight177_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_weight178_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_weight179_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_weight180_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_weight181_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_weight182_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_weight183_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_weight184_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_weight185_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_weightBoxCalc_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_weights0_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_weights10_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_weights15_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_weights7_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_weights8_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_weights9_contains_g

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
lemma weight17_contains : weight17.Contains (fejerWeight 17) := by
  have he : weightBoxCalc 17 = weight17 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 17
lemma weight18_contains : weight18.Contains (fejerWeight 18) := by
  have he : weightBoxCalc 18 = weight18 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 18
lemma weight19_contains : weight19.Contains (fejerWeight 19) := by
  have he : weightBoxCalc 19 = weight19 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 19
lemma weight20_contains : weight20.Contains (fejerWeight 20) := by
  have he : weightBoxCalc 20 = weight20 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 20
lemma weight21_contains : weight21.Contains (fejerWeight 21) := by
  have he : weightBoxCalc 21 = weight21 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 21
lemma weight22_contains : weight22.Contains (fejerWeight 22) := by
  have he : weightBoxCalc 22 = weight22 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 22
lemma weight23_contains : weight23.Contains (fejerWeight 23) := by
  have he : weightBoxCalc 23 = weight23 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 23
lemma weight24_contains : weight24.Contains (fejerWeight 24) := by
  have he : weightBoxCalc 24 = weight24 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 24
lemma weight25_contains : weight25.Contains (fejerWeight 25) := by
  have he : weightBoxCalc 25 = weight25 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 25
lemma weight26_contains : weight26.Contains (fejerWeight 26) := by
  have he : weightBoxCalc 26 = weight26 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 26
lemma weight27_contains : weight27.Contains (fejerWeight 27) := by
  have he : weightBoxCalc 27 = weight27 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 27
lemma weight28_contains : weight28.Contains (fejerWeight 28) := by
  have he : weightBoxCalc 28 = weight28 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 28
lemma weight29_contains : weight29.Contains (fejerWeight 29) := by
  have he : weightBoxCalc 29 = weight29 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 29
lemma weight30_contains : weight30.Contains (fejerWeight 30) := by
  have he : weightBoxCalc 30 = weight30 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 30
lemma weight31_contains : weight31.Contains (fejerWeight 31) := by
  have he : weightBoxCalc 31 = weight31 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 31
lemma weight32_contains : weight32.Contains (fejerWeight 32) := by
  have he : weightBoxCalc 32 = weight32 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 32
lemma weight33_contains : weight33.Contains (fejerWeight 33) := by
  have he : weightBoxCalc 33 = weight33 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 33
lemma weight34_contains : weight34.Contains (fejerWeight 34) := by
  have he : weightBoxCalc 34 = weight34 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 34
lemma weight35_contains : weight35.Contains (fejerWeight 35) := by
  have he : weightBoxCalc 35 = weight35 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 35
lemma weight36_contains : weight36.Contains (fejerWeight 36) := by
  have he : weightBoxCalc 36 = weight36 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 36
lemma weight37_contains : weight37.Contains (fejerWeight 37) := by
  have he : weightBoxCalc 37 = weight37 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 37
lemma weight38_contains : weight38.Contains (fejerWeight 38) := by
  have he : weightBoxCalc 38 = weight38 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 38
lemma weight39_contains : weight39.Contains (fejerWeight 39) := by
  have he : weightBoxCalc 39 = weight39 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 39
lemma weight40_contains : weight40.Contains (fejerWeight 40) := by
  have he : weightBoxCalc 40 = weight40 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 40
lemma weight41_contains : weight41.Contains (fejerWeight 41) := by
  have he : weightBoxCalc 41 = weight41 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 41
lemma weight42_contains : weight42.Contains (fejerWeight 42) := by
  have he : weightBoxCalc 42 = weight42 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 42
lemma weight43_contains : weight43.Contains (fejerWeight 43) := by
  have he : weightBoxCalc 43 = weight43 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 43
lemma weight44_contains : weight44.Contains (fejerWeight 44) := by
  have he : weightBoxCalc 44 = weight44 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 44
lemma weight45_contains : weight45.Contains (fejerWeight 45) := by
  have he : weightBoxCalc 45 = weight45 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 45
lemma weight46_contains : weight46.Contains (fejerWeight 46) := by
  have he : weightBoxCalc 46 = weight46 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 46
lemma weight47_contains : weight47.Contains (fejerWeight 47) := by
  have he : weightBoxCalc 47 = weight47 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 47
lemma weight48_contains : weight48.Contains (fejerWeight 48) := by
  have he : weightBoxCalc 48 = weight48 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 48
lemma weight49_contains : weight49.Contains (fejerWeight 49) := by
  have he : weightBoxCalc 49 = weight49 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 49
lemma weight50_contains : weight50.Contains (fejerWeight 50) := by
  have he : weightBoxCalc 50 = weight50 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 50
lemma weight51_contains : weight51.Contains (fejerWeight 51) := by
  have he : weightBoxCalc 51 = weight51 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 51
lemma weight52_contains : weight52.Contains (fejerWeight 52) := by
  have he : weightBoxCalc 52 = weight52 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 52
lemma weight53_contains : weight53.Contains (fejerWeight 53) := by
  have he : weightBoxCalc 53 = weight53 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 53
lemma weight54_contains : weight54.Contains (fejerWeight 54) := by
  have he : weightBoxCalc 54 = weight54 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 54
lemma weight55_contains : weight55.Contains (fejerWeight 55) := by
  have he : weightBoxCalc 55 = weight55 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 55
lemma weight56_contains : weight56.Contains (fejerWeight 56) := by
  have he : weightBoxCalc 56 = weight56 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 56
lemma weight57_contains : weight57.Contains (fejerWeight 57) := by
  have he : weightBoxCalc 57 = weight57 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 57
lemma weight58_contains : weight58.Contains (fejerWeight 58) := by
  have he : weightBoxCalc 58 = weight58 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 58
lemma weight59_contains : weight59.Contains (fejerWeight 59) := by
  have he : weightBoxCalc 59 = weight59 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 59
lemma weight60_contains : weight60.Contains (fejerWeight 60) := by
  have he : weightBoxCalc 60 = weight60 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 60
lemma weight61_contains : weight61.Contains (fejerWeight 61) := by
  have he : weightBoxCalc 61 = weight61 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 61
lemma weight62_contains : weight62.Contains (fejerWeight 62) := by
  have he : weightBoxCalc 62 = weight62 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 62
lemma weight63_contains : weight63.Contains (fejerWeight 63) := by
  have he : weightBoxCalc 63 = weight63 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 63
lemma weight64_contains : weight64.Contains (fejerWeight 64) := by
  have he : weightBoxCalc 64 = weight64 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 64
lemma weight65_contains : weight65.Contains (fejerWeight 65) := by
  have he : weightBoxCalc 65 = weight65 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 65
lemma weight66_contains : weight66.Contains (fejerWeight 66) := by
  have he : weightBoxCalc 66 = weight66 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 66
lemma weight67_contains : weight67.Contains (fejerWeight 67) := by
  have he : weightBoxCalc 67 = weight67 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 67
lemma weight68_contains : weight68.Contains (fejerWeight 68) := by
  have he : weightBoxCalc 68 = weight68 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 68
lemma weight69_contains : weight69.Contains (fejerWeight 69) := by
  have he : weightBoxCalc 69 = weight69 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 69
lemma weight70_contains : weight70.Contains (fejerWeight 70) := by
  have he : weightBoxCalc 70 = weight70 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 70
lemma weight71_contains : weight71.Contains (fejerWeight 71) := by
  have he : weightBoxCalc 71 = weight71 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 71
lemma weight72_contains : weight72.Contains (fejerWeight 72) := by
  have he : weightBoxCalc 72 = weight72 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 72
lemma weight73_contains : weight73.Contains (fejerWeight 73) := by
  have he : weightBoxCalc 73 = weight73 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 73
lemma weight74_contains : weight74.Contains (fejerWeight 74) := by
  have he : weightBoxCalc 74 = weight74 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 74
lemma weight75_contains : weight75.Contains (fejerWeight 75) := by
  have he : weightBoxCalc 75 = weight75 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 75
lemma weight76_contains : weight76.Contains (fejerWeight 76) := by
  have he : weightBoxCalc 76 = weight76 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 76
lemma weight77_contains : weight77.Contains (fejerWeight 77) := by
  have he : weightBoxCalc 77 = weight77 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 77
lemma weight78_contains : weight78.Contains (fejerWeight 78) := by
  have he : weightBoxCalc 78 = weight78 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 78
lemma weight79_contains : weight79.Contains (fejerWeight 79) := by
  have he : weightBoxCalc 79 = weight79 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains_g 79
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
lemma weight186_contains : weight186.Contains (fejerWeight 186) := by
  rw [← fejerWeight_reverse 186 (by decide)]
  exact weight69_contains
lemma weight187_contains : weight187.Contains (fejerWeight 187) := by
  rw [← fejerWeight_reverse 187 (by decide)]
  exact weight68_contains
lemma weight188_contains : weight188.Contains (fejerWeight 188) := by
  rw [← fejerWeight_reverse 188 (by decide)]
  exact weight67_contains
lemma weight189_contains : weight189.Contains (fejerWeight 189) := by
  rw [← fejerWeight_reverse 189 (by decide)]
  exact weight66_contains
lemma weight190_contains : weight190.Contains (fejerWeight 190) := by
  rw [← fejerWeight_reverse 190 (by decide)]
  exact weight65_contains
lemma weight191_contains : weight191.Contains (fejerWeight 191) := by
  rw [← fejerWeight_reverse 191 (by decide)]
  exact weight64_contains
lemma weight192_contains : weight192.Contains (fejerWeight 192) := by
  rw [← fejerWeight_reverse 192 (by decide)]
  exact weight63_contains
lemma weight193_contains : weight193.Contains (fejerWeight 193) := by
  rw [← fejerWeight_reverse 193 (by decide)]
  exact weight62_contains
lemma weight194_contains : weight194.Contains (fejerWeight 194) := by
  rw [← fejerWeight_reverse 194 (by decide)]
  exact weight61_contains
lemma weight195_contains : weight195.Contains (fejerWeight 195) := by
  rw [← fejerWeight_reverse 195 (by decide)]
  exact weight60_contains
lemma weight196_contains : weight196.Contains (fejerWeight 196) := by
  rw [← fejerWeight_reverse 196 (by decide)]
  exact weight59_contains
lemma weight197_contains : weight197.Contains (fejerWeight 197) := by
  rw [← fejerWeight_reverse 197 (by decide)]
  exact weight58_contains
lemma weight198_contains : weight198.Contains (fejerWeight 198) := by
  rw [← fejerWeight_reverse 198 (by decide)]
  exact weight57_contains
lemma weight199_contains : weight199.Contains (fejerWeight 199) := by
  rw [← fejerWeight_reverse 199 (by decide)]
  exact weight56_contains
lemma weight200_contains : weight200.Contains (fejerWeight 200) := by
  rw [← fejerWeight_reverse 200 (by decide)]
  exact weight55_contains
lemma weight201_contains : weight201.Contains (fejerWeight 201) := by
  rw [← fejerWeight_reverse 201 (by decide)]
  exact weight54_contains
lemma weight202_contains : weight202.Contains (fejerWeight 202) := by
  rw [← fejerWeight_reverse 202 (by decide)]
  exact weight53_contains
lemma weight203_contains : weight203.Contains (fejerWeight 203) := by
  rw [← fejerWeight_reverse 203 (by decide)]
  exact weight52_contains
lemma weight204_contains : weight204.Contains (fejerWeight 204) := by
  rw [← fejerWeight_reverse 204 (by decide)]
  exact weight51_contains
lemma weight205_contains : weight205.Contains (fejerWeight 205) := by
  rw [← fejerWeight_reverse 205 (by decide)]
  exact weight50_contains
lemma weight206_contains : weight206.Contains (fejerWeight 206) := by
  rw [← fejerWeight_reverse 206 (by decide)]
  exact weight49_contains
lemma weight207_contains : weight207.Contains (fejerWeight 207) := by
  rw [← fejerWeight_reverse 207 (by decide)]
  exact weight48_contains
lemma weight208_contains : weight208.Contains (fejerWeight 208) := by
  rw [← fejerWeight_reverse 208 (by decide)]
  exact weight47_contains
lemma weight209_contains : weight209.Contains (fejerWeight 209) := by
  rw [← fejerWeight_reverse 209 (by decide)]
  exact weight46_contains
lemma weight210_contains : weight210.Contains (fejerWeight 210) := by
  rw [← fejerWeight_reverse 210 (by decide)]
  exact weight45_contains
lemma weight211_contains : weight211.Contains (fejerWeight 211) := by
  rw [← fejerWeight_reverse 211 (by decide)]
  exact weight44_contains
lemma weight212_contains : weight212.Contains (fejerWeight 212) := by
  rw [← fejerWeight_reverse 212 (by decide)]
  exact weight43_contains
lemma weight213_contains : weight213.Contains (fejerWeight 213) := by
  rw [← fejerWeight_reverse 213 (by decide)]
  exact weight42_contains
lemma weight214_contains : weight214.Contains (fejerWeight 214) := by
  rw [← fejerWeight_reverse 214 (by decide)]
  exact weight41_contains
lemma weight215_contains : weight215.Contains (fejerWeight 215) := by
  rw [← fejerWeight_reverse 215 (by decide)]
  exact weight40_contains
lemma weight216_contains : weight216.Contains (fejerWeight 216) := by
  rw [← fejerWeight_reverse 216 (by decide)]
  exact weight39_contains
lemma weight217_contains : weight217.Contains (fejerWeight 217) := by
  rw [← fejerWeight_reverse 217 (by decide)]
  exact weight38_contains
lemma weight218_contains : weight218.Contains (fejerWeight 218) := by
  rw [← fejerWeight_reverse 218 (by decide)]
  exact weight37_contains
lemma weight219_contains : weight219.Contains (fejerWeight 219) := by
  rw [← fejerWeight_reverse 219 (by decide)]
  exact weight36_contains
lemma weight220_contains : weight220.Contains (fejerWeight 220) := by
  rw [← fejerWeight_reverse 220 (by decide)]
  exact weight35_contains
lemma weight221_contains : weight221.Contains (fejerWeight 221) := by
  rw [← fejerWeight_reverse 221 (by decide)]
  exact weight34_contains
lemma weight222_contains : weight222.Contains (fejerWeight 222) := by
  rw [← fejerWeight_reverse 222 (by decide)]
  exact weight33_contains
lemma weight223_contains : weight223.Contains (fejerWeight 223) := by
  rw [← fejerWeight_reverse 223 (by decide)]
  exact weight32_contains
lemma weight224_contains : weight224.Contains (fejerWeight 224) := by
  rw [← fejerWeight_reverse 224 (by decide)]
  exact weight31_contains
lemma weight225_contains : weight225.Contains (fejerWeight 225) := by
  rw [← fejerWeight_reverse 225 (by decide)]
  exact weight30_contains
lemma weight226_contains : weight226.Contains (fejerWeight 226) := by
  rw [← fejerWeight_reverse 226 (by decide)]
  exact weight29_contains
lemma weight227_contains : weight227.Contains (fejerWeight 227) := by
  rw [← fejerWeight_reverse 227 (by decide)]
  exact weight28_contains
lemma weight228_contains : weight228.Contains (fejerWeight 228) := by
  rw [← fejerWeight_reverse 228 (by decide)]
  exact weight27_contains
lemma weight229_contains : weight229.Contains (fejerWeight 229) := by
  rw [← fejerWeight_reverse 229 (by decide)]
  exact weight26_contains
lemma weight230_contains : weight230.Contains (fejerWeight 230) := by
  rw [← fejerWeight_reverse 230 (by decide)]
  exact weight25_contains
lemma weight231_contains : weight231.Contains (fejerWeight 231) := by
  rw [← fejerWeight_reverse 231 (by decide)]
  exact weight24_contains
lemma weight232_contains : weight232.Contains (fejerWeight 232) := by
  rw [← fejerWeight_reverse 232 (by decide)]
  exact weight23_contains
lemma weight233_contains : weight233.Contains (fejerWeight 233) := by
  rw [← fejerWeight_reverse 233 (by decide)]
  exact weight22_contains
lemma weight234_contains : weight234.Contains (fejerWeight 234) := by
  rw [← fejerWeight_reverse 234 (by decide)]
  exact weight21_contains
lemma weight235_contains : weight235.Contains (fejerWeight 235) := by
  rw [← fejerWeight_reverse 235 (by decide)]
  exact weight20_contains
lemma weight236_contains : weight236.Contains (fejerWeight 236) := by
  rw [← fejerWeight_reverse 236 (by decide)]
  exact weight19_contains
lemma weight237_contains : weight237.Contains (fejerWeight 237) := by
  rw [← fejerWeight_reverse 237 (by decide)]
  exact weight18_contains
lemma weight238_contains : weight238.Contains (fejerWeight 238) := by
  rw [← fejerWeight_reverse 238 (by decide)]
  exact weight17_contains
lemma weight239_contains : weight239.Contains (fejerWeight 239) := by
  rw [← fejerWeight_reverse 239 (by decide)]
  exact weight16_contains_g
lemma weights1_contains (j : Fin 16) : (weights1 j).Contains (fejerWeight (16+j.val)) := by
  fin_cases j
  · exact weight16_contains_g
  · exact weight17_contains
  · exact weight18_contains
  · exact weight19_contains
  · exact weight20_contains
  · exact weight21_contains
  · exact weight22_contains
  · exact weight23_contains
  · exact weight24_contains
  · exact weight25_contains
  · exact weight26_contains
  · exact weight27_contains
  · exact weight28_contains
  · exact weight29_contains
  · exact weight30_contains
  · exact weight31_contains
lemma weights2_contains (j : Fin 16) : (weights2 j).Contains (fejerWeight (32+j.val)) := by
  fin_cases j
  · exact weight32_contains
  · exact weight33_contains
  · exact weight34_contains
  · exact weight35_contains
  · exact weight36_contains
  · exact weight37_contains
  · exact weight38_contains
  · exact weight39_contains
  · exact weight40_contains
  · exact weight41_contains
  · exact weight42_contains
  · exact weight43_contains
  · exact weight44_contains
  · exact weight45_contains
  · exact weight46_contains
  · exact weight47_contains
lemma weights3_contains (j : Fin 16) : (weights3 j).Contains (fejerWeight (48+j.val)) := by
  fin_cases j
  · exact weight48_contains
  · exact weight49_contains
  · exact weight50_contains
  · exact weight51_contains
  · exact weight52_contains
  · exact weight53_contains
  · exact weight54_contains
  · exact weight55_contains
  · exact weight56_contains
  · exact weight57_contains
  · exact weight58_contains
  · exact weight59_contains
  · exact weight60_contains
  · exact weight61_contains
  · exact weight62_contains
  · exact weight63_contains
lemma weights4_contains (j : Fin 16) : (weights4 j).Contains (fejerWeight (64+j.val)) := by
  fin_cases j
  · exact weight64_contains
  · exact weight65_contains
  · exact weight66_contains
  · exact weight67_contains
  · exact weight68_contains
  · exact weight69_contains
  · exact weight70_contains
  · exact weight71_contains
  · exact weight72_contains
  · exact weight73_contains
  · exact weight74_contains
  · exact weight75_contains
  · exact weight76_contains
  · exact weight77_contains
  · exact weight78_contains
  · exact weight79_contains
lemma weights5_contains (j : Fin 16) : (weights5 j).Contains (fejerWeight (80+j.val)) := by
  fin_cases j
  · exact weight80_contains
  · exact weight81_contains
  · exact weight82_contains
  · exact weight83_contains
  · exact weight84_contains
  · exact weight85_contains
  · exact weight86_contains
  · exact weight87_contains
  · exact weight88_contains
  · exact weight89_contains
  · exact weight90_contains
  · exact weight91_contains
  · exact weight92_contains
  · exact weight93_contains
  · exact weight94_contains
  · exact weight95_contains
lemma weights6_contains (j : Fin 16) : (weights6 j).Contains (fejerWeight (96+j.val)) := by
  fin_cases j
  · exact weight96_contains
  · exact weight97_contains
  · exact weight98_contains
  · exact weight99_contains
  · exact weight100_contains_g
  · exact weight101_contains_g
  · exact weight102_contains
  · exact weight103_contains
  · exact weight104_contains
  · exact weight105_contains
  · exact weight106_contains
  · exact weight107_contains
  · exact weight108_contains
  · exact weight109_contains
  · exact weight110_contains
  · exact weight111_contains
lemma weights11_contains (j : Fin 16) : (weights11 j).Contains (fejerWeight (176+j.val)) := by
  fin_cases j
  · exact weight176_contains_g
  · exact weight177_contains_g
  · exact weight178_contains_g
  · exact weight179_contains_g
  · exact weight180_contains_g
  · exact weight181_contains_g
  · exact weight182_contains_g
  · exact weight183_contains_g
  · exact weight184_contains_g
  · exact weight185_contains_g
  · exact weight186_contains
  · exact weight187_contains
  · exact weight188_contains
  · exact weight189_contains
  · exact weight190_contains
  · exact weight191_contains
lemma weights12_contains (j : Fin 16) : (weights12 j).Contains (fejerWeight (192+j.val)) := by
  fin_cases j
  · exact weight192_contains
  · exact weight193_contains
  · exact weight194_contains
  · exact weight195_contains
  · exact weight196_contains
  · exact weight197_contains
  · exact weight198_contains
  · exact weight199_contains
  · exact weight200_contains
  · exact weight201_contains
  · exact weight202_contains
  · exact weight203_contains
  · exact weight204_contains
  · exact weight205_contains
  · exact weight206_contains
  · exact weight207_contains
lemma weights13_contains (j : Fin 16) : (weights13 j).Contains (fejerWeight (208+j.val)) := by
  fin_cases j
  · exact weight208_contains
  · exact weight209_contains
  · exact weight210_contains
  · exact weight211_contains
  · exact weight212_contains
  · exact weight213_contains
  · exact weight214_contains
  · exact weight215_contains
  · exact weight216_contains
  · exact weight217_contains
  · exact weight218_contains
  · exact weight219_contains
  · exact weight220_contains
  · exact weight221_contains
  · exact weight222_contains
  · exact weight223_contains
lemma weights14_contains (j : Fin 16) : (weights14 j).Contains (fejerWeight (224+j.val)) := by
  fin_cases j
  · exact weight224_contains
  · exact weight225_contains
  · exact weight226_contains
  · exact weight227_contains
  · exact weight228_contains
  · exact weight229_contains
  · exact weight230_contains
  · exact weight231_contains
  · exact weight232_contains
  · exact weight233_contains
  · exact weight234_contains
  · exact weight235_contains
  · exact weight236_contains
  · exact weight237_contains
  · exact weight238_contains
  · exact weight239_contains
lemma weightRows_contains_g_oai (i j : Fin 16) : (weightRows i j).Contains (fejerWeight (16*i.val+j.val)) := by
  fin_cases i
  · exact weights0_contains_g j
  · exact weights1_contains j
  · exact weights2_contains j
  · exact weights3_contains j
  · exact weights4_contains j
  · exact weights5_contains j
  · exact weights6_contains j
  · exact weights7_contains_g j
  · exact weights8_contains_g j
  · exact weights9_contains_g j
  · exact weights10_contains_g j
  · exact weights11_contains j
  · exact weights12_contains j
  · exact weights13_contains j
  · exact weights14_contains j
  · exact weights15_contains_g j
end SharpPlanar.IntegerCompact


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerCompact.weightRows_contains_g_oai := @OAI.SharpPlanar.IntegerCompact.weightRows_contains_g_oai
