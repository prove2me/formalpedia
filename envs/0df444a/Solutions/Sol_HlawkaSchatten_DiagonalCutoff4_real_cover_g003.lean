-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.real_cover_g003
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:11:39.861727+00:00
-- url     : https://prove2.me/submissions/b7bdd335-273e-455c-9d4c-d3f948f8f545

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1096
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1097
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1098
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1099
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1100
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1101
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1102
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1103
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1104
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1105
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1106
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1107
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1108
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1109
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1110
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1111
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1112
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1113
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1114
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1115
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1116
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1117
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1118
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1119
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1120
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1121
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1122
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1123
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1124
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1125
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1126
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1127
set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalCutoff4
theorem real_cover_g003 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  by_cases h0 : p ≤ (8289/2048 : ℝ)
  · exact real_three_w1096 p hpa h0
  by_cases h1 : p ≤ (4145/1024 : ℝ)
  · exact real_three_w1097 p (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p ≤ (8291/2048 : ℝ)
  · exact real_three_w1098 p (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p ≤ (2073/512 : ℝ)
  · exact real_three_w1099 p (le_of_lt (lt_of_not_ge h2)) h3
  by_cases h4 : p ≤ (8293/2048 : ℝ)
  · exact real_three_w1100 p (le_of_lt (lt_of_not_ge h3)) h4
  by_cases h5 : p ≤ (4147/1024 : ℝ)
  · exact real_three_w1101 p (le_of_lt (lt_of_not_ge h4)) h5
  by_cases h6 : p ≤ (8295/2048 : ℝ)
  · exact real_three_w1102 p (le_of_lt (lt_of_not_ge h5)) h6
  by_cases h7 : p ≤ (1037/256 : ℝ)
  · exact real_three_w1103 p (le_of_lt (lt_of_not_ge h6)) h7
  by_cases h8 : p ≤ (8297/2048 : ℝ)
  · exact real_three_w1104 p (le_of_lt (lt_of_not_ge h7)) h8
  by_cases h9 : p ≤ (4149/1024 : ℝ)
  · exact real_three_w1105 p (le_of_lt (lt_of_not_ge h8)) h9
  by_cases h10 : p ≤ (8299/2048 : ℝ)
  · exact real_three_w1106 p (le_of_lt (lt_of_not_ge h9)) h10
  by_cases h11 : p ≤ (2075/512 : ℝ)
  · exact real_three_w1107 p (le_of_lt (lt_of_not_ge h10)) h11
  by_cases h12 : p ≤ (8301/2048 : ℝ)
  · exact real_three_w1108 p (le_of_lt (lt_of_not_ge h11)) h12
  by_cases h13 : p ≤ (4151/1024 : ℝ)
  · exact real_three_w1109 p (le_of_lt (lt_of_not_ge h12)) h13
  by_cases h14 : p ≤ (8303/2048 : ℝ)
  · exact real_three_w1110 p (le_of_lt (lt_of_not_ge h13)) h14
  by_cases h15 : p ≤ (519/128 : ℝ)
  · exact real_three_w1111 p (le_of_lt (lt_of_not_ge h14)) h15
  by_cases h16 : p ≤ (8305/2048 : ℝ)
  · exact real_three_w1112 p (le_of_lt (lt_of_not_ge h15)) h16
  by_cases h17 : p ≤ (4153/1024 : ℝ)
  · exact real_three_w1113 p (le_of_lt (lt_of_not_ge h16)) h17
  by_cases h18 : p ≤ (8307/2048 : ℝ)
  · exact real_three_w1114 p (le_of_lt (lt_of_not_ge h17)) h18
  by_cases h19 : p ≤ (2077/512 : ℝ)
  · exact real_three_w1115 p (le_of_lt (lt_of_not_ge h18)) h19
  by_cases h20 : p ≤ (8309/2048 : ℝ)
  · exact real_three_w1116 p (le_of_lt (lt_of_not_ge h19)) h20
  by_cases h21 : p ≤ (4155/1024 : ℝ)
  · exact real_three_w1117 p (le_of_lt (lt_of_not_ge h20)) h21
  by_cases h22 : p ≤ (8311/2048 : ℝ)
  · exact real_three_w1118 p (le_of_lt (lt_of_not_ge h21)) h22
  by_cases h23 : p ≤ (1039/256 : ℝ)
  · exact real_three_w1119 p (le_of_lt (lt_of_not_ge h22)) h23
  by_cases h24 : p ≤ (8313/2048 : ℝ)
  · exact real_three_w1120 p (le_of_lt (lt_of_not_ge h23)) h24
  by_cases h25 : p ≤ (4157/1024 : ℝ)
  · exact real_three_w1121 p (le_of_lt (lt_of_not_ge h24)) h25
  by_cases h26 : p ≤ (8315/2048 : ℝ)
  · exact real_three_w1122 p (le_of_lt (lt_of_not_ge h25)) h26
  by_cases h27 : p ≤ (2079/512 : ℝ)
  · exact real_three_w1123 p (le_of_lt (lt_of_not_ge h26)) h27
  by_cases h28 : p ≤ (8317/2048 : ℝ)
  · exact real_three_w1124 p (le_of_lt (lt_of_not_ge h27)) h28
  by_cases h29 : p ≤ (4159/1024 : ℝ)
  · exact real_three_w1125 p (le_of_lt (lt_of_not_ge h28)) h29
  by_cases h30 : p ≤ (8319/2048 : ℝ)
  · exact real_three_w1126 p (le_of_lt (lt_of_not_ge h29)) h30
  exact real_three_w1127 p (le_of_lt (lt_of_not_ge h30)) hpb

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  exact HlawkaSchatten.DiagonalCutoff4.real_cover_g003 p hpa hpb

#print axioms solution
