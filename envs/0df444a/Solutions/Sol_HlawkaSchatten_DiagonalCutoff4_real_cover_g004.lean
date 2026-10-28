-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.real_cover_g004
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:39:16.724633+00:00
-- url     : https://prove2.me/submissions/cb59396e-447c-4319-883e-e93c2aae7eeb

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1128
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1129
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1130
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1131
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1132
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1133
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1134
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1135
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1136
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1137
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1138
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1139
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1140
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1141
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1142
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1143
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1144
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1145
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1146
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1147
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1148
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1149
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1150
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1151
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1152
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1153
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1154
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1155
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1156
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1157
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1158
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1159
set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalCutoff4
theorem real_cover_g004 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  by_cases h0 : p ≤ (8321/2048 : ℝ)
  · exact real_three_w1128 p hpa h0
  by_cases h1 : p ≤ (4161/1024 : ℝ)
  · exact real_three_w1129 p (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p ≤ (8323/2048 : ℝ)
  · exact real_three_w1130 p (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p ≤ (2081/512 : ℝ)
  · exact real_three_w1131 p (le_of_lt (lt_of_not_ge h2)) h3
  by_cases h4 : p ≤ (8325/2048 : ℝ)
  · exact real_three_w1132 p (le_of_lt (lt_of_not_ge h3)) h4
  by_cases h5 : p ≤ (4163/1024 : ℝ)
  · exact real_three_w1133 p (le_of_lt (lt_of_not_ge h4)) h5
  by_cases h6 : p ≤ (8327/2048 : ℝ)
  · exact real_three_w1134 p (le_of_lt (lt_of_not_ge h5)) h6
  by_cases h7 : p ≤ (1041/256 : ℝ)
  · exact real_three_w1135 p (le_of_lt (lt_of_not_ge h6)) h7
  by_cases h8 : p ≤ (8329/2048 : ℝ)
  · exact real_three_w1136 p (le_of_lt (lt_of_not_ge h7)) h8
  by_cases h9 : p ≤ (4165/1024 : ℝ)
  · exact real_three_w1137 p (le_of_lt (lt_of_not_ge h8)) h9
  by_cases h10 : p ≤ (8331/2048 : ℝ)
  · exact real_three_w1138 p (le_of_lt (lt_of_not_ge h9)) h10
  by_cases h11 : p ≤ (2083/512 : ℝ)
  · exact real_three_w1139 p (le_of_lt (lt_of_not_ge h10)) h11
  by_cases h12 : p ≤ (8333/2048 : ℝ)
  · exact real_three_w1140 p (le_of_lt (lt_of_not_ge h11)) h12
  by_cases h13 : p ≤ (4167/1024 : ℝ)
  · exact real_three_w1141 p (le_of_lt (lt_of_not_ge h12)) h13
  by_cases h14 : p ≤ (8335/2048 : ℝ)
  · exact real_three_w1142 p (le_of_lt (lt_of_not_ge h13)) h14
  by_cases h15 : p ≤ (521/128 : ℝ)
  · exact real_three_w1143 p (le_of_lt (lt_of_not_ge h14)) h15
  by_cases h16 : p ≤ (8337/2048 : ℝ)
  · exact real_three_w1144 p (le_of_lt (lt_of_not_ge h15)) h16
  by_cases h17 : p ≤ (4169/1024 : ℝ)
  · exact real_three_w1145 p (le_of_lt (lt_of_not_ge h16)) h17
  by_cases h18 : p ≤ (8339/2048 : ℝ)
  · exact real_three_w1146 p (le_of_lt (lt_of_not_ge h17)) h18
  by_cases h19 : p ≤ (2085/512 : ℝ)
  · exact real_three_w1147 p (le_of_lt (lt_of_not_ge h18)) h19
  by_cases h20 : p ≤ (8341/2048 : ℝ)
  · exact real_three_w1148 p (le_of_lt (lt_of_not_ge h19)) h20
  by_cases h21 : p ≤ (4171/1024 : ℝ)
  · exact real_three_w1149 p (le_of_lt (lt_of_not_ge h20)) h21
  by_cases h22 : p ≤ (8343/2048 : ℝ)
  · exact real_three_w1150 p (le_of_lt (lt_of_not_ge h21)) h22
  by_cases h23 : p ≤ (1043/256 : ℝ)
  · exact real_three_w1151 p (le_of_lt (lt_of_not_ge h22)) h23
  by_cases h24 : p ≤ (8345/2048 : ℝ)
  · exact real_three_w1152 p (le_of_lt (lt_of_not_ge h23)) h24
  by_cases h25 : p ≤ (4173/1024 : ℝ)
  · exact real_three_w1153 p (le_of_lt (lt_of_not_ge h24)) h25
  by_cases h26 : p ≤ (8347/2048 : ℝ)
  · exact real_three_w1154 p (le_of_lt (lt_of_not_ge h25)) h26
  by_cases h27 : p ≤ (2087/512 : ℝ)
  · exact real_three_w1155 p (le_of_lt (lt_of_not_ge h26)) h27
  by_cases h28 : p ≤ (8349/2048 : ℝ)
  · exact real_three_w1156 p (le_of_lt (lt_of_not_ge h27)) h28
  by_cases h29 : p ≤ (4175/1024 : ℝ)
  · exact real_three_w1157 p (le_of_lt (lt_of_not_ge h28)) h29
  by_cases h30 : p ≤ (8351/2048 : ℝ)
  · exact real_three_w1158 p (le_of_lt (lt_of_not_ge h29)) h30
  exact real_three_w1159 p (le_of_lt (lt_of_not_ge h30)) hpb

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  exact HlawkaSchatten.DiagonalCutoff4.real_cover_g004 p hpa hpb

#print axioms solution
