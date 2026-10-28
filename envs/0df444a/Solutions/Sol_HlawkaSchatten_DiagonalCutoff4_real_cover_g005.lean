-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.real_cover_g005
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:52:02.875647+00:00
-- url     : https://prove2.me/submissions/3556f41b-11bd-4c91-a57b-d92eda55e6f7

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1160
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1161
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1162
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1163
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1164
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1165
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1166
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1167
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1168
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1169
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1170
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1171
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1172
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1173
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1174
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1175
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1176
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1177
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1178
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1179
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1180
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1181
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1182
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1183
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1184
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1185
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1186
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1187
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1188
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1189
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1190
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1191
set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalCutoff4
theorem real_cover_g005 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  by_cases h0 : p ≤ (8353/2048 : ℝ)
  · exact real_three_w1160 p hpa h0
  by_cases h1 : p ≤ (4177/1024 : ℝ)
  · exact real_three_w1161 p (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p ≤ (8355/2048 : ℝ)
  · exact real_three_w1162 p (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p ≤ (2089/512 : ℝ)
  · exact real_three_w1163 p (le_of_lt (lt_of_not_ge h2)) h3
  by_cases h4 : p ≤ (8357/2048 : ℝ)
  · exact real_three_w1164 p (le_of_lt (lt_of_not_ge h3)) h4
  by_cases h5 : p ≤ (4179/1024 : ℝ)
  · exact real_three_w1165 p (le_of_lt (lt_of_not_ge h4)) h5
  by_cases h6 : p ≤ (8359/2048 : ℝ)
  · exact real_three_w1166 p (le_of_lt (lt_of_not_ge h5)) h6
  by_cases h7 : p ≤ (1045/256 : ℝ)
  · exact real_three_w1167 p (le_of_lt (lt_of_not_ge h6)) h7
  by_cases h8 : p ≤ (8361/2048 : ℝ)
  · exact real_three_w1168 p (le_of_lt (lt_of_not_ge h7)) h8
  by_cases h9 : p ≤ (4181/1024 : ℝ)
  · exact real_three_w1169 p (le_of_lt (lt_of_not_ge h8)) h9
  by_cases h10 : p ≤ (8363/2048 : ℝ)
  · exact real_three_w1170 p (le_of_lt (lt_of_not_ge h9)) h10
  by_cases h11 : p ≤ (2091/512 : ℝ)
  · exact real_three_w1171 p (le_of_lt (lt_of_not_ge h10)) h11
  by_cases h12 : p ≤ (8365/2048 : ℝ)
  · exact real_three_w1172 p (le_of_lt (lt_of_not_ge h11)) h12
  by_cases h13 : p ≤ (4183/1024 : ℝ)
  · exact real_three_w1173 p (le_of_lt (lt_of_not_ge h12)) h13
  by_cases h14 : p ≤ (8367/2048 : ℝ)
  · exact real_three_w1174 p (le_of_lt (lt_of_not_ge h13)) h14
  by_cases h15 : p ≤ (523/128 : ℝ)
  · exact real_three_w1175 p (le_of_lt (lt_of_not_ge h14)) h15
  by_cases h16 : p ≤ (8369/2048 : ℝ)
  · exact real_three_w1176 p (le_of_lt (lt_of_not_ge h15)) h16
  by_cases h17 : p ≤ (4185/1024 : ℝ)
  · exact real_three_w1177 p (le_of_lt (lt_of_not_ge h16)) h17
  by_cases h18 : p ≤ (8371/2048 : ℝ)
  · exact real_three_w1178 p (le_of_lt (lt_of_not_ge h17)) h18
  by_cases h19 : p ≤ (2093/512 : ℝ)
  · exact real_three_w1179 p (le_of_lt (lt_of_not_ge h18)) h19
  by_cases h20 : p ≤ (8373/2048 : ℝ)
  · exact real_three_w1180 p (le_of_lt (lt_of_not_ge h19)) h20
  by_cases h21 : p ≤ (4187/1024 : ℝ)
  · exact real_three_w1181 p (le_of_lt (lt_of_not_ge h20)) h21
  by_cases h22 : p ≤ (8375/2048 : ℝ)
  · exact real_three_w1182 p (le_of_lt (lt_of_not_ge h21)) h22
  by_cases h23 : p ≤ (1047/256 : ℝ)
  · exact real_three_w1183 p (le_of_lt (lt_of_not_ge h22)) h23
  by_cases h24 : p ≤ (8377/2048 : ℝ)
  · exact real_three_w1184 p (le_of_lt (lt_of_not_ge h23)) h24
  by_cases h25 : p ≤ (4189/1024 : ℝ)
  · exact real_three_w1185 p (le_of_lt (lt_of_not_ge h24)) h25
  by_cases h26 : p ≤ (8379/2048 : ℝ)
  · exact real_three_w1186 p (le_of_lt (lt_of_not_ge h25)) h26
  by_cases h27 : p ≤ (2095/512 : ℝ)
  · exact real_three_w1187 p (le_of_lt (lt_of_not_ge h26)) h27
  by_cases h28 : p ≤ (8381/2048 : ℝ)
  · exact real_three_w1188 p (le_of_lt (lt_of_not_ge h27)) h28
  by_cases h29 : p ≤ (4191/1024 : ℝ)
  · exact real_three_w1189 p (le_of_lt (lt_of_not_ge h28)) h29
  by_cases h30 : p ≤ (8383/2048 : ℝ)
  · exact real_three_w1190 p (le_of_lt (lt_of_not_ge h29)) h30
  exact real_three_w1191 p (le_of_lt (lt_of_not_ge h30)) hpb

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  exact HlawkaSchatten.DiagonalCutoff4.real_cover_g005 p hpa hpb

#print axioms solution
