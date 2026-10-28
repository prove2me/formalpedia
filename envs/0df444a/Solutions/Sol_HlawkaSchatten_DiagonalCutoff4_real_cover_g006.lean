-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.real_cover_g006
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:06:15.618761+00:00
-- url     : https://prove2.me/submissions/717418d4-e914-46ac-83d0-daae5987bc42

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1192
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1193
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1194
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1195
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1196
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1197
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1198
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1199
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1200
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1201
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1202
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1203
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1204
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1205
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1206
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1207
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1208
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1209
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1210
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1211
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1212
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1213
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1214
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1215
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1216
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1217
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1218
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1219
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1220
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1221
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1222
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1223
set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalCutoff4
theorem real_cover_g006 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  by_cases h0 : p ≤ (8385/2048 : ℝ)
  · exact real_three_w1192 p hpa h0
  by_cases h1 : p ≤ (4193/1024 : ℝ)
  · exact real_three_w1193 p (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p ≤ (8387/2048 : ℝ)
  · exact real_three_w1194 p (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p ≤ (2097/512 : ℝ)
  · exact real_three_w1195 p (le_of_lt (lt_of_not_ge h2)) h3
  by_cases h4 : p ≤ (8389/2048 : ℝ)
  · exact real_three_w1196 p (le_of_lt (lt_of_not_ge h3)) h4
  by_cases h5 : p ≤ (4195/1024 : ℝ)
  · exact real_three_w1197 p (le_of_lt (lt_of_not_ge h4)) h5
  by_cases h6 : p ≤ (8391/2048 : ℝ)
  · exact real_three_w1198 p (le_of_lt (lt_of_not_ge h5)) h6
  by_cases h7 : p ≤ (1049/256 : ℝ)
  · exact real_three_w1199 p (le_of_lt (lt_of_not_ge h6)) h7
  by_cases h8 : p ≤ (8393/2048 : ℝ)
  · exact real_three_w1200 p (le_of_lt (lt_of_not_ge h7)) h8
  by_cases h9 : p ≤ (4197/1024 : ℝ)
  · exact real_three_w1201 p (le_of_lt (lt_of_not_ge h8)) h9
  by_cases h10 : p ≤ (8395/2048 : ℝ)
  · exact real_three_w1202 p (le_of_lt (lt_of_not_ge h9)) h10
  by_cases h11 : p ≤ (2099/512 : ℝ)
  · exact real_three_w1203 p (le_of_lt (lt_of_not_ge h10)) h11
  by_cases h12 : p ≤ (8397/2048 : ℝ)
  · exact real_three_w1204 p (le_of_lt (lt_of_not_ge h11)) h12
  by_cases h13 : p ≤ (4199/1024 : ℝ)
  · exact real_three_w1205 p (le_of_lt (lt_of_not_ge h12)) h13
  by_cases h14 : p ≤ (8399/2048 : ℝ)
  · exact real_three_w1206 p (le_of_lt (lt_of_not_ge h13)) h14
  by_cases h15 : p ≤ (525/128 : ℝ)
  · exact real_three_w1207 p (le_of_lt (lt_of_not_ge h14)) h15
  by_cases h16 : p ≤ (8401/2048 : ℝ)
  · exact real_three_w1208 p (le_of_lt (lt_of_not_ge h15)) h16
  by_cases h17 : p ≤ (4201/1024 : ℝ)
  · exact real_three_w1209 p (le_of_lt (lt_of_not_ge h16)) h17
  by_cases h18 : p ≤ (8403/2048 : ℝ)
  · exact real_three_w1210 p (le_of_lt (lt_of_not_ge h17)) h18
  by_cases h19 : p ≤ (2101/512 : ℝ)
  · exact real_three_w1211 p (le_of_lt (lt_of_not_ge h18)) h19
  by_cases h20 : p ≤ (8405/2048 : ℝ)
  · exact real_three_w1212 p (le_of_lt (lt_of_not_ge h19)) h20
  by_cases h21 : p ≤ (4203/1024 : ℝ)
  · exact real_three_w1213 p (le_of_lt (lt_of_not_ge h20)) h21
  by_cases h22 : p ≤ (8407/2048 : ℝ)
  · exact real_three_w1214 p (le_of_lt (lt_of_not_ge h21)) h22
  by_cases h23 : p ≤ (1051/256 : ℝ)
  · exact real_three_w1215 p (le_of_lt (lt_of_not_ge h22)) h23
  by_cases h24 : p ≤ (8409/2048 : ℝ)
  · exact real_three_w1216 p (le_of_lt (lt_of_not_ge h23)) h24
  by_cases h25 : p ≤ (4205/1024 : ℝ)
  · exact real_three_w1217 p (le_of_lt (lt_of_not_ge h24)) h25
  by_cases h26 : p ≤ (8411/2048 : ℝ)
  · exact real_three_w1218 p (le_of_lt (lt_of_not_ge h25)) h26
  by_cases h27 : p ≤ (2103/512 : ℝ)
  · exact real_three_w1219 p (le_of_lt (lt_of_not_ge h26)) h27
  by_cases h28 : p ≤ (8413/2048 : ℝ)
  · exact real_three_w1220 p (le_of_lt (lt_of_not_ge h27)) h28
  by_cases h29 : p ≤ (4207/1024 : ℝ)
  · exact real_three_w1221 p (le_of_lt (lt_of_not_ge h28)) h29
  by_cases h30 : p ≤ (8415/2048 : ℝ)
  · exact real_three_w1222 p (le_of_lt (lt_of_not_ge h29)) h30
  exact real_three_w1223 p (le_of_lt (lt_of_not_ge h30)) hpb

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  exact HlawkaSchatten.DiagonalCutoff4.real_cover_g006 p hpa hpb

#print axioms solution
