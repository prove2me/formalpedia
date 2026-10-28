-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.real_cover_g007
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:18:38.668148+00:00
-- url     : https://prove2.me/submissions/413b0c4c-8c91-4641-aa22-2dccbd984c09

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1224
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1225
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1226
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1227
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1228
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1229
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1230
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1231
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1232
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1233
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1234
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1235
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1236
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1237
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1238
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1239
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1240
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1241
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1242
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1243
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1244
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1245
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1246
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1247
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1248
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1249
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1250
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1251
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1252
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1253
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1254
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1255
set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalCutoff4
theorem real_cover_g007 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  by_cases h0 : p ≤ (8417/2048 : ℝ)
  · exact real_three_w1224 p hpa h0
  by_cases h1 : p ≤ (4209/1024 : ℝ)
  · exact real_three_w1225 p (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p ≤ (8419/2048 : ℝ)
  · exact real_three_w1226 p (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p ≤ (2105/512 : ℝ)
  · exact real_three_w1227 p (le_of_lt (lt_of_not_ge h2)) h3
  by_cases h4 : p ≤ (8421/2048 : ℝ)
  · exact real_three_w1228 p (le_of_lt (lt_of_not_ge h3)) h4
  by_cases h5 : p ≤ (4211/1024 : ℝ)
  · exact real_three_w1229 p (le_of_lt (lt_of_not_ge h4)) h5
  by_cases h6 : p ≤ (8423/2048 : ℝ)
  · exact real_three_w1230 p (le_of_lt (lt_of_not_ge h5)) h6
  by_cases h7 : p ≤ (1053/256 : ℝ)
  · exact real_three_w1231 p (le_of_lt (lt_of_not_ge h6)) h7
  by_cases h8 : p ≤ (8425/2048 : ℝ)
  · exact real_three_w1232 p (le_of_lt (lt_of_not_ge h7)) h8
  by_cases h9 : p ≤ (4213/1024 : ℝ)
  · exact real_three_w1233 p (le_of_lt (lt_of_not_ge h8)) h9
  by_cases h10 : p ≤ (8427/2048 : ℝ)
  · exact real_three_w1234 p (le_of_lt (lt_of_not_ge h9)) h10
  by_cases h11 : p ≤ (2107/512 : ℝ)
  · exact real_three_w1235 p (le_of_lt (lt_of_not_ge h10)) h11
  by_cases h12 : p ≤ (8429/2048 : ℝ)
  · exact real_three_w1236 p (le_of_lt (lt_of_not_ge h11)) h12
  by_cases h13 : p ≤ (4215/1024 : ℝ)
  · exact real_three_w1237 p (le_of_lt (lt_of_not_ge h12)) h13
  by_cases h14 : p ≤ (8431/2048 : ℝ)
  · exact real_three_w1238 p (le_of_lt (lt_of_not_ge h13)) h14
  by_cases h15 : p ≤ (527/128 : ℝ)
  · exact real_three_w1239 p (le_of_lt (lt_of_not_ge h14)) h15
  by_cases h16 : p ≤ (8433/2048 : ℝ)
  · exact real_three_w1240 p (le_of_lt (lt_of_not_ge h15)) h16
  by_cases h17 : p ≤ (4217/1024 : ℝ)
  · exact real_three_w1241 p (le_of_lt (lt_of_not_ge h16)) h17
  by_cases h18 : p ≤ (8435/2048 : ℝ)
  · exact real_three_w1242 p (le_of_lt (lt_of_not_ge h17)) h18
  by_cases h19 : p ≤ (2109/512 : ℝ)
  · exact real_three_w1243 p (le_of_lt (lt_of_not_ge h18)) h19
  by_cases h20 : p ≤ (8437/2048 : ℝ)
  · exact real_three_w1244 p (le_of_lt (lt_of_not_ge h19)) h20
  by_cases h21 : p ≤ (4219/1024 : ℝ)
  · exact real_three_w1245 p (le_of_lt (lt_of_not_ge h20)) h21
  by_cases h22 : p ≤ (8439/2048 : ℝ)
  · exact real_three_w1246 p (le_of_lt (lt_of_not_ge h21)) h22
  by_cases h23 : p ≤ (1055/256 : ℝ)
  · exact real_three_w1247 p (le_of_lt (lt_of_not_ge h22)) h23
  by_cases h24 : p ≤ (8441/2048 : ℝ)
  · exact real_three_w1248 p (le_of_lt (lt_of_not_ge h23)) h24
  by_cases h25 : p ≤ (4221/1024 : ℝ)
  · exact real_three_w1249 p (le_of_lt (lt_of_not_ge h24)) h25
  by_cases h26 : p ≤ (8443/2048 : ℝ)
  · exact real_three_w1250 p (le_of_lt (lt_of_not_ge h25)) h26
  by_cases h27 : p ≤ (2111/512 : ℝ)
  · exact real_three_w1251 p (le_of_lt (lt_of_not_ge h26)) h27
  by_cases h28 : p ≤ (8445/2048 : ℝ)
  · exact real_three_w1252 p (le_of_lt (lt_of_not_ge h27)) h28
  by_cases h29 : p ≤ (4223/1024 : ℝ)
  · exact real_three_w1253 p (le_of_lt (lt_of_not_ge h28)) h29
  by_cases h30 : p ≤ (8447/2048 : ℝ)
  · exact real_three_w1254 p (le_of_lt (lt_of_not_ge h29)) h30
  exact real_three_w1255 p (le_of_lt (lt_of_not_ge h30)) hpb

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  exact HlawkaSchatten.DiagonalCutoff4.real_cover_g007 p hpa hpb

#print axioms solution
