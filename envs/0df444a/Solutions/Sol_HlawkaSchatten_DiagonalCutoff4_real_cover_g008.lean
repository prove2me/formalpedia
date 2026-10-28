-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.real_cover_g008
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:52:52.919126+00:00
-- url     : https://prove2.me/submissions/9bc5d1c4-4846-47a6-82a6-ea7a82858d66

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1256
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1257
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1258
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1259
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1260
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1261
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1262
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1263
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1264
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1265
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1266
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1267
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1268
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1269
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1270
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1271
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1272
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1273
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1274
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1275
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1276
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1277
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1278
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1279
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1280
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1281
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1282
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1283
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1284
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1285
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1286
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1287
set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalCutoff4
theorem real_cover_g008 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  by_cases h0 : p ≤ (8449/2048 : ℝ)
  · exact real_three_w1256 p hpa h0
  by_cases h1 : p ≤ (4225/1024 : ℝ)
  · exact real_three_w1257 p (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p ≤ (8451/2048 : ℝ)
  · exact real_three_w1258 p (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p ≤ (2113/512 : ℝ)
  · exact real_three_w1259 p (le_of_lt (lt_of_not_ge h2)) h3
  by_cases h4 : p ≤ (8453/2048 : ℝ)
  · exact real_three_w1260 p (le_of_lt (lt_of_not_ge h3)) h4
  by_cases h5 : p ≤ (4227/1024 : ℝ)
  · exact real_three_w1261 p (le_of_lt (lt_of_not_ge h4)) h5
  by_cases h6 : p ≤ (8455/2048 : ℝ)
  · exact real_three_w1262 p (le_of_lt (lt_of_not_ge h5)) h6
  by_cases h7 : p ≤ (1057/256 : ℝ)
  · exact real_three_w1263 p (le_of_lt (lt_of_not_ge h6)) h7
  by_cases h8 : p ≤ (8457/2048 : ℝ)
  · exact real_three_w1264 p (le_of_lt (lt_of_not_ge h7)) h8
  by_cases h9 : p ≤ (4229/1024 : ℝ)
  · exact real_three_w1265 p (le_of_lt (lt_of_not_ge h8)) h9
  by_cases h10 : p ≤ (8459/2048 : ℝ)
  · exact real_three_w1266 p (le_of_lt (lt_of_not_ge h9)) h10
  by_cases h11 : p ≤ (2115/512 : ℝ)
  · exact real_three_w1267 p (le_of_lt (lt_of_not_ge h10)) h11
  by_cases h12 : p ≤ (8461/2048 : ℝ)
  · exact real_three_w1268 p (le_of_lt (lt_of_not_ge h11)) h12
  by_cases h13 : p ≤ (8463/2048 : ℝ)
  · exact real_three_w1269 p (le_of_lt (lt_of_not_ge h12)) h13
  by_cases h14 : p ≤ (529/128 : ℝ)
  · exact real_three_w1270 p (le_of_lt (lt_of_not_ge h13)) h14
  by_cases h15 : p ≤ (8465/2048 : ℝ)
  · exact real_three_w1271 p (le_of_lt (lt_of_not_ge h14)) h15
  by_cases h16 : p ≤ (4233/1024 : ℝ)
  · exact real_three_w1272 p (le_of_lt (lt_of_not_ge h15)) h16
  by_cases h17 : p ≤ (8467/2048 : ℝ)
  · exact real_three_w1273 p (le_of_lt (lt_of_not_ge h16)) h17
  by_cases h18 : p ≤ (2117/512 : ℝ)
  · exact real_three_w1274 p (le_of_lt (lt_of_not_ge h17)) h18
  by_cases h19 : p ≤ (4235/1024 : ℝ)
  · exact real_three_w1275 p (le_of_lt (lt_of_not_ge h18)) h19
  by_cases h20 : p ≤ (1059/256 : ℝ)
  · exact real_three_w1276 p (le_of_lt (lt_of_not_ge h19)) h20
  by_cases h21 : p ≤ (4237/1024 : ℝ)
  · exact real_three_w1277 p (le_of_lt (lt_of_not_ge h20)) h21
  by_cases h22 : p ≤ (2119/512 : ℝ)
  · exact real_three_w1278 p (le_of_lt (lt_of_not_ge h21)) h22
  by_cases h23 : p ≤ (4239/1024 : ℝ)
  · exact real_three_w1279 p (le_of_lt (lt_of_not_ge h22)) h23
  by_cases h24 : p ≤ (265/64 : ℝ)
  · exact real_three_w1280 p (le_of_lt (lt_of_not_ge h23)) h24
  by_cases h25 : p ≤ (4241/1024 : ℝ)
  · exact real_three_w1281 p (le_of_lt (lt_of_not_ge h24)) h25
  by_cases h26 : p ≤ (2121/512 : ℝ)
  · exact real_three_w1282 p (le_of_lt (lt_of_not_ge h25)) h26
  by_cases h27 : p ≤ (4243/1024 : ℝ)
  · exact real_three_w1283 p (le_of_lt (lt_of_not_ge h26)) h27
  by_cases h28 : p ≤ (1061/256 : ℝ)
  · exact real_three_w1284 p (le_of_lt (lt_of_not_ge h27)) h28
  by_cases h29 : p ≤ (4245/1024 : ℝ)
  · exact real_three_w1285 p (le_of_lt (lt_of_not_ge h28)) h29
  by_cases h30 : p ≤ (2123/512 : ℝ)
  · exact real_three_w1286 p (le_of_lt (lt_of_not_ge h29)) h30
  exact real_three_w1287 p (le_of_lt (lt_of_not_ge h30)) hpb

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  exact HlawkaSchatten.DiagonalCutoff4.real_cover_g008 p hpa hpb

#print axioms solution
