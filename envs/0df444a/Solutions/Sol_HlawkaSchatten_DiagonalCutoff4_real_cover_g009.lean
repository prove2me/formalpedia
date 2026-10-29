-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.real_cover_g009
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:31:29.443041+00:00
-- url     : https://prove2.me/submissions/a6ec39ac-3f89-43d8-9bb5-760fa2cfcd2c

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1288
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1289
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1290
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1291
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1292
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1293
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1294
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1295
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1296
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1297
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1298
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1299
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1300
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1301
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1302
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1303
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1304
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1305
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1306
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1307
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1308
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1309
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1310
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1311
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1312
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1313
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1314
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1315
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1316
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1317
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1318
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1319
set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalCutoff4
theorem real_cover_g009 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  by_cases h0 : p ≤ (531/128 : ℝ)
  · exact real_three_w1288 p hpa h0
  by_cases h1 : p ≤ (4249/1024 : ℝ)
  · exact real_three_w1289 p (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p ≤ (2125/512 : ℝ)
  · exact real_three_w1290 p (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p ≤ (4251/1024 : ℝ)
  · exact real_three_w1291 p (le_of_lt (lt_of_not_ge h2)) h3
  by_cases h4 : p ≤ (1063/256 : ℝ)
  · exact real_three_w1292 p (le_of_lt (lt_of_not_ge h3)) h4
  by_cases h5 : p ≤ (4253/1024 : ℝ)
  · exact real_three_w1293 p (le_of_lt (lt_of_not_ge h4)) h5
  by_cases h6 : p ≤ (2127/512 : ℝ)
  · exact real_three_w1294 p (le_of_lt (lt_of_not_ge h5)) h6
  by_cases h7 : p ≤ (4255/1024 : ℝ)
  · exact real_three_w1295 p (le_of_lt (lt_of_not_ge h6)) h7
  by_cases h8 : p ≤ (133/32 : ℝ)
  · exact real_three_w1296 p (le_of_lt (lt_of_not_ge h7)) h8
  by_cases h9 : p ≤ (4257/1024 : ℝ)
  · exact real_three_w1297 p (le_of_lt (lt_of_not_ge h8)) h9
  by_cases h10 : p ≤ (2129/512 : ℝ)
  · exact real_three_w1298 p (le_of_lt (lt_of_not_ge h9)) h10
  by_cases h11 : p ≤ (4259/1024 : ℝ)
  · exact real_three_w1299 p (le_of_lt (lt_of_not_ge h10)) h11
  by_cases h12 : p ≤ (1065/256 : ℝ)
  · exact real_three_w1300 p (le_of_lt (lt_of_not_ge h11)) h12
  by_cases h13 : p ≤ (4261/1024 : ℝ)
  · exact real_three_w1301 p (le_of_lt (lt_of_not_ge h12)) h13
  by_cases h14 : p ≤ (2131/512 : ℝ)
  · exact real_three_w1302 p (le_of_lt (lt_of_not_ge h13)) h14
  by_cases h15 : p ≤ (4263/1024 : ℝ)
  · exact real_three_w1303 p (le_of_lt (lt_of_not_ge h14)) h15
  by_cases h16 : p ≤ (533/128 : ℝ)
  · exact real_three_w1304 p (le_of_lt (lt_of_not_ge h15)) h16
  by_cases h17 : p ≤ (4265/1024 : ℝ)
  · exact real_three_w1305 p (le_of_lt (lt_of_not_ge h16)) h17
  by_cases h18 : p ≤ (2133/512 : ℝ)
  · exact real_three_w1306 p (le_of_lt (lt_of_not_ge h17)) h18
  by_cases h19 : p ≤ (4267/1024 : ℝ)
  · exact real_three_w1307 p (le_of_lt (lt_of_not_ge h18)) h19
  by_cases h20 : p ≤ (1067/256 : ℝ)
  · exact real_three_w1308 p (le_of_lt (lt_of_not_ge h19)) h20
  by_cases h21 : p ≤ (4269/1024 : ℝ)
  · exact real_three_w1309 p (le_of_lt (lt_of_not_ge h20)) h21
  by_cases h22 : p ≤ (2135/512 : ℝ)
  · exact real_three_w1310 p (le_of_lt (lt_of_not_ge h21)) h22
  by_cases h23 : p ≤ (4271/1024 : ℝ)
  · exact real_three_w1311 p (le_of_lt (lt_of_not_ge h22)) h23
  by_cases h24 : p ≤ (267/64 : ℝ)
  · exact real_three_w1312 p (le_of_lt (lt_of_not_ge h23)) h24
  by_cases h25 : p ≤ (4273/1024 : ℝ)
  · exact real_three_w1313 p (le_of_lt (lt_of_not_ge h24)) h25
  by_cases h26 : p ≤ (2137/512 : ℝ)
  · exact real_three_w1314 p (le_of_lt (lt_of_not_ge h25)) h26
  by_cases h27 : p ≤ (4275/1024 : ℝ)
  · exact real_three_w1315 p (le_of_lt (lt_of_not_ge h26)) h27
  by_cases h28 : p ≤ (1069/256 : ℝ)
  · exact real_three_w1316 p (le_of_lt (lt_of_not_ge h27)) h28
  by_cases h29 : p ≤ (4277/1024 : ℝ)
  · exact real_three_w1317 p (le_of_lt (lt_of_not_ge h28)) h29
  by_cases h30 : p ≤ (2139/512 : ℝ)
  · exact real_three_w1318 p (le_of_lt (lt_of_not_ge h29)) h30
  exact real_three_w1319 p (le_of_lt (lt_of_not_ge h30)) hpb

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  exact HlawkaSchatten.DiagonalCutoff4.real_cover_g009 p hpa hpb

#print axioms solution
