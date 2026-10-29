-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.real_cover_g010
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:58:44.722031+00:00
-- url     : https://prove2.me/submissions/18b1a819-1382-4b24-ae6c-5d4d6dec8336

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1320
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1321
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1322
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1323
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1324
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1325
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1326
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1327
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1328
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1329
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1330
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1331
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1332
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1333
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1334
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1335
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1336
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1337
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1338
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1339
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1340
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1341
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1342
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1343
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1344
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1345
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1346
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1347
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1348
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1349
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1350
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1351
set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalCutoff4
theorem real_cover_g010 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  by_cases h0 : p ≤ (535/128 : ℝ)
  · exact real_three_w1320 p hpa h0
  by_cases h1 : p ≤ (4281/1024 : ℝ)
  · exact real_three_w1321 p (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p ≤ (2141/512 : ℝ)
  · exact real_three_w1322 p (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p ≤ (4283/1024 : ℝ)
  · exact real_three_w1323 p (le_of_lt (lt_of_not_ge h2)) h3
  by_cases h4 : p ≤ (1071/256 : ℝ)
  · exact real_three_w1324 p (le_of_lt (lt_of_not_ge h3)) h4
  by_cases h5 : p ≤ (4285/1024 : ℝ)
  · exact real_three_w1325 p (le_of_lt (lt_of_not_ge h4)) h5
  by_cases h6 : p ≤ (2143/512 : ℝ)
  · exact real_three_w1326 p (le_of_lt (lt_of_not_ge h5)) h6
  by_cases h7 : p ≤ (4287/1024 : ℝ)
  · exact real_three_w1327 p (le_of_lt (lt_of_not_ge h6)) h7
  by_cases h8 : p ≤ (67/16 : ℝ)
  · exact real_three_w1328 p (le_of_lt (lt_of_not_ge h7)) h8
  by_cases h9 : p ≤ (4289/1024 : ℝ)
  · exact real_three_w1329 p (le_of_lt (lt_of_not_ge h8)) h9
  by_cases h10 : p ≤ (2145/512 : ℝ)
  · exact real_three_w1330 p (le_of_lt (lt_of_not_ge h9)) h10
  by_cases h11 : p ≤ (4291/1024 : ℝ)
  · exact real_three_w1331 p (le_of_lt (lt_of_not_ge h10)) h11
  by_cases h12 : p ≤ (1073/256 : ℝ)
  · exact real_three_w1332 p (le_of_lt (lt_of_not_ge h11)) h12
  by_cases h13 : p ≤ (4293/1024 : ℝ)
  · exact real_three_w1333 p (le_of_lt (lt_of_not_ge h12)) h13
  by_cases h14 : p ≤ (2147/512 : ℝ)
  · exact real_three_w1334 p (le_of_lt (lt_of_not_ge h13)) h14
  by_cases h15 : p ≤ (4295/1024 : ℝ)
  · exact real_three_w1335 p (le_of_lt (lt_of_not_ge h14)) h15
  by_cases h16 : p ≤ (537/128 : ℝ)
  · exact real_three_w1336 p (le_of_lt (lt_of_not_ge h15)) h16
  by_cases h17 : p ≤ (4297/1024 : ℝ)
  · exact real_three_w1337 p (le_of_lt (lt_of_not_ge h16)) h17
  by_cases h18 : p ≤ (2149/512 : ℝ)
  · exact real_three_w1338 p (le_of_lt (lt_of_not_ge h17)) h18
  by_cases h19 : p ≤ (4299/1024 : ℝ)
  · exact real_three_w1339 p (le_of_lt (lt_of_not_ge h18)) h19
  by_cases h20 : p ≤ (1075/256 : ℝ)
  · exact real_three_w1340 p (le_of_lt (lt_of_not_ge h19)) h20
  by_cases h21 : p ≤ (4301/1024 : ℝ)
  · exact real_three_w1341 p (le_of_lt (lt_of_not_ge h20)) h21
  by_cases h22 : p ≤ (2151/512 : ℝ)
  · exact real_three_w1342 p (le_of_lt (lt_of_not_ge h21)) h22
  by_cases h23 : p ≤ (4303/1024 : ℝ)
  · exact real_three_w1343 p (le_of_lt (lt_of_not_ge h22)) h23
  by_cases h24 : p ≤ (269/64 : ℝ)
  · exact real_three_w1344 p (le_of_lt (lt_of_not_ge h23)) h24
  by_cases h25 : p ≤ (4305/1024 : ℝ)
  · exact real_three_w1345 p (le_of_lt (lt_of_not_ge h24)) h25
  by_cases h26 : p ≤ (2153/512 : ℝ)
  · exact real_three_w1346 p (le_of_lt (lt_of_not_ge h25)) h26
  by_cases h27 : p ≤ (4307/1024 : ℝ)
  · exact real_three_w1347 p (le_of_lt (lt_of_not_ge h26)) h27
  by_cases h28 : p ≤ (1077/256 : ℝ)
  · exact real_three_w1348 p (le_of_lt (lt_of_not_ge h27)) h28
  by_cases h29 : p ≤ (4309/1024 : ℝ)
  · exact real_three_w1349 p (le_of_lt (lt_of_not_ge h28)) h29
  by_cases h30 : p ≤ (2155/512 : ℝ)
  · exact real_three_w1350 p (le_of_lt (lt_of_not_ge h29)) h30
  exact real_three_w1351 p (le_of_lt (lt_of_not_ge h30)) hpb

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  exact HlawkaSchatten.DiagonalCutoff4.real_cover_g010 p hpa hpb

#print axioms solution
