-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.real_cover_g012
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:32:34.354176+00:00
-- url     : https://prove2.me/submissions/77864e24-57d9-4a6a-89f1-e92057be1797

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1384
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1385
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1386
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1387
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1388
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1389
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1390
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1391
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1392
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1393
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1394
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1395
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1396
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1397
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1398
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1399
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1400
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1401
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1402
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1403
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1404
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1405
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1406
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1407
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1408
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1409
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1410
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1411
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1412
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1413
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1414
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1415
set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalCutoff4
theorem real_cover_g012 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  by_cases h0 : p ≤ (543/128 : ℝ)
  · exact real_three_w1384 p hpa h0
  by_cases h1 : p ≤ (4345/1024 : ℝ)
  · exact real_three_w1385 p (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p ≤ (2173/512 : ℝ)
  · exact real_three_w1386 p (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p ≤ (4347/1024 : ℝ)
  · exact real_three_w1387 p (le_of_lt (lt_of_not_ge h2)) h3
  by_cases h4 : p ≤ (1087/256 : ℝ)
  · exact real_three_w1388 p (le_of_lt (lt_of_not_ge h3)) h4
  by_cases h5 : p ≤ (4349/1024 : ℝ)
  · exact real_three_w1389 p (le_of_lt (lt_of_not_ge h4)) h5
  by_cases h6 : p ≤ (2175/512 : ℝ)
  · exact real_three_w1390 p (le_of_lt (lt_of_not_ge h5)) h6
  by_cases h7 : p ≤ (4351/1024 : ℝ)
  · exact real_three_w1391 p (le_of_lt (lt_of_not_ge h6)) h7
  by_cases h8 : p ≤ (17/4 : ℝ)
  · exact real_three_w1392 p (le_of_lt (lt_of_not_ge h7)) h8
  by_cases h9 : p ≤ (4353/1024 : ℝ)
  · exact real_three_w1393 p (le_of_lt (lt_of_not_ge h8)) h9
  by_cases h10 : p ≤ (2177/512 : ℝ)
  · exact real_three_w1394 p (le_of_lt (lt_of_not_ge h9)) h10
  by_cases h11 : p ≤ (4355/1024 : ℝ)
  · exact real_three_w1395 p (le_of_lt (lt_of_not_ge h10)) h11
  by_cases h12 : p ≤ (1089/256 : ℝ)
  · exact real_three_w1396 p (le_of_lt (lt_of_not_ge h11)) h12
  by_cases h13 : p ≤ (4357/1024 : ℝ)
  · exact real_three_w1397 p (le_of_lt (lt_of_not_ge h12)) h13
  by_cases h14 : p ≤ (2179/512 : ℝ)
  · exact real_three_w1398 p (le_of_lt (lt_of_not_ge h13)) h14
  by_cases h15 : p ≤ (4359/1024 : ℝ)
  · exact real_three_w1399 p (le_of_lt (lt_of_not_ge h14)) h15
  by_cases h16 : p ≤ (545/128 : ℝ)
  · exact real_three_w1400 p (le_of_lt (lt_of_not_ge h15)) h16
  by_cases h17 : p ≤ (4361/1024 : ℝ)
  · exact real_three_w1401 p (le_of_lt (lt_of_not_ge h16)) h17
  by_cases h18 : p ≤ (2181/512 : ℝ)
  · exact real_three_w1402 p (le_of_lt (lt_of_not_ge h17)) h18
  by_cases h19 : p ≤ (4363/1024 : ℝ)
  · exact real_three_w1403 p (le_of_lt (lt_of_not_ge h18)) h19
  by_cases h20 : p ≤ (1091/256 : ℝ)
  · exact real_three_w1404 p (le_of_lt (lt_of_not_ge h19)) h20
  by_cases h21 : p ≤ (4365/1024 : ℝ)
  · exact real_three_w1405 p (le_of_lt (lt_of_not_ge h20)) h21
  by_cases h22 : p ≤ (2183/512 : ℝ)
  · exact real_three_w1406 p (le_of_lt (lt_of_not_ge h21)) h22
  by_cases h23 : p ≤ (4367/1024 : ℝ)
  · exact real_three_w1407 p (le_of_lt (lt_of_not_ge h22)) h23
  by_cases h24 : p ≤ (273/64 : ℝ)
  · exact real_three_w1408 p (le_of_lt (lt_of_not_ge h23)) h24
  by_cases h25 : p ≤ (4369/1024 : ℝ)
  · exact real_three_w1409 p (le_of_lt (lt_of_not_ge h24)) h25
  by_cases h26 : p ≤ (2185/512 : ℝ)
  · exact real_three_w1410 p (le_of_lt (lt_of_not_ge h25)) h26
  by_cases h27 : p ≤ (4371/1024 : ℝ)
  · exact real_three_w1411 p (le_of_lt (lt_of_not_ge h26)) h27
  by_cases h28 : p ≤ (1093/256 : ℝ)
  · exact real_three_w1412 p (le_of_lt (lt_of_not_ge h27)) h28
  by_cases h29 : p ≤ (4373/1024 : ℝ)
  · exact real_three_w1413 p (le_of_lt (lt_of_not_ge h28)) h29
  by_cases h30 : p ≤ (2187/512 : ℝ)
  · exact real_three_w1414 p (le_of_lt (lt_of_not_ge h29)) h30
  exact real_three_w1415 p (le_of_lt (lt_of_not_ge h30)) hpb

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  exact HlawkaSchatten.DiagonalCutoff4.real_cover_g012 p hpa hpb

#print axioms solution
