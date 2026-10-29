-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.real_cover_g014
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:49:25.273109+00:00
-- url     : https://prove2.me/submissions/a90f2a04-41f3-40e2-8123-06f98cfb3484

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1448
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1449
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1450
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1451
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1452
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1453
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1454
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1455
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1456
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1457
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1458
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1459
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1460
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1461
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1462
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1463
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1464
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1465
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1466
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1467
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1468
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1469
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1470
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1471
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1472
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1473
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1474
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1475
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1476
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1477
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1478
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1479
set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalCutoff4
theorem real_cover_g014 (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  by_cases h0 : p ≤ (551/128 : ℝ)
  · exact real_three_w1448 p hpa h0
  by_cases h1 : p ≤ (4409/1024 : ℝ)
  · exact real_three_w1449 p (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p ≤ (2205/512 : ℝ)
  · exact real_three_w1450 p (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p ≤ (4411/1024 : ℝ)
  · exact real_three_w1451 p (le_of_lt (lt_of_not_ge h2)) h3
  by_cases h4 : p ≤ (1103/256 : ℝ)
  · exact real_three_w1452 p (le_of_lt (lt_of_not_ge h3)) h4
  by_cases h5 : p ≤ (4413/1024 : ℝ)
  · exact real_three_w1453 p (le_of_lt (lt_of_not_ge h4)) h5
  by_cases h6 : p ≤ (2207/512 : ℝ)
  · exact real_three_w1454 p (le_of_lt (lt_of_not_ge h5)) h6
  by_cases h7 : p ≤ (4415/1024 : ℝ)
  · exact real_three_w1455 p (le_of_lt (lt_of_not_ge h6)) h7
  by_cases h8 : p ≤ (69/16 : ℝ)
  · exact real_three_w1456 p (le_of_lt (lt_of_not_ge h7)) h8
  by_cases h9 : p ≤ (4417/1024 : ℝ)
  · exact real_three_w1457 p (le_of_lt (lt_of_not_ge h8)) h9
  by_cases h10 : p ≤ (2209/512 : ℝ)
  · exact real_three_w1458 p (le_of_lt (lt_of_not_ge h9)) h10
  by_cases h11 : p ≤ (4419/1024 : ℝ)
  · exact real_three_w1459 p (le_of_lt (lt_of_not_ge h10)) h11
  by_cases h12 : p ≤ (1105/256 : ℝ)
  · exact real_three_w1460 p (le_of_lt (lt_of_not_ge h11)) h12
  by_cases h13 : p ≤ (4421/1024 : ℝ)
  · exact real_three_w1461 p (le_of_lt (lt_of_not_ge h12)) h13
  by_cases h14 : p ≤ (2211/512 : ℝ)
  · exact real_three_w1462 p (le_of_lt (lt_of_not_ge h13)) h14
  by_cases h15 : p ≤ (4423/1024 : ℝ)
  · exact real_three_w1463 p (le_of_lt (lt_of_not_ge h14)) h15
  by_cases h16 : p ≤ (4425/1024 : ℝ)
  · exact real_three_w1464 p (le_of_lt (lt_of_not_ge h15)) h16
  by_cases h17 : p ≤ (4427/1024 : ℝ)
  · exact real_three_w1465 p (le_of_lt (lt_of_not_ge h16)) h17
  by_cases h18 : p ≤ (4429/1024 : ℝ)
  · exact real_three_w1466 p (le_of_lt (lt_of_not_ge h17)) h18
  by_cases h19 : p ≤ (4431/1024 : ℝ)
  · exact real_three_w1467 p (le_of_lt (lt_of_not_ge h18)) h19
  by_cases h20 : p ≤ (4433/1024 : ℝ)
  · exact real_three_w1468 p (le_of_lt (lt_of_not_ge h19)) h20
  by_cases h21 : p ≤ (4435/1024 : ℝ)
  · exact real_three_w1469 p (le_of_lt (lt_of_not_ge h20)) h21
  by_cases h22 : p ≤ (4437/1024 : ℝ)
  · exact real_three_w1470 p (le_of_lt (lt_of_not_ge h21)) h22
  by_cases h23 : p ≤ (4439/1024 : ℝ)
  · exact real_three_w1471 p (le_of_lt (lt_of_not_ge h22)) h23
  by_cases h24 : p ≤ (4441/1024 : ℝ)
  · exact real_three_w1472 p (le_of_lt (lt_of_not_ge h23)) h24
  by_cases h25 : p ≤ (4443/1024 : ℝ)
  · exact real_three_w1473 p (le_of_lt (lt_of_not_ge h24)) h25
  by_cases h26 : p ≤ (4445/1024 : ℝ)
  · exact real_three_w1474 p (le_of_lt (lt_of_not_ge h25)) h26
  by_cases h27 : p ≤ (4447/1024 : ℝ)
  · exact real_three_w1475 p (le_of_lt (lt_of_not_ge h26)) h27
  by_cases h28 : p ≤ (4449/1024 : ℝ)
  · exact real_three_w1476 p (le_of_lt (lt_of_not_ge h27)) h28
  by_cases h29 : p ≤ (4451/1024 : ℝ)
  · exact real_three_w1477 p (le_of_lt (lt_of_not_ge h28)) h29
  by_cases h30 : p ≤ (4453/1024 : ℝ)
  · exact real_three_w1478 p (le_of_lt (lt_of_not_ge h29)) h30
  exact real_three_w1479 p (le_of_lt (lt_of_not_ge h30)) hpb

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (4407/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  exact HlawkaSchatten.DiagonalCutoff4.real_cover_g014 p hpa hpb

#print axioms solution
