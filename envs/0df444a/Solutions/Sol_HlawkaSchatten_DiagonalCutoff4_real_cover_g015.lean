-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.real_cover_g015
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:04:35.832177+00:00
-- url     : https://prove2.me/submissions/2978d862-9a55-4ead-a1e8-e78aaa037704

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1480
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1481
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1482
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1483
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1484
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1485
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1486
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1487
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1488
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1489
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1490
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1491
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1492
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1493
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1494
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1495
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1496
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1497
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1498
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1499
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1500
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1501
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1502
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1503
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1504
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1505
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1506
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1507
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1508
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1509
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1510
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1511
set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalCutoff4
theorem real_cover_g015 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  by_cases h0 : p ≤ (4457/1024 : ℝ)
  · exact real_three_w1480 p hpa h0
  by_cases h1 : p ≤ (4459/1024 : ℝ)
  · exact real_three_w1481 p (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p ≤ (4461/1024 : ℝ)
  · exact real_three_w1482 p (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p ≤ (4463/1024 : ℝ)
  · exact real_three_w1483 p (le_of_lt (lt_of_not_ge h2)) h3
  by_cases h4 : p ≤ (4465/1024 : ℝ)
  · exact real_three_w1484 p (le_of_lt (lt_of_not_ge h3)) h4
  by_cases h5 : p ≤ (4467/1024 : ℝ)
  · exact real_three_w1485 p (le_of_lt (lt_of_not_ge h4)) h5
  by_cases h6 : p ≤ (4469/1024 : ℝ)
  · exact real_three_w1486 p (le_of_lt (lt_of_not_ge h5)) h6
  by_cases h7 : p ≤ (4471/1024 : ℝ)
  · exact real_three_w1487 p (le_of_lt (lt_of_not_ge h6)) h7
  by_cases h8 : p ≤ (4473/1024 : ℝ)
  · exact real_three_w1488 p (le_of_lt (lt_of_not_ge h7)) h8
  by_cases h9 : p ≤ (4475/1024 : ℝ)
  · exact real_three_w1489 p (le_of_lt (lt_of_not_ge h8)) h9
  by_cases h10 : p ≤ (4477/1024 : ℝ)
  · exact real_three_w1490 p (le_of_lt (lt_of_not_ge h9)) h10
  by_cases h11 : p ≤ (4479/1024 : ℝ)
  · exact real_three_w1491 p (le_of_lt (lt_of_not_ge h10)) h11
  by_cases h12 : p ≤ (4481/1024 : ℝ)
  · exact real_three_w1492 p (le_of_lt (lt_of_not_ge h11)) h12
  by_cases h13 : p ≤ (4483/1024 : ℝ)
  · exact real_three_w1493 p (le_of_lt (lt_of_not_ge h12)) h13
  by_cases h14 : p ≤ (4485/1024 : ℝ)
  · exact real_three_w1494 p (le_of_lt (lt_of_not_ge h13)) h14
  by_cases h15 : p ≤ (4487/1024 : ℝ)
  · exact real_three_w1495 p (le_of_lt (lt_of_not_ge h14)) h15
  by_cases h16 : p ≤ (4489/1024 : ℝ)
  · exact real_three_w1496 p (le_of_lt (lt_of_not_ge h15)) h16
  by_cases h17 : p ≤ (4491/1024 : ℝ)
  · exact real_three_w1497 p (le_of_lt (lt_of_not_ge h16)) h17
  by_cases h18 : p ≤ (4493/1024 : ℝ)
  · exact real_three_w1498 p (le_of_lt (lt_of_not_ge h17)) h18
  by_cases h19 : p ≤ (4495/1024 : ℝ)
  · exact real_three_w1499 p (le_of_lt (lt_of_not_ge h18)) h19
  by_cases h20 : p ≤ (4497/1024 : ℝ)
  · exact real_three_w1500 p (le_of_lt (lt_of_not_ge h19)) h20
  by_cases h21 : p ≤ (4499/1024 : ℝ)
  · exact real_three_w1501 p (le_of_lt (lt_of_not_ge h20)) h21
  by_cases h22 : p ≤ (4501/1024 : ℝ)
  · exact real_three_w1502 p (le_of_lt (lt_of_not_ge h21)) h22
  by_cases h23 : p ≤ (4503/1024 : ℝ)
  · exact real_three_w1503 p (le_of_lt (lt_of_not_ge h22)) h23
  by_cases h24 : p ≤ (4505/1024 : ℝ)
  · exact real_three_w1504 p (le_of_lt (lt_of_not_ge h23)) h24
  by_cases h25 : p ≤ (4507/1024 : ℝ)
  · exact real_three_w1505 p (le_of_lt (lt_of_not_ge h24)) h25
  by_cases h26 : p ≤ (4509/1024 : ℝ)
  · exact real_three_w1506 p (le_of_lt (lt_of_not_ge h25)) h26
  by_cases h27 : p ≤ (4511/1024 : ℝ)
  · exact real_three_w1507 p (le_of_lt (lt_of_not_ge h26)) h27
  by_cases h28 : p ≤ (4513/1024 : ℝ)
  · exact real_three_w1508 p (le_of_lt (lt_of_not_ge h27)) h28
  by_cases h29 : p ≤ (4515/1024 : ℝ)
  · exact real_three_w1509 p (le_of_lt (lt_of_not_ge h28)) h29
  by_cases h30 : p ≤ (4517/1024 : ℝ)
  · exact real_three_w1510 p (le_of_lt (lt_of_not_ge h29)) h30
  exact real_three_w1511 p (le_of_lt (lt_of_not_ge h30)) hpb

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  exact HlawkaSchatten.DiagonalCutoff4.real_cover_g015 p hpa hpb

#print axioms solution
