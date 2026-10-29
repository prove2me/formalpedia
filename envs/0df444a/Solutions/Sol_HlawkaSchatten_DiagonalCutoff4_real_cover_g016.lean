-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.real_cover_g016
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:13:16.978887+00:00
-- url     : https://prove2.me/submissions/16d79d31-44f7-4893-8888-01d0365b7416

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1512
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1513
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1514
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1515
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1516
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1517
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1518
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1519
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1520
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1521
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1522
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1523
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1524
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1525
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1526
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1527
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1528
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1529
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1530
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1531
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1532
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1533
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1534
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1535
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1536
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1537
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1538
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1539
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1540
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1541
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1542
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1543
set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalCutoff4
theorem real_cover_g016 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  by_cases h0 : p ≤ (4521/1024 : ℝ)
  · exact real_three_w1512 p hpa h0
  by_cases h1 : p ≤ (4523/1024 : ℝ)
  · exact real_three_w1513 p (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p ≤ (4525/1024 : ℝ)
  · exact real_three_w1514 p (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p ≤ (4527/1024 : ℝ)
  · exact real_three_w1515 p (le_of_lt (lt_of_not_ge h2)) h3
  by_cases h4 : p ≤ (4529/1024 : ℝ)
  · exact real_three_w1516 p (le_of_lt (lt_of_not_ge h3)) h4
  by_cases h5 : p ≤ (4531/1024 : ℝ)
  · exact real_three_w1517 p (le_of_lt (lt_of_not_ge h4)) h5
  by_cases h6 : p ≤ (4533/1024 : ℝ)
  · exact real_three_w1518 p (le_of_lt (lt_of_not_ge h5)) h6
  by_cases h7 : p ≤ (4535/1024 : ℝ)
  · exact real_three_w1519 p (le_of_lt (lt_of_not_ge h6)) h7
  by_cases h8 : p ≤ (4537/1024 : ℝ)
  · exact real_three_w1520 p (le_of_lt (lt_of_not_ge h7)) h8
  by_cases h9 : p ≤ (4539/1024 : ℝ)
  · exact real_three_w1521 p (le_of_lt (lt_of_not_ge h8)) h9
  by_cases h10 : p ≤ (4541/1024 : ℝ)
  · exact real_three_w1522 p (le_of_lt (lt_of_not_ge h9)) h10
  by_cases h11 : p ≤ (4543/1024 : ℝ)
  · exact real_three_w1523 p (le_of_lt (lt_of_not_ge h10)) h11
  by_cases h12 : p ≤ (4545/1024 : ℝ)
  · exact real_three_w1524 p (le_of_lt (lt_of_not_ge h11)) h12
  by_cases h13 : p ≤ (4547/1024 : ℝ)
  · exact real_three_w1525 p (le_of_lt (lt_of_not_ge h12)) h13
  by_cases h14 : p ≤ (4549/1024 : ℝ)
  · exact real_three_w1526 p (le_of_lt (lt_of_not_ge h13)) h14
  by_cases h15 : p ≤ (4551/1024 : ℝ)
  · exact real_three_w1527 p (le_of_lt (lt_of_not_ge h14)) h15
  by_cases h16 : p ≤ (4553/1024 : ℝ)
  · exact real_three_w1528 p (le_of_lt (lt_of_not_ge h15)) h16
  by_cases h17 : p ≤ (4555/1024 : ℝ)
  · exact real_three_w1529 p (le_of_lt (lt_of_not_ge h16)) h17
  by_cases h18 : p ≤ (4557/1024 : ℝ)
  · exact real_three_w1530 p (le_of_lt (lt_of_not_ge h17)) h18
  by_cases h19 : p ≤ (4559/1024 : ℝ)
  · exact real_three_w1531 p (le_of_lt (lt_of_not_ge h18)) h19
  by_cases h20 : p ≤ (4561/1024 : ℝ)
  · exact real_three_w1532 p (le_of_lt (lt_of_not_ge h19)) h20
  by_cases h21 : p ≤ (4563/1024 : ℝ)
  · exact real_three_w1533 p (le_of_lt (lt_of_not_ge h20)) h21
  by_cases h22 : p ≤ (4565/1024 : ℝ)
  · exact real_three_w1534 p (le_of_lt (lt_of_not_ge h21)) h22
  by_cases h23 : p ≤ (4567/1024 : ℝ)
  · exact real_three_w1535 p (le_of_lt (lt_of_not_ge h22)) h23
  by_cases h24 : p ≤ (4569/1024 : ℝ)
  · exact real_three_w1536 p (le_of_lt (lt_of_not_ge h23)) h24
  by_cases h25 : p ≤ (4571/1024 : ℝ)
  · exact real_three_w1537 p (le_of_lt (lt_of_not_ge h24)) h25
  by_cases h26 : p ≤ (4573/1024 : ℝ)
  · exact real_three_w1538 p (le_of_lt (lt_of_not_ge h25)) h26
  by_cases h27 : p ≤ (4575/1024 : ℝ)
  · exact real_three_w1539 p (le_of_lt (lt_of_not_ge h26)) h27
  by_cases h28 : p ≤ (4577/1024 : ℝ)
  · exact real_three_w1540 p (le_of_lt (lt_of_not_ge h27)) h28
  by_cases h29 : p ≤ (4579/1024 : ℝ)
  · exact real_three_w1541 p (le_of_lt (lt_of_not_ge h28)) h29
  by_cases h30 : p ≤ (4581/1024 : ℝ)
  · exact real_three_w1542 p (le_of_lt (lt_of_not_ge h29)) h30
  exact real_three_w1543 p (le_of_lt (lt_of_not_ge h30)) hpb

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  exact HlawkaSchatten.DiagonalCutoff4.real_cover_g016 p hpa hpb

#print axioms solution
