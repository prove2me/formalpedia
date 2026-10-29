-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.real_cover_g018
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:04:01.238121+00:00
-- url     : https://prove2.me/submissions/afd7bbbc-83f5-4c6f-adb0-1b02013ffa57
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1576
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1577
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1578
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1579
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1580
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1581
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1582
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1583
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1584
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1585
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1586
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1587
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1588
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1589
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1590
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1591
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1592
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1593
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1594
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1595
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1596
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1597
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1598
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1599
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1600
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1601
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1602
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1603
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1604
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1605
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1606
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1607
set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalCutoff4
theorem real_cover_g018 (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  by_cases h0 : p ≤ (4649/1024 : ℝ)
  · exact real_three_w1576 p hpa h0
  by_cases h1 : p ≤ (4651/1024 : ℝ)
  · exact real_three_w1577 p (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p ≤ (4653/1024 : ℝ)
  · exact real_three_w1578 p (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p ≤ (4655/1024 : ℝ)
  · exact real_three_w1579 p (le_of_lt (lt_of_not_ge h2)) h3
  by_cases h4 : p ≤ (4657/1024 : ℝ)
  · exact real_three_w1580 p (le_of_lt (lt_of_not_ge h3)) h4
  by_cases h5 : p ≤ (4659/1024 : ℝ)
  · exact real_three_w1581 p (le_of_lt (lt_of_not_ge h4)) h5
  by_cases h6 : p ≤ (4661/1024 : ℝ)
  · exact real_three_w1582 p (le_of_lt (lt_of_not_ge h5)) h6
  by_cases h7 : p ≤ (4663/1024 : ℝ)
  · exact real_three_w1583 p (le_of_lt (lt_of_not_ge h6)) h7
  by_cases h8 : p ≤ (4665/1024 : ℝ)
  · exact real_three_w1584 p (le_of_lt (lt_of_not_ge h7)) h8
  by_cases h9 : p ≤ (4667/1024 : ℝ)
  · exact real_three_w1585 p (le_of_lt (lt_of_not_ge h8)) h9
  by_cases h10 : p ≤ (4669/1024 : ℝ)
  · exact real_three_w1586 p (le_of_lt (lt_of_not_ge h9)) h10
  by_cases h11 : p ≤ (4671/1024 : ℝ)
  · exact real_three_w1587 p (le_of_lt (lt_of_not_ge h10)) h11
  by_cases h12 : p ≤ (4673/1024 : ℝ)
  · exact real_three_w1588 p (le_of_lt (lt_of_not_ge h11)) h12
  by_cases h13 : p ≤ (4675/1024 : ℝ)
  · exact real_three_w1589 p (le_of_lt (lt_of_not_ge h12)) h13
  by_cases h14 : p ≤ (4679/1024 : ℝ)
  · exact real_three_w1590 p (le_of_lt (lt_of_not_ge h13)) h14
  by_cases h15 : p ≤ (4683/1024 : ℝ)
  · exact real_three_w1591 p (le_of_lt (lt_of_not_ge h14)) h15
  by_cases h16 : p ≤ (4687/1024 : ℝ)
  · exact real_three_w1592 p (le_of_lt (lt_of_not_ge h15)) h16
  by_cases h17 : p ≤ (4691/1024 : ℝ)
  · exact real_three_w1593 p (le_of_lt (lt_of_not_ge h16)) h17
  by_cases h18 : p ≤ (4695/1024 : ℝ)
  · exact real_three_w1594 p (le_of_lt (lt_of_not_ge h17)) h18
  by_cases h19 : p ≤ (4699/1024 : ℝ)
  · exact real_three_w1595 p (le_of_lt (lt_of_not_ge h18)) h19
  by_cases h20 : p ≤ (4703/1024 : ℝ)
  · exact real_three_w1596 p (le_of_lt (lt_of_not_ge h19)) h20
  by_cases h21 : p ≤ (4707/1024 : ℝ)
  · exact real_three_w1597 p (le_of_lt (lt_of_not_ge h20)) h21
  by_cases h22 : p ≤ (4711/1024 : ℝ)
  · exact real_three_w1598 p (le_of_lt (lt_of_not_ge h21)) h22
  by_cases h23 : p ≤ (4715/1024 : ℝ)
  · exact real_three_w1599 p (le_of_lt (lt_of_not_ge h22)) h23
  by_cases h24 : p ≤ (4719/1024 : ℝ)
  · exact real_three_w1600 p (le_of_lt (lt_of_not_ge h23)) h24
  by_cases h25 : p ≤ (4723/1024 : ℝ)
  · exact real_three_w1601 p (le_of_lt (lt_of_not_ge h24)) h25
  by_cases h26 : p ≤ (4727/1024 : ℝ)
  · exact real_three_w1602 p (le_of_lt (lt_of_not_ge h25)) h26
  by_cases h27 : p ≤ (4731/1024 : ℝ)
  · exact real_three_w1603 p (le_of_lt (lt_of_not_ge h26)) h27
  by_cases h28 : p ≤ (4735/1024 : ℝ)
  · exact real_three_w1604 p (le_of_lt (lt_of_not_ge h27)) h28
  by_cases h29 : p ≤ (4739/1024 : ℝ)
  · exact real_three_w1605 p (le_of_lt (lt_of_not_ge h28)) h29
  by_cases h30 : p ≤ (4743/1024 : ℝ)
  · exact real_three_w1606 p (le_of_lt (lt_of_not_ge h29)) h30
  exact real_three_w1607 p (le_of_lt (lt_of_not_ge h30)) hpb

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (4647/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  exact HlawkaSchatten.DiagonalCutoff4.real_cover_g018 p hpa hpb

#print axioms solution
