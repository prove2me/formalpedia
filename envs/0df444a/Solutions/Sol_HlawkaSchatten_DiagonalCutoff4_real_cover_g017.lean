-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.real_cover_g017
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:49:00.790984+00:00
-- url     : https://prove2.me/submissions/351a7d74-6c0d-4738-bfe9-2446b97c0042

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1544
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1545
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1546
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1547
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1548
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1549
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1550
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1551
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1552
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1553
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1554
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1555
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1556
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1557
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1558
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1559
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1560
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1561
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1562
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1563
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1564
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1565
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1566
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1567
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1568
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1569
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1570
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1571
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1572
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1573
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1574
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1575
set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalCutoff4
theorem real_cover_g017 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  by_cases h0 : p ≤ (4585/1024 : ℝ)
  · exact real_three_w1544 p hpa h0
  by_cases h1 : p ≤ (4587/1024 : ℝ)
  · exact real_three_w1545 p (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p ≤ (4589/1024 : ℝ)
  · exact real_three_w1546 p (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p ≤ (4591/1024 : ℝ)
  · exact real_three_w1547 p (le_of_lt (lt_of_not_ge h2)) h3
  by_cases h4 : p ≤ (4593/1024 : ℝ)
  · exact real_three_w1548 p (le_of_lt (lt_of_not_ge h3)) h4
  by_cases h5 : p ≤ (4595/1024 : ℝ)
  · exact real_three_w1549 p (le_of_lt (lt_of_not_ge h4)) h5
  by_cases h6 : p ≤ (4597/1024 : ℝ)
  · exact real_three_w1550 p (le_of_lt (lt_of_not_ge h5)) h6
  by_cases h7 : p ≤ (4599/1024 : ℝ)
  · exact real_three_w1551 p (le_of_lt (lt_of_not_ge h6)) h7
  by_cases h8 : p ≤ (4601/1024 : ℝ)
  · exact real_three_w1552 p (le_of_lt (lt_of_not_ge h7)) h8
  by_cases h9 : p ≤ (4603/1024 : ℝ)
  · exact real_three_w1553 p (le_of_lt (lt_of_not_ge h8)) h9
  by_cases h10 : p ≤ (4605/1024 : ℝ)
  · exact real_three_w1554 p (le_of_lt (lt_of_not_ge h9)) h10
  by_cases h11 : p ≤ (4607/1024 : ℝ)
  · exact real_three_w1555 p (le_of_lt (lt_of_not_ge h10)) h11
  by_cases h12 : p ≤ (4609/1024 : ℝ)
  · exact real_three_w1556 p (le_of_lt (lt_of_not_ge h11)) h12
  by_cases h13 : p ≤ (4611/1024 : ℝ)
  · exact real_three_w1557 p (le_of_lt (lt_of_not_ge h12)) h13
  by_cases h14 : p ≤ (4613/1024 : ℝ)
  · exact real_three_w1558 p (le_of_lt (lt_of_not_ge h13)) h14
  by_cases h15 : p ≤ (4615/1024 : ℝ)
  · exact real_three_w1559 p (le_of_lt (lt_of_not_ge h14)) h15
  by_cases h16 : p ≤ (4617/1024 : ℝ)
  · exact real_three_w1560 p (le_of_lt (lt_of_not_ge h15)) h16
  by_cases h17 : p ≤ (4619/1024 : ℝ)
  · exact real_three_w1561 p (le_of_lt (lt_of_not_ge h16)) h17
  by_cases h18 : p ≤ (4621/1024 : ℝ)
  · exact real_three_w1562 p (le_of_lt (lt_of_not_ge h17)) h18
  by_cases h19 : p ≤ (4623/1024 : ℝ)
  · exact real_three_w1563 p (le_of_lt (lt_of_not_ge h18)) h19
  by_cases h20 : p ≤ (4625/1024 : ℝ)
  · exact real_three_w1564 p (le_of_lt (lt_of_not_ge h19)) h20
  by_cases h21 : p ≤ (4627/1024 : ℝ)
  · exact real_three_w1565 p (le_of_lt (lt_of_not_ge h20)) h21
  by_cases h22 : p ≤ (4629/1024 : ℝ)
  · exact real_three_w1566 p (le_of_lt (lt_of_not_ge h21)) h22
  by_cases h23 : p ≤ (4631/1024 : ℝ)
  · exact real_three_w1567 p (le_of_lt (lt_of_not_ge h22)) h23
  by_cases h24 : p ≤ (4633/1024 : ℝ)
  · exact real_three_w1568 p (le_of_lt (lt_of_not_ge h23)) h24
  by_cases h25 : p ≤ (4635/1024 : ℝ)
  · exact real_three_w1569 p (le_of_lt (lt_of_not_ge h24)) h25
  by_cases h26 : p ≤ (4637/1024 : ℝ)
  · exact real_three_w1570 p (le_of_lt (lt_of_not_ge h25)) h26
  by_cases h27 : p ≤ (4639/1024 : ℝ)
  · exact real_three_w1571 p (le_of_lt (lt_of_not_ge h26)) h27
  by_cases h28 : p ≤ (4641/1024 : ℝ)
  · exact real_three_w1572 p (le_of_lt (lt_of_not_ge h27)) h28
  by_cases h29 : p ≤ (4643/1024 : ℝ)
  · exact real_three_w1573 p (le_of_lt (lt_of_not_ge h28)) h29
  by_cases h30 : p ≤ (4645/1024 : ℝ)
  · exact real_three_w1574 p (le_of_lt (lt_of_not_ge h29)) h30
  exact real_three_w1575 p (le_of_lt (lt_of_not_ge h30)) hpb

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  exact HlawkaSchatten.DiagonalCutoff4.real_cover_g017 p hpa hpb

#print axioms solution
