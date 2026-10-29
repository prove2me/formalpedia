-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.real_cover_g021
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:41:48.443911+00:00
-- url     : https://prove2.me/submissions/9cb0c19e-0f9e-489d-8625-8a46b14448d3

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1672
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1673
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1674
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1675
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1676
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1677
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1678
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1679
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1680
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1681
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1682
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1683
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1684
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1685
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1686
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1687
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1688
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1689
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1690
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1691
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1692
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1693
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1694
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1695
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1696
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1697
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1698
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1699
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1700
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1701
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1702
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1703
set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalCutoff4
theorem real_cover_g021 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5247/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  by_cases h0 : p ≤ (5007/1024 : ℝ)
  · exact real_three_w1672 p hpa h0
  by_cases h1 : p ≤ (5011/1024 : ℝ)
  · exact real_three_w1673 p (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p ≤ (5015/1024 : ℝ)
  · exact real_three_w1674 p (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p ≤ (5023/1024 : ℝ)
  · exact real_three_w1675 p (le_of_lt (lt_of_not_ge h2)) h3
  by_cases h4 : p ≤ (5031/1024 : ℝ)
  · exact real_three_w1676 p (le_of_lt (lt_of_not_ge h3)) h4
  by_cases h5 : p ≤ (5039/1024 : ℝ)
  · exact real_three_w1677 p (le_of_lt (lt_of_not_ge h4)) h5
  by_cases h6 : p ≤ (5047/1024 : ℝ)
  · exact real_three_w1678 p (le_of_lt (lt_of_not_ge h5)) h6
  by_cases h7 : p ≤ (5055/1024 : ℝ)
  · exact real_three_w1679 p (le_of_lt (lt_of_not_ge h6)) h7
  by_cases h8 : p ≤ (5063/1024 : ℝ)
  · exact real_three_w1680 p (le_of_lt (lt_of_not_ge h7)) h8
  by_cases h9 : p ≤ (5071/1024 : ℝ)
  · exact real_three_w1681 p (le_of_lt (lt_of_not_ge h8)) h9
  by_cases h10 : p ≤ (5079/1024 : ℝ)
  · exact real_three_w1682 p (le_of_lt (lt_of_not_ge h9)) h10
  by_cases h11 : p ≤ (5087/1024 : ℝ)
  · exact real_three_w1683 p (le_of_lt (lt_of_not_ge h10)) h11
  by_cases h12 : p ≤ (5095/1024 : ℝ)
  · exact real_three_w1684 p (le_of_lt (lt_of_not_ge h11)) h12
  by_cases h13 : p ≤ (5103/1024 : ℝ)
  · exact real_three_w1685 p (le_of_lt (lt_of_not_ge h12)) h13
  by_cases h14 : p ≤ (5111/1024 : ℝ)
  · exact real_three_w1686 p (le_of_lt (lt_of_not_ge h13)) h14
  by_cases h15 : p ≤ (5119/1024 : ℝ)
  · exact real_three_w1687 p (le_of_lt (lt_of_not_ge h14)) h15
  by_cases h16 : p ≤ (5127/1024 : ℝ)
  · exact real_three_w1688 p (le_of_lt (lt_of_not_ge h15)) h16
  by_cases h17 : p ≤ (5135/1024 : ℝ)
  · exact real_three_w1689 p (le_of_lt (lt_of_not_ge h16)) h17
  by_cases h18 : p ≤ (5143/1024 : ℝ)
  · exact real_three_w1690 p (le_of_lt (lt_of_not_ge h17)) h18
  by_cases h19 : p ≤ (5151/1024 : ℝ)
  · exact real_three_w1691 p (le_of_lt (lt_of_not_ge h18)) h19
  by_cases h20 : p ≤ (5159/1024 : ℝ)
  · exact real_three_w1692 p (le_of_lt (lt_of_not_ge h19)) h20
  by_cases h21 : p ≤ (5167/1024 : ℝ)
  · exact real_three_w1693 p (le_of_lt (lt_of_not_ge h20)) h21
  by_cases h22 : p ≤ (5175/1024 : ℝ)
  · exact real_three_w1694 p (le_of_lt (lt_of_not_ge h21)) h22
  by_cases h23 : p ≤ (5183/1024 : ℝ)
  · exact real_three_w1695 p (le_of_lt (lt_of_not_ge h22)) h23
  by_cases h24 : p ≤ (5191/1024 : ℝ)
  · exact real_three_w1696 p (le_of_lt (lt_of_not_ge h23)) h24
  by_cases h25 : p ≤ (5199/1024 : ℝ)
  · exact real_three_w1697 p (le_of_lt (lt_of_not_ge h24)) h25
  by_cases h26 : p ≤ (5207/1024 : ℝ)
  · exact real_three_w1698 p (le_of_lt (lt_of_not_ge h25)) h26
  by_cases h27 : p ≤ (5215/1024 : ℝ)
  · exact real_three_w1699 p (le_of_lt (lt_of_not_ge h26)) h27
  by_cases h28 : p ≤ (5223/1024 : ℝ)
  · exact real_three_w1700 p (le_of_lt (lt_of_not_ge h27)) h28
  by_cases h29 : p ≤ (5231/1024 : ℝ)
  · exact real_three_w1701 p (le_of_lt (lt_of_not_ge h28)) h29
  by_cases h30 : p ≤ (5239/1024 : ℝ)
  · exact real_three_w1702 p (le_of_lt (lt_of_not_ge h29)) h30
  exact real_three_w1703 p (le_of_lt (lt_of_not_ge h30)) hpb

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5247/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  exact HlawkaSchatten.DiagonalCutoff4.real_cover_g021 p hpa hpb

#print axioms solution
