-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.real_cover_g022
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:53:46.047562+00:00
-- url     : https://prove2.me/submissions/1ba12e14-1531-4ba2-b887-fbb34d39d30e

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1704
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1705
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1706
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1707
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1708
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1709
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1710
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1711
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1712
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1713
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1714
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1715
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1716
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1717
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1718
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1719
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1720
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1721
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1722
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1723
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1724
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1725
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1726
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1727
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1728
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1729
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1730
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1731
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1732
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1733
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1734
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1735
set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalCutoff4
theorem real_cover_g022 (p : ℝ) (hpa : (5247/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  by_cases h0 : p ≤ (5255/1024 : ℝ)
  · exact real_three_w1704 p hpa h0
  by_cases h1 : p ≤ (5263/1024 : ℝ)
  · exact real_three_w1705 p (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p ≤ (5271/1024 : ℝ)
  · exact real_three_w1706 p (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p ≤ (5279/1024 : ℝ)
  · exact real_three_w1707 p (le_of_lt (lt_of_not_ge h2)) h3
  by_cases h4 : p ≤ (5287/1024 : ℝ)
  · exact real_three_w1708 p (le_of_lt (lt_of_not_ge h3)) h4
  by_cases h5 : p ≤ (5295/1024 : ℝ)
  · exact real_three_w1709 p (le_of_lt (lt_of_not_ge h4)) h5
  by_cases h6 : p ≤ (5303/1024 : ℝ)
  · exact real_three_w1710 p (le_of_lt (lt_of_not_ge h5)) h6
  by_cases h7 : p ≤ (5311/1024 : ℝ)
  · exact real_three_w1711 p (le_of_lt (lt_of_not_ge h6)) h7
  by_cases h8 : p ≤ (5319/1024 : ℝ)
  · exact real_three_w1712 p (le_of_lt (lt_of_not_ge h7)) h8
  by_cases h9 : p ≤ (5327/1024 : ℝ)
  · exact real_three_w1713 p (le_of_lt (lt_of_not_ge h8)) h9
  by_cases h10 : p ≤ (5335/1024 : ℝ)
  · exact real_three_w1714 p (le_of_lt (lt_of_not_ge h9)) h10
  by_cases h11 : p ≤ (5343/1024 : ℝ)
  · exact real_three_w1715 p (le_of_lt (lt_of_not_ge h10)) h11
  by_cases h12 : p ≤ (5351/1024 : ℝ)
  · exact real_three_w1716 p (le_of_lt (lt_of_not_ge h11)) h12
  by_cases h13 : p ≤ (5359/1024 : ℝ)
  · exact real_three_w1717 p (le_of_lt (lt_of_not_ge h12)) h13
  by_cases h14 : p ≤ (5367/1024 : ℝ)
  · exact real_three_w1718 p (le_of_lt (lt_of_not_ge h13)) h14
  by_cases h15 : p ≤ (5375/1024 : ℝ)
  · exact real_three_w1719 p (le_of_lt (lt_of_not_ge h14)) h15
  by_cases h16 : p ≤ (5383/1024 : ℝ)
  · exact real_three_w1720 p (le_of_lt (lt_of_not_ge h15)) h16
  by_cases h17 : p ≤ (5391/1024 : ℝ)
  · exact real_three_w1721 p (le_of_lt (lt_of_not_ge h16)) h17
  by_cases h18 : p ≤ (5399/1024 : ℝ)
  · exact real_three_w1722 p (le_of_lt (lt_of_not_ge h17)) h18
  by_cases h19 : p ≤ (5407/1024 : ℝ)
  · exact real_three_w1723 p (le_of_lt (lt_of_not_ge h18)) h19
  by_cases h20 : p ≤ (5415/1024 : ℝ)
  · exact real_three_w1724 p (le_of_lt (lt_of_not_ge h19)) h20
  by_cases h21 : p ≤ (5423/1024 : ℝ)
  · exact real_three_w1725 p (le_of_lt (lt_of_not_ge h20)) h21
  by_cases h22 : p ≤ (5431/1024 : ℝ)
  · exact real_three_w1726 p (le_of_lt (lt_of_not_ge h21)) h22
  by_cases h23 : p ≤ (5439/1024 : ℝ)
  · exact real_three_w1727 p (le_of_lt (lt_of_not_ge h22)) h23
  by_cases h24 : p ≤ (5447/1024 : ℝ)
  · exact real_three_w1728 p (le_of_lt (lt_of_not_ge h23)) h24
  by_cases h25 : p ≤ (5455/1024 : ℝ)
  · exact real_three_w1729 p (le_of_lt (lt_of_not_ge h24)) h25
  by_cases h26 : p ≤ (5463/1024 : ℝ)
  · exact real_three_w1730 p (le_of_lt (lt_of_not_ge h25)) h26
  by_cases h27 : p ≤ (5471/1024 : ℝ)
  · exact real_three_w1731 p (le_of_lt (lt_of_not_ge h26)) h27
  by_cases h28 : p ≤ (5487/1024 : ℝ)
  · exact real_three_w1732 p (le_of_lt (lt_of_not_ge h27)) h28
  by_cases h29 : p ≤ (5503/1024 : ℝ)
  · exact real_three_w1733 p (le_of_lt (lt_of_not_ge h28)) h29
  by_cases h30 : p ≤ (5519/1024 : ℝ)
  · exact real_three_w1734 p (le_of_lt (lt_of_not_ge h29)) h30
  exact real_three_w1735 p (le_of_lt (lt_of_not_ge h30)) hpb

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (5247/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  exact HlawkaSchatten.DiagonalCutoff4.real_cover_g022 p hpa hpb

#print axioms solution
