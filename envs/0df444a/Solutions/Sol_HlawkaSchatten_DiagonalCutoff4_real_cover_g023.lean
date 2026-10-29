-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.real_cover_g023
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:05:20.59099+00:00
-- url     : https://prove2.me/submissions/173430d1-e0f8-46ed-bc33-ee986bcda935

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1736
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1737
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1738
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1739
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1740
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1741
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1742
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1743
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1744
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1745
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1746
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1747
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1748
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1749
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1750
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1751
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1752
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1753
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1754
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1755
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1756
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1757
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1758
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1759
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1760
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1761
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1762
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1763
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1764
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1765
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1766
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1767
set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalCutoff4
theorem real_cover_g023 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  by_cases h0 : p ≤ (5551/1024 : ℝ)
  · exact real_three_w1736 p hpa h0
  by_cases h1 : p ≤ (5567/1024 : ℝ)
  · exact real_three_w1737 p (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p ≤ (5583/1024 : ℝ)
  · exact real_three_w1738 p (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p ≤ (5599/1024 : ℝ)
  · exact real_three_w1739 p (le_of_lt (lt_of_not_ge h2)) h3
  by_cases h4 : p ≤ (5615/1024 : ℝ)
  · exact real_three_w1740 p (le_of_lt (lt_of_not_ge h3)) h4
  by_cases h5 : p ≤ (5631/1024 : ℝ)
  · exact real_three_w1741 p (le_of_lt (lt_of_not_ge h4)) h5
  by_cases h6 : p ≤ (5647/1024 : ℝ)
  · exact real_three_w1742 p (le_of_lt (lt_of_not_ge h5)) h6
  by_cases h7 : p ≤ (5663/1024 : ℝ)
  · exact real_three_w1743 p (le_of_lt (lt_of_not_ge h6)) h7
  by_cases h8 : p ≤ (5679/1024 : ℝ)
  · exact real_three_w1744 p (le_of_lt (lt_of_not_ge h7)) h8
  by_cases h9 : p ≤ (5695/1024 : ℝ)
  · exact real_three_w1745 p (le_of_lt (lt_of_not_ge h8)) h9
  by_cases h10 : p ≤ (5711/1024 : ℝ)
  · exact real_three_w1746 p (le_of_lt (lt_of_not_ge h9)) h10
  by_cases h11 : p ≤ (5727/1024 : ℝ)
  · exact real_three_w1747 p (le_of_lt (lt_of_not_ge h10)) h11
  by_cases h12 : p ≤ (5743/1024 : ℝ)
  · exact real_three_w1748 p (le_of_lt (lt_of_not_ge h11)) h12
  by_cases h13 : p ≤ (5759/1024 : ℝ)
  · exact real_three_w1749 p (le_of_lt (lt_of_not_ge h12)) h13
  by_cases h14 : p ≤ (5775/1024 : ℝ)
  · exact real_three_w1750 p (le_of_lt (lt_of_not_ge h13)) h14
  by_cases h15 : p ≤ (5791/1024 : ℝ)
  · exact real_three_w1751 p (le_of_lt (lt_of_not_ge h14)) h15
  by_cases h16 : p ≤ (5807/1024 : ℝ)
  · exact real_three_w1752 p (le_of_lt (lt_of_not_ge h15)) h16
  by_cases h17 : p ≤ (5823/1024 : ℝ)
  · exact real_three_w1753 p (le_of_lt (lt_of_not_ge h16)) h17
  by_cases h18 : p ≤ (5839/1024 : ℝ)
  · exact real_three_w1754 p (le_of_lt (lt_of_not_ge h17)) h18
  by_cases h19 : p ≤ (5855/1024 : ℝ)
  · exact real_three_w1755 p (le_of_lt (lt_of_not_ge h18)) h19
  by_cases h20 : p ≤ (5871/1024 : ℝ)
  · exact real_three_w1756 p (le_of_lt (lt_of_not_ge h19)) h20
  by_cases h21 : p ≤ (5887/1024 : ℝ)
  · exact real_three_w1757 p (le_of_lt (lt_of_not_ge h20)) h21
  by_cases h22 : p ≤ (5903/1024 : ℝ)
  · exact real_three_w1758 p (le_of_lt (lt_of_not_ge h21)) h22
  by_cases h23 : p ≤ (5919/1024 : ℝ)
  · exact real_three_w1759 p (le_of_lt (lt_of_not_ge h22)) h23
  by_cases h24 : p ≤ (5935/1024 : ℝ)
  · exact real_three_w1760 p (le_of_lt (lt_of_not_ge h23)) h24
  by_cases h25 : p ≤ (5951/1024 : ℝ)
  · exact real_three_w1761 p (le_of_lt (lt_of_not_ge h24)) h25
  by_cases h26 : p ≤ (5967/1024 : ℝ)
  · exact real_three_w1762 p (le_of_lt (lt_of_not_ge h25)) h26
  by_cases h27 : p ≤ (5983/1024 : ℝ)
  · exact real_three_w1763 p (le_of_lt (lt_of_not_ge h26)) h27
  by_cases h28 : p ≤ (5999/1024 : ℝ)
  · exact real_three_w1764 p (le_of_lt (lt_of_not_ge h27)) h28
  by_cases h29 : p ≤ (6015/1024 : ℝ)
  · exact real_three_w1765 p (le_of_lt (lt_of_not_ge h28)) h29
  by_cases h30 : p ≤ (6031/1024 : ℝ)
  · exact real_three_w1766 p (le_of_lt (lt_of_not_ge h29)) h30
  exact real_three_w1767 p (le_of_lt (lt_of_not_ge h30)) hpb

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  exact HlawkaSchatten.DiagonalCutoff4.real_cover_g023 p hpa hpb

#print axioms solution
