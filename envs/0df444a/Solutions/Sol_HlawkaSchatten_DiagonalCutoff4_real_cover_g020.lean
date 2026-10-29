-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.real_cover_g020
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:32:07.984443+00:00
-- url     : https://prove2.me/submissions/9eed9d74-4983-4c54-870b-564edb6f9881

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1640
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1641
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1642
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1643
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1644
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1645
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1646
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1647
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1648
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1649
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1650
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1651
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1652
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1653
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1654
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1655
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1656
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1657
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1658
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1659
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1660
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1661
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1662
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1663
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1664
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1665
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1666
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1667
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1668
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1669
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1670
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1671
set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalCutoff4
theorem real_cover_g020 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  by_cases h0 : p ≤ (4879/1024 : ℝ)
  · exact real_three_w1640 p hpa h0
  by_cases h1 : p ≤ (4883/1024 : ℝ)
  · exact real_three_w1641 p (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p ≤ (4887/1024 : ℝ)
  · exact real_three_w1642 p (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p ≤ (4891/1024 : ℝ)
  · exact real_three_w1643 p (le_of_lt (lt_of_not_ge h2)) h3
  by_cases h4 : p ≤ (4895/1024 : ℝ)
  · exact real_three_w1644 p (le_of_lt (lt_of_not_ge h3)) h4
  by_cases h5 : p ≤ (4899/1024 : ℝ)
  · exact real_three_w1645 p (le_of_lt (lt_of_not_ge h4)) h5
  by_cases h6 : p ≤ (4903/1024 : ℝ)
  · exact real_three_w1646 p (le_of_lt (lt_of_not_ge h5)) h6
  by_cases h7 : p ≤ (4907/1024 : ℝ)
  · exact real_three_w1647 p (le_of_lt (lt_of_not_ge h6)) h7
  by_cases h8 : p ≤ (4911/1024 : ℝ)
  · exact real_three_w1648 p (le_of_lt (lt_of_not_ge h7)) h8
  by_cases h9 : p ≤ (4915/1024 : ℝ)
  · exact real_three_w1649 p (le_of_lt (lt_of_not_ge h8)) h9
  by_cases h10 : p ≤ (4919/1024 : ℝ)
  · exact real_three_w1650 p (le_of_lt (lt_of_not_ge h9)) h10
  by_cases h11 : p ≤ (4923/1024 : ℝ)
  · exact real_three_w1651 p (le_of_lt (lt_of_not_ge h10)) h11
  by_cases h12 : p ≤ (4927/1024 : ℝ)
  · exact real_three_w1652 p (le_of_lt (lt_of_not_ge h11)) h12
  by_cases h13 : p ≤ (4931/1024 : ℝ)
  · exact real_three_w1653 p (le_of_lt (lt_of_not_ge h12)) h13
  by_cases h14 : p ≤ (4935/1024 : ℝ)
  · exact real_three_w1654 p (le_of_lt (lt_of_not_ge h13)) h14
  by_cases h15 : p ≤ (4939/1024 : ℝ)
  · exact real_three_w1655 p (le_of_lt (lt_of_not_ge h14)) h15
  by_cases h16 : p ≤ (4943/1024 : ℝ)
  · exact real_three_w1656 p (le_of_lt (lt_of_not_ge h15)) h16
  by_cases h17 : p ≤ (4947/1024 : ℝ)
  · exact real_three_w1657 p (le_of_lt (lt_of_not_ge h16)) h17
  by_cases h18 : p ≤ (4951/1024 : ℝ)
  · exact real_three_w1658 p (le_of_lt (lt_of_not_ge h17)) h18
  by_cases h19 : p ≤ (4955/1024 : ℝ)
  · exact real_three_w1659 p (le_of_lt (lt_of_not_ge h18)) h19
  by_cases h20 : p ≤ (4959/1024 : ℝ)
  · exact real_three_w1660 p (le_of_lt (lt_of_not_ge h19)) h20
  by_cases h21 : p ≤ (4963/1024 : ℝ)
  · exact real_three_w1661 p (le_of_lt (lt_of_not_ge h20)) h21
  by_cases h22 : p ≤ (4967/1024 : ℝ)
  · exact real_three_w1662 p (le_of_lt (lt_of_not_ge h21)) h22
  by_cases h23 : p ≤ (4971/1024 : ℝ)
  · exact real_three_w1663 p (le_of_lt (lt_of_not_ge h22)) h23
  by_cases h24 : p ≤ (4975/1024 : ℝ)
  · exact real_three_w1664 p (le_of_lt (lt_of_not_ge h23)) h24
  by_cases h25 : p ≤ (4979/1024 : ℝ)
  · exact real_three_w1665 p (le_of_lt (lt_of_not_ge h24)) h25
  by_cases h26 : p ≤ (4983/1024 : ℝ)
  · exact real_three_w1666 p (le_of_lt (lt_of_not_ge h25)) h26
  by_cases h27 : p ≤ (4987/1024 : ℝ)
  · exact real_three_w1667 p (le_of_lt (lt_of_not_ge h26)) h27
  by_cases h28 : p ≤ (4991/1024 : ℝ)
  · exact real_three_w1668 p (le_of_lt (lt_of_not_ge h27)) h28
  by_cases h29 : p ≤ (4995/1024 : ℝ)
  · exact real_three_w1669 p (le_of_lt (lt_of_not_ge h28)) h29
  by_cases h30 : p ≤ (4999/1024 : ℝ)
  · exact real_three_w1670 p (le_of_lt (lt_of_not_ge h29)) h30
  exact real_three_w1671 p (le_of_lt (lt_of_not_ge h30)) hpb

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (5003/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  exact HlawkaSchatten.DiagonalCutoff4.real_cover_g020 p hpa hpb

#print axioms solution
