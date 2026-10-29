-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.real_cover_g019
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:19:18.189628+00:00
-- url     : https://prove2.me/submissions/dd7a6efa-fb2a-45ff-a0de-323d2a12260f

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1608
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1609
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1610
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1611
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1612
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1613
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1614
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1615
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1616
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1617
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1618
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1619
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1620
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1621
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1622
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1623
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1624
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1625
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1626
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1627
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1628
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1629
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1630
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1631
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1632
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1633
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1634
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1635
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1636
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1637
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1638
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1639
set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalCutoff4
theorem real_cover_g019 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  by_cases h0 : p ≤ (4751/1024 : ℝ)
  · exact real_three_w1608 p hpa h0
  by_cases h1 : p ≤ (4755/1024 : ℝ)
  · exact real_three_w1609 p (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p ≤ (4759/1024 : ℝ)
  · exact real_three_w1610 p (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p ≤ (4763/1024 : ℝ)
  · exact real_three_w1611 p (le_of_lt (lt_of_not_ge h2)) h3
  by_cases h4 : p ≤ (4767/1024 : ℝ)
  · exact real_three_w1612 p (le_of_lt (lt_of_not_ge h3)) h4
  by_cases h5 : p ≤ (4771/1024 : ℝ)
  · exact real_three_w1613 p (le_of_lt (lt_of_not_ge h4)) h5
  by_cases h6 : p ≤ (4775/1024 : ℝ)
  · exact real_three_w1614 p (le_of_lt (lt_of_not_ge h5)) h6
  by_cases h7 : p ≤ (4779/1024 : ℝ)
  · exact real_three_w1615 p (le_of_lt (lt_of_not_ge h6)) h7
  by_cases h8 : p ≤ (4783/1024 : ℝ)
  · exact real_three_w1616 p (le_of_lt (lt_of_not_ge h7)) h8
  by_cases h9 : p ≤ (4787/1024 : ℝ)
  · exact real_three_w1617 p (le_of_lt (lt_of_not_ge h8)) h9
  by_cases h10 : p ≤ (4791/1024 : ℝ)
  · exact real_three_w1618 p (le_of_lt (lt_of_not_ge h9)) h10
  by_cases h11 : p ≤ (4795/1024 : ℝ)
  · exact real_three_w1619 p (le_of_lt (lt_of_not_ge h10)) h11
  by_cases h12 : p ≤ (4799/1024 : ℝ)
  · exact real_three_w1620 p (le_of_lt (lt_of_not_ge h11)) h12
  by_cases h13 : p ≤ (4803/1024 : ℝ)
  · exact real_three_w1621 p (le_of_lt (lt_of_not_ge h12)) h13
  by_cases h14 : p ≤ (4807/1024 : ℝ)
  · exact real_three_w1622 p (le_of_lt (lt_of_not_ge h13)) h14
  by_cases h15 : p ≤ (4811/1024 : ℝ)
  · exact real_three_w1623 p (le_of_lt (lt_of_not_ge h14)) h15
  by_cases h16 : p ≤ (4815/1024 : ℝ)
  · exact real_three_w1624 p (le_of_lt (lt_of_not_ge h15)) h16
  by_cases h17 : p ≤ (4819/1024 : ℝ)
  · exact real_three_w1625 p (le_of_lt (lt_of_not_ge h16)) h17
  by_cases h18 : p ≤ (4823/1024 : ℝ)
  · exact real_three_w1626 p (le_of_lt (lt_of_not_ge h17)) h18
  by_cases h19 : p ≤ (4827/1024 : ℝ)
  · exact real_three_w1627 p (le_of_lt (lt_of_not_ge h18)) h19
  by_cases h20 : p ≤ (4831/1024 : ℝ)
  · exact real_three_w1628 p (le_of_lt (lt_of_not_ge h19)) h20
  by_cases h21 : p ≤ (4835/1024 : ℝ)
  · exact real_three_w1629 p (le_of_lt (lt_of_not_ge h20)) h21
  by_cases h22 : p ≤ (4839/1024 : ℝ)
  · exact real_three_w1630 p (le_of_lt (lt_of_not_ge h21)) h22
  by_cases h23 : p ≤ (4843/1024 : ℝ)
  · exact real_three_w1631 p (le_of_lt (lt_of_not_ge h22)) h23
  by_cases h24 : p ≤ (4847/1024 : ℝ)
  · exact real_three_w1632 p (le_of_lt (lt_of_not_ge h23)) h24
  by_cases h25 : p ≤ (4851/1024 : ℝ)
  · exact real_three_w1633 p (le_of_lt (lt_of_not_ge h24)) h25
  by_cases h26 : p ≤ (4855/1024 : ℝ)
  · exact real_three_w1634 p (le_of_lt (lt_of_not_ge h25)) h26
  by_cases h27 : p ≤ (4859/1024 : ℝ)
  · exact real_three_w1635 p (le_of_lt (lt_of_not_ge h26)) h27
  by_cases h28 : p ≤ (4863/1024 : ℝ)
  · exact real_three_w1636 p (le_of_lt (lt_of_not_ge h27)) h28
  by_cases h29 : p ≤ (4867/1024 : ℝ)
  · exact real_three_w1637 p (le_of_lt (lt_of_not_ge h28)) h29
  by_cases h30 : p ≤ (4871/1024 : ℝ)
  · exact real_three_w1638 p (le_of_lt (lt_of_not_ge h29)) h30
  exact real_three_w1639 p (le_of_lt (lt_of_not_ge h30)) hpb

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  exact HlawkaSchatten.DiagonalCutoff4.real_cover_g019 p hpa hpb

#print axioms solution
