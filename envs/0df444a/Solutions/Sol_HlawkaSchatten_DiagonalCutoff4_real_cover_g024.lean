-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.real_cover_g024
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:07:08.564004+00:00
-- url     : https://prove2.me/submissions/4da5f6cb-1964-4ba2-9fbd-d48a190a9649

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1768
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1769
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1770
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1771
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1772
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_w1773
set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalCutoff4
theorem real_cover_g024 (p : ℝ) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  by_cases h0 : p ≤ (6063/1024 : ℝ)
  · exact real_three_w1768 p hpa h0
  by_cases h1 : p ≤ (6079/1024 : ℝ)
  · exact real_three_w1769 p (le_of_lt (lt_of_not_ge h0)) h1
  by_cases h2 : p ≤ (6095/1024 : ℝ)
  · exact real_three_w1770 p (le_of_lt (lt_of_not_ge h1)) h2
  by_cases h3 : p ≤ (6111/1024 : ℝ)
  · exact real_three_w1771 p (le_of_lt (lt_of_not_ge h2)) h3
  by_cases h4 : p ≤ (6143/1024 : ℝ)
  · exact real_three_w1772 p (le_of_lt (lt_of_not_ge h3)) h4
  exact real_three_w1773 p (le_of_lt (lt_of_not_ge h4)) hpb

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  exact HlawkaSchatten.DiagonalCutoff4.real_cover_g024 p hpa hpb

#print axioms solution
