-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p013
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:43:41.760125+00:00
-- url     : https://prove2.me/submissions/768519f4-b852-445a-9b8e-31be66c75bc2

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_chart_main_injective_of_collision_margin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_repeated_p013 (p : ℝ) (hpa : (45/8 : ℝ) ≤ p) (hpb : p ≤ (23/4 : ℝ)) :
    ∀ X orders signs, OrderedChart p (214291/100000 : ℝ) (80997/50000 : ℝ) (82257/100000 : ℝ) X orders signs → Function.Injective (fun j => orders j 0) := by
  exact chart_main_injective_of_collision_margin p (214291/100000 : ℝ) (80997/50000 : ℝ) (82257/100000 : ℝ)
    (by linarith only [hpa]) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (45/8 : ℝ) ≤ p) (hpb : p ≤ (23/4 : ℝ)) :
    ∀ X orders signs, OrderedChart p (214291/100000 : ℝ) (80997/50000 : ℝ) (82257/100000 : ℝ) X orders signs → Function.Injective (fun j => orders j 0) := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p013 p hpa hpb

#print axioms solution
