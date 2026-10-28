-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p014
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:43:42.504856+00:00
-- url     : https://prove2.me/submissions/24014164-1152-4ad1-bc15-5146a5c4b9d8

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_chart_main_injective_of_collision_margin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_repeated_p014 (p : ℝ) (hpa : (23/4 : ℝ) ≤ p) (hpb : p ≤ (47/8 : ℝ)) :
    ∀ X orders signs, OrderedChart p (219663/100000 : ℝ) (80409/50000 : ℝ) (82607/100000 : ℝ) X orders signs → Function.Injective (fun j => orders j 0) := by
  exact chart_main_injective_of_collision_margin p (219663/100000 : ℝ) (80409/50000 : ℝ) (82607/100000 : ℝ)
    (by linarith only [hpa]) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (23/4 : ℝ) ≤ p) (hpb : p ≤ (47/8 : ℝ)) :
    ∀ X orders signs, OrderedChart p (219663/100000 : ℝ) (80409/50000 : ℝ) (82607/100000 : ℝ) X orders signs → Function.Injective (fun j => orders j 0) := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p014 p hpa hpb

#print axioms solution
