-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p015
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:44:09.529325+00:00
-- url     : https://prove2.me/submissions/8844e24d-c03b-4d54-996d-b1ab8a67d70f

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_chart_main_injective_of_collision_margin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_repeated_p015 (p : ℝ) (hpa : (47/8 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) :
    ∀ X orders signs, OrderedChart p (225053/100000 : ℝ) (159717/100000 : ℝ) (82943/100000 : ℝ) X orders signs → Function.Injective (fun j => orders j 0) := by
  exact chart_main_injective_of_collision_margin p (225053/100000 : ℝ) (159717/100000 : ℝ) (82943/100000 : ℝ)
    (by linarith only [hpa]) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (47/8 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) :
    ∀ X orders signs, OrderedChart p (225053/100000 : ℝ) (159717/100000 : ℝ) (82943/100000 : ℝ) X orders signs → Function.Injective (fun j => orders j 0) := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p015 p hpa hpb

#print axioms solution
