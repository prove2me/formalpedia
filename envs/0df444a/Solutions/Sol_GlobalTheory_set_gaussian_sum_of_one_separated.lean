-- Prove2me | solution 1 for GlobalTheory.set_gaussian_sum_of_one_separated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:37:56.164809+00:00
-- url     : https://prove2.me/submissions/dcfcb684-e9e2-421a-9ed3-df49fe0f8f7c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteInterClosedBallOfSeparated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_GaussianSumOfOneSeparatedOfLe
import Theorems.Thm_GlobalTheory_gaussian_sum_of_one_separated
import Theorems.Thm_GlobalTheory_gaussian_sum_of_one_separated_of_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric MeasureTheory Module Set Real
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
namespace GlobalTheory
theorem _root_.solution {S : Set E} (w : E) (hd : 1 ≤ finrank ℝ E)
    (hS : S.Pairwise fun a b => 1 ≤ dist a b) :
    (Summable (fun y : S => exp (-(π / 2 * ‖w - y‖ ^ 2))) ∧
      ∑' y : S, exp (-(π / 2 * ‖w - y‖ ^ 2)) ≤ 2 * (3 * (finrank ℝ E : ℝ)) ^ finrank ℝ E) ∧
    (Summable (fun y : S => exp (-(π * ‖w - y‖ ^ 2))) ∧
      ∑' y : S, exp (-(π * ‖w - y‖ ^ 2)) ≤
        2 * (3 * (finrank ℝ E : ℝ)) ^ finrank ℝ E * exp (-(π / 2 * infDist w S ^ 2))) := by
  have hu : Pairwise fun i j : S => 1 ≤ dist (i : E) (j : E) := fun i j hij =>
    hS i.2 j.2 fun h => hij (Subtype.ext h)
  exact ⟨gaussian_sum_of_one_separated Subtype.val w hd hu,
    gaussian_sum_of_one_separated_of_le Subtype.val w hd hu infDist_nonneg fun i => by
      rw [← dist_eq_norm]; exact infDist_le_dist_of_mem i.2⟩
end GlobalTheory
