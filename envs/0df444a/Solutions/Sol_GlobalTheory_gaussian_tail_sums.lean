-- Prove2me | solution 1 for GlobalTheory.gaussian_tail_sums
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:39:44.671657+00:00
-- url     : https://prove2.me/submissions/086fcde5-3b68-4d25-a25b-18c525acf68b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteInterClosedBallOfSeparated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_GaussianSumOfOneSeparatedOfLe
import Theorems.Thm_GlobalTheory_subgroup_gaussian_tail_sixteen
import Theorems.Thm_GlobalTheory_subgroup_gaussian_tail_dyadic
import Theorems.Thm_GlobalTheory_set_gaussian_sum_of_one_separated

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
theorem _root_.solution :
    (∀ (G : AddSubgroup E) (g : ℕ) (R : ℝ), finrank ℝ E = 2 * g → 0 ≤ R →
      16 * (2 * (g : ℝ) + 1) ≤ R ^ 2 → (∀ x ∈ G, x ≠ 0 → R ≤ ‖x‖) →
      Summable (fun x : {x : G // x ≠ 0} => exp (-‖(x.1 : E)‖ ^ 2 / 16)) ∧
        ∑' x : {x : G // x ≠ 0}, exp (-‖(x.1 : E)‖ ^ 2 / 16) ≤ 2 * 9 ^ g * exp (-R ^ 2 / 16)) ∧
    (∀ (S : Set E) (w : E), 1 ≤ finrank ℝ E → (S.Pairwise fun a b => 1 ≤ dist a b) →
      (Summable (fun y : S => exp (-(π / 2 * ‖w - y‖ ^ 2))) ∧
        ∑' y : S, exp (-(π / 2 * ‖w - y‖ ^ 2)) ≤ 2 * (3 * (finrank ℝ E : ℝ)) ^ finrank ℝ E) ∧
      (Summable (fun y : S => exp (-(π * ‖w - y‖ ^ 2))) ∧
        ∑' y : S, exp (-(π * ‖w - y‖ ^ 2)) ≤
          2 * (3 * (finrank ℝ E : ℝ)) ^ finrank ℝ E * exp (-(π / 2 * infDist w S ^ 2)))) ∧
    (∀ (G : AddSubgroup E) (b q : ℝ), 0 < b → (finrank ℝ E : ℝ) + 1 ≤ q * b →
      (∀ y ∈ G, y ≠ 0 → b ≤ ‖y‖ ^ 2) →
      Summable (fun y : {y : G // y ≠ 0} => exp (-(q * ‖(y.1 : E)‖ ^ 2))) ∧
        ∑' y : {y : G // y ≠ 0}, exp (-(q * ‖(y.1 : E)‖ ^ 2)) ≤
          2 * 4.3 ^ finrank ℝ E * exp (-(q * b))) :=
  ⟨fun G _ _ hg hR0 hR hG => subgroup_gaussian_tail_sixteen G hg hR0 hR hG,
    fun _ w hd hS => set_gaussian_sum_of_one_separated w hd hS,
    fun G _ _ hb hd hG => subgroup_gaussian_tail_dyadic G hb hd hG⟩
end GlobalTheory
