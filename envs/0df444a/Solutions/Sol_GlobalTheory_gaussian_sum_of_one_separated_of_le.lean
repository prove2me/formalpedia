-- Prove2me | solution 1 for GlobalTheory.gaussian_sum_of_one_separated_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:27:05.890734+00:00
-- url     : https://prove2.me/submissions/2ab4bce7-d161-4845-bddd-4f515caf3707

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteInterClosedBallOfSeparated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_GaussianSumOfOneSeparatedOfLe
import Theorems.Thm_GlobalTheory_gaussian_sum_of_one_separated

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
theorem _root_.solution {ι : Type*} (u : ι → E) (w : E)
    (hd : 1 ≤ finrank ℝ E) (hu : Pairwise fun i j => 1 ≤ dist (u i) (u j)) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hw : ∀ i, ρ ≤ ‖w - u i‖) :
    Summable (fun i => exp (-(π * ‖w - u i‖ ^ 2))) ∧
      ∑' i, exp (-(π * ‖w - u i‖ ^ 2)) ≤
        2 * (3 * (finrank ℝ E : ℝ)) ^ finrank ℝ E * exp (-(π / 2 * ρ ^ 2)) := by
  obtain ⟨hs, hb⟩ := gaussian_sum_of_one_separated u w hd hu
  have hle : ∀ i, exp (-(π * ‖w - u i‖ ^ 2)) ≤
      exp (-(π / 2 * ‖w - u i‖ ^ 2)) * exp (-(π / 2 * ρ ^ 2)) := fun i => by
    rw [← exp_add, exp_le_exp]
    have h1 : π / 2 * ρ ^ 2 ≤ π / 2 * ‖w - u i‖ ^ 2 := by have := hw i; gcongr
    linarith
  have hs2 := hs.mul_right (exp (-(π / 2 * ρ ^ 2)))
  have hs1 := Summable.of_nonneg_of_le (fun i => (exp_pos _).le) hle hs2
  refine ⟨hs1, (hs1.tsum_le_tsum hle hs2).trans ?_⟩
  rw [tsum_mul_right]
  gcongr
end GlobalTheory
