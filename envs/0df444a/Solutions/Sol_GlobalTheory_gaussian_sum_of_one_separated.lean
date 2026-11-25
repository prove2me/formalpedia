-- Prove2me | solution 1 for GlobalTheory.gaussian_sum_of_one_separated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:18:48.329907+00:00
-- url     : https://prove2.me/submissions/2f42e6b7-4506-4308-9692-dea5dedcda65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteInterClosedBallOfSeparated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_GaussianSumOfOneSeparatedOfLe
import Theorems.Thm_GlobalTheory_summable_exp_neg_of_card_le
import Theorems.Thm_GlobalTheory_finset_card_le_of_separated_family

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
theorem _root_.solution {ι : Type*} (u : ι → E) (w : E) (hd : 1 ≤ finrank ℝ E)
    (hu : Pairwise fun i j => 1 ≤ dist (u i) (u j)) :
    Summable (fun i => exp (-(π / 2 * ‖w - u i‖ ^ 2))) ∧
      ∑' i, exp (-(π / 2 * ‖w - u i‖ ^ 2)) ≤ 2 * (3 * (finrank ℝ E : ℝ)) ^ finrank ℝ E := by
  have h := summable_exp_neg_of_card_le (fun i => π / 2 * ‖w - u i‖ ^ 2) (t := 0)
    (C := (3 * (finrank ℝ E : ℝ)) ^ finrank ℝ E) (fun i => by positivity) ?_
  · simpa only [neg_zero, exp_zero, mul_one] using h
  intro s v hv hs
  have hq : 0 < π / 2 := by positivity
  set R := √(v / (π / 2)) with hRdef
  have hR0 : 0 ≤ R := sqrt_nonneg _
  have hR2 : R ^ 2 = v / (π / 2) := sq_sqrt (by positivity)
  have hv2 : v = π / 2 * R ^ 2 := by rw [hR2]; field_simp
  have hcard := finset_card_le_of_separated_family u one_pos hR0 hu w s fun i hi => by
    rw [dist_comm, dist_eq_norm]
    refine le_sqrt_of_sq_le ?_
    rw [le_div_iff₀ hq, mul_comm]
    exact hs i hi
  refine hcard.trans ?_
  set d := finrank ℝ E
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : 1 + 2 * R / 1 ≤ 3 * (d : ℝ) * exp (v / (2 * d)) := by
    have h2 := add_one_le_exp (v / (2 * d))
    have h3 : 3 * (d : ℝ) * (v / (2 * d) + 1) = 3 / 2 * v + 3 * d := by field_simp
    have h4 : 3 * (d : ℝ) * (v / (2 * d) + 1) ≤ 3 * (d : ℝ) * exp (v / (2 * d)) := by gcongr
    have h5 : 3 / 2 * R ^ 2 ≤ v := by
      rw [hv2]; have := pi_gt_three; gcongr
    nlinarith [sq_nonneg (R - 1)]
  calc (1 + 2 * R / 1) ^ d ≤ (3 * (d : ℝ) * exp (v / (2 * d))) ^ d :=
        pow_le_pow_left₀ (by positivity) h1 _
    _ = _ := by
        rw [mul_pow, ← exp_nat_mul]; congr 2; field_simp; ring
end GlobalTheory
