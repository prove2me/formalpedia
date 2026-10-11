-- Prove2me | solution 1 for HunterPDE.Newtonian.secondPartial_difference_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T17:59:31.29614+00:00
-- url     : https://prove2.me/submissions/e6005eb9-5c57-4ffd-8c59-d99982ca9e2c

import Theorems.Thm_HunterPDE_Newtonian_norm_fderiv_secondPartial_le
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

open HunterPDE.Newtonian

theorem solution (n : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i j : Fin n,
      ∀ z h : EuclideanSpace ℝ (Fin n), z ≠ 0 → ‖h‖ ≤ ‖z‖ / 2 →
      |secondPartial (fundamentalSolution n) i j (z + h) -
        secondPartial (fundamentalSolution n) i j (z - h)| ≤
        C * ‖h‖ * ‖z‖ ^ (-(n : ℝ) - 1) := by
  obtain ⟨B, hB, hder⟩ := norm_fderiv_secondPartial_le n hn
  let p : ℝ := -(n : ℝ) - 1
  refine ⟨2 * B / (2 : ℝ) ^ p, by positivity, ?_⟩
  intro i j z h hz hh
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hp : p ≤ 0 := by dsimp [p]; linarith [Nat.cast_nonneg n (α := ℝ)]
  let s := Metric.closedBall z (‖z‖ / 2)
  have hlow (w : EuclideanSpace ℝ (Fin n)) (hw : w ∈ s) : ‖z‖ / 2 ≤ ‖w‖ := by
    have hw' : ‖w - z‖ ≤ ‖z‖ / 2 := by simpa [s, Metric.mem_closedBall, dist_eq_norm] using hw
    have ht' : ‖z‖ - ‖w‖ ≤ ‖w - z‖ := by simpa [norm_sub_rev] using norm_sub_norm_le z w
    linarith
  have hne (w : EuclideanSpace ℝ (Fin n)) (hw : w ∈ s) : w ≠ 0 := by
    exact norm_pos_iff.mp (lt_of_lt_of_le (half_pos hr) (hlow w hw))
  have hbound (w : EuclideanSpace ℝ (Fin n)) (hw : w ∈ s) :
      ‖fderiv ℝ (secondPartial (fundamentalSolution n) i j) w‖ ≤ B * (‖z‖ / 2) ^ p := by
    exact (hder i j w (hne w hw)).2.trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (half_pos hr) (hlow w hw) hp) hB)
  have hm := (convex_closedBall z (‖z‖ / 2)).norm_image_sub_le_of_norm_fderiv_le
    (fun w hw => (hder i j w (hne w hw)).1) hbound
    (x := z - h) (y := z + h)
    (by simpa [s, Metric.mem_closedBall, dist_eq_norm, norm_neg] using hh)
    (by simpa [s, Metric.mem_closedBall, dist_eq_norm] using hh)
  have hsub : z + h - (z - h) = (2 : ℝ) • h := by module
  rw [hsub, norm_smul] at hm
  rw [Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hm
  rw [Real.div_rpow (norm_nonneg z) (by norm_num)] at hm
  rw [Real.norm_eq_abs] at hm
  dsimp [p] at hm ⊢
  convert hm using 1 <;> ring
