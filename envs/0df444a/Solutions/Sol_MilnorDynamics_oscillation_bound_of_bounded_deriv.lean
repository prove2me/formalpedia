-- Prove2me | solution 1 for MilnorDynamics.oscillation_bound_of_bounded_deriv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T00:20:34.231379+00:00
-- url     : https://prove2.me/submissions/a378132e-762b-41ae-b4d7-aecea87ce6bb

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set
open MilnorDynamics

/-- Variant 1: mean value inequality along the segment joining two points of the
compact set, with the derivative bound taken on an open thickening of that
compact set. -/
theorem solution (U : Set ℂ) (hU : IsOpen U)
    (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, DifferentiableOn ℂ (f n) U)
    (hderiv : ∀ K ⊆ U, IsCompact K → ∃ B, ∀ n, ∀ z ∈ K, ‖deriv (f n) z‖ ≤ B) :
    ∀ K ⊆ U, IsCompact K → ∀ ε > 0, ∃ δ > 0, ∀ n, ∀ x ∈ K, ∀ y ∈ K,
      ‖x - y‖ < δ → ‖f n x - f n y‖ < ε := by
  intro K hKU hK ε hε
  obtain ⟨δ₀, hδ₀pos, hδ₀U⟩ := hK.exists_cthickening_subset_open hU hKU
  have hKcth : IsCompact (Metric.cthickening δ₀ K) := hK.cthickening
  obtain ⟨B, hB⟩ := hderiv (Metric.cthickening δ₀ K) hδ₀U hKcth
  have hCpos : (0 : ℝ) < max B 0 + 1 := by positivity
  refine ⟨min δ₀ (ε / (max B 0 + 1)), lt_min hδ₀pos (by positivity),
    fun n x hx y hy hxy => ?_⟩
  have hxyδ : ‖x - y‖ < δ₀ := lt_of_lt_of_le hxy (min_le_left _ _)
  have hxyε : ‖x - y‖ < ε / (max B 0 + 1) := lt_of_lt_of_le hxy (min_le_right _ _)
  have hsegK : segment ℝ x y ⊆ Metric.cthickening δ₀ K :=
    (segment_subset_closedBall_left x y).trans
      ((Metric.closedBall_subset_cthickening hx (dist x y)).trans
        (Metric.cthickening_mono (by rw [dist_eq_norm]; exact le_of_lt hxyδ) K))
  have hsegU : segment ℝ x y ⊆ U := hsegK.trans hδ₀U
  have hD : ∀ p ∈ segment ℝ x y, DifferentiableAt ℂ (f n) p := fun p hp =>
    ((hf n) p (hsegU hp)).differentiableAt (hU.mem_nhds (hsegU hp))
  have hBd : ∀ p ∈ segment ℝ x y, ‖deriv (f n) p‖ ≤ max B 0 := fun p hp =>
    (hB n p (hsegK hp)).trans (le_max_left _ _)
  have hmvt : ‖f n y - f n x‖ ≤ (max B 0) * ‖y - x‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le hD hBd (convex_segment x y)
      (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  have hstep : ‖f n x - f n y‖ ≤ (max B 0 + 1) * ‖x - y‖ := by
    have h1 : ‖f n x - f n y‖ ≤ (max B 0) * ‖x - y‖ := by
      simpa [norm_sub_rev] using hmvt
    have h2 : (max B 0) * ‖x - y‖ ≤ (max B 0 + 1) * ‖x - y‖ := by
      have := norm_nonneg (x - y)
      nlinarith
    linarith
  have hmul : (max B 0 + 1) * (ε / (max B 0 + 1)) = ε := by
    rw [mul_comm]
    exact div_mul_cancel₀ ε (ne_of_gt hCpos)
  have hlt : (max B 0 + 1) * ‖x - y‖ < ε := by
    have := mul_lt_mul_of_pos_left hxyε hCpos
    rwa [hmul] at this
  linarith
