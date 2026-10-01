-- Prove2me | solution 1 for MilnorDynamics.exists_deriv_bound_of_locally_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T00:03:57.703478+00:00
-- url     : https://prove2.me/submissions/d3e9cbfc-02c6-4bae-b632-c627d1587934

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set
open MilnorDynamics

/-- Variant 1: push the compact set into an open thickening, bound the family
there once, and apply Cauchy's estimate on the disc of that radius about each
point of the compact set. -/
theorem solution (U : Set ℂ) (hU : IsOpen U)
    (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, DifferentiableOn ℂ (f n) U)
    (hb : ∀ K ⊆ U, IsCompact K → ∃ M, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M) :
    ∀ K ⊆ U, IsCompact K → ∃ B, ∀ n, ∀ z ∈ K, ‖deriv (f n) z‖ ≤ B := by
  intro K hKU hK
  obtain ⟨δ, hδpos, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hKcth : IsCompact (Metric.cthickening δ K) := hK.cthickening
  obtain ⟨M, hM⟩ := hb (Metric.cthickening δ K) hδU hKcth
  refine ⟨M / δ, fun n z hz => ?_⟩
  have hcb : Metric.closedBall z δ ⊆ Metric.cthickening δ K := Metric.closedBall_subset_cthickening hz δ
  have hballU : Metric.closedBall z δ ⊆ U := hcb.trans hδU
  have hD : DiffContOnCl ℂ (f n) (Metric.ball z δ) :=
    (((hf n).mono hballU).mono Metric.closure_ball_subset_closedBall).diffContOnCl
  have hC : ∀ w ∈ Metric.sphere z δ, ‖f n w‖ ≤ M := fun w hw =>
    hM n w (hcb (Metric.sphere_subset_closedBall hw))
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδpos hD hC
