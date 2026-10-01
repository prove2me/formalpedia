-- Prove2me | solution 1 for MilnorDynamics.escapes_on_compacts_implies_diverges
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T03:39:29.627979+00:00
-- url     : https://prove2.me/submissions/c6505161-5f2b-4fe7-a95e-292b5ad3e5ad

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set
open MilnorDynamics

/-- A compact subset of `ℂ \ {0,1}` is bounded, so uniform escape on compacta forces the
family to avoid it eventually.  Neither differentiability nor the omitted values are used;
they are carried for signature compatibility with the parent target. -/
theorem solution (U : Set ℂ) (hU : IsOpen U) (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, DifferentiableOn ℂ (f n) U ∧ MapsTo (f n) U ({0, 1}ᶜ : Set ℂ))
    (hesc : ∀ K ⊆ U, IsCompact K → ∀ R : ℝ, ∀ᶠ n in atTop, ∀ z ∈ K, R < ‖f n z‖) :
    DivergesLocallyUniformlyFrom f U ({0, 1}ᶜ : Set ℂ) := by
  intro K hKU hK K' _ hK'
  by_cases hne : K'.Nonempty
  · obtain ⟨w, hw⟩ := hne
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall w).mp hK'.isBounded
    filter_upwards [hesc K hKU hK (R + ‖w‖)] with n hn
    intro x hx hxK'
    have h1 : dist (f n x) w ≤ R := by
      simpa [Metric.mem_closedBall] using hR hxK'
    have h2 : R + ‖w‖ < ‖f n x‖ := hn x hx
    have h3 : ‖f n x‖ ≤ dist (f n x) w + ‖w‖ := by
      calc ‖f n x‖ = ‖(f n x - w) + w‖ := by ring_nf
        _ ≤ ‖f n x - w‖ + ‖w‖ := norm_add_le _ _
        _ = dist (f n x) w + ‖w‖ := by rw [dist_eq_norm]
    linarith
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    simp
