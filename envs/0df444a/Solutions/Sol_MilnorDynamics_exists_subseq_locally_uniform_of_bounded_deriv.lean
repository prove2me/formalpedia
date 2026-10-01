-- Prove2me | solution 1 for MilnorDynamics.exists_subseq_locally_uniform_of_bounded_deriv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T00:19:23.56879+00:00
-- url     : https://prove2.me/submissions/c4c93fc6-3d99-419f-955c-667c5ee402e1

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies
import Theorems.Thm_MilnorDynamics_oscillation_bound_of_bounded_deriv
import Theorems.Thm_MilnorDynamics_exists_subseq_locally_uniform_of_oscillation_bounded

open scoped OnePoint
open Filter Set
open MilnorDynamics

/-- The extraction step, reduced to a uniform oscillation bound from the
derivative bounds and the Arzela-Ascoli-plus-diagonal extraction that consumes
it. -/
theorem solution (U : Set ℂ) (hU : IsOpen U)
    (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, DifferentiableOn ℂ (f n) U)
    (hb : ∀ K ⊆ U, IsCompact K → ∃ M, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M)
    (hderiv : ∀ K ⊆ U, IsCompact K → ∃ B, ∀ n, ∀ z ∈ K, ‖deriv (f n) z‖ ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℂ → ℂ, ContinuousOn g U ∧
      TendstoLocallyUniformlyOn (fun n => f (φ n)) g atTop U :=
  exists_subseq_locally_uniform_of_oscillation_bounded U hU f hb
    (oscillation_bound_of_bounded_deriv U hU f hf hderiv)
