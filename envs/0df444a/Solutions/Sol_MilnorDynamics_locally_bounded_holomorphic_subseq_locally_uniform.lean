-- Prove2me | solution 1 for MilnorDynamics.locally_bounded_holomorphic_subseq_locally_uniform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T23:48:35.309508+00:00
-- url     : https://prove2.me/submissions/10982a49-328a-4b15-8e13-341a9aea49a8

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies
import Theorems.Thm_MilnorDynamics_exists_deriv_bound_of_locally_bounded
import Theorems.Thm_MilnorDynamics_exists_subseq_locally_uniform_of_bounded_deriv

open scoped OnePoint
open Filter Set
open MilnorDynamics

/-- The holomorphic Arzela-Ascoli extraction, reduced to a Cauchy-estimate step
that produces uniform derivative bounds on compacta and an extraction step that
consumes them. -/
theorem solution (U : Set ℂ) (hU : IsOpen U)
    (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, DifferentiableOn ℂ (f n) U)
    (hb : ∀ K ⊆ U, IsCompact K → ∃ M, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℂ → ℂ, ContinuousOn g U ∧
      TendstoLocallyUniformlyOn (fun n => f (φ n)) g atTop U :=
  exists_subseq_locally_uniform_of_bounded_deriv U hU f hf hb
    (exists_deriv_bound_of_locally_bounded U hU f hf hb)
