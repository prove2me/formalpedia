-- Prove2me | solution 1 for MilnorDynamics.exists_subseq_locally_uniform_of_oscillation_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T01:12:33.830106+00:00
-- url     : https://prove2.me/submissions/850bdb28-b4d3-4e50-898f-c00714dd1646

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies
import Theorems.Thm_MilnorDynamics_tendstoLocallyUniformlyOn_of_equicontinuous_of_pointwise
import Theorems.Thm_MilnorDynamics_exists_subseq_tendsto_pointwise_of_locally_bounded

open scoped OnePoint
open Filter Set
open MilnorDynamics

/-- The diagonal extraction, reduced to extracting a pointwise convergent
subsequence and then upgrading pointwise convergence to local uniformity. -/
theorem solution (U : Set ℂ) (hU : IsOpen U) (f : ℕ → ℂ → ℂ)
    (hb : ∀ K ⊆ U, IsCompact K → ∃ M, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M)
    (hmod : ∀ K ⊆ U, IsCompact K → ∀ ε > 0, ∃ δ > 0, ∀ n, ∀ x ∈ K, ∀ y ∈ K,
      ‖x - y‖ < δ → ‖f n x - f n y‖ < ε) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℂ → ℂ, ContinuousOn g U ∧
      TendstoLocallyUniformlyOn (fun n => f (φ n)) g atTop U := by
  obtain ⟨φ, hφ, g, hgcont, hgpt⟩ :=
    exists_subseq_tendsto_pointwise_of_locally_bounded U hU f hb hmod
  exact ⟨φ, hφ, g, hgcont,
    tendstoLocallyUniformlyOn_of_equicontinuous_of_pointwise U hU (fun n => f (φ n)) g
      (fun K hKU hK ε hε => by
        obtain ⟨δ, hδpos, hδ⟩ := hmod K hKU hK ε hε
        exact ⟨δ, hδpos, fun n => hδ (φ n)⟩) hgcont hgpt⟩
