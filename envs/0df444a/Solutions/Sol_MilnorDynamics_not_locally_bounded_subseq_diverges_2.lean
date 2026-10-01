-- Prove2me | solution 2 for MilnorDynamics.not_locally_bounded_subseq_diverges
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T06:44:33.370676+00:00
-- url     : https://prove2.me/submissions/9014a03f-2b42-4994-bc4d-b243aa75961b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies
import Theorems.Thm_MilnorDynamics_exists_subseq_escapes_locally
import Theorems.Thm_MilnorDynamics_escapes_on_compacts_implies_diverges

open scoped OnePoint
open Filter Set
open MilnorDynamics

/-- The escape step of Montel's theorem, reduced to the real-valued escape child
and the proved metric bridge: unboundedness on a compact gives a subsequence
whose moduli escape on every compact, and escaping past the radius of a compact
subset of `{0,1}ᶜ` is divergence from `{0,1}ᶜ`. -/
theorem solution (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U)
    (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, DifferentiableOn ℂ (f n) U ∧ MapsTo (f n) U ({0, 1}ᶜ : Set ℂ))
    (hbdd : ∃ K ⊆ U, IsCompact K ∧
      ¬ (∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      DivergesLocallyUniformlyFrom (fun n => f (φ n)) U ({0, 1}ᶜ : Set ℂ) := by
  obtain ⟨φ, hφ, hesc⟩ := exists_subseq_escapes_locally U hU hUc f hf hbdd
  exact ⟨φ, hφ, escapes_on_compacts_implies_diverges U hU (fun n => f (φ n))
    (fun n => hf (φ n)) hesc⟩
