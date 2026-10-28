-- Prove2me | solution 1 for MilnorDynamics.exists_subseq_escapes_of_bounded_reciprocal_and_unbounded
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T13:08:22.549414+00:00
-- url     : https://prove2.me/submissions/617f8cf0-4307-47a7-88cb-16591e316a1f

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies
import Theorems.Thm_MilnorDynamics_exists_subseq_escapes_locally

open scoped OnePoint
open Filter Set
open MilnorDynamics

theorem solution (U : Set ℂ) (hU : IsOpen U)
    (hUc : IsConnected U) (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, DifferentiableOn ℂ (f n) U ∧ MapsTo (f n) U ({0, 1}ᶜ : Set ℂ))
    (hrecip : ∀ K ⊆ U, IsCompact K → ∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖(f n)⁻¹ z‖ ≤ M)
    (hbdd : ∃ K ⊆ U, IsCompact K ∧
      ¬ (∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ K ⊆ U, IsCompact K → ∀ R : ℝ, ∀ᶠ n in atTop, ∀ z ∈ K, R < ‖f (φ n) z‖ := by
  apply MilnorDynamics.exists_subseq_escapes_locally <;> assumption


