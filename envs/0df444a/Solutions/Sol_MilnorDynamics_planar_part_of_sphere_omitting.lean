-- Prove2me | solution 1 for MilnorDynamics.planar_part_of_sphere_omitting
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T21:12:39.089304+00:00
-- url     : https://prove2.me/submissions/054cc9f6-a188-4fee-91ba-e4c7c0b9cc70

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set
open MilnorDynamics

/-- Variant 1: resolve the `OnePoint` case split with the registered `cases`
eliminator, whose alternatives are `infty` and `coe`. -/
theorem solution (U : Set ℂ) (g : ℂ → OnePoint ℂ)
    (hg : IsHolomorphicOn U g)
    (homit : ∀ z ∈ U, g z ≠ ((0 : ℂ) : OnePoint ℂ) ∧
      g z ≠ ((1 : ℂ) : OnePoint ℂ) ∧ g z ≠ ∞) :
    ∃ ĝ : ℂ → ℂ, DifferentiableOn ℂ ĝ U ∧ MapsTo ĝ U ({0, 1}ᶜ : Set ℂ) ∧
      ∀ z ∈ U, ((ĝ z : ℂ) : OnePoint ℂ) = g z := by
  have hagree : ∀ z ∈ U, ((chartFinite (g z) : ℂ) : OnePoint ℂ) = g z := by
    intro z hz
    cases h : g z with
    | infty => exact absurd h (homit z hz).2.2
    | coe t => rfl
  refine ⟨fun z => chartFinite (g z), ?_, ?_, hagree⟩
  · intro z hz
    exact (hg.2.1 z hz (homit z hz).2.2).differentiableWithinAt
  · intro z hz
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => (homit z hz).1 (by rw [← hagree z hz, h]),
      fun h => (homit z hz).2.1 (by rw [← hagree z hz, h])⟩
