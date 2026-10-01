-- Prove2me | solution 2 for MilnorDynamics.planar_part_of_sphere_omitting
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T21:12:43.451986+00:00
-- url     : https://prove2.me/submissions/7322660e-255e-42ba-9ed8-f586aae785da

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set
open MilnorDynamics

/-- Variant 2: same bridge, but the `OnePoint` case split is driven by the
registered `OnePoint.rec` eliminator through `induction ... using`, the finite
branch closes by `simpa` after unfolding the affine chart, and the codomain
condition is discharged by `rintro` on the disjunction form. -/
theorem solution (U : Set ℂ) (g : ℂ → OnePoint ℂ)
    (hg : IsHolomorphicOn U g)
    (homit : ∀ z ∈ U, g z ≠ ((0 : ℂ) : OnePoint ℂ) ∧
      g z ≠ ((1 : ℂ) : OnePoint ℂ) ∧ g z ≠ ∞) :
    ∃ ĝ : ℂ → ℂ, DifferentiableOn ℂ ĝ U ∧ MapsTo ĝ U ({0, 1}ᶜ : Set ℂ) ∧
      ∀ z ∈ U, ((ĝ z : ℂ) : OnePoint ℂ) = g z := by
  have hagree : ∀ z ∈ U, ((chartFinite (g z) : ℂ) : OnePoint ℂ) = g z := by
    intro z hz
    induction h : g z using OnePoint.rec with
    | infty => exact absurd h (homit z hz).2.2
    | coe t => simpa [chartFinite]
  exact ⟨fun z => chartFinite (g z),
    (fun z hz => (hg.2.1 z hz (homit z hz).2.2).differentiableWithinAt),
    (fun z hz => by
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (h | h)
      · exact (homit z hz).1 (by rw [← hagree z hz, h])
      · exact (homit z hz).2.1 (by rw [← hagree z hz, h])),
    hagree⟩
