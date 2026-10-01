-- Prove2me | solution 2 for MilnorDynamics.thrice_punctured_plane_disk_cover
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T23:04:34.651507+00:00
-- url     : https://prove2.me/submissions/195ce8b3-4c1e-4337-bb5d-76f27080b8fb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies
import Theorems.Thm_MilnorDynamics_disc_cover_proper_and_local_exists
import Theorems.Thm_MilnorDynamics_disc_cover_of_proper_local_homeo

-- Milnor Lemma 2.5 -- Variant B of the reduction.
--
-- Same two children as variant A, but the surjectivity is first packaged as a named
-- `have` about the restriction, and the covering conjunct is then obtained by a
-- single `exact`.  This changes the order in which the parent's conjuncts are built.

open scoped OnePoint
open Filter Set
open MilnorDynamics

theorem solution :
    ∃ p : ℂ → ℂ, DifferentiableOn ℂ p (Metric.ball 0 1) ∧
      ∃ hp : MapsTo p (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ),
        Function.Surjective hp.restrict ∧ IsCoveringMap hp.restrict := by
  obtain ⟨p, hdiff, hp, himage, hproper, hlocal⟩ :=
    MilnorDynamics.disc_cover_proper_and_local_exists
  have hcov : IsCoveringMap (hp.restrict p (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ)) :=
    MilnorDynamics.disc_cover_of_proper_local_homeo hdiff hp himage hproper hlocal
  have hsurj : Function.Surjective (hp.restrict p (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ)) := by
    rintro ⟨y, hy⟩
    have hy' : (y : ℂ) ∈ p '' (Metric.ball 0 1) := himage ▸ hy
    rcases hy' with ⟨z, hz, hzy⟩
    refine ⟨⟨z, hz⟩, ?_⟩
    apply Subtype.ext
    exact hzy
  exact ⟨p, hdiff, hp, hsurj, hcov⟩
