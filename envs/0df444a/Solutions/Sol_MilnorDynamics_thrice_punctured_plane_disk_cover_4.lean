-- Prove2me | solution 4 for MilnorDynamics.thrice_punctured_plane_disk_cover
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T09:55:41.115684+00:00
-- url     : https://prove2.me/submissions/7e2797f2-95c0-4fd7-b696-765fda212926
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Milnor Lemma 2.5 -- repaired parent, variant P1.
--
-- Identical to the sketch-accepted candidate 5260 in structure and imports.  The
-- CE on candidate 5149 was mechanical: it did `intro x hx` on a goal that is the
-- *conjunction* `Function.Surjective hp.restrict ∧ IsCoveringMap hp.restrict`, and
-- `intro` only works on a forall/exists goal.  This variant uses `rintro` on both
-- sides so the conjunction is destructured explicitly, which is the form that
-- already validated as 5260.
--
-- Sole remaining dependency: `disc_cover_proper_and_local_exists` (3efd79e3, Open).

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies
import Theorems.Thm_MilnorDynamics_disc_cover_proper_and_local_exists
import Theorems.Thm_MilnorDynamics_disc_cover_of_proper_local_homeo

open scoped OnePoint
open Filter Set
open MilnorDynamics

theorem solution :
    ∃ p : ℂ → ℂ, DifferentiableOn ℂ p (Metric.ball 0 1) ∧
      ∃ hp : MapsTo p (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ),
        Function.Surjective hp.restrict ∧ IsCoveringMap hp.restrict := by
  obtain ⟨p, hdiff, hp, himage, hproper, hlocal⟩ :=
    MilnorDynamics.disc_cover_proper_and_local_exists
  refine ⟨p, hdiff, hp, ?_, ?_⟩
  · rintro ⟨y, hy⟩
    have hy' : (y : ℂ) ∈ p '' (Metric.ball 0 1) := himage ▸ hy
    rcases hy' with ⟨z, hz, hzy⟩
    subst hzy
    exact ⟨⟨z, hz⟩, rfl⟩
  · exact MilnorDynamics.disc_cover_of_proper_local_homeo hdiff hp himage hproper hlocal
