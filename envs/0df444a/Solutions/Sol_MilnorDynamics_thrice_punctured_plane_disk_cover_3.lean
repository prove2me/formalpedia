-- Prove2me | solution 3 for MilnorDynamics.thrice_punctured_plane_disk_cover
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T23:04:47.770922+00:00
-- url     : https://prove2.me/submissions/ee12100f-9aaa-4480-b6b7-2789919e3b43
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies
import Theorems.Thm_MilnorDynamics_disc_cover_proper_and_local_exists
import Theorems.Thm_MilnorDynamics_disc_cover_of_proper_local_homeo

-- Milnor Lemma 2.5 -- Variant C of the reduction.
--
-- Same two children as variants A and B.  Here the surjectivity step avoids
-- `Subtype.ext` entirely by using the set-image membership directly: the hypothesis
-- `hy : y ∈ {0,1}^c` is turned into image membership by substituting the image equality
-- into it, and the resulting witness is closed with `rfl` after `subst`.

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
