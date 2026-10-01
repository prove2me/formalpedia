-- Prove2me | solution 1 for MilnorDynamics.thrice_punctured_plane_disk_cover
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T23:04:20.598377+00:00
-- url     : https://prove2.me/submissions/fa839755-3fc9-4714-8bf9-66a41893726d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies
import Theorems.Thm_MilnorDynamics_disc_cover_proper_and_local_exists
import Theorems.Thm_MilnorDynamics_disc_cover_of_proper_local_homeo

-- Milnor Lemma 2.5: the thrice-punctured sphere is hyperbolic.
--
-- This is a REDUCTION (proof sketch). It imports two Open children that together
-- supply every conjunct of the parent, and closes the goal by direct application.
--
--   `disc_cover_proper_and_local_exists` supplies the witness together with all four
--   of its properties: complex differentiability on the open unit disc, avoidance of
--   both punctures, image exactly `{0,1}^c`, and -- crucially -- that the restriction
--   from the disc into `{0,1}^c` is a PROPER MAP and a LOCAL HOMEOMORPHISM.  The
--   witness is the modular lambda function pulled back by the Cayley bijection.
--
--   `disc_cover_of_proper_local_homeo` turns those last two properties into
--   `IsCoveringMap` of the restriction.  It is the general theorem that a proper
--   local homeomorphism onto a Hausdorff space is a covering map, which the platform
--   already has as the Proved theorem
--   `s2_isCoveringMap_of_isProperMap_of_isLocalHomeomorph`.
--
-- Surjectivity of the restriction is elementary once the image is known: the equality
-- `p '' (Metric.ball 0 1) = {0,1}^c` says every point of `{0,1}^c` is `p z` for some
-- `z` in the disc, and `MapsTo` places that `z` in the domain of the restriction, so
-- the equation holds in the codomain subtype by `Subtype.ext`.

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
    refine ⟨⟨z, hz⟩, ?_⟩
    apply Subtype.ext
    exact hzy
  · exact MilnorDynamics.disc_cover_of_proper_local_homeo hdiff hp himage hproper hlocal
