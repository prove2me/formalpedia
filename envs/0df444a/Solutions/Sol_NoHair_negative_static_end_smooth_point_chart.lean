-- Prove2me | solution 1 for NoHair.negative_static_end_smooth_point_chart
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T11:00:23.003802+00:00
-- url     : https://prove2.me/submissions/bf224fbb-a6f3-4919-9ae6-11f111a2e30e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_static_harmonic_lapse_positive_conserved_flux
import Theorems.Thm_NoHair_positive_flux_static_end_point_compactification
import Definitions.Def_NoHair_staticReflectionAndCap

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

noncomputable section

theorem solution (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h)
    (hbound : HasStaticMinusInversionBound N h) :
    Nonempty (StaticMinusPointChart Ω N h) := by
  exact positive_flux_static_end_point_compactification Ω W N h c hbound
    (static_harmonic_lapse_positive_conserved_flux Ω W N h c)
