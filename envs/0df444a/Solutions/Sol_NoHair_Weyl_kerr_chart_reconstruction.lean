-- Prove2me | solution 1 for NoHair.Weyl.kerr_chart_reconstruction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T22:19:05.117802+00:00
-- url     : https://prove2.me/submissions/973d47b4-7240-410b-87a2-7670b436a22a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_NoHair_KerrNewmanEinstein_Atoms
import Theorems.Thm_NoHair_Weyl_kerr_radial_quadrature_values
import Theorems.Thm_NoHair_Weyl_kerr_local_weyl_coordinates
import Theorems.Thm_NoHair_Weyl_kerr_weyl_coefficient_identity

open NoHair NoHair.Weyl

theorem solution (m a : ℝ) (hm : IsKerrNewmanBlackHoleParams m a 0) :
    IsWeylRepresentation m a (kerrNewmanMetric m a 0) (kerrErnst m a) ∧
    ∀ y ∈ offAxisExterior m a, ∃ V c, y ∈ V ∧ IsKerrWeylChart m a V c := by
  obtain ⟨hquad, hvalues⟩ := kerr_radial_quadrature_values m a hm
  refine ⟨⟨hquad, ?_, ?_⟩, kerr_local_weyl_coordinates m a hm⟩
  · intro y hy
    change m + Real.sqrt (m^2-a^2-0^2) < ksRadius a y at hy
    have hr : 0 < ksRadius a y := lt_trans (add_pos_of_pos_of_nonneg hm.1 (Real.sqrt_nonneg _)) hy
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    exact continuousAt_const.add ((((KNE.hasCP_profile m a 0 y hr).diff.continuousAt).mul
      (ksNull_differentiableAt a y hr i).continuousAt).mul
      (ksNull_differentiableAt a y hr j).continuousAt)
  · intro V c hc y hy
    obtain ⟨hw, hh⟩ := hvalues (Real.log ((c y) 2), (c y) 3)
    exact kerr_weyl_coefficient_identity m a hm V c hc y hy hw hh
