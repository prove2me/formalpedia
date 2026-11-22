-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanMarkedDoubleIntegralMap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T22:06:25.861524+00:00
-- url     : https://prove2.me/submissions/5fd2d52e-3bba-4bdc-bb60-8c1894cf7db9

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Ω → ℝ × Bool) (Z : Ω → ℝ)
    (g : (ℝ × Bool) × ℝ → ℝ)
    (hT : Measurable T) (hZ : Measurable Z)
    (hg : Measurable g) :
    (∫ a, ∫ z, g (a, z) ∂P.map Z ∂P.map T) =
      (∫ ω, ∫ ξ, g (T ω, Z ξ) ∂P ∂P) := by
  have hInner (a : ℝ × Bool) :
      (∫ z, g (a, z) ∂P.map Z) =
        (∫ ξ, g (a, Z ξ) ∂P) := by
    apply integral_map hZ.aemeasurable
    exact (hg.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hOuter :
      Measurable (fun a : ℝ × Bool => ∫ z, g (a, z) ∂P.map Z) :=
    hg.stronglyMeasurable.integral_prod_right' |>.measurable
  calc
    (∫ a, ∫ z, g (a, z) ∂P.map Z ∂P.map T)
        = ∫ a, ∫ ξ, g (a, Z ξ) ∂P ∂P.map T := by
          simp_rw [hInner]
    _ = ∫ ω, ∫ ξ, g (T ω, Z ξ) ∂P ∂P := by
      apply integral_map hT.aemeasurable
      simpa only [hInner] using hOuter.aestronglyMeasurable
