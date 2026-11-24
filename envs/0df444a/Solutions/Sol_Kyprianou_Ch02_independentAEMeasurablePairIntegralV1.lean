-- Prove2me | solution 1 for Kyprianou.Ch02.independentAEMeasurablePairIntegralV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:58:02.282875+00:00
-- url     : https://prove2.me/submissions/80727853-2560-46fe-ab70-458222511b3f

import Mathlib
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

theorem solution
    {Ω A B : Type} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (a : Ω → A) (b : Ω → B) (ha : AEMeasurable a P) (hb : AEMeasurable b P)
    (hind : IndepFun a b P)
    (F : A × B → ℂ) (hF : Measurable F) (C : ℝ) (hC : ∀ z, ‖F z‖ ≤ C) :
    (∫ ω, F (a ω, b ω) ∂P) = ∫ ω, (∫ ω', F (a ω, b ω') ∂P) ∂P := by
  letI : IsProbabilityMeasure (P.map a) := Measure.isProbabilityMeasure_map ha
  letI : IsProbabilityMeasure (P.map b) := Measure.isProbabilityMeasure_map hb
  have hFi : Integrable F ((P.map a).prod (P.map b)) :=
    Integrable.of_bound hF.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  calc
    (∫ ω, F (a ω, b ω) ∂P) = ∫ z, F z ∂((P.map a).prod (P.map b)) := by
      rw [← hind.map_prod_eq_prod_map_map ha hb]
      exact (integral_map (ha.prodMk hb) hF.aestronglyMeasurable).symm
    _ = ∫ x, ∫ y, F (x, y) ∂(P.map b) ∂(P.map a) := integral_prod F hFi
    _ = ∫ ω, ∫ y, F (a ω, y) ∂(P.map b) ∂P :=
      integral_map ha hF.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    _ = ∫ ω, ∫ ω', F (a ω, b ω') ∂P ∂P := by
      apply integral_congr_ae
      filter_upwards with ω
      exact integral_map hb (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
