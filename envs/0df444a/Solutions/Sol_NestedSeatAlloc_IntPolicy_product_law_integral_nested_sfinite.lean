-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.product_law_integral_nested_sfinite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T14:06:28.487102+00:00
-- url     : https://prove2.me/submissions/c3a8218d-698b-4481-8357-8c88fc36e72b

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

theorem solution {Ω α β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure Ω) (U : Ω → α) (Z : Ω → β)
    (hU : Measurable U) (hZ : Measurable Z)
    (hsU : SFinite (Measure.map U P))
    (hsZ : SFinite (Measure.map Z P))
    (F : β × α → ℝ) (hF : Measurable F)
    (hjoint : Measure.map (fun ω => (Z ω, U ω)) P =
      (Measure.map Z P).prod (Measure.map U P))
    (hInt : Integrable F ((Measure.map Z P).prod (Measure.map U P))) :
    (∫ ω, F (Z ω, U ω) ∂P) =
      ∫ z, ∫ u, F (z, u) ∂(Measure.map U P) ∂(Measure.map Z P) := by
  letI : SFinite (Measure.map U P) := hsU
  letI : SFinite (Measure.map Z P) := hsZ
  have hZU : Measurable (fun ω => (Z ω, U ω)) := hZ.prodMk hU
  calc
    (∫ ω, F (Z ω, U ω) ∂P) =
        ∫ zu, F zu ∂(Measure.map (fun ω => (Z ω, U ω)) P) := by
      exact (integral_map hZU.aemeasurable hF.aestronglyMeasurable).symm
    _ = ∫ zu, F zu ∂((Measure.map Z P).prod (Measure.map U P)) := by
      rw [hjoint]
    _ = ∫ z, ∫ u, F (z, u) ∂(Measure.map U P) ∂(Measure.map Z P) := by
      exact integral_prod F hInt
