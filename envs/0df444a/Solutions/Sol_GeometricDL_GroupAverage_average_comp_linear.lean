-- Prove2me | solution 1 for GeometricDL.GroupAverage.average_comp_linear
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:36:02.13263+00:00
-- url     : https://prove2.me/submissions/50242dac-cc1f-41b5-92be-a2923c5d3a55

import Mathlib
open MeasureTheory

theorem solution {G : Type*} [Group G] [MeasurableSpace G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (μ : Measure G) (ρ : G →* (E →L[ℝ] E)) (f : E →L[ℝ] Y) (x : E)
    (hx : Integrable (fun g => ρ g x) μ) :
    (μ Set.univ).toReal⁻¹ • ∫ g, f (ρ g x) ∂μ = f ((μ Set.univ).toReal⁻¹ • ∫ g, ρ g x ∂μ) := by
  rw [ContinuousLinearMap.integral_comp_comm f hx, map_smul]
