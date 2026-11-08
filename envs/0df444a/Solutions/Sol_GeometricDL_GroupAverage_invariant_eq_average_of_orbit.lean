-- Prove2me | solution 1 for GeometricDL.GroupAverage.invariant_eq_average_of_orbit
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:30:23.113187+00:00
-- url     : https://prove2.me/submissions/77002587-73a2-42f1-a3aa-0ac061e7787b

import Mathlib
import Definitions.Def_GeometricDL_GroupAverage_IsGInvariant
open MeasureTheory

open GeometricDL.GroupAverage in
theorem solution {G : Type*} [Group G] [MeasurableSpace G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (μ : Measure G) [IsFiniteMeasure μ] [NeZero μ]
    (ρ : G →* (E →L[ℝ] E)) (f : E → Y) (hf : IsGInvariant ρ f) (x : E) :
    f x = (μ Set.univ).toReal⁻¹ • ∫ g, f (ρ g x) ∂μ := by
  have h1 : (fun g => f (ρ g x)) = fun _ => f x := funext (fun g => hf g x)
  rw [h1, integral_const, smul_smul, measureReal_def]
  have hne : μ Set.univ ≠ 0 := Measure.measure_univ_ne_zero.mpr (NeZero.ne μ)
  have hpos : (μ Set.univ).toReal ≠ 0 :=
    (ENNReal.toReal_pos hne (measure_ne_top μ _)).ne'
  rw [inv_mul_cancel₀ hpos, one_smul]
