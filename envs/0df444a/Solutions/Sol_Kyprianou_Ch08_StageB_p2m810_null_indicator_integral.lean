-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_null_indicator_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:49:53.809708+00:00
-- url     : https://prove2.me/submissions/1dcbc81d-f0e9-495f-87a2-73ccf932a7d8


import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Strict record limit proof. -/
theorem solution :
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (g : Ω → ℝ) (A : Set Ω), Integrable g P → NullMeasurableSet A P →
      AEStronglyMeasurable (A.indicator g) P ∧
      (∫ ω, A.indicator g ω ∂P) = ∫ ω in A, g ω ∂P := by
  classical
  intro Ω mΩ P g A hg hA
  let B := toMeasurable P A
  have hB : MeasurableSet B := measurableSet_toMeasurable P A
  have hBA : B =ᵐ[P] A := hA.toMeasurable_ae_eq
  have he : B.indicator g =ᵐ[P] A.indicator g := by
    filter_upwards [hBA] with ω hω
    change (ω ∈ B) = (ω ∈ A) at hω
    change B.indicator g ω = A.indicator g ω
    by_cases h : ω ∈ B
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (Eq.mp hω h)]
    · have ha : ω ∉ A := fun hm => h (Eq.mpr hω hm)
      rw [Set.indicator_of_notMem h, Set.indicator_of_notMem ha]
  refine ⟨(hg.aestronglyMeasurable.indicator hB).congr he, ?_⟩
  rw [← integral_congr_ae he,integral_indicator hB,Measure.restrict_congr_set hBA]
