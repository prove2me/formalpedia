-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_height_family_null_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:45:09.367056+00:00
-- url     : https://prove2.me/submissions/3344ba45-713e-4892-8758-1422fc82b035

import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_filtered_avram_model
import Theorems.Thm_Kyprianou_Ch08_StageB_actual_height_effective_event_measurable
import Theorems.Thm_Kyprianou_Ch08_StageB_actual_height_no_drawdown_null_measurable_of_effective_event
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Strict record limit proof. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (l h : ℝ), 0 < l → 0 < h →
      NullMeasurableSet {ω | NoDrawdownBeforeUpcrossing D.X l h ω} P := by
  intro Ω mΩ P hP D ψ W hψ hW l h hl hh
  obtain ⟨F,A,hAX,hψA⟩ := source_result81_filtered_avram_model Ω P D ψ hψ
  exact actual_height_no_drawdown_null_measurable_of_effective_event A D hAX l h hl hh
    (actual_height_effective_event_measurable A l h hl hh)
