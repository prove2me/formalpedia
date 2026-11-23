-- Prove2me | solution 3 for Kyprianou.Ch08.StageB.actualHeightSourceNoDrawdownNullMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T12:48:21.618376+00:00
-- url     : https://prove2.me/submissions/03487363-d4f5-4d07-9aa2-a7e2ba1bd377

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_law_positive_mgf
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_filtered_avram_model
import Theorems.Thm_Kyprianou_Ch08_StageB_actual_height_effective_event_measurable
import Theorems.Thm_Kyprianou_Ch08_StageB_actual_height_no_drawdown_null_measurable_of_effective_event
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) :
    ∀ h : ℝ, 0 < h →
      NullMeasurableSet
        {ω : Ω | NoDrawdownBeforeUpcrossing D.X 1 h ω} P := by
  let ψ := tripletLaplace (-D.triplet.drift)
    D.gaussianCoefficient D.triplet.levyMeasure
  have hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ := by
    intro β t hβ ht
    obtain ⟨hi, he⟩ :=
      source_result81_law_positive_mgf Ω P D t β hβ
    refine ⟨hi, ?_⟩
    change ψ β = Real.log
      (∫ ω, Real.exp (β * D.X t ω) ∂P) / (t : ℝ)
    rw [he, Real.log_exp,
      mul_div_cancel_left₀ _ (NNReal.coe_pos.mpr ht).ne']
  obtain ⟨F, A, hAX, _⟩ :=
    source_result81_filtered_avram_model Ω P D ψ hψ
  intro h hh
  exact actual_height_no_drawdown_null_measurable_of_effective_event
    A D hAX 1 h (by norm_num) hh
    (actual_height_effective_event_measurable
      A 1 h (by norm_num) hh)
