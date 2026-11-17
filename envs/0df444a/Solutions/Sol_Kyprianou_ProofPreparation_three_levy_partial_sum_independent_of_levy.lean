-- Prove2me | solution 1 for Kyprianou.ProofPreparation.three_levy_partial_sum_independent_of_levy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T23:27:19.231421+00:00
-- url     : https://prove2.me/submissions/cd937e17-4890-473e-b860-a3c31670e8a4

import Theorems.Thm_Kyprianou_ProofPreparation_levy_two_component_finite_sets_independent
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false
open Kyprianou Kyprianou.ProofPreparation

private theorem levy_fixed_time_aemeasurable
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : IsLevyProcess X P) (t : ℝ≥0) :
    AEMeasurable (X t) P := by
  have hs := (hX.stationary_increments 0 t).aemeasurable_fst
  have hz (ω : Ω) : X 0 ω = 0 := congrFun hX.start_zero ω
  change AEMeasurable (fun ω => X (0 + t) ω - X 0 ω) P at hs
  simpa [hz] using hs

/-- Finite dimensional independence of two-component sums and the
    third component, with distinct finite observation sets allowed. -/

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Xgauss Xlarge Xsmall : ℝ≥0 → Ω → ℝ)
    (hgauss : IsLevyProcess Xgauss P)
    (hlarge : IsLevyProcess Xlarge P)
    (hsmall : IsLevyProcess Xsmall P)
    (hind : Kyprianou.IndependentLevyItoComponents P Xgauss Xlarge Xsmall) :
    IndepFun
      (fun ω => fun t => Xgauss t ω + Xlarge t ω)
      (fun ω => fun t => Xsmall t ω) P := by
  have hX : ∀ t : ℝ≥0,
      AEMeasurable (fun ω => Xgauss t ω + Xlarge t ω) P := by
    intro t
    exact (levy_fixed_time_aemeasurable P Xgauss hgauss t).add
      (levy_fixed_time_aemeasurable P Xlarge hlarge t)
  have hY : ∀ t : ℝ≥0, AEMeasurable (Xsmall t) P :=
    fun t => levy_fixed_time_aemeasurable P Xsmall hsmall t
  exact ProbabilityTheory.IndepFun.process_indepFun_process₀
    hX hY (fun I J =>
      levy_two_component_finite_sets_independent
        P Xgauss Xlarge Xsmall hgauss hlarge hsmall hind I J)
