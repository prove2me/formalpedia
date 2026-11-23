-- Prove2me | solution 1 for Kyprianou.Ch02.prmMarkedIntegralMeasurableAmbientV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T13:44:04.290721+00:00
-- url     : https://prove2.me/submissions/d3c68897-68ba-4a3b-9296-3b56f1af5f51

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_prmMarkedIntegralMeasurableLocalEvalSigmaV1
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (R : Set (ℝ × ℝ)) (hRm : MeasurableSet R) :
    Measurable (fun ω => ∫ z in R, z.2 ∂(N.N ω)) := by
  classical
  have hlocal := Kyprianou.Ch02.prmMarkedIntegralMeasurableLocalEvalSigmaV1
    P ν N R hRm
  have hle :
      (⨆ C ∈ {C : Set (ℝ × ℝ) | C ⊆ R ∧ MeasurableSet C},
         MeasurableSpace.comap (fun ω => N.N ω C) inferInstance) ≤
      (inferInstance : MeasurableSpace Ω) := by
    refine iSup_le fun C => iSup_le fun hC => ?_
    exact (N.measurable_eval hC.2).comap_le
  exact hlocal.mono hle le_rfl
