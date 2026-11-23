-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.sourceReflectedPathRegularityAE
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T12:21:30.89966+00:00
-- url     : https://prove2.me/submissions/dbd7ee4a-47e7-40fa-bf06-d00325e2dcc4

import Mathlib.Topology.Order.LeftRight
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_no_positive_jumps
import Theorems.Thm_Kyprianou_Ch08_StageB_runningSup_path_structure_of_cadlag
import Theorems.Thm_Kyprianou_Ch08_StageB_reflected_regularity_of_cadlag_no_positive_jumps
import Theorems.Thm_AvramDividend_Classical_cadlag_no_downward_jumps_upperSemicontinuousOn_Icc
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Semicontinuity.Defs
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P) :
    ∀ᵐ ω ∂P,
      (∀ t : ℝ≥0,
        ContinuousWithinAt
          (fun s : ℝ≥0 => reflectAtSup D.X 0 s ω)
          (Set.Ici t) t) ∧
      (∀ z : ℝ≥0,
        UpperSemicontinuousOn
          (fun s : ℝ≥0 => reflectAtSup D.X 0 s ω)
          (Set.Icc 0 z)) := by
  filter_upwards [D.levy.cadlag_ae, source_result81_no_positive_jumps Ω P D] with ω hc hNoUp
  have hX0 : D.X 0 ω = 0 := by simpa using congrFun D.levy.start_zero ω
  have hstruct := Kyprianou.Ch08.StageB.runningSup_path_structure_of_cadlag D.X ω hc hX0
  have hreg := Kyprianou.Ch08.StageB.reflected_regularity_of_cadlag_no_positive_jumps
    D.X ω hc hX0 hstruct.1 hstruct.2.1 hstruct.2.2 hNoUp
  have hUSC (z : ℝ≥0) : UpperSemicontinuousOn (fun s : ℝ≥0 => reflectAtSup D.X 0 s ω) (Set.Icc 0 z) :=
    cadlag_no_downward_jumps_upperSemicontinuousOn_Icc
      (fun s : ℝ≥0 => reflectAtSup D.X 0 s ω) z hreg.1 hreg.2.1 hreg.2.2
  exact ⟨hreg.1, hUSC⟩
