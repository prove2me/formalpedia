-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m87_qpos_two_sided_occupation_sections_measurable_for_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T04:34:39.243153+00:00
-- url     : https://prove2.me/submissions/28f538ee-724d-4268-9994-3e64e46eb23a

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_filtered_avram_model
import Theorems.Thm_Kyprianou_Ch08_StageB_qzero_avram_upper_shifted_clock_eq
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_avram_source_lower_clock_eq
import Theorems.Thm_AvramDividend_Classical_chat03_both_named_passage_clocks_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_Kyprianou_Ch08_StageB_qzero_killed_two_sided_occupation_sections_measurable
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    ∀ (a x : ℝ), 0 < a → 0 ≤ x → x ≤ a →
    ∀ (A : Set ℝ), MeasurableSet A →
      Measurable (fun t : ℝ≥0 =>
        P {ω | (t : WithTop ℝ≥0) <
          min (tauMinus (shifted D.X x) 0 ω)
            (tauPlus (shifted D.X x) a ω) ∧
          shifted D.X x t ω ∈ A}) := by
  exact Kyprianou.Ch08.StageB.qzero_killed_two_sided_occupation_sections_measurable
