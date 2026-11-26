-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41DeterministicFutureProductV19
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:20:59.766325+00:00
-- url     : https://prove2.me/submissions/9dd35cde-6540-421a-bf5f-785b0cbadbde

import Mathlib
import Theorems.Thm_AvramDividend_Classical_finite_time_state_future_product_of_cylinders
import Theorems.Thm_AvramDividend_Classical_finite_future_increment_sigma_indep_past
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_full_future_source_law
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal inferInstance) (L : SpectrallyNegativeLevy P F) (s : NNReal) :
    Measure.map (fun w => (L.X s w, fun t : NNReal => L.X (s+t) w - L.X s w)) P =
      (Measure.map (L.X s) P).prod (Measure.map (fun w t => L.X t w) P) := by
  rw [finite_time_state_future_product_of_cylinders L s (L.X s) (L.adapted s)
    (finite_future_increment_sigma_indep_past L s)]
  rw [avram_wave6_03_original_rightCont_stopped_full_future_source_law L (fun _ => s)
    (fun t => @MeasurableSet.const Ω (F.rightCont t) (s ≤ t))]
