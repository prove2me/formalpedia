-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41CadlagPhysicalJumpsCountableV17
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:16:34.868822+00:00
-- url     : https://prove2.me/submissions/41ba826b-8b38-4f49-a050-124a327d1134

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_cadlagNNRealDiscontinuitiesCountableV1
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    (x l : NNReal → ℝ)
    (hR : ∀ s, ContinuousWithinAt x (Ici s) s)
    (hL : ∀ s, 0 < s → Tendsto x (nhdsWithin s (Iio s)) (nhds (l s))) :
    Set.Countable {s : NNReal | 0 < s ∧ x s ≠ l s} := by
  apply (Kyprianou.Ch02.cadlagNNRealDiscontinuitiesCountableV1 x hR
    (fun s hs => ⟨l s,hL s hs⟩)).mono
  intro s hs hc
  letI : NeBot (nhdsWithin s (Iio s)) := nhdsLT_neBot_of_exists_lt ⟨0,hs.1⟩
  exact hs.2 (tendsto_nhds_unique hc.continuousWithinAt (hL s hs.1))
