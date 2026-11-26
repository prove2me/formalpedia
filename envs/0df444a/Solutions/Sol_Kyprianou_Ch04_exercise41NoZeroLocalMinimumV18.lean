-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41NoZeroLocalMinimumV18
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:36:01.631269+00:00
-- url     : https://prove2.me/submissions/dca49a74-d5f0-473a-8ba0-e6fb2b5a6b08

import Theorems.Thm_Kyprianou_Ch04_exercise41WindowInfimumNullV24
import Theorems.Thm_Kyprianou_Ch04_exercise41NoLocalMinimumFromNullWindowsV25
import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration NNReal inferInstance)
    (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift) :
    ∀ᵐ w ∂P, ∀ s : NNReal, 0 < s → L.X s w = 0 →
      ¬ (∃ e : NNReal, 0 < e ∧ ∀ u ∈ Icc (s - e) (s + e), 0 ≤ L.X u w) := by
  let q := TopologicalSpace.denseSeq NNReal
  have hq : DenseRange q := TopologicalSpace.denseRange_denseSeq NNReal
  have h (j : ℕ) := exercise41WindowInfimumNullV24 P F L hBV hd q (q j)
  filter_upwards [ae_all_iff.mpr h] with w hw
  exact exercise41NoLocalMinimumFromNullWindowsV25 (fun t => L.X t w) q hq (L.rightCont w) hw

