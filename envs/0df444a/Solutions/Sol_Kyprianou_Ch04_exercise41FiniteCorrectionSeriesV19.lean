-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41FiniteCorrectionSeriesV19
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:20:53.980313+00:00
-- url     : https://prove2.me/submissions/a0880899-37fc-4ec4-81f8-5ca07daf0454

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    {ι : Type} (d z : ι → ℝ)
    (hd : Set.Finite (Function.support d))
    (hz : Set.Finite (Function.support z)) :
    Summable (fun s => ‖d s - z s‖) ∧
    (∑' s, (d s - z s)) = (∑' s, d s) - (∑' s, z s) := by
  refine ⟨summable_of_hasFiniteSupport ((hd.union hz).subset ?_), ?_⟩
  · intro s hs
    by_contra hn
    have hds : d s = 0 := by simpa [Function.mem_support] using (fun h => hn (Or.inl h))
    have hzs : z s = 0 := by simpa [Function.mem_support] using (fun h => hn (Or.inr h))
    simp [Function.mem_support,hds,hzs] at hs
  · exact (summable_of_hasFiniteSupport hd).tsum_sub (summable_of_hasFiniteSupport hz)
