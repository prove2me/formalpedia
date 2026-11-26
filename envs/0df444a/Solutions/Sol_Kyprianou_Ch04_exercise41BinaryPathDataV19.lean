-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41BinaryPathDataV19
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:21:00.87413+00:00
-- url     : https://prove2.me/submissions/1fb80516-2b17-4a80-a387-b7156e3581b7

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41IndicatorRightV17
import Theorems.Thm_Kyprianou_Ch04_exercise41IndicatorLeftV17
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
    (hL : ∀ s, 0 < s → Tendsto x (nhdsWithin s (Iio s)) (nhds (l s)))
    (hNoJump : ∀ s, 0 < s → Function.leftLim x s = 0 → x s = 0)
    (hDep : ∀ s, x s = 0 → ∃ e : NNReal, 0 < e ∧
      ∀ u : NNReal, 0 < u → u < e → 0 < x (s+u))
    (hArr : ∀ s, 0 < s → x s = 0 → Function.leftLim x s = 0 →
      ∃ e : NNReal, 0 < e ∧ ∀ u : NNReal, 0 < u →
        u < min e s → x (s-u) < 0) :
    let f := fun u => if x u < 0 then (-1 : ℝ) else 0
    (∀ s, ContinuousWithinAt f (Ici s) s) ∧
    (∀ s, 0 < s → Tendsto f (nhdsWithin s (Iio s)) (nhds (Function.leftLim f s))) ∧
    (∀ s, 0 < s → Function.leftLim f s = (if 0 < l s then 0 else -1)) := by
  dsimp only
  refine ⟨fun s => exercise41IndicatorRightV17 x s (hR s) (hDep s), ?_, ?_⟩
  all_goals
    intro s hs
    letI : NeBot (nhdsWithin s (Iio s)) := nhdsLT_neBot_of_exists_lt ⟨0,hs⟩
    have hxl := leftLim_eq_of_tendsto (hL s hs)
    have H := exercise41IndicatorLeftV17 x s hs (l s) (hL s hs) (fun hz =>
      hArr s hs (hNoJump s hs (hxl.trans hz)) (hxl.trans hz))
    have he := leftLim_eq_of_tendsto H
  · rw [he]
    exact H
  · exact he
