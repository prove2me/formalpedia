-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41ArrivalFromNoMinimumV18
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:07:08.272161+00:00
-- url     : https://prove2.me/submissions/8b5c2681-5d3d-4cdd-a9b1-d89ea8318baa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch04_exercise41IsolatedZeroCutoffV13
import Theorems.Thm_Kyprianou_Ch04_exercise41NegativeBeforeZeroV22
import Theorems.Thm_Kyprianou_Ch04_exercise41ArrivalFromCutoffV22
import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    (x : NNReal → ℝ)
    (hR : ∀ s, ContinuousWithinAt x (Ici s) s)
    (hL : ∀ s, 0 < s → ∃ l, Tendsto x (nhdsWithin s (Iio s)) (nhds l))
    (hNeg : ∀ s l, 0 < s → Tendsto x (nhdsWithin s (Iio s)) (nhds l) → x s ≤ l)
    (hVisits : ∀ t : NNReal, Set.Finite {s : NNReal | 0 < s ∧ s ≤ t ∧ x s = 0})
    (hDep : ∀ s : NNReal, x s = 0 → ∃ e : NNReal, 0 < e ∧
      ∀ u : NNReal, 0 < u → u < e → 0 < x (s + u))
    (hMin : ∀ s : NNReal, 0 < s → x s = 0 →
      ¬ (∃ e : NNReal, 0 < e ∧ ∀ u ∈ Icc (s - e) (s + e), 0 ≤ x u)) :
    ∀ s : NNReal, 0 < s → x s = 0 → Function.leftLim x s = 0 →
      ∃ e : NNReal, 0 < e ∧ ∀ u : NNReal, 0 < u → u < min e s → x (s-u) < 0 := by
  let q := TopologicalSpace.denseSeq NNReal
  have hq : DenseRange q := TopologicalSpace.denseRange_denseSeq NNReal
  intro s hs hz _
  obtain ⟨j,hj,hjs,hgap⟩ := exercise41IsolatedZeroCutoffV13 x q hq s hs (hVisits s)
  obtain ⟨v,hv,hn⟩ := exercise41NegativeBeforeZeroV22 x (q j) s hjs hs hz (hDep s hz) (hMin s hs hz)
  exact exercise41ArrivalFromCutoffV22 x hR hL hNeg (q j) v s hv.1 hv.2 hn hgap

