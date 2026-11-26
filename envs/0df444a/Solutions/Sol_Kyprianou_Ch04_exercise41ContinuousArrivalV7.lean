-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41ContinuousArrivalV7
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:18:03.450393+00:00
-- url     : https://prove2.me/submissions/f5db6627-2ccb-48dd-b6e7-7e39ed9cb955
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch04_exercise41NoZeroLocalMinimumV18
import Theorems.Thm_Kyprianou_Ch04_exercise41ArrivalFromNoMinimumV18
import Theorems.Thm_Kyprianou_Ch04_exercise41ZeroVisitsLocallyFiniteV1
import Theorems.Thm_Kyprianou_Ch04_exercise41PositiveDepartureV7
import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

open Kyprianou.Ch04
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration NNReal inferInstance)
    (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift) :
    ∀ᵐ w ∂P, ∀ s : NNReal, 0 < s → L.X s w = 0 →
      Function.leftLim (fun t => L.X t w) s = 0 →
      ∃ ε : NNReal, 0 < ε ∧ ∀ u : NNReal, 0 < u →
        u < min ε s → L.X (s - u) w < 0 := by
  filter_upwards [exercise41NoZeroLocalMinimumV18 P F L hBV hd,
    exercise41ZeroVisitsLocallyFiniteV1 P F L hBV hd,
    exercise41PositiveDepartureV7 P F L hBV hd] with w hm hv hp
  exact exercise41ArrivalFromNoMinimumV18 (fun s => L.X s w)
    (L.rightCont w) (L.leftLim w) (L.noPosJumps w) hv hp hm
