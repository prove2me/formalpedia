-- Prove2me | solution 1 for Kyprianou.Ch01.independentLevySum
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:39:01.255992+00:00
-- url     : https://prove2.me/submissions/15ff8f17-1eca-4695-972c-e68ad71afe03
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch01_independentLevySum_zero
import Theorems.Thm_Kyprianou_Ch01_independentLevySum_cadlag
import Theorems.Thm_Kyprianou_Ch01_independentLevySum_indepIncrements
import Theorems.Thm_Kyprianou_Ch01_independentLevySum_stationaryIncrements
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : ℝ≥0 → Ω → ℝ)
    (hX : IsLevyProcess X P)
    (hY : IsLevyProcess Y P)
    (hXY : IndepFun (fun ω => fun t => X t ω)
      (fun ω => fun t => Y t ω) P) :
    IsLevyProcess (fun t ω => X t ω + Y t ω) P := by
  exact ⟨
    Kyprianou.Ch01.independentLevySum_zero P X Y hX hY,
    Kyprianou.Ch01.independentLevySum_indepIncrements P X Y hX hY hXY,
    Kyprianou.Ch01.independentLevySum_stationaryIncrements P X Y hX hY hXY,
    Kyprianou.Ch01.independentLevySum_cadlag P X Y hX hY⟩
