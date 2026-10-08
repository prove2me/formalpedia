-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.theorem1_global_optimality
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T10:28:09.2215+00:00
-- url     : https://prove2.me/submissions/ce1cf3e3-31f8-4fe7-a2b0-fe4f12bdfbf8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem1_global_optimality_base
import Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem1_global_optimality_step
import Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem1_global_optimality_assembly

open MeasureTheory ProbabilityTheory
open NestedSeatAlloc.IntPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (hM : IsSeatModel P X f)
    (hp : IsProtectionPolicy p) (h20 : SubdiffCondition P X f p) :
    IsOptimal P X f p := by
  apply theorem1_global_optimality_assembly P X f p hM hp h20
  · have hbase := theorem1_global_optimality_base P X f p hM hp
    exact hbase
  · intro k s hk hs h20k hprev q hq
    have hstep := theorem1_global_optimality_step P X f p k s hM hp hk hs h20k hprev q hq
    exact hstep
