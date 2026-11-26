-- Prove2me | solution 1 for Kyprianou.Ch04.cor412_alltime_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:40:34.743724+00:00
-- url     : https://prove2.me/submissions/d4f73e85-4a3e-4651-8440-4f10f6fea3b9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_measurable
import Theorems.Thm_Kyprianou_Ch04_pathRunningInfimumLimit
import Theorems.Thm_Kyprianou_Ch04_infimumLimitSupport
import Theorems.Thm_Kyprianou_Ch04_cor412_alltime_meas_only
import Theorems.Thm_Kyprianou_Ch04_cor412_alltime_nonneg
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) :
    let B : Set Ω := {w | BddBelow (range (fun t : NNReal => L.X t w))}
    let D : Ω → ℝ := B.indicator (fun w => -sInf (range (fun t => L.X t w)))
    Measurable D ∧ ∀ w, 0 ≤ D w := by
  classical
  exact ⟨Kyprianou.Ch04.cor412_alltime_meas_only P F L,
    Kyprianou.Ch04.cor412_alltime_nonneg P F L⟩
