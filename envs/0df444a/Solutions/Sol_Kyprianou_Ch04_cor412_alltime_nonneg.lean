-- Prove2me | solution 1 for Kyprianou.Ch04.cor412_alltime_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:38:30.855798+00:00
-- url     : https://prove2.me/submissions/19dad1a7-9211-40b5-b7b1-3a2060635076

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_measurable
import Theorems.Thm_Kyprianou_Ch04_pathRunningInfimumLimit
import Theorems.Thm_Kyprianou_Ch04_infimumLimitSupport
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) :
    let B : Set Ω := {w | BddBelow (range (fun t : NNReal => L.X t w))}
    let D : Ω → ℝ := B.indicator (fun w => -sInf (range (fun t => L.X t w)))
    ∀ w, 0 ≤ D w := by
  classical
  intro B D
  intro w
  by_cases hw : w ∈ B
  · have h := csInf_le hw (show L.X 0 w ∈ range (fun t => L.X t w) from ⟨0,rfl⟩)
    rw [L.X_zero] at h
    simpa [D,hw] using neg_nonneg.mpr h
  · simp [D,hw]
