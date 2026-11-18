-- Prove2me | solution 1 for Kyprianou.Ch07.unitIncrementIntegrable_of_finiteMean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T08:18:17.808113+00:00
-- url     : https://prove2.me/submissions/a795bfa7-8970-4082-a5f8-159bbdaa95f1

import Mathlib
import Theorems.Thm_thm_7_11
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hMoment : Integrable (fun ω => |X 1 ω|) P)
    (s : ℝ≥0) :
    Integrable (fun ω => X (s + 1) ω - X s ω) P := by
  have hMeas1 : Measurable (X 1) := hX.1 1
  have hInt : Integrable (X 1) P := by
    apply (integrable_norm_iff hMeas1.aestronglyMeasurable).mp
    simpa only [Real.norm_eq_abs] using hMoment
  have hMeasD : Measurable (fun ω => X (s + 1) ω - X s ω) :=
    (hX.1 (s + 1)).sub (hX.1 s)
  have hLaw :
      P.map (fun ω => X (s + 1) ω - X s ω) = P.map (X 1) :=
    hX.2.2.1 s 1
  have hPushInt : Integrable (id : ℝ → ℝ) (P.map (X 1)) :=
    (thm_7_11 P hMeas1 measurable_id).1.mp (by simpa only [id_eq] using hInt)
  have hPushD : Integrable (id : ℝ → ℝ)
      (P.map (fun ω => X (s + 1) ω - X s ω)) := by
    simpa only [hLaw] using hPushInt
  have hD : Integrable (fun ω => id (X (s + 1) ω - X s ω)) P :=
    (thm_7_11 P hMeasD measurable_id).1.mpr hPushD
  simpa only [id_eq] using hD
