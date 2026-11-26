-- Prove2me | solution 1 for Kyprianou.Ch05.renewalCutoffTailIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:00:49.874108+00:00
-- url     : https://prove2.me/submissions/1e8451ba-2d2d-4815-9be3-5364623ccca5

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_realPositiveTailIntegrable
import Theorems.Thm_Kyprianou_Ch05_cutoffShiftTailIntegrable
import Theorems.Thm_Kyprianou_Ch05_probabilityTailAntitone
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- The shifted truncated tail is dominated by the integrable positive tail. -/
theorem solution
    (F : Measure Real) [IsProbabilityMeasure F]
    (hSupport : F (Iio (0 : Real)) = 0)
    (hInt : Integrable (fun z : Real => z) F)
    (u y : Real) (hu : 0 < u) (hy : 0 < y) :
    Integrable (fun t : Real => if y < t then (F (Ioi (t+u))).toReal else 0) := by
  obtain ⟨ha,hn,_⟩ := probabilityTailAntitone F
  exact cutoffShiftTailIntegrable _ ha hn (realPositiveTailIntegrable F hInt) u y hu hy
