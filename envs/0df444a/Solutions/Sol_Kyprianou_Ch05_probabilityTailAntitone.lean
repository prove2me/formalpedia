-- Prove2me | solution 1 for Kyprianou.Ch05.probabilityTailAntitone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:00:46.915521+00:00
-- url     : https://prove2.me/submissions/2c80ae87-9380-474c-b2e8-57ada660ec15

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess

open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Probability tail real values are antitone and lie in the unit interval. -/
theorem solution
    (F : Measure Real) [IsProbabilityMeasure F] :
    Antitone (fun t : Real => (F (Ioi t)).toReal) ∧
      (∀ t : Real, 0 ≤ (F (Ioi t)).toReal) ∧
      (∀ t : Real, (F (Ioi t)).toReal ≤ 1) := by
  refine ⟨?_,fun _ => ENNReal.toReal_nonneg,?_⟩
  · intro a b hab
    exact ENNReal.toReal_mono (measure_ne_top F _) (measure_mono (Ioi_subset_Ioi hab))
  · intro t
    simpa using ENNReal.toReal_mono (by simp : (1 : ENNReal) ≠ ⊤)
      (show F (Ioi t) ≤ 1 from (measure_mono (subset_univ _)).trans_eq (measure_univ (μ := F)))
