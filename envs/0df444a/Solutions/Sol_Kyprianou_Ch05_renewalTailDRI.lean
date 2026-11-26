-- Prove2me | solution 1 for Kyprianou.Ch05.renewalTailDRI
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T19:00:43.516998+00:00
-- url     : https://prove2.me/submissions/f0d05dff-aff5-44b9-8d1c-27c5c673776c

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Theorems.Thm_Kyprianou_Ch05_renewalCutoffTailIntegrable
import Theorems.Thm_Kyprianou_Ch05_boundedCutoffAntitoneOscillation
import Theorems.Thm_Kyprianou_Ch05_boundedFunctionDRIFromOscillation
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- The truncated tail is integrable and its Darboux gap is at most twice the mesh. -/
theorem solution
    (F : Measure Real) [IsProbabilityMeasure F]
    (hSupport : F (Iio (0 : Real)) = 0)
    (hInt : Integrable (fun z : Real => z) F)
    (u y : Real) (hu : 0 < u) (hy : 0 < y) :
    DirectlyRiemannIntegrable
      (fun t : Real => if y < t then (F (Ioi (t + u))).toReal else 0) := by
  let g : Real → Real := fun t => (F (Ioi (t+u))).toReal
  have ha : Antitone g := by
    intro a b hab
    exact ENNReal.toReal_mono (measure_ne_top F _)
      (measure_mono (Ioi_subset_Ioi (by linarith : a+u ≤ b+u)))
  have hn (t : Real) : 0 ≤ g t := ENNReal.toReal_nonneg
  have hb (t : Real) : g t ≤ 1 := by
    simpa using ENNReal.toReal_mono (by simp : (1 : ENNReal) ≠ ⊤)
      (show F (Ioi (t+u)) ≤ 1 from (measure_mono (subset_univ _)).trans_eq (measure_univ (μ := F)))
  apply boundedFunctionDRIFromOscillation _
    (renewalCutoffTailIntegrable F hSupport hInt u y hu hy)
  · intro t
    split <;> first | exact hn t | exact le_rfl
  · intro t
    split <;> first | exact hb t | norm_num
  · exact fun d hd => boundedCutoffAntitoneOscillation g ha hn hb y d hd
