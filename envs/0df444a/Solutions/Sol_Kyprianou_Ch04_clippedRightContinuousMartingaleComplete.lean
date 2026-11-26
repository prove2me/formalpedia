-- Prove2me | solution 1 for Kyprianou.Ch04.clippedRightContinuousMartingaleComplete
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T10:59:12.064584+00:00
-- url     : https://prove2.me/submissions/ac84a716-4d46-4310-9678-062a4b2d6987

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_clippedRightContinuousAdapted
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_bounded_stop_eval_measurable
import Theorems.Thm_Kyprianou_Ch04_clippedRightContinuousMartingaleEventBalance
import Theorems.Thm_Kyprianou_Ch04_clippedClockCoe
import Theorems.Thm_Kyprianou_Ch04_kw47_martingale_of_event_increment_zero
open MeasureTheory Filter Set Topology Kyprianou.Ch04
open scoped NNReal
set_option autoImplicit false

/-- Bounded clipping preserves a right-continuous martingale in a usual filtration. -/
theorem solution {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (hRC : F.IsRightContinuous)
    (hNull : ∀ (s : NNReal) (N A : Set Ω), MeasurableSet N → P N = 0 →
      A ⊆ N → MeasurableSet[F s] A)
    (J : NNReal → Ω → ℝ) (hM : Martingale J F P)
    (hr : ∀ᵐ w ∂P, ∀ t : NNReal,
      ContinuousWithinAt (fun u => J u w) (Ici t) t)
    (tau : Ω → WithTop NNReal) (ht : IsStoppingTime F tau) :
    Martingale (fun (t : NNReal) w =>
      J ((min (tau w) (t : WithTop NNReal)).untopD t) w) F P := by
  have hA := clippedRightContinuousAdapted P F hNull J hM.stronglyAdapted hr tau ht
  have hMR : Martingale J F.rightCont P := by
    rwa [Filtration.IsRightContinuous.eq]
  have htR : IsStoppingTime F.rightCont tau := by
    rwa [Filtration.IsRightContinuous.eq]
  have h := clippedRightContinuousMartingaleEventBalance P F J hMR hr tau htR
  rw [Filtration.IsRightContinuous.eq] at h
  apply kw47_martingale_of_event_increment_zero P F _ hA h.1
  intro a b hab A hAm
  rw [integral_sub (h.1 a).integrableOn (h.1 b).integrableOn,h.2 a b hab A hAm,sub_self]
