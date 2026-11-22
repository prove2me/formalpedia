-- Prove2me | solution 1 for Kyprianou.Ch01.rightNaturalClippedSupermartingaleExpectedBound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:35:10.314979+00:00
-- url     : https://prove2.me/submissions/63a83c82-260e-423e-881e-907bc5374c61

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Theorems.Thm_Kyprianou_Ch01_rightNaturalStoppingMinTimeFinite
import Theorems.Thm_MarkovProcess_integral_stoppedValue_le_of_le

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Finite clipped optional sampling in the exact right-natural filtration. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y M : ℝ≥0 → Ω → ℝ)
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (hF : ∀ t, F t = naturalSigmaRight Y t)
    (hSM : Supermartingale M F P)
    (C : ℝ) (hC : ∀ t ω, ‖M t ω‖ ≤ C)
    (hright : ∀ ω v, ContinuousWithinAt (fun t : ℝ≥0 => M t ω) (Set.Ici v) v)
    (tau : Ω → WithTop ℝ≥0)
    (hTau : IsNaturalRightStoppingTime Y tau)
    (n : ℝ≥0) :
    (∫ ω, M ((min (tau ω) (n : WithTop ℝ≥0)).untopD n) ω ∂P) ≤
      ∫ ω, M 0 ω ∂P := by
  have hclip :=
    Kyprianou.Ch01.rightNaturalStoppingMinTimeFinite
      Y F hF tau hTau n
  dsimp only at hclip
  obtain ⟨hclock, hstopping, hbound⟩ := hclip
  exact MarkovProcess.integral_stoppedValue_le_of_le
    hSM hC hright hstopping hbound
