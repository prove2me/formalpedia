-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanRightClippedDiscountedValueMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T18:55:24.591619+00:00
-- url     : https://prove2.me/submissions/586df2b1-c0f8-48d7-ada2-03581a91801a

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_rightNaturalStoppingMinTimeFinite
import Theorems.Thm_Kyprianou_Ch01_mckeanDiscountedValue_rightStoppedMeasurable

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Finite clipped stopping times permit measurable sampled values. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ)
    (x K q phi : ℝ)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (hAllContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω))
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (hF : ∀ t, F t = naturalSigmaRight (fun u ω => x + X u ω) t)
    (tau : Ω → WithTop ℝ≥0)
    (hTau : IsNaturalRightStoppingTime (fun t ω => x + X t ω) tau)
    (n : ℕ) :
    let barrier := Real.log (K * phi / (1 + phi))
    let T : Ω → ℝ≥0 := fun ω =>
      (min (tau ω) (((n : ℝ≥0)) : WithTop ℝ≥0)).untopD (n : ℝ≥0)
    Measurable (fun ω : Ω =>
      Real.exp (-q * (T ω : ℝ)) *
        mckeanValue K barrier phi (x + X (T ω) ω)) := by
  dsimp only
  let Y : ℝ≥0 → Ω → ℝ := fun t ω => x + X t ω
  let T : Ω → ℝ≥0 := fun ω =>
    (min (tau ω) (((n : ℝ≥0)) : WithTop ℝ≥0)).untopD (n : ℝ≥0)
  have hClip :=
    Kyprianou.Ch01.rightNaturalStoppingMinTimeFinite
      Y F hF tau hTau (n : ℝ≥0)
  dsimp only at hClip
  have hStop : IsStoppingTime F
      (fun ω => ((T ω : ℝ≥0) : WithTop ℝ≥0)) :=
    hClip.2.1
  have hRight : IsNaturalRightStoppingTime Y
      (fun ω => ((T ω : ℝ≥0) : WithTop ℝ≥0)) := by
    intro t
    rw [← hF t]
    exact hStop t
  have hMeas :=
    Kyprianou.Ch01.mckeanDiscountedValue_rightStoppedMeasurable
      X x K q phi hXmeas hAllContinuous
        (fun ω => ((T ω : ℝ≥0) : WithTop ℝ≥0)) hRight
  dsimp only at hMeas
  change Measurable (fun ω : Ω =>
      Real.exp (-q * (T ω : ℝ)) *
        mckeanValue K (Real.log (K * phi / (1 + phi))) phi
          (x + X (T ω) ω)) at hMeas
  exact hMeas
