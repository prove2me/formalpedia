-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanDiscountedValueOptionalSamplingRight
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:02:00.028635+00:00
-- url     : https://prove2.me/submissions/abde7ba3-147e-42cd-a229-f1c0773f4efb

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_rightNaturalStoppedPut_measurable_of_continuous
import Theorems.Thm_Kyprianou_Ch01_mckeanDiscountedValueRightStoppedExpectedUpper
import Theorems.Thm_Kyprianou_Ch01_discountedPut_integrable_of_measurable

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma K q x : ℝ)
    (hsigma : 0 < sigma) (hK : 0 < K) (hq : 0 < q)
    (hB : IsLinearBrownian P X sigma gamma)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (hAllContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω)) :
    let phi : ℝ :=
      (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) + gamma) /
        sigma ^ 2
    let barrier : ℝ := Real.log (K * phi / (1 + phi))
    ∀ tau : Ω → WithTop ℝ≥0,
      IsNaturalRightStoppingTime (fun t ω => x + X t ω) tau →
      let Z : Ω → ℝ := fun ω =>
        match tau ω with
        | none => 0
        | some t => Real.exp (-q * (t : ℝ)) *
            mckeanValue K barrier phi (x + X t ω)
      Integrable (discountedPut X x K q tau) P ∧
        Integrable Z P ∧
        (∫ ω, Z ω ∂P) ≤ mckeanValue K barrier phi x := by
  dsimp only
  intro tau hTau
  have hMeasPut :=
    Kyprianou.Ch01.rightNaturalStoppedPut_measurable_of_continuous
      X hXmeas hAllContinuous x K q tau hTau
  have hPutInt :=
    Kyprianou.Ch01.discountedPut_integrable_of_measurable
      P X x K q hK hq tau hMeasPut
  have hRest :=
    Kyprianou.Ch01.mckeanDiscountedValueRightStoppedExpectedUpper
      P X sigma gamma K q x hsigma hK hq hB hXmeas hAllContinuous
      tau hTau
  exact ⟨hPutInt, hRest.1, hRest.2⟩
