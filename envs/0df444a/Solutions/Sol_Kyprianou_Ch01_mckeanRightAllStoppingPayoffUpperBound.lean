-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanRightAllStoppingPayoffUpperBound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T15:38:49.578603+00:00
-- url     : https://prove2.me/submissions/da72c604-1927-4702-ada3-a8e691cfdd14
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_mckeanDiscountedValueOptionalSamplingRight
import Theorems.Thm_Kyprianou_Ch01_mckeanValueMajorizesPutPayoff
import Theorems.Thm_Kyprianou_Ch01_mckeanPhiPositive

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
      (∫ ω, discountedPut X x K q tau ω ∂P) ≤
        mckeanValue K barrier phi x := by
  dsimp only
  let phi : ℝ :=
    (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) + gamma) /
      sigma ^ 2
  let barrier : ℝ := Real.log (K * phi / (1 + phi))
  change ∀ tau : Ω → WithTop ℝ≥0,
    IsNaturalRightStoppingTime (fun t ω => x + X t ω) tau →
      (∫ ω, discountedPut X x K q tau ω ∂P) ≤
        mckeanValue K barrier phi x
  intro tau hstop
  let Z : Ω → ℝ := fun ω =>
    match tau ω with
    | none => 0
    | some t => Real.exp (-q * (t : ℝ)) *
        mckeanValue K barrier phi (x + X t ω)
  have hphi : 0 < phi :=
    Kyprianou.Ch01.mckeanPhiPositive sigma gamma q hsigma hq
  have hsampling :=
    Kyprianou.Ch01.mckeanDiscountedValueOptionalSamplingRight
      P X sigma gamma K q x hsigma hK hq hB hXmeas hAllContinuous
      tau hstop
  change Integrable (discountedPut X x K q tau) P ∧
    Integrable Z P ∧
    (∫ ω, Z ω ∂P) ≤ mckeanValue K barrier phi x at hsampling
  obtain ⟨hputInt, hZInt, hZupper⟩ := hsampling
  have hpoint (ω : Ω) : discountedPut X x K q tau ω ≤ Z ω := by
    cases ht : tau ω with
    | top =>
        simp [discountedPut, Z, ht]
    | coe t =>
        have hmaj := Kyprianou.Ch01.mckeanValueMajorizesPutPayoff
          K phi (x + X t ω) hK hphi
        change max (K - Real.exp (x + X t ω)) 0 ≤
          mckeanValue K barrier phi (x + X t ω) at hmaj
        have hm := mul_le_mul_of_nonneg_left hmaj
          (le_of_lt (Real.exp_pos (-q * (t : ℝ))))
        simpa [discountedPut, Z, ht] using hm
  exact (integral_mono hputInt hZInt hpoint).trans hZupper
