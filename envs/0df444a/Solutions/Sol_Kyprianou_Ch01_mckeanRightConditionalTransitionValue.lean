-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanRightConditionalTransitionValue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T21:12:38.618489+00:00
-- url     : https://prove2.me/submissions/c43bb907-7da7-42ed-bc22-1162990e2811

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_levyIncrement_indep_naturalSigmaRight
import Theorems.Thm_Kyprianou_Ch01_boundedIndependentIncrementConditionalMixingFiltration
import Theorems.Thm_Kyprianou_Ch01_levyIncrement_McKeanIntegralStationary
import Theorems.Thm_Kyprianou_Ch01_naturalSigmaRight_measurable_past
import Theorems.Thm_Kyprianou_Ch01_naturalSigmaRight_le_ambient
import Theorems.Thm_Kyprianou_Ch01_mckeanValue_measurable
import Theorems.Thm_Kyprianou_Ch01_mckeanValueBoundedNonnegative
import Theorems.Thm_Kyprianou_Ch01_mckeanPhiPositive

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Right-natural Brownian transition formula by independent increments and stationarity. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma K q x : ℝ)
    (hsigma : 0 < sigma) (hK : 0 < K) (hq : 0 < q)
    (hB : IsLinearBrownian P X sigma gamma)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (hAllContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω))
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (hF : ∀ t, F t = naturalSigmaRight (fun u ω => x + X u ω) t) :
    let phi : ℝ :=
      (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) + gamma) / sigma ^ 2
    let barrier : ℝ := Real.log (K * phi / (1 + phi))
    ∀ s t : ℝ≥0, s ≤ t →
      P[(fun ω => Real.exp (-q * (t : ℝ)) *
        mckeanValue K barrier phi (x + X t ω)) | F s] =ᵐ[P]
      (fun ω => Real.exp (-q * (t : ℝ)) *
        ∫ ξ, mckeanValue K barrier phi
          ((x + X s ω) + X (t - s) ξ) ∂P) := by
  dsimp only
  let phi : ℝ :=
    (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) + gamma) / sigma ^ 2
  let b : ℝ := Real.log (K * phi / (1 + phi))
  have hphi : 0 < phi :=
    Kyprianou.Ch01.mckeanPhiPositive sigma gamma q hsigma hq
  intro s t hst
  let d : ℝ := Real.exp (-q * (t : ℝ))
  let Y : Ω → ℝ := fun ω => x + X s ω
  let Z : Ω → ℝ := fun ω => X t ω - X s ω
  let f : ℝ → ℝ := fun z => d * mckeanValue K b phi z
  have hYm : @Measurable Ω ℝ (F s) inferInstance Y := by
    rw [hF s]
    exact Kyprianou.Ch01.naturalSigmaRight_measurable_past
      (fun u ω => x + X u ω) s s le_rfl
  have hIndep : Indep (MeasurableSpace.comap Z inferInstance) (F s) P := by
    rw [hF s]
    exact Kyprianou.Ch01.levyIncrement_indep_naturalSigmaRight
      P X x hB.1 hXmeas hAllContinuous s t hst
  have hFmz : Measurable Z := (hXmeas t).sub (hXmeas s)
  have hf : Measurable f :=
    measurable_const.mul (Kyprianou.Ch01.mckeanValue_measurable K b phi)
  have hBound (z : ℝ) : ‖f z‖ ≤ d * K := by
    have hv := Kyprianou.Ch01.mckeanValueBoundedNonnegative
      K phi z hK hphi
    change 0 ≤ mckeanValue K b phi z ∧ mckeanValue K b phi z ≤ K at hv
    change ‖d * mckeanValue K b phi z‖ ≤ d * K
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _),
      abs_of_nonneg hv.1]
    exact mul_le_mul_of_nonneg_left hv.2 (Real.exp_nonneg _)
  have hMix :=
    Kyprianou.Ch01.boundedIndependentIncrementConditionalMixingFiltration
      P F s Y Z f (d * K)
      hYm hFmz hf hBound hIndep
  have hLeft :
      (fun ω => f (Y ω + Z ω)) =
        (fun ω => d * mckeanValue K b phi (x + X t ω)) := by
    funext ω
    dsimp [f, Y, Z]
    congr 1
    ring
  have hRight :
      (fun ω => ∫ ξ, f (Y ω + Z ξ) ∂P) =
        (fun ω => d * (∫ ξ, mckeanValue K b phi
          ((x + X s ω) + X (t - s) ξ) ∂P)) := by
    funext ω
    dsimp [f, Y, Z]
    rw [integral_const_mul]
    congr 1
    exact Kyprianou.Ch01.levyIncrement_McKeanIntegralStationary
      P X hB.1 s t hst K b phi (x + X s ω)
  rw [hLeft, hRight] at hMix
  exact hMix
