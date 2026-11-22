-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanBrownianDiscountedSemigroupExcessive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T20:46:18.803802+00:00
-- url     : https://prove2.me/submissions/e6e19c9d-5587-4acb-b267-de7b1f7fbc17

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_mckeanPhiPositive
import Theorems.Thm_Kyprianou_Ch01_mckeanAffineExponentialSupportingMajorant
import Theorems.Thm_Kyprianou_Ch01_brownianMcKeanNegativeRootExponentialMean
import Theorems.Thm_Kyprianou_Ch01_mckeanValueBoundedNonnegative
import Theorems.Thm_Kyprianou_Ch01_mckeanValue_measurable
import Theorems.Thm_Kyprianou_Ch01_affineExpSupportDiscountedIntegralBound

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Brownian q-excessivity follows from the proved affine-support integral engine. -/
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
      (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) + gamma) / sigma ^ 2
    let barrier : ℝ := Real.log (K * phi / (1 + phi))
    ∀ s t : ℝ≥0, s ≤ t → ∀ y : ℝ,
      Real.exp (-q * (t : ℝ)) *
        (∫ ξ, mckeanValue K barrier phi (y + X (t - s) ξ) ∂P)
      ≤ Real.exp (-q * (s : ℝ)) * mckeanValue K barrier phi y := by
  dsimp only
  let phi : ℝ :=
    (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) + gamma) / sigma ^ 2
  let b : ℝ := Real.log (K * phi / (1 + phi))
  have hphi : 0 < phi :=
    Kyprianou.Ch01.mckeanPhiPositive sigma gamma q hsigma hq
  intro s t hst y
  let u : ℝ := min y b
  let A : ℝ := K - (1 + 1 / phi) * Real.exp u
  let B : ℝ := Real.exp u / phi
  have hAff :
      0 ≤ A ∧ 0 ≤ B ∧
      mckeanValue K b phi y =
        A + B * Real.exp (-phi * (y - u)) ∧
      ∀ z, mckeanValue K b phi z ≤
        A + B * Real.exp (-phi * (z - u)) :=
    Kyprianou.Ch01.mckeanAffineExponentialSupportingMajorant
      K phi y hK hphi
  rcases hAff with ⟨hA, _hB, hTouch, hMaj⟩
  let delta : ℝ≥0 := t - s
  have hMoment :
      Integrable (fun ξ => Real.exp (-phi * X delta ξ - q * (delta : ℝ))) P ∧
      (∫ ξ, Real.exp (-phi * X delta ξ - q * (delta : ℝ)) ∂P) = 1 :=
    Kyprianou.Ch01.brownianMcKeanNegativeRootExponentialMean
      P X sigma gamma q hsigma hq hB hXmeas delta
  have hNorm (z : ℝ) : ‖mckeanValue K b phi z‖ ≤ K := by
    have hv := Kyprianou.Ch01.mckeanValueBoundedNonnegative
      K phi z hK hphi
    change 0 ≤ mckeanValue K b phi z ∧ mckeanValue K b phi z ≤ K at hv
    rw [Real.norm_eq_abs, abs_of_nonneg hv.1]
    exact hv.2
  have hCore :
      Real.exp (-q * (delta : ℝ)) *
        (∫ ξ, mckeanValue K b phi (y + X delta ξ) ∂P)
      ≤ mckeanValue K b phi y :=
    Kyprianou.Ch01.affineExpSupportDiscountedIntegralBound
      P (X delta) (mckeanValue K b phi) K q phi y u A B delta
      hK.le hq.le hA (hXmeas delta)
      (Kyprianou.Ch01.mckeanValue_measurable K b phi)
      hNorm hMaj hTouch hMoment
  have htReal : ((t - s : ℝ≥0) : ℝ) + (s : ℝ) = (t : ℝ) := by
    exact_mod_cast tsub_add_cancel_of_le hst
  have hDisc :
      Real.exp (-q * (t : ℝ)) =
        Real.exp (-q * (s : ℝ)) * Real.exp (-q * (delta : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [delta]
    nlinarith [htReal]
  calc
    Real.exp (-q * (t : ℝ)) *
        (∫ ξ, mckeanValue K b phi (y + X (t - s) ξ) ∂P)
      = Real.exp (-q * (s : ℝ)) *
          (Real.exp (-q * (delta : ℝ)) *
            (∫ ξ, mckeanValue K b phi (y + X delta ξ) ∂P)) := by
          rw [hDisc]
          ring
    _ ≤ Real.exp (-q * (s : ℝ)) * mckeanValue K b phi y :=
      mul_le_mul_of_nonneg_left hCore (Real.exp_nonneg _)
