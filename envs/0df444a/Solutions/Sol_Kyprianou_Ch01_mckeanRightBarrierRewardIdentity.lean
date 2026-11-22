-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanRightBarrierRewardIdentity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T15:35:47.937232+00:00
-- url     : https://prove2.me/submissions/c1299d27-2f9f-4468-b0c8-9b816c1857ed

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_mckeanPhiPositive
import Theorems.Thm_Kyprianou_Ch01_mckeanExpectedPutAboveBarrier
import Theorems.Thm_Kyprianou_Ch01_mckeanExpectedPutAtOrBelowBarrier

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
    let tauStar : Ω → WithTop ℝ≥0 :=
      firstLowerPassage X x barrier
    Integrable (discountedPut X x K q tauStar) P ∧
      (∫ ω, discountedPut X x K q tauStar ω ∂P) =
        mckeanValue K barrier phi x := by
  dsimp only
  let phi : ℝ :=
    (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) + gamma) /
      sigma ^ 2
  let barrier : ℝ := Real.log (K * phi / (1 + phi))
  change Integrable (discountedPut X x K q
      (firstLowerPassage X x barrier)) P ∧
    (∫ ω, discountedPut X x K q
      (firstLowerPassage X x barrier) ω ∂P) =
        mckeanValue K barrier phi x
  have hphi : 0 < phi := by
    dsimp [phi]
    exact Kyprianou.Ch01.mckeanPhiPositive sigma gamma q hsigma hq
  have hden : 0 < 1 + phi := by linarith
  have harg : 0 < K * phi / (1 + phi) :=
    div_pos (mul_pos hK hphi) hden
  have hexp : Real.exp barrier = K * phi / (1 + phi) := by
    dsimp [barrier]
    exact Real.exp_log harg
  have hKbarrier : Real.exp barrier ≤ K := by
    rw [hexp]
    apply (div_le_iff₀ hden).2
    nlinarith [hK]
  rcases lt_trichotomy x barrier with hlt | heq | hgt
  · have hbelow :=
      Kyprianou.Ch01.mckeanExpectedPutAtOrBelowBarrier
        P X sigma gamma K q x barrier
        hsigma hK hq hlt.le hKbarrier hB hXmeas
    have hvalue : mckeanValue K barrier phi x =
        K - Real.exp x := by
      simp [mckeanValue, hlt]
    rw [hvalue]
    exact hbelow
  · subst x
    have hbelow :=
      Kyprianou.Ch01.mckeanExpectedPutAtOrBelowBarrier
        P X sigma gamma K q barrier barrier
        hsigma hK hq (le_refl barrier) hKbarrier hB hXmeas
    have hvalue : mckeanValue K barrier phi barrier =
        K - Real.exp barrier := by
      simp [mckeanValue]
    rw [hvalue]
    exact hbelow
  · have habove :=
      Kyprianou.Ch01.mckeanExpectedPutAboveBarrier
        P X sigma gamma K q x barrier
        hsigma hq hgt hKbarrier hB hXmeas hAllContinuous
    have hvalue : mckeanValue K barrier phi x =
        (K - Real.exp barrier) *
          Real.exp (-phi * (x - barrier)) := by
      simp [mckeanValue, not_lt.mpr hgt.le]
    change Integrable (discountedPut X x K q
        (firstLowerPassage X x barrier)) P ∧
      (∫ ω, discountedPut X x K q
        (firstLowerPassage X x barrier) ω ∂P) =
        (K - Real.exp barrier) *
          Real.exp (-(x - barrier) * phi) at habove
    have hcomm : -(x - barrier) * phi =
        -phi * (x - barrier) := by ring
    rw [hcomm] at habove
    rw [hvalue]
    exact habove
