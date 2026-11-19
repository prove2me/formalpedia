-- Prove2me | solution 1 for Kyprianou.Ch01.brownianUpperZeroBarrierLaplaceOne
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T00:35:47.206281+00:00
-- url     : https://prove2.me/submissions/86c3db56-1b5f-4d7b-9b64-a0d85e35cb2f

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_brownianUpperZeroBarrierLaplaceIntegrable
import Theorems.Thm_Kyprianou_Ch01_brownianDiscountedUpperPassage
import Theorems.Thm_Kyprianou_Ch01_passageLaplaceUpperBarrierAntitone
import Theorems.Thm_Kyprianou_Ch01_passageLaplaceNormBoundNonnegativeDiscountPublic
import Theorems.Thm_Kyprianou_Ch01_expNegBarrierBoundForcesUnity
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Zero-level Brownian passage expectation by positive-barrier monotone squeeze. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (sigma gamma q : ℝ)
    (hsigma : 0 < sigma) (hq : 0 < q)
    (hX : IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t)) :
    Integrable (passageLaplace (firstUpperPassage X 0) q) P ∧
    (∫ ω, passageLaplace (firstUpperPassage X 0) q ω ∂P) = 1 := by
  have hInt := brownianUpperZeroBarrierLaplaceIntegrable
    P X sigma gamma q hsigma hq hX hMeas
  refine ⟨hInt, le_antisymm ?_ ?_⟩
  · calc
      (∫ ω, passageLaplace (firstUpperPassage X 0) q ω ∂P) ≤
          ∫ _ω : Ω, (1 : ℝ) ∂P := by
            apply integral_mono hInt (integrable_const _)
            intro ω
            have h := passageLaplaceNormBoundNonnegativeDiscountPublic
              (firstUpperPassage X 0) q hq.le ω
            exact le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using h)
      _ = 1 := by simp
  · let κ : ℝ :=
      (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) - gamma) / sigma ^ 2
    have hκ : 0 ≤ κ := by
      have hs2 : 0 < sigma ^ 2 := sq_pos_of_pos hsigma
      have hsq : 0 ≤ 2 * sigma ^ 2 * q := by positivity
      have hroot : gamma ≤ Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) := by
        calc
          gamma ≤ |gamma| := le_abs_self gamma
          _ = Real.sqrt (gamma ^ 2) := (Real.sqrt_sq_eq_abs gamma).symm
          _ ≤ Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) :=
            Real.sqrt_le_sqrt (by linarith)
      exact div_nonneg (sub_nonneg.mpr hroot) hs2.le
    apply expNegBarrierBoundForcesUnity κ
      (∫ ω, passageLaplace (firstUpperPassage X 0) q ω ∂P) hκ
    intro a ha
    have hpos := brownianDiscountedUpperPassage
      P X sigma gamma q a hsigma hq ha hX hMeas
    calc
      Real.exp (-a * κ) =
          (∫ ω, passageLaplace (firstUpperPassage X a) q ω ∂P) := hpos.2.symm
      _ ≤ (∫ ω, passageLaplace (firstUpperPassage X 0) q ω ∂P) := by
        apply integral_mono hpos.1 hInt
        intro ω
        exact passageLaplaceUpperBarrierAntitone
          X 0 a ha.le q hq.le ω
