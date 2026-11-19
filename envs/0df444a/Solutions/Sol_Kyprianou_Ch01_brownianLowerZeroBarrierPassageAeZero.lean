-- Prove2me | solution 1 for Kyprianou.Ch01.brownianLowerZeroBarrierPassageAeZero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T00:56:15.297045+00:00
-- url     : https://prove2.me/submissions/7fd83302-52bc-4323-93a0-fac56cb4f25e

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_brownianLowerZeroBarrierImmediate
import Theorems.Thm_Kyprianou_Ch01_passageLaplaceNormBoundNonnegativeDiscountPublic
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (sigma gamma : ℝ)
    (hsigma : 0 < sigma)
    (hX : IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t)) :
    ∀ᵐ ω ∂P, firstLowerPassage X 0 0 ω = 0 := by
  let L : Ω → ℝ :=
    passageLaplace (firstLowerPassage X 0 0) (1 : ℝ)
  have hmain := brownianLowerZeroBarrierImmediate
    P X sigma gamma 1 hsigma (by norm_num) hX hMeas
  have hInt : Integrable L P := hmain.1
  have hbound : ∀ ω, L ω ≤ 1 := by
    intro ω
    have hnorm := passageLaplaceNormBoundNonnegativeDiscountPublic
      (firstLowerPassage X 0 0) 1 (by norm_num) ω
    exact le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hnorm)
  have hsub : Integrable (fun ω => (1 : ℝ) - L ω) P :=
    (integrable_const _).sub hInt
  have hnonneg :
      (0 : Ω → ℝ) ≤ᵐ[P] (fun ω => 1 - L ω) := by
    filter_upwards [] with ω
    exact sub_nonneg.mpr (hbound ω)
  have hzero : (∫ ω, ((1 : ℝ) - L ω) ∂P) = 0 := by
    rw [integral_sub (integrable_const _) hInt]
    simp [L, hmain.2]
  have heq : (fun ω => (1 : ℝ) - L ω) =ᵐ[P]
      (fun _ => (0 : ℝ)) :=
    (integral_eq_zero_iff_of_nonneg_ae hnonneg hsub).mp hzero
  filter_upwards [heq] with ω hw
  have hvalue : L ω = 1 := by
    have hz : 1 - L ω = 0 := hw
    linarith
  change passageLaplace (firstLowerPassage X 0 0) 1 ω = 1 at hvalue
  cases hτ : firstLowerPassage X 0 0 ω with
  | top =>
      simp [passageLaplace, hτ] at hvalue
  | coe t =>
      have hexp : Real.exp (-(t : ℝ)) = 1 := by
        simpa [passageLaplace, hτ] using hvalue
      have ht : (t : ℝ) = 0 := by
        have hc : -(t : ℝ) = 0 :=
          Real.exp_injective (by simpa using hexp)
        linarith
      have ht0 : t = 0 := by exact_mod_cast ht
      simp [hτ, ht0]
