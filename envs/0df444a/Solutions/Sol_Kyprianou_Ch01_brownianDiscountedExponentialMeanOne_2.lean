-- Prove2me | solution 2 for Kyprianou.Ch01.brownianDiscountedExponentialMeanOne
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T21:25:12.028779+00:00
-- url     : https://prove2.me/submissions/4d41d11b-6f09-4db6-8398-4d5bd7a60c87

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_brownianAdjustmentRoot
import Theorems.Thm_Kyprianou_Ch01_brownianRealExpMoment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The positive Brownian adjustment root makes the discount equal the
    Gaussian cumulant and normalises the exponential moment to one. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma q : ℝ) (hsigma : 0 < sigma) (hq : 0 < q)
    (hX : Kyprianou.Ch01.IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t)) (t : ℝ≥0) :
    let theta := (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) - gamma) / sigma ^ 2
    Integrable (fun ω => Real.exp (theta * X t ω - q * (t : ℝ))) P ∧
    (∫ ω, Real.exp (theta * X t ω - q * (t : ℝ)) ∂P) = 1 := by
  dsimp
  let theta := (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) - gamma) / sigma ^ 2
  have hpsi : sigma ^ 2 * theta ^ 2 / 2 + gamma * theta = q :=
    (Kyprianou.Ch01.brownianAdjustmentRoot sigma gamma q hsigma hq).2
  obtain ⟨hint, heq⟩ :=
    Kyprianou.Ch01.brownianRealExpMoment P X sigma gamma theta
      hsigma hX hMeas t
  have hfn (ω : Ω) :
      Real.exp (theta * X t ω - q * (t : ℝ)) =
        Real.exp (theta * X t ω) * Real.exp (-(q * (t : ℝ))) := by
    rw [sub_eq_add_neg, Real.exp_add]
  have hf : Integrable
      (fun ω => Real.exp (theta * X t ω - q * (t : ℝ))) P := by
    simpa only [hfn] using hint.mul_const (Real.exp (-(q * (t : ℝ))))
  refine ⟨hf, ?_⟩
  calc
    (∫ ω, Real.exp (theta * X t ω - q * (t : ℝ)) ∂P) =
      (∫ ω, Real.exp (theta * X t ω) * Real.exp (-(q * (t : ℝ))) ∂P) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hfn
    _ = Real.exp ((sigma ^ 2 * theta ^ 2 / 2 + gamma * theta) * (t : ℝ)) *
          Real.exp (-(q * (t : ℝ))) := by rw [integral_mul_const, heq]
    _ = 1 := by
      rw [hpsi, ← Real.exp_add]
      have hz : q * (t : ℝ) + -(q * (t : ℝ)) = 0 := by ring
      rw [hz, Real.exp_zero]
