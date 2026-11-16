-- Prove2me | solution 1 for Kyprianou.Ch01.brownianDiscountedExponentialPastMartingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T21:28:16.103196+00:00
-- url     : https://prove2.me/submissions/c9fcf311-5c8d-4e81-a6b9-6a8a368c9643

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_brownianAdjustmentRoot
import Theorems.Thm_Kyprianou_Ch01_brownianRealExponentialMartingale
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Brownian exponential-martingale normalisation with the exact discount. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma q : ℝ)
    (hsigma : 0 < sigma) (hq : 0 < q)
    (hX : Kyprianou.Ch01.IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t)) :
    let theta : ℝ := (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) - gamma) / sigma ^ 2
    ∀ (s t : ℝ≥0), s ≤ t →
      Integrable (fun ω => Real.exp (theta * X t ω - q * (t : ℝ))) P ∧
      ∀ A : Set Ω,
        @MeasurableSet Ω (Kyprianou.Ch01.naturalSigma X s) A →
        (∫ ω in A, Real.exp (theta * X t ω - q * (t : ℝ)) ∂P) =
        (∫ ω in A, Real.exp (theta * X s ω - q * (s : ℝ)) ∂P) := by
  dsimp
  let theta : ℝ :=
    (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) - gamma) / sigma ^ 2
  have hpsi : sigma ^ 2 * theta ^ 2 / 2 + gamma * theta = q :=
    (Kyprianou.Ch01.brownianAdjustmentRoot sigma gamma q hsigma hq).2
  intro s t hst
  have hm := Kyprianou.Ch01.brownianRealExponentialMartingale
    P X sigma gamma theta hsigma hX hMeas s t hst
  dsimp at hm
  simpa only [hpsi] using hm
