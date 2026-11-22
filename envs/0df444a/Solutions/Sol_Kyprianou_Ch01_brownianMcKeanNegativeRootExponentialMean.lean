-- Prove2me | solution 1 for Kyprianou.Ch01.brownianMcKeanNegativeRootExponentialMean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T20:42:45.276181+00:00
-- url     : https://prove2.me/submissions/f3bdf8bf-e19a-4bba-9a86-360b230a9b80

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_brownianRealExponentialMartingale
import Theorems.Thm_Kyprianou_Ch01_mckeanBrownianPhiHarmonicRoot

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Apply the proved real exponential martingale at the negative McKean root. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma q : ℝ) (hsigma : 0 < sigma) (hq : 0 < q)
    (hB : IsLinearBrownian P X sigma gamma)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (t : ℝ≥0) :
    let phi := (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) + gamma) / sigma ^ 2
    Integrable (fun ω => Real.exp (-phi * X t ω - q * (t : ℝ))) P ∧
      (∫ ω, Real.exp (-phi * X t ω - q * (t : ℝ)) ∂P) = 1 := by
  dsimp only
  let phi : ℝ :=
    (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) + gamma) / sigma ^ 2
  have hRoot : (sigma ^ 2 / 2) * phi ^ 2 - gamma * phi - q = 0 := by
    exact Kyprianou.Ch01.mckeanBrownianPhiHarmonicRoot
      sigma gamma q hsigma hq
  have hPsi : sigma ^ 2 * (-phi) ^ 2 / 2 + gamma * (-phi) = q := by
    nlinarith [hRoot]
  have hPsi2 : sigma ^ 2 * phi ^ 2 / 2 + -(gamma * phi) = q := by
    nlinarith [hRoot]
  have hMart :=
    Kyprianou.Ch01.brownianRealExponentialMartingale
      P X sigma gamma (-phi) hsigma hB hXmeas (0 : ℝ≥0) t (show (0 : ℝ≥0) ≤ t from bot_le)
  dsimp only at hMart
  have hStart : X 0 = fun _ => 0 := hB.1.start_zero
  constructor
  · simpa only [hPsi] using hMart.1
  · have hWhole := hMart.2 Set.univ MeasurableSet.univ
    change (∫ ω, Real.exp (-phi * X t ω - q * (t : ℝ)) ∂P) = 1
    simpa [hPsi2, hStart] using hWhole
