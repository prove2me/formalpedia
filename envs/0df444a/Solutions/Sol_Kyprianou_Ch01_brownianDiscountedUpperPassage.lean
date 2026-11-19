-- Prove2me | solution 1 for Kyprianou.Ch01.brownianDiscountedUpperPassage
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T09:05:46.052054+00:00
-- url     : https://prove2.me/submissions/907d5427-b31a-4d8e-a427-01586dfeedea

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Theorems.Thm_Kyprianou_Ch01_brownianUpperStoppedExponentialMeanOnePublic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The upper first-passage Laplace transform from the stopped exponential identity. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma q x : ℝ)
    (hsigma : 0 < sigma) (hq : 0 < q) (hx : 0 < x)
    (hX : IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t)) :
    Integrable (passageLaplace (firstUpperPassage X x) q) P ∧
    (∫ ω, passageLaplace (firstUpperPassage X x) q ω ∂P) =
      Real.exp (-x * ((Real.sqrt
        (gamma ^ 2 + 2 * sigma ^ 2 * q) - gamma) / sigma ^ 2)) := by
  let theta : ℝ :=
    (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) - gamma) / sigma ^ 2
  obtain ⟨hInt, hstop⟩ :=
    brownianUpperStoppedExponentialMeanOnePublic
      P X sigma gamma q x hsigma hq hx hX hMeas
  refine ⟨hInt, ?_⟩
  have hweighted :
      Real.exp (theta * x) *
        (∫ ω, passageLaplace (firstUpperPassage X x) q ω ∂P) = 1 := by
    simpa only [integral_const_mul] using hstop
  have hinv : Real.exp (-x * theta) * Real.exp (theta * x) = 1 := by
    rw [← Real.exp_add]
    have hsum : -x * theta + theta * x = 0 := by ring
    rw [hsum, Real.exp_zero]
  change (∫ ω, passageLaplace (firstUpperPassage X x) q ω ∂P) =
    Real.exp (-x * theta)
  calc
    (∫ ω, passageLaplace (firstUpperPassage X x) q ω ∂P) =
      (Real.exp (-x * theta) * Real.exp (theta * x)) *
        (∫ ω, passageLaplace (firstUpperPassage X x) q ω ∂P) := by
          rw [hinv, one_mul]
    _ = Real.exp (-x * theta) *
        (Real.exp (theta * x) *
          (∫ ω, passageLaplace (firstUpperPassage X x) q ω ∂P)) := by ring
    _ = Real.exp (-x * theta) := by rw [hweighted, mul_one]
