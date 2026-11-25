-- Prove2me | solution 1 for Kyprianou.Ch04.monotoneLIntegralBudgetV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:27:43.95368+00:00
-- url     : https://prove2.me/submissions/ea932762-8737-465c-90f0-07cefe8f651f

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Monotone convergence preserves the finite grid moment budget. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (f : ℕ → Ω → ℝ) (K : ℝ)
    (hint : ∀ k, Integrable (f k) P)
    (hmeas : ∀ k, Measurable (f k))
    (hnonneg : ∀ k ω, 0 ≤ f k ω)
    (hmono : ∀ ω, Monotone (fun k => f k ω))
    (hbudget : ∀ k, (∫ ω, f k ω ∂P) ≤ K) :
    (∫⁻ ω, ⨆ k, ENNReal.ofReal (f k ω) ∂P) ≤ ENNReal.ofReal K := by
  change (∫⁻ ω, ⨆ k, (ENNReal.ofReal ∘ f k) ω ∂P) ≤ _
  rw [lintegral_iSup (fun k => ENNReal.measurable_ofReal.comp (hmeas k))
    (fun i j hij ω => ENNReal.ofReal_le_ofReal (hmono ω hij))]
  refine iSup_le fun k => ?_
  change (∫⁻ ω, ENNReal.ofReal (f k ω) ∂P) ≤ _
  rw [← ofReal_integral_eq_lintegral_ofReal (hint k)
    (Eventually.of_forall (hnonneg k))]
  exact ENNReal.ofReal_le_ofReal (hbudget k)
