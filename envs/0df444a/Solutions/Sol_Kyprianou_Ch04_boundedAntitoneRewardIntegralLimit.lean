-- Prove2me | solution 1 for Kyprianou.Ch04.boundedAntitoneRewardIntegralLimit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:36:39.184417+00:00
-- url     : https://prove2.me/submissions/aaf5048a-727b-41f6-826c-561d33f4e6f5

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Bounded decreasing real rewards converge in expectation to their infimum. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (g : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (g n))
    (h0 : ∀ n w, 0 ≤ g n w) (h1 : ∀ n w, g n w ≤ 1)
    (ha : ∀ w, Antitone (fun n => g n w)) :
    Tendsto (fun n => ∫ w, g n w ∂P) atTop
      (nhds (∫ w, ⨅ n, g n w ∂P)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
  · exact fun n => (hm n).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (h0 n w)]
      exact h1 n w
  · apply Eventually.of_forall
    intro w
    exact tendsto_atTop_ciInf (ha w) ⟨0, by rintro x ⟨n,rfl⟩; exact h0 n w⟩
