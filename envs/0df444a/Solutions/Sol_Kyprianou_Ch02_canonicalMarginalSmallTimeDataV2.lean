-- Prove2me | solution 1 for Kyprianou.Ch02.canonicalMarginalSmallTimeDataV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:00:15.354684+00:00
-- url     : https://prove2.me/submissions/d33d7d36-9f29-4aad-b52c-4fc0783c8a14

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent

import Theorems.Thm_Kyprianou_Ch02_canonicalMarginalSmallTimeExplicitDataV1
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false
open Filter Topology Set
theorem solution
    (M : {t : ℝ // 0 < t} → ProbabilityMeasure ℝ)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hT : ∀ t ξ, charFun (M t : Measure ℝ) ξ =
      Complex.exp (((t.val : ℝ) : ℂ) * Kyprianou.Ch01.levyTripleExponent T ξ)) :
    ∃ (r b_r : ℝ) (σ_sq_r : ℝ≥0) (ts : ℕ → {t : ℝ // 0 < t}),
      r ∈ Set.Ioc (1 / 2 : ℝ) 1 ∧
      T.levyMeasure {x | |x| = r} = 0 ∧
      Tendsto (fun n => (ts n).val) atTop (nhds (0 : ℝ)) ∧
      Tendsto (fun n => (ts n).val⁻¹ *
        ∫ x in {x | |x| < r}, x ∂(M (ts n) : Measure ℝ))
        atTop (nhds b_r) ∧
      Tendsto (fun n => (ts n).val⁻¹ *
        ∫ x in {x | |x| < r}, x ^ 2 ∂(M (ts n) : Measure ℝ))
        atTop (nhds (σ_sq_r : ℝ)) ∧
      T.drift = b_r + ∫ x in {x | r ≤ |x| ∧ |x| < 1}, x ∂T.levyMeasure ∧
      (T.gaussianVariance : ℝ) =
        (σ_sq_r : ℝ) - ∫ x in {x | |x| < r}, x ^ 2 ∂T.levyMeasure ∧
      ∀ f : BoundedContinuousFunction ℝ ℝ,
        (∃ r' > 0, ∀ x, |x| < r' → f x = 0) →
        Tendsto (fun n => (ts n).val⁻¹ *
          ∫ x, f x ∂(M (ts n) : Measure ℝ))
          atTop (nhds (∫ x, f x ∂T.levyMeasure)) := by
  apply Kyprianou.Ch02.canonicalMarginalSmallTimeExplicitDataV1 M T
  intro t ξ
  simpa only [Kyprianou.Ch01.levyTripleExponent] using hT t ξ
