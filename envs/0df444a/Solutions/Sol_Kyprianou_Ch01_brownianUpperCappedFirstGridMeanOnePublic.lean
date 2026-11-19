-- Prove2me | solution 1 for Kyprianou.Ch01.brownianUpperCappedFirstGridMeanOnePublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T10:20:23.826318+00:00
-- url     : https://prove2.me/submissions/58bd3ed0-6dc4-41e7-a64e-0c7ad3340bcc

import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_brownianAdjustmentRoot
import Theorems.Thm_Kyprianou_Ch01_naturalGridFirstCrossingMeasurablePublic
import Theorems.Thm_Kyprianou_Ch01_brownianRealExponentialGridOptionalSamplingPublic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The explicit sentinel-capped first-crossing grid has unit stopped exponential mean. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma q x : ℝ)
    (hsigma : 0 < sigma) (hq : 0 < q) (hx : 0 < x)
    (hX : IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (T : ℝ≥0) :
    let theta : ℝ :=
      (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) - gamma) / sigma ^ 2
    let G : ℕ → Ω → ℝ := fun N ω =>
      let K : ℕ := N + 1
      let delta : ℝ≥0 := T / (K : ℝ≥0)
      let tau : Ω → ℕ := fun ξ => by
        classical
        exact Nat.find (show ∃ k : ℕ,
          k = K ∨ x < X ((k : ℝ≥0) * delta) ξ from ⟨K, Or.inl rfl⟩)
      Real.exp (theta * X ((tau ω : ℝ≥0) * delta) ω -
        q * (((tau ω : ℝ≥0) * delta) : ℝ))
    ∀ N : ℕ, Integrable (G N) P ∧ (∫ ω, G N ω ∂P) = 1 := by
  intro theta G N
  let K : ℕ := N + 1
  let delta : ℝ≥0 := T / (K : ℝ≥0)
  let tau : Ω → ℕ := fun ξ => by
    classical
    exact Nat.find (show ∃ k : ℕ,
      k = K ∨ x < X ((k : ℝ≥0) * delta) ξ from ⟨K, Or.inl rfl⟩)
  obtain ⟨hBound, hStop⟩ :=
    naturalGridFirstCrossingMeasurablePublic X x delta K
  have hroot : sigma ^ 2 * theta ^ 2 / 2 + gamma * theta = q :=
    (brownianAdjustmentRoot sigma gamma q hsigma hq).2
  obtain ⟨hInt, hMean⟩ :=
    brownianRealExponentialGridOptionalSamplingPublic
      P X sigma gamma theta hsigma hX hMeas delta tau K hBound hStop
  constructor
  · simpa only [G, hroot] using hInt
  · simpa only [G, hroot] using hMean
