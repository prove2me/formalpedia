-- Prove2me | solution 1 for Kyprianou.Ch01.brownianCappedGridUniformIntegrableWithLimitPublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:24:38.96835+00:00
-- url     : https://prove2.me/submissions/b1d56637-b043-4ec7-84fe-92ee61eb1f17

import Theorems.Thm_Kyprianou_Ch01_brownianCappedGridUniformLpTwoNormBoundPublic
import Theorems.Thm_Kyprianou_Ch01_uniformIntegrableOfUniformLpTwoBoundPublic
import Theorems.Thm_Kyprianou_Ch01_brownianCappedFirstGridPointwiseConvergencePublic
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Filter
open scoped NNReal ENNReal
set_option autoImplicit false
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
    let tauT : Ω → ℝ≥0 := fun ω =>
      match firstUpperPassage X x ω with
      | none => T
      | some t => min t T
    (∀ N : ℕ, AEStronglyMeasurable (G N) P) ∧
    Integrable (fun ω => Real.exp (theta * X (tauT ω) ω -
      q * (tauT ω : ℝ))) P ∧
    UnifIntegrable G 1 P := by
  intro theta G tauT
  obtain ⟨hG, C, hC⟩ :=
    brownianCappedGridUniformLpTwoNormBoundPublic
      P X sigma gamma q x hsigma hq hx hX hMeas T
  have hUI : UniformIntegrable G 1 P :=
    uniformIntegrableOfUniformLpTwoBoundPublic P G hG C hC
  have hAE :=
    brownianCappedFirstGridPointwiseConvergencePublic
      P X sigma gamma q x hsigma hq hx hX hMeas T
  exact ⟨hG, hUI.integrable_of_ae_tendsto hAE, hUI.unifIntegrable⟩