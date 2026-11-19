-- Prove2me | solution 1 for Kyprianou.Ch01.brownianUpperCappedFirstGridIntegralLimitPublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T12:16:28.390012+00:00
-- url     : https://prove2.me/submissions/28353d81-9d9e-4754-b7a2-849534c4084f

import Theorems.Thm_Kyprianou_Ch01_brownianUpperCappedFirstGridMeanOnePublic
import Theorems.Thm_Kyprianou_Ch01_brownianCappedGridStoppedExponentialL1ConvergencePublic
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
    Integrable (fun ω => Real.exp (theta * X (tauT ω) ω -
      q * (tauT ω : ℝ))) P ∧
    Tendsto (fun N : ℕ => ∫ ω, G N ω ∂P) atTop
      (nhds (∫ ω, Real.exp (theta * X (tauT ω) ω -
        q * (tauT ω : ℝ)) ∂P)) := by
  intro theta G tauT
  obtain ⟨hInt, hL1⟩ :=
    brownianCappedGridStoppedExponentialL1ConvergencePublic
      P X sigma gamma q x hsigma hq hx hX hMeas T
  have hG : ∀ᶠ N : ℕ in atTop, Integrable (G N) P := by
    filter_upwards [] with N
    exact (brownianUpperCappedFirstGridMeanOnePublic
      P X sigma gamma q x hsigma hq hx hX hMeas T N).1
  exact ⟨hInt, tendsto_integral_of_L1
    (fun ω => Real.exp (theta * X (tauT ω) ω - q * (tauT ω : ℝ)))
    hInt.aestronglyMeasurable hG hL1⟩