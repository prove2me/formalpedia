-- Prove2me | solution 1 for Kyprianou.Ch01.brownianCappedGridUniformLpTwoNormBoundPublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:28:41.681914+00:00
-- url     : https://prove2.me/submissions/96160851-4954-496d-8d29-8d72c1b9d1fd

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Theorems.Thm_Kyprianou_Ch01_brownianUpperCappedFirstGridMeanOnePublic
import Theorems.Thm_Kyprianou_Ch01_brownianGridFirstCrossingUniformL2Public
import Theorems.Thm_Kyprianou_Ch01_uniformLpTwoNormOfBoundedSquareMomentsPublic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
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
    ∃ C : ℝ≥0, ∀ N : ℕ, eLpNorm (G N) 2 P ≤ (C : ENNReal) := by
  intro theta G tauT
  have hM : ∀ N : ℕ, AEStronglyMeasurable (G N) P := by
    intro N
    exact (brownianUpperCappedFirstGridMeanOnePublic
      P X sigma gamma q x hsigma hq hx hX hMeas T N).1.aestronglyMeasurable
  have hBound : ∀ N : ℕ,
      Integrable (fun ω => G N ω ^ 2) P ∧
        (∫ ω, G N ω ^ 2 ∂P) ≤
          Real.exp (sigma ^ 2 * theta ^ 2 * (T : ℝ)) := by
    intro N
    simpa only [G] using
      (brownianGridFirstCrossingUniformL2Public
        P X sigma gamma q x hsigma hq hX hMeas
        T (N + 1) (Nat.succ_pos N))
  obtain ⟨C, hC⟩ :=
    uniformLpTwoNormOfBoundedSquareMomentsPublic
      P G hM
      (Real.exp (sigma ^ 2 * theta ^ 2 * (T : ℝ)))
      (Real.exp_pos _).le hBound
  exact ⟨hM, C, hC⟩