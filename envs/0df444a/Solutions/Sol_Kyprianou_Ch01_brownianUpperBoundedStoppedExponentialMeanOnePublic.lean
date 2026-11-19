-- Prove2me | solution 1 for Kyprianou.Ch01.brownianUpperBoundedStoppedExponentialMeanOnePublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T10:04:37.973517+00:00
-- url     : https://prove2.me/submissions/ab308c38-f728-452c-9f90-0e8c007c339c

import Mathlib.Topology.Separation.Hausdorff
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_brownianUpperCappedFirstGridMeanOnePublic
import Theorems.Thm_Kyprianou_Ch01_brownianUpperCappedFirstGridIntegralLimitPublic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Continuous bounded stopping follows from first-crossing grids and their integral convergence. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma q x : ℝ)
    (hsigma : 0 < sigma) (hq : 0 < q) (hx : 0 < x)
    (hX : IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t)) :
    let theta : ℝ :=
      (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) - gamma) / sigma ^ 2
    ∀ T : ℝ≥0,
      let tauT : Ω → ℝ≥0 := fun ω =>
        match firstUpperPassage X x ω with
        | none => T
        | some t => min t T
      Integrable (fun ω => Real.exp
        (theta * X (tauT ω) ω - q * (tauT ω : ℝ))) P ∧
      (∫ ω, Real.exp
        (theta * X (tauT ω) ω - q * (tauT ω : ℝ)) ∂P) = 1 := by
  intro theta T tauT
  let G : ℕ → Ω → ℝ := fun N ω =>
    let K : ℕ := N + 1
    let delta : ℝ≥0 := T / (K : ℝ≥0)
    let tau : Ω → ℕ := fun ξ => by
      classical
      exact Nat.find (show ∃ k : ℕ,
        k = K ∨ x < X ((k : ℝ≥0) * delta) ξ from ⟨K, Or.inl rfl⟩)
    Real.exp (theta * X ((tau ω : ℝ≥0) * delta) ω -
      q * (((tau ω : ℝ≥0) * delta) : ℝ))
  have hGrid (N : ℕ) : Integrable (G N) P ∧
      (∫ ω, G N ω ∂P) = 1 :=
    (brownianUpperCappedFirstGridMeanOnePublic
       P X sigma gamma q x hsigma hq hx hX hMeas T) N
  obtain ⟨hInt, hconv⟩ :=
    brownianUpperCappedFirstGridIntegralLimitPublic
      P X sigma gamma q x hsigma hq hx hX hMeas T
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hlim1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop
      (nhds (∫ ω, Real.exp
        (theta * X (tauT ω) ω - q * (tauT ω : ℝ)) ∂P)) :=
    hconv.congr' (Filter.Eventually.of_forall fun N => (hGrid N).2)
  have heq : (∫ ω, Real.exp
      (theta * X (tauT ω) ω - q * (tauT ω : ℝ)) ∂P) = 1 :=
    tendsto_nhds_unique hlim1 hconst
  exact ⟨hInt, heq⟩
