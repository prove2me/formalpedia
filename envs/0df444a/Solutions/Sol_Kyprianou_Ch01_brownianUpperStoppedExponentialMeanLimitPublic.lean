-- Prove2me | solution 1 for Kyprianou.Ch01.brownianUpperStoppedExponentialMeanLimitPublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T09:23:16.184196+00:00
-- url     : https://prove2.me/submissions/c32473aa-5563-448e-80ea-77cd9feef788

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Theorems.Thm_Kyprianou_Ch01_brownianUpperBoundedStoppedExponentialMeanOnePublic
import Theorems.Thm_Kyprianou_Ch01_brownianUpperStoppedExponentialPointwiseLimitPublic
import Theorems.Thm_Kyprianou_Ch01_brownianUpperStoppedExponentialUniformBoundPublic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The almost-sure passage limit and common integrable cap imply convergence of expectations. -/
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
    let F : ℕ → Ω → ℝ := fun N ω =>
      let T : ℝ≥0 := N
      let tauT : ℝ≥0 :=
        match firstUpperPassage X x ω with
        | none => T
        | some t => min t T
      Real.exp (theta * X tauT ω - q * (tauT : ℝ))
    Integrable (passageLaplace (firstUpperPassage X x) q) P ∧
    Tendsto (fun N : ℕ => ∫ ω, F N ω ∂P)
      atTop (nhds (Real.exp (theta * x) *
        (∫ ω, passageLaplace (firstUpperPassage X x) q ω ∂P))) := by
  let theta : ℝ :=
    (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) - gamma) / sigma ^ 2
  let F : ℕ → Ω → ℝ := fun N ω =>
    let T : ℝ≥0 := N
    let tauT : ℝ≥0 :=
      match firstUpperPassage X x ω with
      | none => T
      | some t => min t T
    Real.exp (theta * X tauT ω - q * (tauT : ℝ))
  obtain ⟨hInt0, hPt⟩ :=
    brownianUpperStoppedExponentialPointwiseLimitPublic
      P X sigma gamma q x hsigma hq hx hX hMeas
  have hBound :=
    brownianUpperStoppedExponentialUniformBoundPublic
      P X sigma gamma q x hsigma hq hx hX hMeas
  have hIntN (N : ℕ) : Integrable (F N) P :=
    (brownianUpperBoundedStoppedExponentialMeanOnePublic
      P X sigma gamma q x hsigma hq hx hX hMeas (N : ℝ≥0)).1
  have hMeasN (N : ℕ) : AEStronglyMeasurable (F N) P :=
    (hIntN N).aestronglyMeasurable
  have hDomInt : Integrable (fun _ : Ω => Real.exp (theta * x)) P :=
    integrable_const _
  have hBoundN (N : ℕ) :
      ∀ᵐ ω ∂P, ‖F N ω‖ ≤ Real.exp (theta * x) :=
    hBound.mono (fun ω hω => hω N)
  have hDCT : Tendsto (fun N : ℕ => ∫ ω, F N ω ∂P)
      atTop (nhds (∫ ω, Real.exp (theta * x) *
        passageLaplace (firstUpperPassage X x) q ω ∂P)) :=
    tendsto_integral_of_dominated_convergence
      (fun _ : Ω => Real.exp (theta * x))
      hMeasN hDomInt hBoundN hPt
  refine ⟨hInt0, ?_⟩
  simpa only [integral_const_mul] using hDCT
