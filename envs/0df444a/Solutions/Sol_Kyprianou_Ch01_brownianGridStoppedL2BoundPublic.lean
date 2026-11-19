-- Prove2me | solution 1 for Kyprianou.Ch01.brownianGridStoppedL2BoundPublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T10:14:06.534241+00:00
-- url     : https://prove2.me/submissions/464c7be4-02d6-4adc-a710-9f663462d718

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_brownianAdjustmentRoot
import Theorems.Thm_Kyprianou_Ch01_brownianRealExponentialGridOptionalSamplingPublic
import Theorems.Thm_Kyprianou_Ch01_gridStoppedExponentialSquareDominationPublic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Uniform L² bound for a capped-grid stopped discounted Brownian exponential. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (sigma gamma q : ℝ)
    (hsigma : 0 < sigma) (hq : 0 < q)
    (hX : IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (delta : ℝ≥0) (tau : Ω → ℕ) (N : ℕ)
    (hBound : ∀ ω, tau ω ≤ N)
    (hStop : ∀ n, n < N →
      @MeasurableSet Ω (naturalSigma X ((n : ℝ≥0) * delta))
        {ω | n < tau ω}) :
    let theta := (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) - gamma) / sigma ^ 2
    let M : Ω → ℝ := fun ω =>
      Real.exp (theta * X ((tau ω : ℝ≥0) * delta) ω -
        q * (((tau ω : ℝ≥0) * delta) : ℝ))
    Integrable (fun ω => M ω ^ 2) P ∧
      (∫ ω, M ω ^ 2 ∂P) ≤
        Real.exp (sigma ^ 2 * theta ^ 2 * (((N : ℝ≥0) * delta) : ℝ)) := by
  dsimp
  let theta : ℝ := (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) - gamma) / sigma ^ 2
  let psi2 : ℝ := sigma ^ 2 * (2 * theta) ^ 2 / 2 + gamma * (2 * theta)
  let M : Ω → ℝ := fun ω =>
    Real.exp (theta * X ((tau ω : ℝ≥0) * delta) ω -
      q * (((tau ω : ℝ≥0) * delta) : ℝ))
  let G : Ω → ℝ := fun ω =>
    Real.exp ((2 * theta) * X ((tau ω : ℝ≥0) * delta) ω -
      psi2 * (((tau ω : ℝ≥0) * delta) : ℝ))
  let C : ℝ := Real.exp (sigma ^ 2 * theta ^ 2 * (((N : ℝ≥0) * delta) : ℝ))
  have hr : sigma ^ 2 * theta ^ 2 / 2 + gamma * theta = q :=
    (brownianAdjustmentRoot sigma gamma q hsigma hq).2
  have hIntM : Integrable M P := by
    simpa only [M, hr] using
      (brownianRealExponentialGridOptionalSamplingPublic P X sigma gamma theta
        hsigma hX hMeas delta tau N hBound hStop).1
  obtain ⟨hIntG, hGmean⟩ :=
    brownianRealExponentialGridOptionalSamplingPublic
      P X sigma gamma (2 * theta) hsigma hX hMeas
      delta tau N hBound hStop
  have hSm : AEStronglyMeasurable (fun ω => M ω ^ 2) P :=
    hIntM.aestronglyMeasurable.pow 2
  have hCG : Integrable (fun ω => C * G ω) P := hIntG.const_mul C
  have hBoundPoint (ω : Ω) : M ω ^ 2 ≤ C * G ω :=
    gridStoppedExponentialSquareDominationPublic X sigma gamma theta q
      hr delta tau N hBound ω
  have hIntSq : Integrable (fun ω => M ω ^ 2) P :=
    hCG.mono_nonneg hSm
      (Filter.Eventually.of_forall fun ω => sq_nonneg (M ω))
      (Filter.Eventually.of_forall hBoundPoint)
  refine ⟨hIntSq, ?_⟩
  calc
    (∫ ω, M ω ^ 2 ∂P) ≤ (∫ ω, C * G ω ∂P) :=
      integral_mono_ae hIntSq hCG (Filter.Eventually.of_forall hBoundPoint)
    _ = C * (∫ ω, G ω ∂P) := integral_const_mul _ _
    _ = C := by rw [hGmean, mul_one]
