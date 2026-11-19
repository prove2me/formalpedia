-- Prove2me | solution 1 for Kyprianou.Ch01.brownianRealExponentialGridOptionalSamplingPublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T09:53:50.909982+00:00
-- url     : https://prove2.me/submissions/33f2cefb-f629-4bfd-a766-b2e6090e5222

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_naturalSigma_le_ambient
import Theorems.Thm_Kyprianou_Ch01_brownianRealExponentialMartingale
import Theorems.Thm_Kyprianou_Ch01_brownianRealExpMoment
import Theorems.Thm_Kyprianou_Ch01_finiteGridOptionalStoppingEventwisePublic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Every Gaussian exponential compensated by its cumulant has unit mean. -/
private theorem realExpMeanOne
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma theta : ℝ) (hsigma : 0 < sigma)
    (hX : IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t)) (t : ℝ≥0) :
    let psi := sigma ^ 2 * theta ^ 2 / 2 + gamma * theta
    Integrable (fun ω => Real.exp (theta * X t ω - psi * (t : ℝ))) P ∧
    (∫ ω, Real.exp (theta * X t ω - psi * (t : ℝ)) ∂P) = 1 := by
  dsimp
  let psi := sigma ^ 2 * theta ^ 2 / 2 + gamma * theta
  obtain ⟨hint, heq⟩ :=
    brownianRealExpMoment P X sigma gamma theta hsigma hX hMeas t
  have hfn (ω : Ω) :
      Real.exp (theta * X t ω - psi * (t : ℝ)) =
        Real.exp (theta * X t ω) * Real.exp (-(psi * (t : ℝ))) := by
    rw [sub_eq_add_neg, Real.exp_add]
  have hf : Integrable
      (fun ω => Real.exp (theta * X t ω - psi * (t : ℝ))) P := by
    simpa only [hfn] using hint.mul_const (Real.exp (-(psi * (t : ℝ))))
  refine ⟨hf, ?_⟩
  calc
    (∫ ω, Real.exp (theta * X t ω - psi * (t : ℝ)) ∂P) =
        (∫ ω, Real.exp (theta * X t ω) * Real.exp (-(psi * (t : ℝ))) ∂P) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hfn
    _ = Real.exp (psi * (t : ℝ)) * Real.exp (-(psi * (t : ℝ))) := by
          rw [integral_mul_const, heq]
    _ = 1 := by
          rw [← Real.exp_add]
          have hz : psi * (t : ℝ) + -(psi * (t : ℝ)) = 0 := by ring
          rw [hz, Real.exp_zero]

/-- Optional sampling for any real Brownian exponential parameter on a finite grid. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (sigma gamma theta : ℝ)
    (hsigma : 0 < sigma)
    (hX : IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (delta : ℝ≥0) (τ : Ω → ℕ) (N : ℕ)
    (hBound : ∀ ω, τ ω ≤ N)
    (hStop : ∀ n, n < N →
      @MeasurableSet Ω (naturalSigma X ((n : ℝ≥0) * delta))
        {ω | n < τ ω}) :
    let psi : ℝ := sigma ^ 2 * theta ^ 2 / 2 + gamma * theta
    Integrable (fun ω => Real.exp
      (theta * X ((τ ω : ℝ≥0) * delta) ω -
        psi * (((τ ω : ℝ≥0) * delta) : ℝ))) P ∧
    (∫ ω, Real.exp (theta * X ((τ ω : ℝ≥0) * delta) ω -
        psi * (((τ ω : ℝ≥0) * delta) : ℝ)) ∂P) = 1 := by
  let psi : ℝ := sigma ^ 2 * theta ^ 2 / 2 + gamma * theta
  let T : ℕ → ℝ≥0 := fun n => (n : ℝ≥0) * delta
  let F : ℕ → MeasurableSpace Ω := fun n => naturalSigma X (T n)
  let M : ℕ → Ω → ℝ := fun n ω =>
    Real.exp (theta * X (T n) ω - psi * (T n : ℝ))
  have hF (n : ℕ) : F n ≤ (inferInstance : MeasurableSpace Ω) :=
    naturalSigma_le_ambient X hMeas (T n)
  have hInt (n : ℕ) : Integrable (M n) P :=
    (realExpMeanOne P X sigma gamma theta hsigma hX hMeas (T n)).1
  have hMart (n : ℕ) (A : Set Ω)
      (hA : @MeasurableSet Ω (F n) A) :
      (∫ ω in A, M (n + 1) ω ∂P) =
        (∫ ω in A, M n ω ∂P) := by
    have hn : T n ≤ T (n + 1) := by
      dsimp [T]
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast Nat.le_succ n) (by positivity)
    exact (brownianRealExponentialMartingale
      P X sigma gamma theta hsigma hX hMeas
      (T n) (T (n+1)) hn).2 A hA
  obtain ⟨hIntτ, hEq⟩ :=
    finiteGridOptionalStoppingEventwisePublic P F M τ N hF hBound hInt hStop hMart
  have hZero : (∫ ω, M 0 ω ∂P) = 1 := by
    simpa only [M, T, psi, Nat.cast_zero, zero_mul] using
      (realExpMeanOne P X sigma gamma theta hsigma hX hMeas 0).2
  exact ⟨hIntτ, hEq.trans hZero⟩
