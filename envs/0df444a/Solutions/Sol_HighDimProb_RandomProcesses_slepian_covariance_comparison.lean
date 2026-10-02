-- Prove2me | solution 1 for HighDimProb.RandomProcesses.slepian_covariance_comparison
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-02T08:06:36.523634+00:00
-- url     : https://prove2.me/submissions/b551698a-10bb-4f85-a23f-50887af4576a

import Mathlib


open MeasureTheory ProbabilityTheory

namespace SlepianProof

/-- The moment assumptions in Slepian's inequality order the covariance matrices. -/
lemma covariance_comparison {Ω T : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : T → Ω → ℝ)
    (hXG : IsGaussianProcess X P) (hYG : IsGaussianProcess Y P)
    (hXmean : ∀ i, ∫ ω, X i ω ∂P = 0) (hYmean : ∀ i, ∫ ω, Y i ω ∂P = 0)
    (hvar : ∀ i, ∫ ω, (X i ω) ^ 2 ∂P = ∫ ω, (Y i ω) ^ 2 ∂P)
    (hinc : ∀ i j, ∫ ω, (X i ω - X j ω) ^ 2 ∂P ≤
      ∫ ω, (Y i ω - Y j ω) ^ 2 ∂P) :
    (∀ i, cov[X i, X i; P] = cov[Y i, Y i; P]) ∧
      ∀ i j, cov[Y i, Y j; P] ≤ cov[X i, X j; P] := by
  have hvX (i : T) : Var[X i; P] = ∫ ω, (X i ω) ^ 2 ∂P := by
    simp only [variance_eq_integral (hXG.aemeasurable i), hXmean, sub_zero]
  have hvY (i : T) : Var[Y i; P] = ∫ ω, (Y i ω) ^ 2 ∂P := by
    simp only [variance_eq_integral (hYG.aemeasurable i), hYmean, sub_zero]
  have hv (i : T) : Var[X i; P] = Var[Y i; P] := by rw [hvX, hvY, hvar]
  refine ⟨fun i => ?_, fun i j => ?_⟩
  · rw [covariance_self (hXG.aemeasurable i), covariance_self (hYG.aemeasurable i), hv]
  · have hmX : (∫ ω, X i ω - X j ω ∂P) = 0 := by
      rw [integral_sub (hXG.hasGaussianLaw_eval i).integrable
        (hXG.hasGaussianLaw_eval j).integrable, hXmean, hXmean, sub_self]
    have hmY : (∫ ω, Y i ω - Y j ω ∂P) = 0 := by
      rw [integral_sub (hYG.hasGaussianLaw_eval i).integrable
        (hYG.hasGaussianLaw_eval j).integrable, hYmean, hYmean, sub_self]
    have hx := variance_fun_sub (hXG.hasGaussianLaw_eval i).memLp_two
      (hXG.hasGaussianLaw_eval j).memLp_two
    have hy := variance_fun_sub (hYG.hasGaussianLaw_eval i).memLp_two
      (hYG.hasGaussianLaw_eval j).memLp_two
    rw [variance_eq_integral (X := fun ω => X i ω - X j ω) ((hXG.aemeasurable i).sub (hXG.aemeasurable j)), hmX] at hx
    rw [variance_eq_integral (X := fun ω => Y i ω - Y j ω) ((hYG.aemeasurable i).sub (hYG.aemeasurable j)), hmY] at hy
    simp only [sub_zero] at hx hy
    rw [hv i, hv j] at hx
    have hi := hinc i j
    linarith

end SlepianProof

theorem solution {Ω T : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : T → Ω → ℝ)
    (hXG : IsGaussianProcess X P) (hYG : IsGaussianProcess Y P)
    (hXmean : ∀ i, ∫ ω, X i ω ∂P = 0) (hYmean : ∀ i, ∫ ω, Y i ω ∂P = 0)
    (hvar : ∀ i, ∫ ω, (X i ω) ^ 2 ∂P = ∫ ω, (Y i ω) ^ 2 ∂P)
    (hinc : ∀ i j, ∫ ω, (X i ω - X j ω) ^ 2 ∂P ≤
      ∫ ω, (Y i ω - Y j ω) ^ 2 ∂P) :
    (∀ i, cov[X i, X i; P] = cov[Y i, Y i; P]) ∧
      ∀ i j, cov[Y i, Y j; P] ≤ cov[X i, X j; P] := by
  exact SlepianProof.covariance_comparison P X Y hXG hYG hXmean hYmean hvar hinc
