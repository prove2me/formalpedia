-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.hasWeightedSupport_of_mem_ideal_pow
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T06:06:32.971928+00:00
-- url     : https://prove2.me/submissions/998965e8-65bf-4cc7-9316-41bc42bdc289

import Definitions.Def_OAI_PiExponent_WeightedSupport
import Mathlib.RingTheory.Ideal.Operations
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_pow_eq_span_fin_products
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_hasWeightedSupport_fin_product
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_hasWeightedSupport_of_mem_ideal_span_generators

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

open scoped BigOperators

theorem solution
    {m : ℕ} (v : Fin (m + 1) → ℝ)
    (R : ℝ) (n : ℕ)
    (f : MvPolynomial (Fin (m + 1)) ℂ →+*
      MvPowerSeries (Fin (m + 1)) ℂ)
    (I : Ideal (MvPolynomial (Fin (m + 1)) ℂ))
    (hf0 : ∀ Q, FormalInterpolation.hasWeightedSupport v 0 (f Q))
    (hI : ∀ Q, Q ∈ I → FormalInterpolation.hasWeightedSupport v R (f Q))
    (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hP : P ∈ I ^ n) :
    FormalInterpolation.hasWeightedSupport v ((n : ℝ) * R) (f P) := by
  classical
  let S : Set (MvPolynomial (Fin (m + 1)) ℂ) :=
    {Q | ∃ s : Fin n → MvPolynomial (Fin (m + 1)) ℂ,
      (∀ i, s i ∈ I) ∧ Q = ∏ i, s i}
  have hpow : I ^ n = Ideal.span S := by
    simpa [S] using
      (FormalInterpolation.pow_eq_span_fin_products I n)
  have hgen : ∀ Q ∈ S,
      FormalInterpolation.hasWeightedSupport v ((n : ℝ) * R) (f Q) := by
    intro Q hQ
    rcases hQ with ⟨s, hsI, rfl⟩
    exact FormalInterpolation.hasWeightedSupport_fin_product
      v R n f I hf0 hI s hsI
  rw [hpow] at hP
  exact FormalInterpolation.hasWeightedSupport_of_mem_ideal_span_generators
    v ((n : ℝ) * R) f hf0 S hgen P hP