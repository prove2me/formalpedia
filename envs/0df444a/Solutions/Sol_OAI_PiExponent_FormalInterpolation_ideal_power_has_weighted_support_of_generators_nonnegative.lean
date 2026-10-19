-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.ideal_power_has_weighted_support_of_generators_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T05:48:13.512482+00:00
-- url     : https://prove2.me/submissions/be6fab4b-75d5-42a5-8ef3-202eda339279

import Definitions.Def_OAI_PiExponent_WeightedSupport
import Mathlib.RingTheory.Ideal.Operations
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_hasWeightedSupport_of_mem_span
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_hasWeightedSupport_of_mem_ideal_pow

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution
    {m : ℕ} (v : Fin (m + 1) → ℝ)
    (hv : ∀ i, 0 ≤ v i)
    (R : ℝ) (n : ℕ)
    (f : MvPolynomial (Fin (m + 1)) ℂ →+*
      MvPowerSeries (Fin (m + 1)) ℂ)
    (x : Fin (m + 1) → MvPolynomial (Fin (m + 1)) ℂ)
    (hf0 : ∀ Q, FormalInterpolation.hasWeightedSupport v 0 (f Q))
    (hx : ∀ i, FormalInterpolation.hasWeightedSupport v R (f (x i)))
    (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hP : P ∈ (Ideal.span (Set.range x)) ^ n) :
    FormalInterpolation.hasWeightedSupport v ((n : ℝ) * R) (f P) := by
  have hI : ∀ Q ∈ Ideal.span (Set.range x),
      FormalInterpolation.hasWeightedSupport v R (f Q) := by
    intro Q hQ
    exact OAI.PiExponent.FormalInterpolation.hasWeightedSupport_of_mem_span
      v R f x hf0 hx Q hQ
  exact OAI.PiExponent.FormalInterpolation.hasWeightedSupport_of_mem_ideal_pow
    (I := Ideal.span (Set.range x)) v R n f hf0 hI P hP