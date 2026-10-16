-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.hasWeightedSupport_of_mem_ideal_span_generators
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T06:26:55.863218+00:00
-- url     : https://prove2.me/submissions/4173a154-d0a0-4462-b811-76e82442943b

import Definitions.Def_OAI_PiExponent_WeightedSupport
import Mathlib.RingTheory.Ideal.Operations
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_hasWeightedSupport_zero_closure
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_hasWeightedSupport_add_closure
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_hasWeightedSupport_mul_closure

open OAI.PiExponent.FormalInterpolation

theorem solution {m : ℕ} (v : Fin (m + 1) → ℝ) (B : ℝ)
    (f : MvPolynomial (Fin (m + 1)) ℂ →+* MvPowerSeries (Fin (m + 1)) ℂ)
    (hf0 : ∀ Q, hasWeightedSupport v 0 (f Q))
    (S : Set (MvPolynomial (Fin (m + 1)) ℂ))
    (hS : ∀ Q ∈ S, hasWeightedSupport v B (f Q))
    (P : MvPolynomial (Fin (m + 1)) ℂ) (hP : P ∈ Ideal.span S) :
    hasWeightedSupport v B (f P) := by
  refine Submodule.span_induction
    (p := fun Q _ => hasWeightedSupport v B (f Q)) ?_ ?_ ?_ ?_ hP
  · intro Q hQ
    exact hS Q hQ
  · simpa only [map_zero] using hasWeightedSupport_zero_closure v B
  · intro Q R _ _ hQ hR
    simpa only [map_add] using
      hasWeightedSupport_add_closure v B (f Q) (f R) hQ hR
  · intro Q R _ hR
    change hasWeightedSupport v B (f (Q * R))
    rw [map_mul]
    exact hasWeightedSupport_mul_closure v B (f Q) (f R) (hf0 Q) hR
