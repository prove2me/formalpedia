-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.homogeneous_coordinate_power_sum_mem
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:28:56.382895+00:00
-- url     : https://prove2.me/submissions/e79f816f-cf59-4034-ba07-cafe1a22d312

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_span_range_component_mem
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinate_power_sum_component

open scoped BigOperators

theorem solution
    {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : ℝ))
    (D : Nat) (hD : 0 < D)
    (m : Nat) (p : Fin m → MvPolynomial (Fin d) ℂ)
    (hp : ∀ j, MvPolynomial.IsWeightedHomogeneous w (p j) (D : ℚ))
    (i : Fin d) (K : Nat) (c : Fin (K + 1) → ℂ)
    (hsum : (∑ n : Fin (K + 1), MvPolynomial.C (c n) *
      (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ (n : Nat)) ∈
      Ideal.span (Set.range p)) :
    ∀ n : Fin (K + 1), MvPolynomial.C (c n) *
      (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ (n : Nat) ∈
      Ideal.span (Set.range p) := by
  intro n
  have hn := OAI.PiExponent.FormalInterpolation.span_range_component_mem
    (w := w) (D := D) (m := m) (p := p) (hp := hp)
    (∑ k : Fin (K + 1), MvPolynomial.C (c k) *
      (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ (k : Nat)) hsum
    (((n : ℕ) : ℚ) * w i)
  rw [OAI.PiExponent.FormalInterpolation.coordinate_power_sum_component
    (w := w) (i := i) (K := K) (c := c) (hw := hw) n] at hn
  exact hn