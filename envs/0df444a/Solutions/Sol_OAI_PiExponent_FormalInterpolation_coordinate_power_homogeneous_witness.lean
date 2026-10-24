-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.coordinate_power_homogeneous_witness
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T10:03:32.641912+00:00
-- url     : https://prove2.me/submissions/d6f97002-e729-459d-8304-bb60a3ac7b2c

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_homogeneous_mem_span_has_homogeneous_coefficients

open scoped BigOperators

theorem solution
    {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : ℝ))
    (D : Nat) (hD : 0 < D)
    (m : Nat) (p : Fin m → MvPolynomial (Fin d) ℂ)
    (hp : ∀ j, MvPolynomial.IsWeightedHomogeneous w (p j) (D : ℚ))
    (i : Fin d) (N : Nat) (hN : 0 < N)
    (hmem : (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ N ∈ Ideal.span (Set.range p)) :
    ∃ q : Fin m → MvPolynomial (Fin d) ℂ,
      (∀ j, MvPolynomial.IsWeightedHomogeneous w (q j) ((N : ℚ) * w i - (D : ℚ))) ∧
      (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ N = ∑ j, q j * p j := by
  have hX : MvPolynomial.IsWeightedHomogeneous w
      ((MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ N) ((N : ℚ) * w i) := by
    simpa [nsmul_eq_mul] using
      (MvPolynomial.IsWeightedHomogeneous.pow
        (MvPolynomial.isWeightedHomogeneous_X ℂ w i) N)
  exact OAI.PiExponent.FormalInterpolation.homogeneous_mem_span_has_homogeneous_coefficients
    (w := w) (hw := hw) (D := D) (hD := hD) (m := m) (p := p) (hp := hp)
    (f := (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ N) (E := (N : ℚ) * w i) hX hmem
