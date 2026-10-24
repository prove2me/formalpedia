-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.homogeneous_coefficients_of_span_coordinate_power
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:21:30.027442+00:00
-- url     : https://prove2.me/submissions/23cdb01d-8121-45ab-b9f7-9836abe917ab

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_homogeneous_coefficients_of_explicit_relation

open scoped BigOperators

theorem solution
    {d : Nat} (w : Fin d → ℚ)
    (D : Nat) (m : Nat)
    (p : Fin m → MvPolynomial (Fin d) Complex)
    (hp : ∀ j, MvPolynomial.IsWeightedHomogeneous w (p j) (D : ℚ))
    (i : Fin d) (N : Nat) (hN : 0 < N)
    (hmem : MvPolynomial.X i ^ N ∈ Ideal.span (Set.range p)) :
    ∃ c : Fin m → MvPolynomial (Fin d) Complex,
      (∀ j, MvPolynomial.IsWeightedHomogeneous w (c j) (N • w i - (D : ℚ))) ∧
      MvPolynomial.X i ^ N = ∑ j : Fin m, c j * p j := by
  obtain ⟨a, ha⟩ :=
    (Ideal.mem_span_range_iff_exists_fun (x := MvPolynomial.X i ^ N) (v := p)).mp hmem
  have hX : MvPolynomial.IsWeightedHomogeneous w (MvPolynomial.X i ^ N) (N • w i) :=
    (MvPolynomial.isWeightedHomogeneous_X (R := Complex) w i).pow N
  exact OAI.PiExponent.FormalInterpolation.homogeneous_coefficients_of_explicit_relation
    w D m p hp (MvPolynomial.X i ^ N) (N • w i) hX a ha
