-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_adjoin_of_homogeneous_coordinate_power_relations
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:17:48.460563+00:00
-- url     : https://prove2.me/submissions/4db8d878-96ba-4deb-ab2b-6c2666efbb43

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_quotient_of_coordinate_powers_in_ideal
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_adjoin_of_homogeneous_quotient

open scoped BigOperators

theorem solution
    {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : Real))
    (D : Nat) (hD : 0 < D)
    (m : Nat) (p : Fin m → MvPolynomial (Fin d) Complex)
    (hp : ∀ j, MvPolynomial.IsWeightedHomogeneous w (p j) (D : ℚ))
    (hrel : ∀ i : Fin d, ∃ N : Nat, 0 < N ∧
      ∃ c : Fin m → MvPolynomial (Fin d) Complex,
        (∀ j, MvPolynomial.IsWeightedHomogeneous w (c j) (N • w i - (D : ℚ))) ∧
        MvPolynomial.X i ^ N = ∑ j : Fin m, c j * p j) :
    Module.Finite (Algebra.adjoin Complex (Set.range p)) (MvPolynomial (Fin d) Complex) := by
  have hpow : ∀ i : Fin d, ∃ N : Nat, 0 < N ∧
      MvPolynomial.X i ^ N ∈ Ideal.span (Set.range p) := by
    intro i
    obtain ⟨N, hN, c, hc, hEq⟩ := hrel i
    refine ⟨N, hN, ?_⟩
    rw [hEq]
    apply Ideal.sum_mem
    intro j hj
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
  have hquot :=
    OAI.PiExponent.FormalInterpolation.finite_quotient_of_coordinate_powers_in_ideal
      d m p hpow
  exact OAI.PiExponent.FormalInterpolation.finite_adjoin_of_homogeneous_quotient
    (w := w) hw D hD m p hp hquot