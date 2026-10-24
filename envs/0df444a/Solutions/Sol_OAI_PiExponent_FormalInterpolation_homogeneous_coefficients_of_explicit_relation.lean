-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.homogeneous_coefficients_of_explicit_relation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:26:11.735907+00:00
-- url     : https://prove2.me/submissions/c62f79bc-8a20-4799-b596-1758e430ce2f

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weightedHomogeneousComponent_mul_of_right_homogeneous

open scoped BigOperators

theorem solution
    {d : Nat} (w : Fin d → ℚ)
    (D : Nat) (m : Nat)
    (p : Fin m → MvPolynomial (Fin d) Complex)
    (hp : ∀ j, MvPolynomial.IsWeightedHomogeneous w (p j) (D : ℚ))
    (f : MvPolynomial (Fin d) Complex) (E : ℚ)
    (hf : MvPolynomial.IsWeightedHomogeneous w f E)
    (a : Fin m → MvPolynomial (Fin d) Complex)
    (ha : ∑ j : Fin m, a j * p j = f) :
    ∃ c : Fin m → MvPolynomial (Fin d) Complex,
      (∀ j, MvPolynomial.IsWeightedHomogeneous w (c j) (E - (D : ℚ))) ∧
      f = ∑ j : Fin m, c j * p j := by
  classical
  let c : Fin m → MvPolynomial (Fin d) Complex :=
    fun j => MvPolynomial.weightedHomogeneousComponent w (E - (D : ℚ)) (a j)
  refine ⟨c, ?_, ?_⟩
  · intro j
    dsimp [c]
    exact MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (w := w) (n := E - (D : ℚ)) (φ := a j)
  · change f = ∑ j : Fin m, c j * p j
    calc
      f = MvPolynomial.weightedHomogeneousComponent w E f := by
        symm
        exact hf.weightedHomogeneousComponent_same
      _ = MvPolynomial.weightedHomogeneousComponent w E
          (∑ j : Fin m, a j * p j) := by rw [ha]
      _ = ∑ j : Fin m,
          MvPolynomial.weightedHomogeneousComponent w E (a j * p j) := by
        simp only [map_sum]
      _ = ∑ j : Fin m, c j * p j := by
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [c]
        exact OAI.PiExponent.FormalInterpolation.weightedHomogeneousComponent_mul_of_right_homogeneous
          (w := w) (D := (D : ℚ)) (E := E) (a := a j) (p := p j) (hp := hp j)