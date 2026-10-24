-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_adjoin_of_coordinate_powers
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:56:30.844995+00:00
-- url     : https://prove2.me/submissions/ea57b7dc-c7ea-47bc-b077-3960ee8cbaf2

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinate_power_homogeneous_witness
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_module_of_homogeneous_coordinate_relations

open scoped BigOperators

theorem solution
    {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : ℝ))
    (D : Nat) (hD : 0 < D)
    (m : Nat) (p : Fin m → MvPolynomial (Fin d) ℂ)
    (hp : ∀ j, MvPolynomial.IsWeightedHomogeneous w (p j) (D : ℚ))
    (hpow : ∀ i : Fin d, ∃ N : Nat, 0 < N ∧
      (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ N ∈ Ideal.span (Set.range p)) :
    Module.Finite (Algebra.adjoin ℂ (Set.range p)) (MvPolynomial (Fin d) ℂ) := by
  have hrels : ∀ i : Fin d, ∃ N : Nat, 0 < N ∧
      ∃ q : Fin m → MvPolynomial (Fin d) ℂ,
        (∀ j, MvPolynomial.IsWeightedHomogeneous w (q j) ((N : ℚ) * w i - (D : ℚ))) ∧
        (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ N = ∑ j, q j * p j := by
    intro i
    obtain ⟨N, hN, hmem⟩ := hpow i
    exact ⟨N, hN,
      OAI.PiExponent.FormalInterpolation.coordinate_power_homogeneous_witness
        w hw D hD m p hp i N hN hmem⟩
  exact OAI.PiExponent.FormalInterpolation.finite_module_of_homogeneous_coordinate_relations
    w hw D hD m p hp hrels
