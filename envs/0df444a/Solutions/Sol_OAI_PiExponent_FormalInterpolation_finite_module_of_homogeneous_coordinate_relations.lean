-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_module_of_homogeneous_coordinate_relations
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T10:04:29.923238+00:00
-- url     : https://prove2.me/submissions/d18d367d-8bd1-4784-b3a9-0cd9f9f7a488

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinate_power_relations_finite_quotient
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_quotient_filtered_lifting

open scoped BigOperators

theorem solution
    {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : ℝ))
    (D : Nat) (hD : 0 < D)
    (m : Nat) (p : Fin m → MvPolynomial (Fin d) ℂ)
    (hp : ∀ j, MvPolynomial.IsWeightedHomogeneous w (p j) (D : ℚ))
    (hrels : ∀ i : Fin d, ∃ N : Nat, 0 < N ∧
      ∃ q : Fin m → MvPolynomial (Fin d) ℂ,
        (∀ j, MvPolynomial.IsWeightedHomogeneous w (q j) ((N : ℚ) * w i - (D : ℚ))) ∧
        (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ N = ∑ j, q j * p j) :
    Module.Finite (Algebra.adjoin ℂ (Set.range p)) (MvPolynomial (Fin d) ℂ) := by
  have hpower : ∀ i : Fin d, ∃ N : Nat, 0 < N ∧
      ∃ q : Fin m → MvPolynomial (Fin d) ℂ,
        (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ N = ∑ j, q j * p j := by
    intro i
    rcases hrels i with ⟨N, hN, q, _hqhom, hrel⟩
    exact ⟨N, hN, q, hrel⟩
  have hquot :
      Module.Finite ℂ
        (MvPolynomial (Fin d) ℂ ⧸ Ideal.span (Set.range p)) :=
    OAI.PiExponent.FormalInterpolation.coordinate_power_relations_finite_quotient
      d m p hpower
  exact OAI.PiExponent.FormalInterpolation.finite_quotient_filtered_lifting
    w hw D hD m p hp hquot
