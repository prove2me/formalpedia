-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.bounded_sections_finite_witness_20261023_21
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:39:15.445961+00:00
-- url     : https://prove2.me/submissions/7d4f5414-52b8-4e19-9e17-2c0cc8ee9bb6

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_sections_finite_witness_20261023_22

open scoped BigOperators

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (s D : Nat)
    (hpoint : ∀ x : Fin d → Complex,
      (∃ i : Fin d, x i ≠ 0) →
      ∃ g : MvPolynomial (Fin d) Complex,
        g ∈ I ^ s ∧
        (∀ a ∈ g.support,
          ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real)) ∧
        MvPolynomial.eval x
          (MvPolynomial.weightedHomogeneousComponent
            (fun k => (w k : ℚ)) (D : ℚ) g) ≠ 0) :
    ∃ m : Nat, ∃ g : Fin m → MvPolynomial (Fin d) Complex,
      (∀ j, g j ∈ I ^ s) ∧
      (∀ j, ∀ a ∈ (g j).support,
        ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real)) ∧
      ∀ x : Fin d → Complex,
        (∀ j : Fin m,
          MvPolynomial.eval x
            (MvPolynomial.weightedHomogeneousComponent
              (fun k => (w k : ℚ)) (D : ℚ) (g j)) = 0) →
        ∀ i : Fin d, x i = 0 := by
  apply OAI.PiExponent.FormalInterpolation.bounded_sections_finite_witness_20261023_22 <;> assumption
