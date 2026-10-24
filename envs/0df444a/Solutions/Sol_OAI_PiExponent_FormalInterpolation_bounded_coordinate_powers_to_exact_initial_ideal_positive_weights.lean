-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.bounded_coordinate_powers_to_exact_initial_ideal_positive_weights
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T19:27:12.093271+00:00
-- url     : https://prove2.me/submissions/e55ccb79-e4cd-4911-b217-43d231a92788

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_coordinate_powers_arithmetic
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_coordinate_powers_algebra

open scoped BigOperators

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (R : Real)
    (hw : ∀ i, 0 < (w i : Real))
    (hsections : ∃ s : Nat, 0 < s ∧ ∃ B : Nat,
      (B : Real) < (s : Real) * R ∧
      ∀ i : Fin d, ∃ n : Nat, 0 < n ∧
        MvPolynomial.X i ^ n ∈ I ^ s ∧
        (n : Real) * (w i : Real) ≤ (B : Real)) :
    ∃ s : Nat, 0 < s ∧ ∃ D : Nat,
      (D : Real) < (s : Real) * R ∧
      0 < D ∧
      ∀ i : Fin d, ∃ n : Nat, 0 < n ∧
        MvPolynomial.X i ^ n ∈ Ideal.span
          {h : MvPolynomial (Fin d) Complex |
            ∃ g : MvPolynomial (Fin d) Complex,
              g ∈ I ^ s ∧
              (∀ a ∈ g.support,
                ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real)) ∧
              h = MvPolynomial.weightedHomogeneousComponent
                (fun k => (w k : ℚ)) (D : ℚ) g} := by
  rcases hsections with ⟨s, hs, B, hBR, hcoord⟩
  obtain ⟨q, D, hq, hDpos, hDcut, hcommon⟩ :=
    OAI.PiExponent.FormalInterpolation.bounded_coordinate_powers_arithmetic
      I w R hw s hs B hBR hcoord
  exact OAI.PiExponent.FormalInterpolation.bounded_coordinate_powers_algebra
    I w R hw s hs B q D hq hDpos hDcut hcommon