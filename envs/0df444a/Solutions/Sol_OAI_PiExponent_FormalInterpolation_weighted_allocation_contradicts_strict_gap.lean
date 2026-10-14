-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_allocation_contradicts_strict_gap
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T08:33:50.625868+00:00
-- url     : https://prove2.me/submissions/30103440-e31c-476f-aafd-38bc2cceb124

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem solution
    {m n : Nat} (v : Fin (m + 1) → Real) (R : Fin n → Real)
    (a : Fin (m + 1) → Nat)
    (F : Fin n → MvPolynomial (Fin (m + 1)) Complex)
    (hcoeff : ∀ i b, b ≤ a →
      MvPolynomial.coeff (InterpolationMatrix.exponentVector b) (F i) ≠ 0 →
        R i ≤ ∑ j, v j * (b j : Real))
    (hweight : ∑ j, v j * (a j : Real) < ∑ i, R i)
    (b : Fin n → Fin (m + 1) → Nat)
    (hbound : ∀ i, b i ≤ a)
    (hsum : ∀ j, (∑ i, b i j) = a j)
    (hnz : ∀ i, MvPolynomial.coeff (InterpolationMatrix.exponentVector (b i)) (F i) ≠ 0) :
    False := by
  classical
  have htotal : (∑ i, R i) ≤ ∑ i, ∑ j, v j * (b i j : Real) := by
    apply Finset.sum_le_sum
    intro i hi
    exact hcoeff i (b i) (hbound i) (hnz i)
  have hsumweight : (∑ i, ∑ j, v j * (b i j : Real)) =
      ∑ j, v j * (a j : Real) := by
    calc
      (∑ i, ∑ j, v j * (b i j : Real)) =
          ∑ j, ∑ i, v j * (b i j : Real) := Finset.sum_comm
      _ = ∑ j, v j * (∑ i, (b i j : Real)) := by
        simp [Finset.mul_sum]
      _ = ∑ j, v j * ((∑ i, b i j : Nat) : Real) := by
        simp
      _ = ∑ j, v j * (a j : Real) := by simp_rw [hsum]
  linarith
