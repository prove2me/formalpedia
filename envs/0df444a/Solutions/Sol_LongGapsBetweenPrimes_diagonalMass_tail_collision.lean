-- Prove2me | solution 1 for LongGapsBetweenPrimes.diagonalMass_tail_collision
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:01:12.107502+00:00
-- url     : https://prove2.me/submissions/0dfb74eb-2522-4dfc-90dd-646030211db9

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_tupleMass_nonneg
import Theorems.Thm_LongGapsBetweenPrimes_sum_tupleMass
import Theorems.Thm_LongGapsBetweenPrimes_diagonal_tail_le
import Theorems.Thm_LongGapsBetweenPrimes_diagonal_collision_le

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P M k : ℕ} {β C D : ℝ}
    (h : CoefficientEstimates P β C) (hM : 0 < M)
    (hmin : ∀ p ∈ P.primeFactors, M < p) (hD : 0 < D) (hβ : 0 ≤ β) :
    coefficientMoment P 0 ^ k - diagonalMass P k D ≤
      D ^ (-β) * coefficientMoment P β ^ k +
        (16 * (k : ℝ) ^ 2 / M) * coefficientMoment P 0 ^ k := by
  classical
  calc
    _ ≤ (∑ r ∈ (Finset.univ : Finset (DivisorTuple P k)).filter
          (fun r => D < (tupleProduct r : ℝ)), tupleMass r) +
        ∑ r : DivisorTuple P k, tupleMass r *
          if ¬∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val then 1 else 0 := by
      rw [← sum_tupleMass, diagonalMass, tupleRegion]
      simp only [Finset.sum_filter]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro r _
      have hmass := tupleMass_nonneg r
      split_ifs <;> grind
    _ ≤ _ := add_le_add (diagonal_tail_le P k hD hβ) (diagonal_collision_le h hM hmin)
end LongGapsBetweenPrimes
