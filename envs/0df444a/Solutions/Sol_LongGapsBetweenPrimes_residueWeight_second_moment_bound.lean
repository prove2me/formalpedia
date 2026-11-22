-- Prove2me | solution 1 for LongGapsBetweenPrimes.residueWeight_second_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:08:02.437464+00:00
-- url     : https://prove2.me/submissions/621094d5-2409-4410-9b29-13b96c68c573

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_assignment_row_bound
import Theorems.Thm_LongGapsBetweenPrimes_assignmentProduct_tupleAssignment
import Theorems.Thm_LongGapsBetweenPrimes_residueWeight_second_moment

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k : ℕ} (hP : Squarefree P) (hk : 1 ≤ k)
    {M D : ℝ} (hM : 1 < M) (hmin : ∀ p ∈ P.primeFactors, M ≤ (p : ℝ))
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (hroot : ∀ p, Function.Injective (root p)) :
    |Finset.expect Finset.univ (fun t => residueWeight P k D root t ^ 2) - diagonalMass P k D| ≤
      (Real.exp ((k : ℝ) * Real.log D / ((M - 1) * Real.log M)) - 1) * diagonalMass P k D := by
  apply residueWeight_second_moment hP D root hroot
  intro r
  apply sub_le_sub_right _ 1
  apply assignment_row_bound (fun p : PrimeIndex P => p.val) hk (tupleAssignment r.val) hM
    (fun p => hmin p.val p.property)
  rw [assignmentProduct_tupleAssignment hP r.val (Finset.mem_filter.mp r.property).2.1]
  exact (Finset.mem_filter.mp r.property).2.2
end LongGapsBetweenPrimes
