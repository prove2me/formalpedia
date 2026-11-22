-- Prove2me | solution 1 for LongGapsBetweenPrimes.exists_simultaneous_root_of_moments
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:10:39.24178+00:00
-- url     : https://prove2.me/submissions/93a524a6-8b62-4850-a84a-080bd6d61312

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_residueWeight_eq_replaced_of_uncovered

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k T : ℕ} {D L U : ℝ}
    (root : (p : PrimeIndex P) → Fin k → Fin p.val)
    (hlower : L ≤ integerAverage T (fun n => residueWeight P k D root (residueVector P n) ^ 2))
    (hupper : ∀ i,
      integerAverage T (fun n => replacedResidueWeight P k D root i (residueVector P n) ^ 2) ≤ U)
    (hgap : (k : ℝ) * U < L) :
    ∃ n < T, ∀ i : Fin k, ∃ p : PrimeIndex P, residueVector P n p = root p i := by
  classical
  by_contra! h
  have hpointwise (n : ℕ) (hn : n ∈ Finset.range T) :
      residueWeight P k D root (residueVector P n) ^ 2 ≤
        ∑ i, replacedResidueWeight P k D root i (residueVector P n) ^ 2 := by
    obtain ⟨i, hi⟩ := h n (Finset.mem_range.mp hn)
    rw [residueWeight_eq_replaced_of_uncovered D root i (residueVector P n) hi]
    apply Finset.single_le_sum ?_ (Finset.mem_univ i)
    intro j _
    exact sq_nonneg _
  apply (not_le_of_gt hgap)
  calc
    L ≤ integerAverage T (fun n => residueWeight P k D root (residueVector P n) ^ 2) := hlower
    _ ≤ ∑ i, integerAverage T
        (fun n => replacedResidueWeight P k D root i (residueVector P n) ^ 2) := by
      unfold integerAverage
      rw [← Finset.sum_div, Finset.sum_comm]
      exact div_le_div_of_nonneg_right (Finset.sum_le_sum hpointwise) (Nat.cast_nonneg T)
    _ ≤ ∑ _i : Fin k, U := Finset.sum_le_sum (fun i _ => hupper i)
    _ = (k : ℝ) * U := by simp
end LongGapsBetweenPrimes
