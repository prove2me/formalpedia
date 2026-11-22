-- Prove2me | solution 1 for LongGapsBetweenPrimes.basisWeight_interval_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:08:40.549802+00:00
-- url     : https://prove2.me/submissions/0e82f441-1d6d-417d-a26d-349236e04e04

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_assignmentProduct_tupleAssignment
import Theorems.Thm_LongGapsBetweenPrimes_assignmentProduct_pos
import Theorems.Thm_LongGapsBetweenPrimes_assignmentProduct_dvd
import Theorems.Thm_LongGapsBetweenPrimes_tupleRegion_card_le
import Theorems.Thm_LongGapsBetweenPrimes_integerAverage_bounded_periodic_weight
import Theorems.Thm_LongGapsBetweenPrimes_integerAverage_residues
import Theorems.Thm_LongGapsBetweenPrimes_abs_productBasis_le_one
import Theorems.Thm_LongGapsBetweenPrimes_tupleAmplitude_abs_le
import Theorems.Thm_LongGapsBetweenPrimes_basisProduct_mod_invariant

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k T : ℕ} (hP : Squarefree P) (hT : 0 < T)
    {D : ℝ} (hD : 1 ≤ D)
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (hroot : ∀ p, Function.Injective (root p))
    (hcoeff : ∀ d ∈ P.divisors, |coefficient P d| ≤ 1)
    (f : (p : PrimeIndex P) → Option (Fin k) → Fin p.val → ℝ)
    (hfnone : ∀ p t, f p none t = 1) (hf : ∀ p i t, |f p i t| ≤ 1) :
    |integerAverage T (fun n => basisWeight P k D f (residueVector P n) ^ 2) -
      Finset.expect Finset.univ (fun t => basisWeight P k D f t ^ 2)| ≤ 16 * D ^ 6 / T := by
  rw [← integerAverage_residues hP (fun t => basisWeight P k D f t ^ 2)]
  have hcut (r : tupleRegion P k D) :
      (assignmentProduct (fun p : PrimeIndex P => p.val) (tupleAssignment r.val) : ℝ) ≤ D := by
    rw [assignmentProduct_tupleAssignment hP r.val (Finset.mem_filter.mp r.property).2.1]
    exact (Finset.mem_filter.mp r.property).2.2
  calc
    _ ≤ (Fintype.card (tupleRegion P k D) : ℝ) ^ 2 * (D ^ 2 / T) :=
      integerAverage_bounded_periodic_weight (Nat.pos_of_ne_zero hP.ne_zero) hT
        (zero_le_one.trans hD)
        (fun r : tupleRegion P k D =>
          assignmentProduct (fun p : PrimeIndex P => p.val) (tupleAssignment r.val))
        (fun r => assignmentProduct_pos _) (fun r => assignmentProduct_dvd _) hcut
        (fun r => tupleAmplitude r.val) (fun r => tupleAmplitude_abs_le hcoeff r.val)
        (fun r n => productBasis f (tupleAssignment r.val) (residueVector P n))
        (fun r n => abs_productBasis_le_one f hf _ _)
        (fun r n => basisProduct_mod_invariant f hfnone _ _)
    _ ≤ (4 * D ^ 2) ^ 2 * (D ^ 2 / T) := by
      gcongr
      exact tupleRegion_card_le hP hD root hroot
    _ = 16 * D ^ 6 / T := by ring
end LongGapsBetweenPrimes
