-- Prove2me | solution 1 for LongGapsBetweenPrimes.residueWeight_interval_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:10:44.065911+00:00
-- url     : https://prove2.me/submissions/02effdab-9402-4d07-bf59-40f551bef19f

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_abs_rawLocalBasis_le_one
import Theorems.Thm_LongGapsBetweenPrimes_basisWeight_interval_error

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k T : ℕ} (hP : Squarefree P) (hT : 0 < T)
    {D : ℝ} (hD : 1 ≤ D)
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (hroot : ∀ p, Function.Injective (root p))
    (hcoeff : ∀ d ∈ P.divisors, |coefficient P d| ≤ 1) :
    |integerAverage T (fun n => residueWeight P k D root (residueVector P n) ^ 2) -
      Finset.expect Finset.univ (fun t => residueWeight P k D root t ^ 2)| ≤ 16 * D ^ 6 / T :=
  basisWeight_interval_error hP hT hD root hroot hcoeff (fun p => rawLocalBasis (root p))
    (fun _ _ => rfl) (fun p i t =>
      abs_rawLocalBasis_le_one (Nat.mem_primeFactors.mp p.property).1.one_lt _ i t)
end LongGapsBetweenPrimes
