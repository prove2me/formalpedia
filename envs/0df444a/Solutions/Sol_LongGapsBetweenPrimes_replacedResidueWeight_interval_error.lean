-- Prove2me | solution 1 for LongGapsBetweenPrimes.replacedResidueWeight_interval_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:10:59.251812+00:00
-- url     : https://prove2.me/submissions/cb45a048-7c22-435c-9cbd-6c8dcc9e8114

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_basisWeight_interval_error
import Theorems.Thm_LongGapsBetweenPrimes_abs_replacedLocalBasis_le_one

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k T : ℕ} (hP : Squarefree P) (hT : 0 < T)
    {D : ℝ} (hD : 1 ≤ D)
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (hroot : ∀ p, Function.Injective (root p))
    (hcoeff : ∀ d ∈ P.divisors, |coefficient P d| ≤ 1) (i : Fin k) :
    |integerAverage T (fun n => replacedResidueWeight P k D root i (residueVector P n) ^ 2) -
      Finset.expect Finset.univ (fun t => replacedResidueWeight P k D root i t ^ 2)| ≤
        16 * D ^ 6 / T :=
  basisWeight_interval_error hP hT hD root hroot hcoeff (fun p => replacedLocalBasis (root p) i)
    (fun _ _ => rfl)
    (fun p j t => abs_replacedLocalBasis_le_one
      (Nat.mem_primeFactors.mp p.property).1.one_lt _ i j t)
end LongGapsBetweenPrimes
