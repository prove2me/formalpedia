-- Prove2me | solution 1 for LongGapsBetweenPrimes.prime_dvd_assignmentProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:05:04.596486+00:00
-- url     : https://prove2.me/submissions/c0c05864-c87a-4f4a-9047-a421e70dd378

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k : ℕ} (σ : PrimeIndex P → Option (Fin k))
    (p : PrimeIndex P) (hp : (σ p).isSome) :
    p.val ∣ assignmentProduct (fun p : PrimeIndex P => p.val) σ := by
  exact Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)
end LongGapsBetweenPrimes
