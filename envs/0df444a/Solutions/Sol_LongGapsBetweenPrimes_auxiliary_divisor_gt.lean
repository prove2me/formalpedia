-- Prove2me | solution 1 for LongGapsBetweenPrimes.auxiliary_divisor_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:57:04.078609+00:00
-- url     : https://prove2.me/submissions/f6ace911-f41c-488e-b8e3-b534328fe3df

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_mem_auxiliaryPrimes
import Theorems.Thm_LongGapsBetweenPrimes_prime_dvd_auxiliaryProduct

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {Z Y d : ℕ} (hd : d ∈ (auxiliaryProduct Z Y).divisors.erase 1) :
    Z < d := by
  obtain ⟨hd1, hd⟩ := Finset.mem_erase.mp hd
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd1
  have hpP := prime_dvd_auxiliaryProduct hp (hpd.trans (Nat.mem_divisors.mp hd).1)
  exact (mem_auxiliaryPrimes.mp hpP).2.1.trans_le
    (Nat.le_of_dvd (Nat.pos_of_mem_divisors hd) hpd)
end LongGapsBetweenPrimes
