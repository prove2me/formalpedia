-- Prove2me | solution 1 for LongGapsBetweenPrimes.prime_dvd_auxiliaryProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:33:28.497202+00:00
-- url     : https://prove2.me/submissions/62fab0db-e949-405b-a388-f976ae5f4dee

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_auxiliaryPrimes_prime

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {Z Y p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ auxiliaryProduct Z Y) : p ∈ auxiliaryPrimes Z Y := by
  obtain ⟨q, hq, hpq⟩ := ((Nat.prime_iff.mp hp).dvd_finsetProd_iff id).mp hdvd
  exact ((Nat.prime_dvd_prime_iff_eq hp (auxiliaryPrimes_prime hq)).mp hpq).symm ▸ hq
end LongGapsBetweenPrimes
