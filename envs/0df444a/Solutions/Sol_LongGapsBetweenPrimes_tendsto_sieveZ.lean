-- Prove2me | solution 1 for LongGapsBetweenPrimes.tendsto_sieveZ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:31:27.316785+00:00
-- url     : https://prove2.me/submissions/7f1816ea-48e6-410a-8f31-20dc2146f241

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution : Filter.Tendsto sieveZ Filter.atTop Filter.atTop :=
  tendsto_nat_floor_atTop.comp (Filter.tendsto_pow_atTop (by decide : (6 : ℕ) ≠ 0))
end LongGapsBetweenPrimes
