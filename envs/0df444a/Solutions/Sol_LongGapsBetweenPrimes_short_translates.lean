-- Prove2me | solution 1 for LongGapsBetweenPrimes.short_translates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:22:24.32435+00:00
-- url     : https://prove2.me/submissions/e59b364c-48b8-4e91-bd5d-cd37d477135b

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_sieveDelta_pos
import Theorems.Thm_LongGapsBetweenPrimes_sieveDelta_lt_half
import Theorems.Thm_LongGapsBetweenPrimes_short_translates_with_sieveDelta

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution : ShortTranslates :=
  ⟨sieveDelta, sieveDelta_pos, sieveDelta_lt_half, short_translates_with_sieveDelta⟩
end LongGapsBetweenPrimes
