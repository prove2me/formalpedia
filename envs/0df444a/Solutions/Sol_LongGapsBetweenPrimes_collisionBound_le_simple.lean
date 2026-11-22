-- Prove2me | solution 1 for LongGapsBetweenPrimes.collisionBound_le_simple
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:10:48.970492+00:00
-- url     : https://prove2.me/submissions/7c289c82-5bda-4596-8fad-0c1f208022c5

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {n : ℕ} {M x : ℝ} (hx : 0 < x)
    (hn : (n : ℝ) ≤ x) (hM : x ^ 4 ≤ M) :
    16 * (n : ℝ) ^ 2 / M ≤ 16 / x ^ 2 := by
  calc
    16 * (n : ℝ) ^ 2 / M ≤ 16 * x ^ 2 / x ^ 4 := by gcongr
    _ = 16 / x ^ 2 := by field_simp
end LongGapsBetweenPrimes
