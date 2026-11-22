-- Prove2me | solution 1 for LongGapsBetweenPrimes.abs_rawLocalBasis_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:04:24.9308+00:00
-- url     : https://prove2.me/submissions/5d262265-f25d-4503-9d4c-3b9935c0543b

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_abs_residueFactor_le_one

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {p k : ℕ} (hp : 1 < p) (root : Fin k → Fin p)
    (i : Option (Fin k)) (t : Fin p) : |rawLocalBasis root i t| ≤ 1 := by
  cases i with
  | none => simp [rawLocalBasis]
  | some j => exact abs_residueFactor_le_one hp _ _
end LongGapsBetweenPrimes
