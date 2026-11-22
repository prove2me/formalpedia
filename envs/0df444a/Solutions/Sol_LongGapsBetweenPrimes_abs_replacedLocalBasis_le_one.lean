-- Prove2me | solution 1 for LongGapsBetweenPrimes.abs_replacedLocalBasis_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:09:30.311125+00:00
-- url     : https://prove2.me/submissions/f8cfb5fd-9821-4661-b68a-cdc98b725ce0

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_abs_residueFactor_le_one

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {p k : ℕ} (hp : 1 < p)
    (root : Fin k → Fin p) (i : Fin k) (j : Option (Fin k)) (t : Fin p) :
    |replacedLocalBasis root i j t| ≤ 1 := by
  cases j with
  | none => simp [replacedLocalBasis]
  | some j =>
      simp only [replacedLocalBasis]
      split_ifs
      · have hp' : (2 : ℝ) ≤ p := by exact_mod_cast Nat.succ_le_of_lt hp
        rw [abs_of_nonneg (div_nonneg zero_le_one (by linarith))]
        exact (div_le_one (by linarith)).mpr (by linarith)
      · exact abs_residueFactor_le_one hp _ _
end LongGapsBetweenPrimes
