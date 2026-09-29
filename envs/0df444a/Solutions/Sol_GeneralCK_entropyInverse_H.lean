-- Prove2me | solution 1 for GeneralCK.entropyInverse_H
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T20:57:29.295996+00:00
-- url     : https://prove2.me/submissions/26007f13-26a4-4efd-a881-325a61da2b75

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_GeneralCK_statement
import Definitions.Def_GeneralCK_bellman
import Theorems.Thm_GeneralCK_entropyInverse_H_lower

/-! Precise target, not a proof of the Courtade--Kumar conjecture. -/
namespace GeneralCK
open scoped BigOperators





















theorem H_complement (p : ℝ) : H (1 - p) = H p := by simp [H]







end GeneralCK

open GeneralCK
theorem solution {m : ℝ} (hm : 0 ≤ m) (hm' : m ≤ 1) :
    entropyInverse (H m) = min m (1 - m) := by
  by_cases hl : m ≤ 1 / 2
  · rw [entropyInverse_H_lower hm hl, min_eq_left (by linarith)]
  · rw [← H_complement m, entropyInverse_H_lower (by linarith) (by linarith),
      min_eq_right (by linarith)]
