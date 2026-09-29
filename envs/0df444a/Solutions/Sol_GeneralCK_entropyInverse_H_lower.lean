-- Prove2me | solution 1 for GeneralCK.entropyInverse_H_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T20:56:53.838452+00:00
-- url     : https://prove2.me/submissions/c8f1cf16-e7c8-48b8-a118-c60a3ad88b93

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_GeneralCK_statement
import Definitions.Def_GeneralCK_bellman
import Theorems.Thm_GeneralCK_H_strictMonoOn

/-! Precise target, not a proof of the Courtade--Kumar conjecture. -/
namespace GeneralCK
open scoped BigOperators





























end GeneralCK

open GeneralCK
theorem solution {v : ℝ} (hv : 0 ≤ v) (hv' : v ≤ 1 / 2) :
    entropyInverse (H v) = v := by
  apply le_antisymm
  · apply csInf_le
    · exact ⟨0, fun _ hx => hx.1⟩
    · exact ⟨hv, hv', le_rfl⟩
  · apply le_csInf
    · exact ⟨v, hv, hv', le_rfl⟩
    · intro b hb
      by_contra hn
      have := H_strictMonoOn ⟨hb.1, hb.2.1⟩ ⟨hv, hv'⟩ (lt_of_not_ge hn)
      exact (not_lt_of_ge hb.2.2) this
