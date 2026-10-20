-- Prove2me | solution 1 for HardyLittlewood.twin_tuple_admissible
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T21:56:16.164701+00:00
-- url     : https://prove2.me/submissions/5e732248-20a4-4b84-b5e1-ba7a75b32a29

import Mathlib
import Definitions.Def_HardyLittlewood_constellation
import Definitions.Def_HardyLittlewood_counting
import Definitions.Def_HardyLittlewood_series

open HardyLittlewood

theorem solution : IsAdmissibleTuple (![0, 1] : Fin 2 → ℕ) := by
  intro q hq hs
  obtain ⟨i, hi⟩ := hs 1
  have h2 := hq.two_le
  haveI : Fact q.Prime := ⟨hq⟩
  fin_cases i
  · simp at hi
  · simp at hi
    -- (2 : ZMod q) = 1 → q ∣ 1
    have : ((2 : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) := by simpa using hi
    rw [ZMod.natCast_eq_natCast_iff'] at this
    rw [Nat.mod_eq_of_lt (by omega : 1 < q)] at this
    rcases Nat.lt_or_ge 2 q with h | h
    · rw [Nat.mod_eq_of_lt h] at this; omega
    · have : q = 2 := by omega
      subst this; simp at *
