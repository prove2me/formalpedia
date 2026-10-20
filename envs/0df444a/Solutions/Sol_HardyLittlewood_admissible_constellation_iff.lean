-- Prove2me | solution 1 for HardyLittlewood.admissible_constellation_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T21:56:36.175511+00:00
-- url     : https://prove2.me/submissions/0dab65c9-77ef-4d00-b86e-4ffdecf267d5

import Mathlib
import Definitions.Def_HardyLittlewood_constellation
import Definitions.Def_HardyLittlewood_counting
import Definitions.Def_HardyLittlewood_series

open HardyLittlewood

theorem solution {k : ℕ} (m : Fin k.succ → ℕ) (p : ℕ) :
    IsAdmissiblePrimeConstellation m p ↔
      IsPrimeConstellation m p ∧ IsAdmissibleTuple m := by
  have key : ∀ q : ℕ, Function.Surjective (fun i : Fin k.succ => (p + 2 * m i : ZMod q)) ↔
      Function.Surjective (fun i : Fin k.succ => (2 * m i : ZMod q)) := by
    intro q
    constructor
    · intro hs y
      obtain ⟨i, hi⟩ := hs (p + y)
      exact ⟨i, by simpa using hi⟩
    · intro hs y
      obtain ⟨i, hi⟩ := hs (y - p)
      exact ⟨i, by simp only at hi ⊢; rw [hi]; ring⟩
  unfold IsAdmissiblePrimeConstellation IsAdmissibleTuple
  simp only [key]
