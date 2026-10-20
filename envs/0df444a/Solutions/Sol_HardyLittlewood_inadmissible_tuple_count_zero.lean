-- Prove2me | solution 1 for HardyLittlewood.inadmissible_tuple_count_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T21:56:22.689827+00:00
-- url     : https://prove2.me/submissions/4f9837b7-36af-4e9f-8063-984d5db5407d

import Mathlib
import Definitions.Def_HardyLittlewood_constellation
import Definitions.Def_HardyLittlewood_counting
import Definitions.Def_HardyLittlewood_series

open HardyLittlewood

theorem solution {k : ℕ} (m : Fin k.succ → ℕ)
    (q : ℕ) (hq : q.Prime)
    (h : ∀ p : ℕ, Function.Surjective (fun i : Fin k.succ => (p + 2 * m i : ZMod q)))
    (n : ℕ) : primeTupleCounting m n = 0 := by
  unfold primeTupleCounting
  have : {p : ℕ | p ≤ n ∧ IsAdmissiblePrimeConstellation m p} = ∅ := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro _ ⟨_, hadm⟩
    exact hadm q hq (h p)
  rw [this, Set.ncard_empty]
