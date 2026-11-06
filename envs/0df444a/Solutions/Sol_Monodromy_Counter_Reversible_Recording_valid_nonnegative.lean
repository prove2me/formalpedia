-- Prove2me | solution 1 for Monodromy.Counter.Reversible.Recording.valid_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:28:26.335202+00:00
-- url     : https://prove2.me/submissions/4c44d133-aeb4-4a39-b29c-d679473a4347

import Definitions.Def_Monodromy_Counter
import Mathlib.Tactic.FinCases

open Monodromy
open Monodromy.Counter
open Monodromy.Counter.Reversible
open Monodromy.Counter.Reversible.Recording
variable {n m : ℕ}

theorem solution (program : Counter.Program n m) (state : State (n + 2) (size m))
    (valid : Valid program state) (index : Fin (n + 2)) : 0 ≤ state.2 index := by
  refine Fin.addCases (fun old => valid.1 old) ?_ index
  intro extra
  cases hcontrol : (nodeEquiv m).symm state.1 with
  | inl pair =>
    rcases pair with ⟨row, position⟩
    have h := valid.2
    rw [hcontrol] at h
    fin_cases extra
    · simpa [Radix.Valid, historyRegister] using h.1
    · simpa [Radix.Valid, historyRegister] using h.2.1
  | inr row =>
    have h := valid.2
    rw [hcontrol] at h
    fin_cases extra
    · simpa [admissible, historyRegister] using h.1
    · simpa [admissible, historyRegister] using h.2.1.ge
