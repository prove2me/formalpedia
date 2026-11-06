-- Prove2me | solution 1 for Monodromy.CounterContinuation.advance_dec_first
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:14:54.081784+00:00
-- url     : https://prove2.me/submissions/a3e7fe18-d4d1-40bb-8320-57eaa3e87869

import Definitions.Def_Monodromy_Counter
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FinCases

open Monodromy
open Monodromy.CounterContinuation
open CoupledContinuation
variable {m : ℕ} [NeZero m]

private theorem compile_table_address (program : Counter.Program 2 m)
    (position : Fin m) (phase : Fin 3) :
    (compile program).table (finProdFinEquiv (position, phase)) =
      instructionWord program position phase := by
  simp [compile, wordTable]

private theorem advance_at (program : Counter.Program 2 m) (left right : ℤ)
    (position : Fin m) (phase : Fin 3) :
    (compile program).advance (prepare left right (label position phase)) =
      execute (Word.driver (instructionWord program position phase))
        (prepare left right (label position phase)) := by
  have run := CoupledContinuation.Program.advance_prepare (compile program) left right 0
    (finProdFinEquiv (position, phase))
  simpa only [mul_zero, zero_add, compile_table_address, label] using run

private theorem label_eq (position : Fin m) (phase : Fin 3) :
    label position phase = (phase.val : ℤ) + 3 * (position.val : ℤ) := by
  simp [label, finProdFinEquiv]

private theorem execute_word_atom (gate : Gate) (state : Memory) :
    execute (Word.driver (Word.atom gate)) state = execute gate.driver state := by
  simp [Word.atom, execute_word_cons, execute_word_nil]

theorem solution (program : Counter.Program 2 m) (position zero nonzero : Fin m)
    (register : Fin 2) (instruction : program position = .dec register zero nonzero) (left right : ℤ) :
    (compile program).advance (prepare left right (label position 0)) =
      prepare left right (label position 1 + if (![left, right] register) = 0 then 1 else 0) := by
  rw [advance_at]
  simp [instructionWord, instruction]
  rw [execute_word_append, execute_control_word, execute_word_atom]
  fin_cases register
  · change execute B_left _ = _
    rw [execute_B_left]
    congr 1
    simp [label_eq]
    omega
  · change execute B_right _ = _
    rw [execute_B_right]
    congr 1
    simp [label_eq]
    omega
