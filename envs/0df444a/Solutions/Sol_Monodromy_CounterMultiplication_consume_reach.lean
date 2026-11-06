-- Prove2me | solution 1 for Monodromy.CounterMultiplication.consume_reach
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:37:56.84537+00:00
-- url     : https://prove2.me/submissions/b75343f1-f16c-4029-9bef-1202be7f50f0

import Definitions.Def_Monodromy_Counter
import Lean.Elab.Tactic.Omega
import Mathlib.Computability.StateTransition
import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.FinCases

open Monodromy
open Monodromy.CounterMultiplication

private theorem phase_reaches (factor count : ℕ) (bound : count ≤ factor) (first second : ℕ) :
    StateTransition.Reaches (Counter.step (program factor))
      (configuration factor (phase factor count) first second)
      (configuration factor 0 first (second + count)) := by
  induction count generalizing second with
  | zero =>
      exact Relation.ReflTransGen.refl
  | succ count ih =>
      have count_bound : count ≤ factor := by omega
      apply Relation.ReflTransGen.head
        (b := configuration factor (phase factor count) first (second + 1))
      · simp [Counter.step, program, configuration, phase,
          Nat.mod_eq_of_lt (show count + 1 < factor + 4 by omega),
          Nat.mod_eq_of_lt (show count < factor + 4 by omega), bound]
        funext register
        fin_cases register <;> simp
      · change StateTransition.Reaches _ _ _
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          ih count_bound (second + 1)

theorem solution (factor first second : ℕ) :
    StateTransition.Reaches (Counter.step (program factor))
      (configuration factor 0 first second)
      (configuration factor 0 0 (second + factor * first)) := by
  induction first generalizing second with
  | zero =>
      exact Relation.ReflTransGen.refl
  | succ first ih =>
      apply Relation.ReflTransGen.head
        (b := configuration factor (phase factor factor) first second)
      · simp [Counter.step, program, configuration]
        funext register
        fin_cases register <;> simp
      · simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (phase_reaches factor factor (Nat.le_refl factor) first second).trans
            (ih (second + factor))
