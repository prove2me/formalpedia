-- Prove2me | solution 1 for Monodromy.Counter.DivMod.consume_reaches
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:43:12.961193+00:00
-- url     : https://prove2.me/submissions/f5d0f1a5-f56f-403d-a484-4a1d141cf0f2

module
public import Definitions.Def_Monodromy_Counter
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.FinCases

@[expose] public section

open Monodromy
open Monodromy.Counter
open Monodromy.Counter.DivMod
variable (p : ℕ) [NeZero p]

namespace Monodromy.Counter.DivMod

private theorem program_consume_aux (remainder : Fin p) :
    program p (consume p remainder) = .dec 0 (transfer p remainder) (next p remainder) := by
  simp [program, consume, remainder.isLt]

private theorem program_bump_aux : program p (bump p) = .inc 1 (consume p 0) := by
  have first : ¬ 4 * p < p := by omega
  have second : ¬ 4 * p < 2 * p := by omega
  have third : ¬ 4 * p < 3 * p := by omega
  simp [program, bump, first, second, third]

private theorem update_first_aux (first second value : ℕ) :
    Function.update ![first, second] 0 value = ![value, second] := by
  funext index
  fin_cases index <;> simp

private theorem update_second_aux (first second value : ℕ) :
    Function.update ![first, second] 1 value = ![first, value] := by
  funext index
  fin_cases index <;> simp

private theorem step_consume_zero_aux (remainder : Fin p) (second : ℕ) :
    Counter.step (program p) (configuration p (consume p remainder) 0 second) =
      some (configuration p (transfer p remainder) 0 second) := by
  simp [Counter.step, configuration, program_consume_aux]

private theorem step_consume_succ_aux (remainder : Fin p) (first second : ℕ) :
    Counter.step (program p) (configuration p (consume p remainder) (first + 1) second) =
      some (configuration p (next p remainder) first second) := by
  simp [Counter.step, configuration, program_consume_aux, update_first_aux]

private theorem step_bump_aux (first second : ℕ) :
    Counter.step (program p) (configuration p (bump p) first second) =
      some (configuration p (consume p 0) first (second + 1)) := by
  simp [Counter.step, configuration, program_bump_aux, update_second_aux]

private theorem residue_small_aux (remainder : Fin p) : residue p remainder.val = remainder := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt remainder.isLt

private theorem reaches_step_aux {first second : Counter.Configuration 2 (size p)}
    (edge : Counter.step (program p) first = some second) :
    StateTransition.Reaches (Counter.step (program p)) first second := by
  apply Relation.ReflTransGen.single
  exact edge

private theorem prepend_aux {first middle last : Counter.Configuration 2 (size p)}
    (edge : Counter.step (program p) first = some middle)
    (rest : StateTransition.Reaches (Counter.step (program p)) middle last) :
    StateTransition.Reaches (Counter.step (program p)) first last := by
  change Relation.ReflTransGen (fun a b => b ∈ Counter.step (program p) a) _ _
  exact Relation.ReflTransGen.head edge rest

end Monodromy.Counter.DivMod

theorem solution (first second : ℕ) (remainder : Fin p) :
    StateTransition.Reaches (Counter.step (program p))
      (configuration p (consume p remainder) first second)
      (configuration p (transfer p (residue p (first + remainder.val))) 0
        (second + (first + remainder.val) / p)) := by
  induction first generalizing second remainder with
  | zero =>
      simpa only [Nat.zero_add, residue_small_aux, Nat.div_eq_of_lt remainder.isLt,
        Nat.add_zero] using (reaches_step_aux p (step_consume_zero_aux p remainder second))
  | succ first recursive =>
      by_cases bound : remainder.val + 1 < p
      · let next_remainder : Fin p := ⟨remainder.val + 1, bound⟩
        have next_step : Counter.step (program p)
            (configuration p (consume p remainder) (first + 1) second) =
            some (configuration p (consume p next_remainder) first second) := by
          simpa only [next, dite_eq_left bound] using step_consume_succ_aux p remainder first second
        have run := prepend_aux p next_step (recursive second next_remainder)
        have same_sum : first + next_remainder.val = first + 1 + remainder.val := by
          dsimp [next_remainder]
          omega
        simpa only [same_sum] using run
      · have last : remainder.val + 1 = p := by omega
        have next_step : Counter.step (program p)
            (configuration p (consume p remainder) (first + 1) second) =
            some (configuration p (bump p) first second) := by
          simpa only [next, dite_eq_right bound] using step_consume_succ_aux p remainder first second
        have run := prepend_aux p next_step
          (prepend_aux p (step_bump_aux p first second) (recursive (second + 1) 0))
        have same_sum : first + 1 + remainder.val = first + p := by omega
        have residue_eq : residue p (first + p) = residue p first := by
          apply Fin.ext
          exact Nat.add_mod_right first p
        simpa only [Fin.val_zero, Nat.add_zero, same_sum, residue_eq,
          Nat.add_div_right first (Nat.pos_of_ne_zero (NeZero.ne p)),
          Nat.add_assoc, Nat.add_comm 1 (first / p)] using run
