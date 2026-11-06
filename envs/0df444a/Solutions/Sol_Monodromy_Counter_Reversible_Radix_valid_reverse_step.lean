-- Prove2me | solution 1 for Monodromy.Counter.Reversible.Radix.valid_reverse_step
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:29:16.371857+00:00
-- url     : https://prove2.me/submissions/a777299a-4d12-4413-8565-16001c5eb542

module
public import Definitions.Def_Monodromy_Counter
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.FinCases

@[expose] public section

open Monodromy
open Monodromy.Counter
open Monodromy.Counter.Reversible
open Monodromy.Counter.Reversible.Radix
variable (p : ℕ) [NeZero p]

theorem solution {first last : State 2 (size p)}
    (valid : Valid p first)
    (transition : Reversible.step (reverseTable (table p)) first = some last) :
    Valid p last := by
  classical
  unfold Reversible.step at transition
  split at transition
  next available =>
    have selected := Fin.find_spec available
    have executed := Option.some.inj transition
    subst last
    obtain ⟨arc, index_eq⟩ := (arcEquiv p).surjective
      (Fin.find (fun index => ((reverseTable (table p)) index).enabled first) available)
    rw [← index_eq] at selected ⊢
    simp only [reverseTable, table_arc] at selected ⊢
    unfold Valid at valid
    rw [← selected.1] at valid
    rcases arc with position | ⟨remainder, arc⟩
    · fin_cases position <;>
        simp_all [reverseEdge, reverseAction, Edge.enabled, Edge.execute,
          Action.enabled, Action.apply, Valid, origin, destination, operation,
          admissible, Function.update] <;> omega
    · fin_cases arc <;>
        simp_all [reverseEdge, reverseAction, Edge.enabled, Edge.execute,
          Action.enabled, Action.apply, Valid, origin, destination, operation,
          admissible, Function.update] <;> omega
  next unavailable => simp at transition
