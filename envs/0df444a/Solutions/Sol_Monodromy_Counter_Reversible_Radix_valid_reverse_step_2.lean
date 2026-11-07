-- Prove2me | solution 2 for Monodromy.Counter.Reversible.Radix.valid_reverse_step
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T14:59:54.874081+00:00
-- url     : https://prove2.me/submissions/ef243495-1c57-4e6f-b1d2-ab27e4a0afcb

-- Generated mechanically from the frozen source; no own-target import.
module
public import Definitions.Def_Monodromy_Counter
public import Lean.Elab.Tactic.Omega
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Computability.StateTransition
public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Function.Conjugate
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Homotopy.Lifting
public import Theorems.Thm_Monodromy_Counter_Reversible_step_iff

@[expose] public section


-- Original target, hoisted to top-level theorem solution.
open Monodromy
open Monodromy.Counter
open Monodromy.Counter.Reversible
open Monodromy.Counter.Reversible.Radix
variable (p : ℕ) [NeZero p]
theorem solution {first last : State 2 (size p)}
    (valid : Valid p first) (transition : step (reverseTable (table p)) first = some last) :
    Valid p last := by
  obtain ⟨index, enabled, rfl⟩ :=
    (step_iff _ (reverseTable_deterministic _ (targetCompatible p))).mp transition
  obtain ⟨arc, rfl⟩ := (arcEquiv p).surjective index
  rcases first with ⟨position, values⟩
  have position_eq : nodeEquiv p (destination p arc) = position := by
    simpa only [reverseTable, reverseEdge, table_arc, Edge.enabled] using enabled.1
  subst position
  have action_enabled : (reverseAction (operation p arc)).enabled values := by
    simpa only [reverseTable, reverseEdge, table_arc] using enabled.2
  clear enabled
  rcases arc with index | ⟨remainder, index⟩ <;> fin_cases index <;>
    simp_all [Valid, admissible, reverseTable, reverseEdge, table_arc, Edge.execute,
      reverseAction, Action.apply, Action.enabled, origin, destination, operation]
  all_goals try omega
