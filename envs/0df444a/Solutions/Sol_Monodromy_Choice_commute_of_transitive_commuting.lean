-- Prove2me | solution 1 for Monodromy.Choice.commute_of_transitive_commuting
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T14:56:00.93291+00:00
-- url     : https://prove2.me/submissions/1518aac5-4f10-40dc-bb69-221cee6592c1

-- Generated mechanically from the frozen source; no own-target import.
module
public import Definitions.Def_Monodromy_Choice
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Logic.Function.Conjugate
public import Mathlib.Tactic.FunProp
public import Mathlib.Topology.Homotopy.Lifting

@[expose] public section


-- Original target, hoisted to top-level theorem solution.
open Monodromy
open Monodromy.Choice
theorem solution {H S : Type*} (action : H → S → S)
    (transitive : ∀ first second, ∃ symmetry, action symmetry first = second)
    (commuting : ∀ first second, Function.Commute (action first) (action second))
    (f g : S → S) (f_equivariant : ∀ symmetry, Function.Commute f (action symmetry))
    (g_equivariant : ∀ symmetry, Function.Commute g (action symmetry)) : Function.Commute f g := by
  intro state
  obtain ⟨first, sends_first⟩ := transitive state (f state)
  obtain ⟨second, sends_second⟩ := transitive state (g state)
  calc
    f (g state) = f (action second state) := congrArg f sends_second.symm
    _ = action second (f state) := f_equivariant second state
    _ = action second (action first state) := congrArg (action second) sends_first.symm
    _ = action first (action second state) := commuting second first state
    _ = action first (g state) := congrArg (action first) sends_second
    _ = g (action first state) := (g_equivariant first state).symm
    _ = g (f state) := congrArg g sends_first
