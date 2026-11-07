-- Prove2me | solution 2 for Monodromy.Counter.Reversible.Recording.halt_no_outgoing
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T14:56:52.064194+00:00
-- url     : https://prove2.me/submissions/2c0e7326-3402-41e3-8e72-3d4cc4c71f41

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

@[expose] public section


-- Original target, hoisted to top-level theorem solution.
open Monodromy
open Monodromy.Counter
open Monodromy.Counter.Reversible
open Monodromy.Counter.Reversible.Recording
variable {n m : ℕ}
theorem solution (program : Counter.Program n m) (row : Fin m)
    (halted : program row = .halt) (index : Fin (edges program)) :
    (table program index).source ≠ dispatch row := by
  obtain ⟨arc, rfl⟩ := (arcEquiv program).surjective index
  rw [table_arc]
  rcases arc with ⟨other, edge⟩ | arc
  · change copy other (packing n m edge).source ≠ copy row (Radix.entry (base m))
    exact fun same => packing_no_outgoing_dispatch edge ((copy_eq_iff other row _ _).mp same).2
  · intro same
    have raw : extraOrigin program arc = Sum.inl (row, Radix.entry (base m)) :=
      (nodeEquiv m).injective same
    rcases arc with ⟨⟨other, branch⟩, active⟩
    cases instruction : program other with
    | inc register target =>
        rw [extraOrigin_inc program ⟨(other, branch), active⟩ register target instruction] at raw
        have rows := (Prod.mk.inj (Sum.inl.inj raw)).1
        have impossible := instruction.symm.trans ((congrArg program rows).trans halted)
        cases impossible
    | dec register zero nonzero =>
        rw [extraOrigin_dec program ⟨(other, branch), active⟩ register zero nonzero instruction] at raw
        split at raw
        · cases raw
        · have rows := (Prod.mk.inj (Sum.inl.inj raw)).1
          have impossible := instruction.symm.trans ((congrArg program rows).trans halted)
          cases impossible
    | halt =>
        unfold Active at active
        rw [instruction] at active
        exact active.elim
