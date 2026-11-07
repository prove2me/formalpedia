-- Prove2me | solution 1 for Monodromy.Counter.step_map_live
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T14:57:00.560759+00:00
-- url     : https://prove2.me/submissions/96c1681b-12d0-4524-917f-7b3079fdc6e5

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
variable {n m k : ℕ}
theorem solution (address : Fin m → Fin k)
    (oldProgram : Program n m) (newProgram : Program n k)
    (agrees : ∀ label, oldProgram label ≠ .halt →
      newProgram (address label) = mapInstruction address (oldProgram label))
    {state result : Configuration n m} (running : step oldProgram state = some result) :
    step newProgram (mapConfiguration address state) = some (mapConfiguration address result) := by
  have live : oldProgram state.pc ≠ .halt := by
    intro stopped
    simp [step, stopped] at running
  have same : step newProgram (mapConfiguration address state) =
      (step oldProgram state).map (mapConfiguration address) := by
    unfold step
    simp only [mapConfiguration, agrees state.pc live]
    cases instruction : oldProgram state.pc with
    | inc => rfl
    | dec register =>
        cases value : state.counters register <;> simp [mapInstruction, mapConfiguration, value]
    | halt => rfl
  rw [running] at same
  exact same
