-- Prove2me | solution 1 for Monodromy.CoupledContinuation.zeroTest_native_dom
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T15:00:52.877576+00:00
-- url     : https://prove2.me/submissions/63a6688b-597b-43b3-8a76-ef18d087875d

-- Generated mechanically from the frozen source; no own-target import.
module
public import Definitions.Def_Monodromy_ForwardBoundary
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
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Computability.Halting
public import Mathlib.Computability.PartrecCode
public import Mathlib.Computability.Primrec.Basic
public import Mathlib.Computability.Primrec.List
public import Mathlib.Computability.StateTransition
public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Logic.Function.Conjugate
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Homotopy.Lifting
public import Theorems.Thm_Monodromy_CoupledContinuation_Program_eval_prepareInt
public import Theorems.Thm_Monodromy_Observation_stopped_dom_iff

@[expose] public section


-- Original target, hoisted to top-level theorem solution.
open Monodromy
open Monodromy.CoupledContinuation
theorem solution (input : ℤ) :
    (zeroTest.eval (prepare input 0 0)).Dom ↔ input = 0 := by
  change (zeroTest.eval (Labels.prepare (((input, 0), 0) : Labels))).Dom ↔ _
  rw [Program.eval_prepareInt]
  change (StateTransition.eval
    (Observation.stopped zeroTest.nextInt zeroTest.haltInt) (((input, 0), 0) : Labels)).Dom ↔ _
  rw [Observation.stopped_dom_iff]
  constructor
  · rintro ⟨rounds, stops⟩
    by_contra nonzero
    have fixed : zeroTest.nextInt (((input, 0), 0) : Labels) = ((input, 0), 0) := by
      simp [zeroTest, Program.nextInt, Word.atom, Word.evalInt, Gate.evalInt, nonzero]
    have repeated := Function.iterate_fixed fixed rounds
    rw [repeated] at stops
    have keeps_running : zeroTest.haltInt (((input, 0), 0) : Labels) = false := by
      norm_num [zeroTest, Program.haltInt, Program.indexInt]
    rw [keeps_running] at stops
    contradiction
  · intro zero
    subst input
    refine ⟨1, ?_⟩
    change zeroTest.haltInt (zeroTest.nextInt (((0, 0), 0) : Labels)) = true
    norm_num [zeroTest, Program.haltInt, Program.indexInt, Program.nextInt,
      Word.atom, Word.evalInt, Gate.evalInt]
