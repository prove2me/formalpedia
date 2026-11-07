-- Prove2me | solution 2 for Monodromy.CoupledContinuation.Word.evalInt_translation
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T14:57:47.690193+00:00
-- url     : https://prove2.me/submissions/8690b1ef-6351-4ca0-967a-48abada9cdc6

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

@[expose] public section


-- Inline helper skeleton from Monodromy.ForwardBoundary.


/-!
# The computational boundary of fixed observations

Removing the two zero-conditional loops leaves
a finite control quotient with a bounded primitive-recursive halting test.
One actual conditional loop yields a strictly different halting domain under
the same fixed input representation.
-/

@[expose] public section

namespace Monodromy.ForwardBoundary









end Monodromy.ForwardBoundary

namespace Monodromy.CoupledContinuation





/-- A signed nonconditional gate is a translation on the complete branch presentation. -/
theorem Gate.evalInt_translation (gate : Gate) (backward : Bool) (free : gate.ProbeFree)
    (labels : Labels) :
    Gate.evalInt gate backward labels = labels + Gate.evalInt gate backward 0 := by
  rcases labels with ⟨⟨left, right⟩, control⟩
  cases gate <;> simp_all [Gate.ProbeFree, Gate.evalInt, Prod.mk_add_mk]





end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation.Program

variable {degree : ℕ} [NeZero degree]





















end Monodromy.CoupledContinuation.Program

namespace Monodromy.CoupledContinuation.Program

variable {degree : ℕ} [NeZero degree]





end Monodromy.CoupledContinuation.Program

namespace Monodromy.CoupledContinuation.Program

variable {degree : ℕ} [NeZero degree]



end Monodromy.CoupledContinuation.Program

namespace Monodromy.CoupledContinuation







end Monodromy.CoupledContinuation

end


-- Original target, hoisted to top-level theorem solution.
open Monodromy
open Monodromy.CoupledContinuation
theorem solution (word : Word) (free : word.ProbeFree) (labels : Labels) :
    Word.evalInt word labels = labels + Word.evalInt word 0 := by
  induction word generalizing labels with
  | nil => simp [Word.evalInt]
  | cons atom rest recursive =>
      rcases atom with ⟨gate, backward⟩
      change Word.evalInt rest (Gate.evalInt gate backward labels) =
        labels + Word.evalInt rest (Gate.evalInt gate backward 0)
      calc
        Word.evalInt rest (Gate.evalInt gate backward labels) =
            Gate.evalInt gate backward labels + Word.evalInt rest 0 :=
          recursive free.2 _
        _ = (labels + Gate.evalInt gate backward 0) + Word.evalInt rest 0 := by
          rw [Gate.evalInt_translation gate backward free.1 labels]
        _ = labels + (Gate.evalInt gate backward 0 + Word.evalInt rest 0) := add_assoc _ _ _
        _ = labels + Word.evalInt rest (Gate.evalInt gate backward 0) :=
          congrArg (labels + ·) (recursive free.2 _).symm
