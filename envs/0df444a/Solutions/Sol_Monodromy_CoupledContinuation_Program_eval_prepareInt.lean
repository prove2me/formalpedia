-- Prove2me | solution 1 for Monodromy.CoupledContinuation.Program.eval_prepareInt
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:27:05.517609+00:00
-- url     : https://prove2.me/submissions/9186a029-ac68-407e-a5e3-4ed0da4b35b4

import Definitions.Def_Monodromy_Continuation
import Mathlib.Computability.StateTransition

open Monodromy
open Monodromy.CoupledContinuation
open Monodromy.CoupledContinuation.Program

private theorem haltSignal_prepare_local {degree : ℕ} [NeZero degree]
    (program : Program degree) (left right quotient : ℤ) (index : Fin degree) :
    program.haltSignal (prepare left right ((degree : ℤ) * quotient + index.val)) =
      if program.stop index then 1 else 0 := by
  unfold Program.haltSignal
  rw [controlRoot_prepare]
  have root := congrArg (fun value : Circle => (value : ℂ))
    (Radix.readRoot_digit degree quotient index)
  rw [root]
  exact Choice.dispatch_root
    (fun first second same => Radix.omega_injective degree (Subtype.ext same))
    (fun first second => (Radix.omega_complex_pow degree first).trans
      (Radix.omega_complex_pow degree second).symm)
    (Radix.omega_regular degree) index

private theorem haltSignal_prepareInt_local {degree : ℕ} [NeZero degree]
    (program : Program degree) (labels : Labels) :
    program.haltSignal (Labels.prepare labels) = if program.haltInt labels then 1 else 0 := by
  have actual := haltSignal_prepare_local program labels.1.1 labels.1.2
    (labels.2 / (degree : ℤ)) (indexInt degree labels)
  rw [Program.control_decomposition] at actual
  exact actual

private theorem step_prepareInt_local {degree : ℕ} [NeZero degree]
    (program : Program degree) (labels : Labels) :
    program.step (Labels.prepare labels) = (program.stepInt labels).map Labels.prepare := by
  unfold Program.step Program.stepInt
  rw [haltSignal_prepareInt_local]
  cases program.haltInt labels <;> simp [Program.advance_prepareInt]

theorem solution {degree : ℕ} [NeZero degree] (program : Program degree) (labels : Labels) :
    program.eval (Labels.prepare labels) = Labels.prepare <$> program.evalInt labels := by
  have refinement : StateTransition.Respects program.stepInt program.step
      (fun first second => Labels.prepare first = second) := by
    apply StateTransition.fun_respects.mpr
    intro source
    cases result : program.stepInt source with
    | none =>
        change program.step (Labels.prepare source) = none
        simp [step_prepareInt_local, result]
    | some successor =>
        apply Relation.TransGen.single
        simp [step_prepareInt_local, result]
  exact StateTransition.tr_eval' program.stepInt program.step Labels.prepare refinement labels
