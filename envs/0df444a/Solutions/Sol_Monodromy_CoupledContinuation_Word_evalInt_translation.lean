-- Prove2me | solution 1 for Monodromy.CoupledContinuation.Word.evalInt_translation
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:26:07.443029+00:00
-- url     : https://prove2.me/submissions/3cdab3e5-bc31-46d6-a1ad-9330fe6c23f1

import Definitions.Def_Monodromy_ForwardBoundary

open Monodromy
open Monodromy.CoupledContinuation

theorem solution (word : Word) (free : word.ProbeFree) (labels : Labels) :
    Word.evalInt word labels = labels + Word.evalInt word 0 := by
  have gate_translation (gate : Gate) (gateFree : gate.ProbeFree)
      (backward : Bool) (labels : Labels) :
      Gate.evalInt gate backward labels = labels + Gate.evalInt gate backward 0 := by
    cases gate <;> simp_all [Gate.ProbeFree, Gate.evalInt, Prod.ext_iff]
  induction word generalizing labels with
  | nil => simp [Word.evalInt]
  | cons head rest ih =>
      rcases head with ⟨gate, backward⟩
      rcases free with ⟨gateFree, restFree⟩
      simp only [Word.evalInt]
      rw [ih restFree (Gate.evalInt gate backward labels),
        gate_translation gate gateFree,
        ih restFree (Gate.evalInt gate backward 0)]
      simp only [add_assoc]
