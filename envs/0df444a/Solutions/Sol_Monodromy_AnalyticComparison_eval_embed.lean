-- Prove2me | solution 1 for Monodromy.AnalyticComparison.eval_embed
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:36:11.439044+00:00
-- url     : https://prove2.me/submissions/7eff8036-8285-4e33-950a-78182acebc39

import Definitions.Def_Monodromy_Effectiveness
import Mathlib.Computability.StateTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

open Monodromy
open Monodromy.AnalyticComparison
open CoupledContinuation
variable {degree : ℕ} [NeZero degree]

namespace Monodromy.AnalyticComparison

private theorem zero_int (n : ℤ) :
    zero (n : ℝ) = if n = 0 then 1 else 0 := by
  split_ifs with h
  · subst n
    simp [zero]
  · rw [zero, Real.sinc_of_ne_zero]
    · rw [mul_comm, Real.sin_int_mul_pi]
      simp
    · exact mul_ne_zero Real.pi_ne_zero (Int.cast_ne_zero.mpr h)

private theorem gate_embed (operation : Gate) (backward : Bool) (labels : Labels) :
    gate operation backward (embed labels) = embed (operation.evalInt backward labels) := by
  rcases labels with ⟨⟨left, right⟩, control⟩
  cases operation <;> cases backward <;>
    simp [gate, Gate.evalInt, embed, zero_int]

private theorem word_embed (operations : Word) (labels : Labels) :
    word operations (embed labels) = embed (operations.evalInt labels) := by
  induction operations generalizing labels with
  | nil => rfl
  | cons atom rest recursive =>
      rcases atom with ⟨operation, backward⟩
      rw [word, Word.evalInt, gate_embed, recursive]

private theorem readRoot_embed (labels : Labels) :
    Radix.readRoot degree ((2 * Real.pi) * (labels.2 : ℝ)) =
      Radix.omega degree (Program.indexInt degree labels) := by
  have decomposition := Program.control_decomposition (degree := degree) labels
  have cast_decomposition :
      (((degree : ℤ) * (labels.2 / (degree : ℤ)) +
        (Program.indexInt degree labels).val : ℤ) : ℝ) = (labels.2 : ℝ) := by
    exact_mod_cast decomposition
  rw [← cast_decomposition]
  exact Radix.readRoot_digit degree (labels.2 / (degree : ℤ))
    (Program.indexInt degree labels)

private theorem weight_embed (labels : Labels) (marked : Fin degree) :
    weight degree marked (embed labels).2 =
      if marked = Program.indexInt degree labels then 1 else 0 := by
  change weight degree marked (labels.2 : ℝ) = _
  rw [weight, readRoot_embed]
  by_cases h : marked = Program.indexInt degree labels
  · subst marked
    rw [Choice.kernel_self (f := fun z : ℂ => z ^ degree)
      (Radix.omega_regular degree (Program.indexInt degree labels))]
    simp
  · rw [if_neg h]
    have other : (Radix.omega degree (Program.indexInt degree labels) : ℂ) ≠
        Radix.omega degree marked := by
      intro same
      apply h
      exact Radix.omega_injective degree (Subtype.ext same.symm)
    have same_fiber :
        (Radix.omega degree (Program.indexInt degree labels) : ℂ) ^ degree =
          (Radix.omega degree marked : ℂ) ^ degree := by
      rw [Radix.omega_complex_pow, Radix.omega_complex_pow]
    rw [Choice.kernel_other (f := fun z : ℂ => z ^ degree) other same_fiber]
    rfl

private theorem next_embed (program : Program degree) (labels : Labels) :
    next program (embed labels) = embed (program.nextInt labels) := by
  classical
  simp [next, Program.nextInt, weight_embed, word_embed]

private theorem halt_embed (program : Program degree) (labels : Labels) :
    halt program (embed labels) = if program.haltInt labels then 1 else 0 := by
  classical
  unfold halt
  simp only [weight_embed]
  rw [Finset.sum_eq_single (Program.indexInt degree labels)]
  · simp only [Program.haltInt, if_true, one_mul]
    rfl
  · intro marked _ different
    simp [different]
  · simp

private theorem step_embed (program : Program degree) (labels : Labels) :
    step program (embed labels) = embed <$> program.stepInt labels := by
  cases h : program.haltInt labels <;>
    simp [step, Program.stepInt, halt_embed, h, next_embed]

end Monodromy.AnalyticComparison

theorem solution (program : Program degree) (labels : Labels) :
    eval program (embed labels) = embed <$> program.evalInt labels := by
  unfold eval Program.evalInt
  apply StateTransition.tr_eval' program.stepInt (step program) embed
  rw [StateTransition.fun_respects]
  intro current
  cases h : program.stepInt current with
  | none =>
      simp [StateTransition.FRespects, step_embed, h]
  | some next =>
      exact Relation.TransGen.single (by
        rw [step_embed, h]
        rfl)
