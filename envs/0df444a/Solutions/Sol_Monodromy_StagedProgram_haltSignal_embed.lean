-- Prove2me | solution 1 for Monodromy.StagedProgram.haltSignal_embed
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:16:01.33299+00:00
-- url     : https://prove2.me/submissions/34af6a42-79f4-487c-99fd-2da221737db9

module
public import Definitions.Def_Monodromy_Continuation
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Ring

@[expose] public section

open Monodromy
open Monodromy.StagedProgram
open CoupledContinuation
open Fin.NatCast
variable (count degree : ℕ) [NeZero count] [NeZero degree]

theorem solution (stages : Fin count → Program degree) (mark : Fin degree → Bool)
    (left right quotient : ℤ) (index : Fin degree) (phase : Fin count) :
    (markedCompile count degree stages mark).haltSignal
      (embed count phase (prepare left right ((degree : ℤ) * quotient + index.val))) =
      if (if phase = 0 then mark index else false) then 1 else 0 := by
  change (markedCompile count degree stages mark).haltSignal
    (embed count phase (Labels.prepare
      ((left, right), (degree : ℤ) * quotient + index.val))) = _
  rw [embed_prepare]
  have control :
      ((count * degree : ℕ) : ℤ) * quotient +
          (address count degree (index, phase)).val =
        (count : ℤ) * ((degree : ℤ) * quotient + index.val) + phase.val := by
    rw [address_val]
    push_cast
    ring
  have prepared :
      Labels.prepare (pack count phase.val
        ((left, right), (degree : ℤ) * quotient + index.val)) =
      prepare left right
        (((count * degree : ℕ) : ℤ) * quotient +
          (address count degree (index, phase)).val) := by
    rw [control]
    rfl
  rw [prepared]
  have observed :
      controlRoot (count * degree)
        (prepare left right
          (((count * degree : ℕ) : ℤ) * quotient +
            (address count degree (index, phase)).val)) =
        (Radix.omega (count * degree) (address count degree (index, phase)) : ℂ) := by
    rw [controlRoot_prepare]
    exact congrArg (fun value : Circle => (value : ℂ))
      (Radix.readRoot_digit (count * degree) quotient
        (address count degree (index, phase)))
  unfold Program.haltSignal
  rw [observed]
  apply (Choice.dispatch_root
    (fun first second same => Radix.omega_injective (count * degree) (Subtype.ext same))
    (fun first second => (Radix.omega_complex_pow (count * degree) first).trans
      (Radix.omega_complex_pow (count * degree) second).symm)
    (Radix.omega_regular (count * degree))
    (address count degree (index, phase))).trans
  simp [markedCompile]
