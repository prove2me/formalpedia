-- Prove2me | solution 1 for Monodromy.StagedProgram.cycle_reaches
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T15:01:22.387589+00:00
-- url     : https://prove2.me/submissions/9ae37adb-e5fa-4f62-bd67-7655d2d8b0ca

-- Generated mechanically from the frozen source; no own-target import.
module
public import Definitions.Def_Monodromy_Continuation
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
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Logic.Function.Conjugate
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Homotopy.Lifting
public import Theorems.Thm_Monodromy_StagedProgram_cycle_ofFn
public import Theorems.Thm_Monodromy_StagedProgram_haltSignal_embed

@[expose] public section


-- Inline helper skeleton from Monodromy.Continuation.


@[expose] public section

/-!
# Coupled analytic continuation

Two retained logarithmic memory roots share one upper control root through
`F(w₁,w₂,z) = (exp w₁, exp w₂, exp z / (w₁*w₂))`. The two actual lower
lifts generate the upper input path. The returned root is the actual upper
lift endpoint; integer labels occur only in preparation and proofs.

The matching lower product covering and upper pullback covering are explicit.
Their actual lifts agree with the complete runtime curves. Five fixed loops
provide memory shifts, zero-conditional control writes and a control shift.
Concatenation and reversal follow from lift uniqueness. A finite power-root
observation routes whole base paths by normalized analytic kernels at returns.

Five oriented loops give a finite word language and finite root-controlled
program tables with internal stopping. Effective semantics and machine
simulation are proved in the subsequent research layers.
-/

noncomputable section

namespace Monodromy.CoupledContinuation

open unitInterval












attribute [local fun_prop] analyticAt_fst analyticAt_snd





















































































































end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation

open unitInterval























end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation









end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation





end Monodromy.CoupledContinuation


namespace Monodromy.CoupledPullback
























end Monodromy.CoupledPullback


namespace Monodromy.CoupledPullback











end Monodromy.CoupledPullback

namespace Monodromy.CoupledContinuation



















end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation



attribute [local fun_prop] analyticAt_fst analyticAt_snd



end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation

open unitInterval

variable (degree : ℕ) [NeZero degree]



























end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation

open unitInterval














































end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation

open unitInterval













section FiniteRouting

variable (degree : ℕ) [NeZero degree]



























end FiniteRouting











































end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation



end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation

open unitInterval



































end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation



namespace Program

variable {degree : ℕ} [NeZero degree]















end Program

end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation











end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation





end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation



end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation.Program

variable {degree : ℕ} [NeZero degree]

















end Monodromy.CoupledContinuation.Program

/-!
## Reversible conditional control

A finite permutation of control cells is compiled into signed words of the
existing conditional loop. Its inverse is selected from the returned roots.
-/

namespace Monodromy.ReversibleControl

open CoupledContinuation



























variable {degree : ℕ} [NeZero degree]



























end Monodromy.ReversibleControl

/-! Finite root-controlled memory translations use the same signed native A paths. -/

namespace Monodromy.ReversibleMemory

open CoupledContinuation



























variable {degree : ℕ} [NeZero degree]

















end Monodromy.ReversibleMemory


/-!
## Integer coordinates of actual returned roots

These coordinates state and prove the action of the existing geometric execution.
They do not participate in path generation or add an execution rule.
-/

namespace Monodromy.CoupledContinuation













namespace Program

variable {degree : ℕ} [NeZero degree]

























end Program

end Monodromy.CoupledContinuation


/-!
## Finite cyclic staging in the existing upper branch

The compiler emits only the existing signed geometric words. A finite stage is
packed into the upper branch, and every generated word is executed by the
unchanged native lifting kernel.
-/

namespace Monodromy.StagedProgram

open CoupledContinuation
open Fin.NatCast



















variable (count degree : ℕ) [NeZero count] [NeZero degree]




























/-- A complete cycle is the ordinary composition of the supplied stage advances. -/
theorem iterate_embed (stages : Fin count → Program degree) (steps : ℕ)
    (phase : Fin count) (state : Memory) :
    ((compile count degree stages).advance)^[steps] (embed count phase state) =
      embed count ((finRotate count)^[steps] phase)
        ((List.range steps).foldl
          (fun point position => (stages ((finRotate count)^[position] phase)).advance point) state) := by
  induction steps with
  | zero => rfl
  | succ steps recursive =>
      rw [Function.iterate_succ_apply', recursive, advance_embed]
      simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Function.iterate_succ_apply']

theorem rotate_iterate (steps : ℕ) (phase : Fin count) :
    (finRotate count)^[steps] phase = phase + (steps : Fin count) := by
  induction steps with
  | zero => simp
  | succ steps recursive =>
      rw [Function.iterate_succ_apply', recursive, finRotate_apply]
      simp only [Nat.cast_add, Nat.cast_one, add_assoc]


























end Monodromy.StagedProgram

/-! Static phase-zero stopping for the existing finite-stage compiler. -/

namespace Monodromy.StagedProgram

open CoupledContinuation
open Fin.NatCast

variable (count degree : ℕ) [NeZero count] [NeZero degree]



@[simp] theorem markedCompile_advance (stages : Fin count → Program degree) (mark : Fin degree → Bool)
    : (markedCompile count degree stages mark).advance =
      (compile count degree stages).advance := rfl





theorem halt_embed_iff (stages : Fin count → Program degree) (mark : Fin degree → Bool)
    (left right quotient : ℤ) (index : Fin degree) (phase : Fin count) :
    (markedCompile count degree stages mark).haltSignal
      (embed count phase (prepare left right ((degree : ℤ) * quotient + index.val))) = 1 ↔
      phase = 0 ∧ mark index = true := by
  rw [haltSignal_embed]
  by_cases zero : phase = 0
  · cases mark index <;> simp [zero]
  · simp [zero]

theorem step_embed (stages : Fin count → Program degree) (mark : Fin degree → Bool)
    (left right quotient : ℤ) (index : Fin degree) (phase : Fin count) :
    (markedCompile count degree stages mark).step
      (embed count phase (prepare left right ((degree : ℤ) * quotient + index.val))) =
      if phase = 0 ∧ mark index = true then none else
        some (embed count (finRotate count phase)
          ((stages phase).advance (prepare left right ((degree : ℤ) * quotient + index.val)))) := by
  simp only [Program.step, halt_embed_iff, markedCompile_advance, advance_embed]

/-- Nonzero packed phases always execute their actual next stage. -/
theorem interior_step (stages : Fin count → Program degree) (mark : Fin degree → Bool)
    (phase : Fin count) (nonzero : phase ≠ 0) (state : Memory) :
    (markedCompile count degree stages mark).step (embed count phase state) =
      some (embed count (finRotate count phase) ((stages phase).advance state)) := by
  obtain ⟨labels, rfl⟩ := labelsEquiv.surjective state
  change (markedCompile count degree stages mark).step (embed count phase (Labels.prepare labels)) =
    some (embed count (finRotate count phase) ((stages phase).advance (Labels.prepare labels)))
  have actual := step_embed count degree stages mark labels.1.1 labels.1.2
    (labels.2 / (degree : ℤ)) (Program.indexInt degree labels) phase
  rw [Program.control_decomposition] at actual
  simpa only [nonzero, false_and, ite_false, Labels.prepare] using actual







/-- Before a complete clock cycle, its phase cannot revisit zero. -/
theorem rotated_zero_ne_zero (steps : ℕ) (positive : 0 < steps) (before : steps < count) :
    ((finRotate count)^[steps] (0 : Fin count)) ≠ 0 := by
  rw [rotate_iterate, zero_add]
  intro same
  have values := congrArg Fin.val same
  simp only [Fin.val_natCast, Nat.mod_eq_of_lt before, Fin.val_zero] at values
  omega



private theorem positive_reaches_iterate {State : Type*}
    (advance : State → State) (transition : State → Option State) (state : State)
    (steps : ℕ) (positive : 0 < steps)
    (active : ∀ round : ℕ, round < steps →
      transition (advance^[round] state) = some (advance^[round + 1] state)) :
    StateTransition.Reaches₁ transition state (advance^[steps] state) := by
  revert positive active
  induction steps with
  | zero => intro impossible _; omega
  | succ steps recursive =>
      intro _ active
      by_cases first : steps = 0
      · subst steps
        apply Relation.TransGen.single
        exact active 0 (by omega)
      · have previous := recursive (by omega) (fun round before => active round (by omega))
        exact previous.tail (active steps (by omega))





end Monodromy.StagedProgram

/-! First-return predecessor uniqueness for reversible advances. -/

namespace Monodromy.ReversibleReturn

variable {State Source : Type*}









end Monodromy.ReversibleReturn


/-! Marked inverse execution and first-return transport. -/

namespace Monodromy.CoupledContinuation.Program

noncomputable section

variable {degree : ℕ} [NeZero degree]







end

end Monodromy.CoupledContinuation.Program

namespace Monodromy.ReversibleReturn

variable {State : Type*}





end Monodromy.ReversibleReturn

end

end


-- Original target, hoisted to top-level theorem solution.
open Monodromy
open Monodromy.StagedProgram
open CoupledContinuation
open Fin.NatCast
variable (count degree : ℕ) [NeZero count] [NeZero degree]
theorem solution (stages : Fin count → Program degree) (mark : Fin degree → Bool)
    (left right quotient : ℤ) (index : Fin degree) (unmarked : mark index = false) :
    StateTransition.Reaches₁ (markedCompile count degree stages mark).step
      (embed count 0 (prepare left right ((degree : ℤ) * quotient + index.val)))
      (embed count 0 ((List.ofFn stages).foldl (fun point stage => stage.advance point)
        (prepare left right ((degree : ℤ) * quotient + index.val)))) := by
  have active : ∀ round : ℕ, round < count →
      (markedCompile count degree stages mark).step
        (((compile count degree stages).advance)^[round]
          (embed count 0 (prepare left right ((degree : ℤ) * quotient + index.val)))) =
      some (((compile count degree stages).advance)^[round + 1]
        (embed count 0 (prepare left right ((degree : ℤ) * quotient + index.val)))) := by
    intro round before
    rw [Function.iterate_succ_apply']
    by_cases initial : round = 0
    · subst round
      simp only [Function.iterate_zero_apply]
      rw [step_embed, advance_embed]
      simp [unmarked]
    · rw [iterate_embed]
      have phase_nonzero := rotated_zero_ne_zero count round (by omega) before
      rw [interior_step count degree stages mark _ phase_nonzero, advance_embed]
  have run := positive_reaches_iterate (compile count degree stages).advance
    (markedCompile count degree stages mark).step
    (embed count 0 (prepare left right ((degree : ℤ) * quotient + index.val))) count
    (Nat.pos_of_ne_zero (NeZero.ne count)) active
  rw [cycle_ofFn] at run
  exact run
