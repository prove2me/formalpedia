-- Prove2me | solution 2 for Monodromy.CounterContinuation.two_returns
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T15:00:48.800892+00:00
-- url     : https://prove2.me/submissions/1ae1e811-b31b-4352-91ba-2659366185be

-- Generated mechanically from the frozen source; no own-target import.
module
public import Definitions.Def_Monodromy_Continuation
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
public import Theorems.Thm_Monodromy_CounterContinuation_advance_dec_first

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





















theorem execute_word_atom (gate : Gate) (backward : Bool) (state : Memory) :
    execute (Word.driver (Word.atom gate backward)) state =
      execute (if backward then gate.driver.reverse else gate.driver) state := by
  rw [Word.atom, execute_word_cons, execute_word_nil]













end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation



namespace Program

variable {degree : ℕ} [NeZero degree]











theorem haltSignal_prepare (program : Program degree) (left right quotient : ℤ) (index : Fin degree) :
    program.haltSignal (prepare left right ((degree : ℤ) * quotient + index.val)) =
      if program.stop index then 1 else 0 := by
  unfold haltSignal
  rw [controlRoot_prepare]
  have root := congrArg (fun value : Circle => (value : ℂ))
    (Radix.readRoot_digit degree quotient index)
  rw [root]
  exact Choice.dispatch_root
    (fun first second same => Radix.omega_injective degree (Subtype.ext same))
    (fun first second => (Radix.omega_complex_pow degree first).trans
      (Radix.omega_complex_pow degree second).symm)
    (Radix.omega_regular degree) index

theorem step_prepare (program : Program degree) (left right quotient : ℤ) (index : Fin degree) :
    program.step (prepare left right ((degree : ℤ) * quotient + index.val)) =
      if program.stop index then none else
        some (execute (Word.driver (program.table index))
          (prepare left right ((degree : ℤ) * quotient + index.val))) := by
  unfold step
  rw [haltSignal_prepare]
  cases program.stop index <;> simp [advance_prepare]

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

























































end Monodromy.StagedProgram

/-! Static phase-zero stopping for the existing finite-stage compiler. -/

namespace Monodromy.StagedProgram

open CoupledContinuation
open Fin.NatCast

variable (count degree : ℕ) [NeZero count] [NeZero degree]































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


-- Inline helper skeleton from Monodromy.Counter.


/-!
# Counter machines and native continuation

The standard finite counter semantics is retained. A three-phase finite
compiler realizes each two-counter step by two actual geometric returns;
the faithful configuration encoding preserves complete partial execution.

Classical finite counter macros and prime coding compile an entire finite
Turing table through three source registers to the same two-counter target.
Every arithmetic loop has a separate finite control region, with marked
source entries and no intermediate return boundary.
-/

@[expose] public section

namespace Monodromy.Counter









variable {n m : ℕ} (program : Program n m) (state : Configuration n m)















variable {k : ℕ}











end Monodromy.Counter

noncomputable section

namespace Monodromy.CounterContinuation

open CoupledContinuation



theorem label_eq {m : ℕ} (position : Fin m) (phase : Fin 3) :
    label position phase = (phase.val : ℤ) + 3 * (position.val : ℤ) := by
  simp [label, finProdFinEquiv]



















theorem compile_table_address {m : ℕ} (program : Counter.Program 2 m)
    (position : Fin m) (phase : Fin 3) :
    (compile program).table (finProdFinEquiv (position, phase)) = instructionWord program position phase := by
  simp [compile, wordTable]

theorem compile_stop_address {m : ℕ} (program : Counter.Program 2 m)
    (position : Fin m) (phase : Fin 3) :
    (compile program).stop (finProdFinEquiv (position, phase)) = stopping program position phase := by
  simp [compile, stopTable]

variable {m : ℕ} [NeZero m]

theorem advance_at (program : Counter.Program 2 m) (left right : ℤ)
    (position : Fin m) (phase : Fin 3) :
    (compile program).advance (prepare left right (label position phase)) =
      execute (Word.driver (instructionWord program position phase))
        (prepare left right (label position phase)) := by
  have run := CoupledContinuation.Program.advance_prepare (compile program) left right 0
    (finProdFinEquiv (position, phase))
  simpa only [mul_zero, zero_add, compile_table_address, label] using run

theorem step_at (program : Counter.Program 2 m) (left right : ℤ)
    (position : Fin m) (phase : Fin 3) :
    (compile program).step (prepare left right (label position phase)) =
      if stopping program position phase then none else
        some (execute (Word.driver (instructionWord program position phase))
          (prepare left right (label position phase))) := by
  have run := CoupledContinuation.Program.step_prepare (compile program) left right 0
    (finProdFinEquiv (position, phase))
  simpa only [mul_zero, zero_add, compile_table_address, compile_stop_address, label] using run

end Monodromy.CounterContinuation

namespace Monodromy.CounterContinuation

open CoupledContinuation

variable {m : ℕ} [NeZero m]

theorem advance_inc_first (program : Counter.Program 2 m) (position target : Fin m)
    (register : Fin 2) (instruction : program position = .inc register target) (left right : ℤ) :
    (compile program).advance (prepare left right (label position 0)) =
      prepare left right (label position 1) := by
  rw [advance_at]
  simp [instructionWord, instruction]
  rw [execute_control_word]
  congr 1
  simp [label_eq]
  omega

theorem advance_inc_second (program : Counter.Program 2 m) (position target : Fin m)
    (register : Fin 2) (instruction : program position = .inc register target) (left right : ℤ) :
    (compile program).advance (prepare left right (label position 1)) =
      prepare (left + if register = 0 then 1 else 0) (right + if register = 1 then 1 else 0)
        (label target 0) := by
  rw [advance_at]
  simp [instructionWord, instruction]
  rw [execute_word_append, execute_word_atom]
  fin_cases register
  · change execute (Word.driver (Word.control _)) (execute A_left _) = _
    rw [execute_A_left, execute_control_word]
    congr 1 <;> simp
  · change execute (Word.driver (Word.control _)) (execute A_right _) = _
    rw [execute_A_right, execute_control_word]
    congr 1 <;> simp



theorem advance_dec_positive (program : Counter.Program 2 m) (position zero nonzero : Fin m)
    (register : Fin 2) (instruction : program position = .dec register zero nonzero) (left right : ℤ) :
    (compile program).advance (prepare left right (label position 1)) =
      prepare (left - if register = 0 then 1 else 0) (right - if register = 1 then 1 else 0)
        (label nonzero 0) := by
  rw [advance_at]
  simp [instructionWord, instruction]
  rw [execute_word_append, execute_word_atom]
  fin_cases register
  · change execute (Word.driver (Word.control _)) (execute A_left.reverse _) = _
    rw [execute_A_left_reverse, execute_control_word]
    congr 1 <;> simp
  · change execute (Word.driver (Word.control _)) (execute A_right.reverse _) = _
    rw [execute_A_right_reverse, execute_control_word]
    congr 1 <;> simp

theorem advance_dec_zero (program : Counter.Program 2 m) (position zero nonzero : Fin m)
    (register : Fin 2) (instruction : program position = .dec register zero nonzero) (left right : ℤ) :
    (compile program).advance (prepare left right (label position 2)) =
      prepare left right (label zero 0) := by
  rw [advance_at]
  simp [instructionWord, instruction]
  rw [execute_control_word]
  congr 1
  omega

theorem step_running_at (program : Counter.Program 2 m) (position : Fin m) (phase : Fin 3)
    (running : stopping program position phase = false) (left right : ℤ) :
    (compile program).step (prepare left right (label position phase)) =
      some ((compile program).advance (prepare left right (label position phase))) := by
  rw [step_at, running]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [advance_at]

theorem step_phase_one (program : Counter.Program 2 m) (position : Fin m) (left right : ℤ) :
    (compile program).step (prepare left right (label position 1)) =
      some ((compile program).advance (prepare left right (label position 1))) := by
  apply step_running_at
  simp [stopping]

theorem step_phase_two (program : Counter.Program 2 m) (position : Fin m) (left right : ℤ) :
    (compile program).step (prepare left right (label position 2)) =
      some ((compile program).advance (prepare left right (label position 2))) := by
  apply step_running_at
  simp [stopping]

end Monodromy.CounterContinuation

namespace Monodromy.CounterContinuation

open CoupledContinuation

variable {m : ℕ}



variable [NeZero m]













end Monodromy.CounterContinuation


namespace Monodromy.CounterContinuation

variable {m : ℕ} [NeZero m]



end Monodromy.CounterContinuation

namespace Monodromy.CounterContinuation

open CoupledContinuation









variable {m : ℕ} [NeZero m]







end Monodromy.CounterContinuation

namespace Monodromy.PrimeCode



namespace Basis

variable {n : ℕ} (basis : Basis n)

























end Basis





































end Monodromy.PrimeCode

namespace Monodromy.Counter.RegisterRelocation

variable {n k m : ℕ}





















end Monodromy.Counter.RegisterRelocation

namespace Monodromy.Counter

variable {n m k : ℕ}





end Monodromy.Counter

namespace Monodromy.CounterMultiplication

















































end Monodromy.CounterMultiplication

namespace Monodromy.Counter.DivMod

variable (p : ℕ) [NeZero p]
































































end Monodromy.Counter.DivMod

namespace Monodromy.CounterPrimeProbe

variable (p : ℕ) [NeZero p]





























































end Monodromy.CounterPrimeProbe

namespace Monodromy.Counter.TuringCompiler

open Turing

variable (a q : ℕ) [NeZero a] [NeZero q]











































































































end Monodromy.Counter.TuringCompiler

namespace Monodromy.Counter.Compression

variable {m : ℕ}








































































































end Monodromy.Counter.Compression

namespace Monodromy.Counter.EntryDispatch

variable {a m : ℕ}























end Monodromy.Counter.EntryDispatch

/-!
## Locally reversible counter tables
-/

namespace Monodromy.Counter.Reversible









namespace Action

variable {n : ℕ}



















end Action

variable {n q e : ℕ}

namespace Edge







end Edge

























namespace Action











end Action



































namespace Action



end Action





















end Monodromy.Counter.Reversible

/-!
## Static finite port matchings
-/

namespace Monodromy.ReversiblePorts

variable {q e : ℕ}

























open Counter.Reversible





















end Monodromy.ReversiblePorts

/-!
## Native guarded routing
-/

namespace Monodromy.ReversibleRouting

open CoupledContinuation Counter.Reversible ReversiblePorts

variable {q e : ℕ} [NeZero (q + e)]



variable (table : Table 2 q e) (owner : Fin e → Fin q)
  (matching : ∀ guard, Matching owner (selected table guard))





























end Monodromy.ReversibleRouting

/-!
## The fixed reversible native compiler
-/

namespace Monodromy.ReversibleCompilation

open Counter.Reversible CoupledContinuation ReversiblePorts

variable {q e : ℕ} [NeZero q]











































































end Monodromy.ReversibleCompilation

/-!
## Complete execution and actual lifted results
-/

namespace Monodromy.ReversibleCompilation

open Counter.Reversible CoupledContinuation

variable {q e : ℕ} [NeZero q]



















































end Monodromy.ReversibleCompilation

/-!
## Protected source register relocation
-/

namespace Monodromy.Counter.Reversible.RegisterRelocation

variable {n m q e : ℕ}







































end Monodromy.Counter.Reversible.RegisterRelocation

/-!
## Composition by gluing control interfaces
-/

namespace Monodromy.Counter.Reversible.Glue

variable {n q₁ q₂ e₁ e₂ : ℕ}









































/-! Finite traces inside larger control graphs. -/

section FiniteTrace

variable {n m q k e f : ℕ}







end FiniteTrace

end Monodromy.Counter.Reversible.Glue

/-!
## Finite port identification

A partial matching identifies existing output and input positions. Original
edges and actions are retained, including in cyclic networks.
-/

noncomputable section

namespace Monodromy.Counter.Reversible.PortNetwork

variable {n q e : ℕ}



variable {original : Table n q e} (wiring : Wiring original)



















































end Monodromy.Counter.Reversible.PortNetwork

end


/-!
## One reversible radix graph: unpacking and packing
-/

namespace Monodromy.Counter.Reversible.Radix

variable (p : ℕ) [NeZero p]




































































































end Monodromy.Counter.Reversible.Radix

/-!
## Read-only remainder observation by identified radix ports
-/

noncomputable section

namespace Monodromy.Counter.Reversible.RadixObservation

variable (p m : ℕ) [NeZero p]



















































































end Monodromy.Counter.Reversible.RadixObservation

end


/-!
## A source specification for reversible transition recording
-/

namespace Monodromy.Counter.Recorded

variable {n m : ℕ}





























end Monodromy.Counter.Recorded


/-!
## Recoverable execution histories

Finite copies of the reversed radix graph record each instruction branch.
The source registers are protected while the history is packed; the workspace
returns to zero at every dispatch. This is an intermediate reversible source
graph, prior to compression into the two native memory coordinates.
-/

noncomputable section

namespace Monodromy.Counter.Reversible.Recording

variable {n m : ℕ}


















































































































































/-! The natural domain is preserved at every intermediate port. -/













































































































end Monodromy.Counter.Reversible.Recording

end

/-!
## Reversible prime compression

A finite virtual register vector is encoded in prime exponents. All arithmetic
uses the same two-counter radix graph; shared ports select and restore tests.
Exact first returns preserve the entire source configuration. Ordinary traces
are derived from that stronger execution statement.
-/

noncomputable section

namespace Monodromy.Counter.Reversible.PrimeCompression

variable {n q e : ℕ}























































































































































































































































































































































end Monodromy.Counter.Reversible.PrimeCompression

end


/-! Finite source marks on the same native geometric word table. -/

noncomputable section

namespace Monodromy.ReversibleCompilation

open Counter.Reversible CoupledContinuation

variable {q e : ℕ} [NeZero q]









































end Monodromy.ReversibleCompilation

end

end

end


-- Original target, hoisted to top-level theorem solution.
open Monodromy
open Monodromy.CounterContinuation
open CoupledContinuation
variable {m : ℕ}
variable [NeZero m]
theorem solution (program : Counter.Program 2 m)
    (state result : Counter.Configuration 2 m) (source_step : Counter.step program state = some result) :
    ∃ middle : Memory,
      (compile program).step (encode state) = some middle ∧
      (compile program).step middle = some (encode result) := by
  cases instruction : program state.pc with
  | halt => simp [Counter.step, instruction] at source_step
  | inc register target =>
      have result_eq : result =
          ⟨target, Function.update state.counters register (state.counters register + 1)⟩ := by
        simpa [Counter.step, instruction] using source_step.symm
      subst result
      have running : stopping program state.pc 0 = false := by
        simp [stopping, instructionStop, instruction]
      refine ⟨prepare (state.counters 0 : ℤ) (state.counters 1 : ℤ) (label state.pc 1), ?_, ?_⟩
      · change (compile program).step
          (prepare (state.counters 0 : ℤ) (state.counters 1 : ℤ) (label state.pc 0)) = _
        rw [step_running_at program state.pc 0 running,
          advance_inc_first program state.pc target register instruction]
      · rw [step_phase_one, advance_inc_second program state.pc target register instruction]
        apply congrArg some
        unfold encode
        fin_cases register <;> simp [Function.update]
  | dec register zero nonzero =>
      have running : stopping program state.pc 0 = false := by
        simp [stopping, instructionStop, instruction]
      cases counter : state.counters register with
      | zero =>
          have result_eq : result = ⟨zero, state.counters⟩ := by
            simpa [Counter.step, instruction, counter] using source_step.symm
          subst result
          have zero_value : (![((state.counters 0 : ℤ)), ((state.counters 1 : ℤ))] register) = 0 := by
            have casted := congrArg (fun value : ℕ => (value : ℤ)) counter
            fin_cases register <;> simpa using casted
          have first_return :
              (compile program).advance
                (prepare (state.counters 0 : ℤ) (state.counters 1 : ℤ) (label state.pc 0)) =
              prepare (state.counters 0 : ℤ) (state.counters 1 : ℤ) (label state.pc 2) := by
            rw [advance_dec_first program state.pc zero nonzero register instruction, zero_value]
            simp only [ite_true]
            congr 1
            simp [label_eq]
            omega
          refine ⟨prepare (state.counters 0 : ℤ) (state.counters 1 : ℤ) (label state.pc 2), ?_, ?_⟩
          · change (compile program).step
              (prepare (state.counters 0 : ℤ) (state.counters 1 : ℤ) (label state.pc 0)) = _
            rw [step_running_at program state.pc 0 running, first_return]
          · rw [step_phase_two, advance_dec_zero program state.pc zero nonzero register instruction]
            rfl
      | succ value =>
          have result_eq : result = ⟨nonzero, Function.update state.counters register value⟩ := by
            simpa [Counter.step, instruction, counter] using source_step.symm
          subst result
          have nonzero_value : (![((state.counters 0 : ℤ)), ((state.counters 1 : ℤ))] register) ≠ 0 := by
            have casted := congrArg (fun value : ℕ => (value : ℤ)) counter
            have positive : (![((state.counters 0 : ℤ)), ((state.counters 1 : ℤ))] register) = (value : ℤ) + 1 := by
              fin_cases register <;> simpa using casted
            omega
          have first_return :
              (compile program).advance
                (prepare (state.counters 0 : ℤ) (state.counters 1 : ℤ) (label state.pc 0)) =
              prepare (state.counters 0 : ℤ) (state.counters 1 : ℤ) (label state.pc 1) := by
            simpa only [ite_eq_right nonzero_value, add_zero] using
              advance_dec_first program state.pc zero nonzero register instruction
                (state.counters 0 : ℤ) (state.counters 1 : ℤ)
          refine ⟨prepare (state.counters 0 : ℤ) (state.counters 1 : ℤ) (label state.pc 1), ?_, ?_⟩
          · change (compile program).step
              (prepare (state.counters 0 : ℤ) (state.counters 1 : ℤ) (label state.pc 0)) = _
            rw [step_running_at program state.pc 0 running, first_return]
          · rw [step_phase_one, advance_dec_positive program state.pc zero nonzero register instruction]
            apply congrArg some
            unfold encode
            fin_cases register <;> simp_all [Function.update]
