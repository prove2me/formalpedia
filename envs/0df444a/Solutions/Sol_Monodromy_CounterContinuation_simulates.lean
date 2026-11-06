-- Prove2me | solution 1 for Monodromy.CounterContinuation.simulates
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:30:55.831112+00:00
-- url     : https://prove2.me/submissions/45eaca34-3109-4b75-8316-6e0ed494ed9f

module
public import Definitions.Def_Monodromy_Counter
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.FinCases

@[expose] public section

open Monodromy
open Monodromy.CounterContinuation
open CoupledContinuation
variable {m : ℕ}
variable [NeZero m]

namespace Monodromy.CoupledContinuation

private theorem execute_word_atom (gate : Gate) (backward : Bool) (state : Memory) :
    execute (Word.driver (Word.atom gate backward)) state =
      execute (if backward then gate.driver.reverse else gate.driver) state := by
  rw [Word.atom, execute_word_cons, execute_word_nil]

namespace Program

variable {degree : ℕ} [NeZero degree]

private theorem haltSignal_prepare (program : Program degree) (left right quotient : ℤ)
    (index : Fin degree) :
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

private theorem step_prepare (program : Program degree) (left right quotient : ℤ) (index : Fin degree) :
    program.step (prepare left right ((degree : ℤ) * quotient + index.val)) =
      if program.stop index then none else
        some (execute (Word.driver (program.table index))
          (prepare left right ((degree : ℤ) * quotient + index.val))) := by
  unfold step
  rw [haltSignal_prepare]
  cases program.stop index <;> simp [advance_prepare]

end Program

end Monodromy.CoupledContinuation

namespace Monodromy.CounterContinuation

open CoupledContinuation

private theorem label_eq {m : ℕ} (position : Fin m) (phase : Fin 3) :
    label position phase = (phase.val : ℤ) + 3 * (position.val : ℤ) := by
  simp [label, finProdFinEquiv]

private theorem compile_table_address {m : ℕ} (program : Counter.Program 2 m)
    (position : Fin m) (phase : Fin 3) :
    (compile program).table (finProdFinEquiv (position, phase)) = instructionWord program position phase := by
  simp [compile, wordTable]

private theorem compile_stop_address {m : ℕ} (program : Counter.Program 2 m)
    (position : Fin m) (phase : Fin 3) :
    (compile program).stop (finProdFinEquiv (position, phase)) = stopping program position phase := by
  simp [compile, stopTable]

private theorem advance_at (program : Counter.Program 2 m) (left right : ℤ)
    (position : Fin m) (phase : Fin 3) :
    (compile program).advance (prepare left right (label position phase)) =
      execute (Word.driver (instructionWord program position phase))
        (prepare left right (label position phase)) := by
  have run := CoupledContinuation.Program.advance_prepare (compile program) left right 0
    (finProdFinEquiv (position, phase))
  simpa only [mul_zero, zero_add, compile_table_address, label] using run

private theorem step_at (program : Counter.Program 2 m) (left right : ℤ)
    (position : Fin m) (phase : Fin 3) :
    (compile program).step (prepare left right (label position phase)) =
      if stopping program position phase then none else
        some (execute (Word.driver (instructionWord program position phase))
          (prepare left right (label position phase))) := by
  have run := CoupledContinuation.Program.step_prepare (compile program) left right 0
    (finProdFinEquiv (position, phase))
  simpa only [mul_zero, zero_add, compile_table_address, compile_stop_address, label] using run

private theorem advance_inc_first (program : Counter.Program 2 m) (position target : Fin m)
    (register : Fin 2) (instruction : program position = .inc register target) (left right : ℤ) :
    (compile program).advance (prepare left right (label position 0)) =
      prepare left right (label position 1) := by
  rw [advance_at]
  simp [instructionWord, instruction]
  rw [execute_control_word]
  congr 1
  simp [label_eq]
  omega

private theorem advance_inc_second (program : Counter.Program 2 m) (position target : Fin m)
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

private theorem advance_dec_first (program : Counter.Program 2 m) (position zero nonzero : Fin m)
    (register : Fin 2) (instruction : program position = .dec register zero nonzero) (left right : ℤ) :
    (compile program).advance (prepare left right (label position 0)) =
      prepare left right (label position 1 + if (![left, right] register) = 0 then 1 else 0) := by
  rw [advance_at]
  simp [instructionWord, instruction]
  rw [execute_word_append, execute_control_word, execute_word_atom]
  fin_cases register
  · change execute B_left _ = _
    rw [execute_B_left]
    congr 1
    simp [label_eq]
    omega
  · change execute B_right _ = _
    rw [execute_B_right]
    congr 1
    simp [label_eq]
    omega

private theorem advance_dec_positive (program : Counter.Program 2 m) (position zero nonzero : Fin m)
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

private theorem advance_dec_zero (program : Counter.Program 2 m) (position zero nonzero : Fin m)
    (register : Fin 2) (instruction : program position = .dec register zero nonzero) (left right : ℤ) :
    (compile program).advance (prepare left right (label position 2)) =
      prepare left right (label zero 0) := by
  rw [advance_at]
  simp [instructionWord, instruction]
  rw [execute_control_word]
  congr 1
  omega

private theorem step_running_at (program : Counter.Program 2 m) (position : Fin m) (phase : Fin 3)
    (running : stopping program position phase = false) (left right : ℤ) :
    (compile program).step (prepare left right (label position phase)) =
      some ((compile program).advance (prepare left right (label position phase))) := by
  rw [step_at, running]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [advance_at]

private theorem step_phase_one (program : Counter.Program 2 m) (position : Fin m) (left right : ℤ) :
    (compile program).step (prepare left right (label position 1)) =
      some ((compile program).advance (prepare left right (label position 1))) := by
  apply step_running_at
  simp [stopping]

private theorem step_phase_two (program : Counter.Program 2 m) (position : Fin m) (left right : ℤ) :
    (compile program).step (prepare left right (label position 2)) =
      some ((compile program).advance (prepare left right (label position 2))) := by
  apply step_running_at
  simp [stopping]

/-- A source halt is read by the native finite-root stopping signal. -/
private theorem step_halt (program : Counter.Program 2 m) (state : Counter.Configuration 2 m)
    (instruction : program state.pc = .halt) : (compile program).step (encode state) = none := by
  unfold encode
  rw [step_at]
  simp [stopping, instructionStop, instruction]

/-- Every live source step is realized by exactly two nonempty native returns. -/
private theorem two_returns (program : Counter.Program 2 m)
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

end Monodromy.CounterContinuation

/-- The geometric program refines the standard two-counter transition system. -/
theorem solution (program : Counter.Program 2 m) :
    StateTransition.Respects (Counter.step program) (compile program).step
      (fun first second => encode first = second) := by
  apply StateTransition.fun_respects.mpr
  intro state
  cases source_step : Counter.step program state with
  | none =>
      change (compile program).step (encode state) = none
      cases instruction : program state.pc with
      | halt => exact Monodromy.CounterContinuation.step_halt program state instruction
      | inc register target => simp [Counter.step, instruction] at source_step
      | dec register zero nonzero =>
          cases counter : state.counters register <;>
            simp [Counter.step, instruction, counter] at source_step
  | some result =>
      change StateTransition.Reaches₁ (compile program).step (encode state) (encode result)
      obtain ⟨middle, first_return, second_return⟩ :=
        Monodromy.CounterContinuation.two_returns program state result source_step
      have first_reach : StateTransition.Reaches₁ (compile program).step (encode state) middle :=
        Relation.TransGen.single first_return
      exact first_reach.tail second_return
