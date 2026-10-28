-- Prove2me | solution 1 for OAI.CommonBasesFPRAS.sampleThen_afterSampling
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T02:20:05.795015+00:00
-- url     : https://prove2.me/submissions/04919159-9028-4857-a2b6-6a3d7b5b469e

import Definitions.Def_CountingMatroidProgramShift
set_option autoImplicit false
set_option maxHeartbeats 800000

open OAI.CommonBasesFPRAS

theorem program_execution_add_steps {k s n : ℕ} (P : Program k s)
    (O : IndependenceOracle n) (c : MachineConfig k s)
    (bits : ℕ → Bool) (a b : ℕ) :
    execution P O c bits (a+b) =
      execution P O (execution P O c bits a) (fun t => bits (a+t)) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change machineStep P O (bits (a+b)) (execution P O c bits (a+b)) = _
    rw [ih]
    rfl

theorem shift_machineStep {k s n : ℕ} (P : Program k s)
 (O : IndependenceOracle n) (bit : Bool) (c : MachineConfig k s) :
 machineStep (shiftProgram P) O bit (embedConfig c) = embedConfig (machineStep P O bit c) := by
 cases c with
 | mk regs ctrl out calls ops =>
  cases hout : out with
  | none =>
    cases hinstr : P ctrl with
    | push r b next => simp [machineStep, shiftProgram, embedConfig, shiftState, shiftInstruction, hout, hinstr, Function.update]
    | pop r e z o =>
      cases hreg : regs r with
      | nil => simp [machineStep, shiftProgram, embedConfig, shiftState, shiftInstruction, hout, hinstr, hreg]
      | cons b rest => cases b <;> simp [machineStep, shiftProgram, embedConfig, shiftState, shiftInstruction, hout, hinstr, hreg, Function.update]
    | coin z o => cases bit <;> simp [machineStep, shiftProgram, embedConfig, shiftState, shiftInstruction, hout, hinstr]
    | query w r no yes =>
      by_cases hlen : (regs r).length = n
      · have hread : ∀ j : Fin n, (regs r)[j.val]?.getD false = (regs r)[j.val] := by
          intro j
          have hj : j.val < (regs r).length := by rw [hlen]; exact j.isLt
          simp [List.getElem?_eq_getElem hj]
        have hsame : O w (fun j : Fin n => (regs r)[j.val]?.getD false) =
            O w (fun j : Fin n => (regs r)[j.val]) := by
          congr 1
          funext j
          exact hread j
        cases hquery : O w (fun j => (regs r)[j.val]?.getD false) with
        | false =>
          have hquery' : O w (fun j : Fin n => (regs r)[j.val]) = false := by
            rw [← hsame]
            exact hquery
          simp [machineStep, shiftProgram, embedConfig, shiftState, shiftInstruction,
            hinstr, hlen, hquery']
        | true =>
          have hquery' : O w (fun j : Fin n => (regs r)[j.val]) = true := by
            rw [← hsame]
            exact hquery
          simp [machineStep, shiftProgram, embedConfig, shiftState, shiftInstruction,
            hinstr, hlen, hquery']
      · simp [machineStep, shiftProgram, embedConfig, shiftState, shiftInstruction,
          hinstr, hlen]
    | halt => simp [machineStep, shiftProgram, embedConfig, shiftState, shiftInstruction, hout, hinstr]
  | some x => simp [machineStep, embedConfig, hout]

/-- Re-indexing a program's control states preserves its complete run, including
the input-bit stream, oracle-call count, and bit-operation count. -/
theorem shift_execution {k s n : ℕ} (P : Program k s)
    (O : IndependenceOracle n) (c : MachineConfig k s)
    (bits : ℕ → Bool) (t : ℕ) :
    execution (shiftProgram P) O (embedConfig c) bits t =
      embedConfig (execution P O c bits t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [execution]
    rw [ih, shift_machineStep]

/-- After entering the shifted evaluator region, the combined program takes
exactly the same steps as the evaluator's shifted copy. -/
theorem sampleThen_machineStep {s n : ℕ} (P : Program 2 s)
    (O : IndependenceOracle n) (bit : Bool) (c : MachineConfig 2 (s+4))
    (hc : 4 ≤ c.control.val) :
    machineStep (sampleThenProgram P) O bit c =
      machineStep (shiftProgram P) O bit c := by
  have hprog : sampleThenProgram P c.control = shiftProgram P c.control := by
    have hlt : ¬ c.control.val < 4 := by omega
    simp [sampleThenProgram, shiftProgram, shiftInstruction, hlt]
  simp only [machineStep]
  rw [hprog]

/-- Complete-run simulation after the sampler has transferred control to state four. -/
theorem sampleThen_execution {s n : ℕ} (P : Program 2 s)
    (O : IndependenceOracle n) (c : MachineConfig 2 s)
    (bits : ℕ → Bool) (t : ℕ) :
    execution (sampleThenProgram P) O (embedConfig c) bits t =
      embedConfig (execution P O c bits t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [execution]
    rw [ih]
    have hc : 4 ≤ (embedConfig (execution P O c bits t)).control.val := by
      simp [embedConfig, shiftState]
    rw [sampleThen_machineStep P O (bits t) _ hc, shift_machineStep]

/-- Register contents after `m` three-instruction sampling cycles. -/
private theorem sampleThen_cycle {s n : ℕ} (P : Program 2 s)
    (O : IndependenceOracle n) (c : MachineConfig 2 (s+4))
    (bits : ℕ → Bool) (b : Bool) (rest : List Bool)
    (hcontrol : c.control.val = 0) (houtput : c.output = none)
    (hcounter : c.registers 8 = b :: rest) :
    execution (sampleThenProgram P) O c bits 3 =
      { c with
        registers := Function.update (Function.update c.registers 8 rest) 9
          (bits 1 :: c.registers 9)
        control := 0
        bitOperations := c.bitOperations + 3 } := by
  cases hbit : bits 1 <;>
    simp [execution, machineStep, sampleThenProgram, hcontrol, houtput,
      hcounter, hbit, Function.update, Nat.add_assoc]

/-- Exact prefix simulation: the combined program draws only at positions
`3m+1`, maintains the unary counter, and leaves evaluator inputs untouched. -/
theorem sampleThen_prefix {s n : ℕ} (P : Program 2 s)
    (O : IndependenceOracle n) (c : MachineConfig 2 s)
    (bits : ℕ → Bool) (K m : ℕ) (hm : m ≤ K) :
    execution (sampleThenProgram P) O (sampledProgramConfig c bits K 0)
        bits (3*m) = sampledProgramConfig c bits K m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hrem : K-m = (K-(m+1))+1 := by omega
    rw [show 3*(m+1) = 3*m+3 by omega,
      program_execution_add_steps, ih (by omega)]
    rw [sampleThen_cycle P O _ (fun t => bits (3*m+t)) false
      (List.replicate (K-(m+1)) false) (by simp [sampledProgramConfig]) rfl
      (by simp [sampledProgramConfig, hrem, List.replicate_succ])]
    simp [sampledProgramConfig, programSampledStack, Function.update,
      Nat.mul_add, Nat.add_assoc]
    funext i
    by_cases h8 : i = 8 <;> by_cases h9 : i = 9 <;> simp_all [Function.update]

/-- Sampling and evaluation compose without changing the evaluator's run:
after the exact `3K+1` sampling instructions, the remaining random stream is
passed to the shifted evaluator and all of its transitions are preserved. -/
theorem sampleThen_afterSampling_lemma {s n : ℕ} (P : Program 2 s)
    (O : IndependenceOracle n) (c : MachineConfig 2 s)
    (bits : ℕ → Bool) (K t : ℕ) :
    execution (sampleThenProgram P) O (sampledProgramConfig c bits K 0)
        bits (3*K+1+t) =
      embedConfig (execution P O (afterSampleConfig c bits K)
        (fun j => bits (3*K+1+j)) t) := by
  have hsplit := program_execution_add_steps
    (P := sampleThenProgram P) (O := O)
    (c := sampledProgramConfig c bits K 0) (bits := bits)
    (a := 3*K+1) (b := t)
  rw [show 3*K+1+t = (3*K+1)+t by omega, hsplit]
  have hdone : execution (sampleThenProgram P) O
      (sampledProgramConfig c bits K 0) bits (3*K+1) =
      embedConfig (afterSampleConfig c bits K) := by
    have hsplit' := program_execution_add_steps
      (P := sampleThenProgram P) (O := O)
      (c := sampledProgramConfig c bits K 0) (bits := bits)
      (a := 3*K) (b := 1)
    rw [show 3*K+1 = 3*K+1 by rfl, hsplit',
      sampleThen_prefix P O c bits K K (by omega)]
    simp [execution, machineStep, sampleThenProgram, sampledProgramConfig,
      afterSampleConfig, embedConfig, shiftState, Function.update, Nat.add_assoc]
  rw [hdone]
  exact sampleThen_execution P O (afterSampleConfig c bits K)
    (fun j => bits (3*K+1+j)) t

theorem solution {s n : ℕ} (P : Program 2 s)
    (O : IndependenceOracle n) (c : MachineConfig 2 s)
    (bits : ℕ → Bool) (K t : ℕ) :
    execution (sampleThenProgram P) O (sampledProgramConfig c bits K 0)
        bits (3*K+1+t) =
      embedConfig (execution P O (afterSampleConfig c bits K)
        (fun j => bits (3*K+1+j)) t) := by
  exact sampleThen_afterSampling_lemma P O c bits K t

