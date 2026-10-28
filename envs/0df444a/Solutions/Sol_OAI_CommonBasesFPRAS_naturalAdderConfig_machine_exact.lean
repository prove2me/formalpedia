-- Prove2me | solution 1 for OAI.CommonBasesFPRAS.naturalAdderConfig_machine_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T20:50:32.157752+00:00
-- url     : https://prove2.me/submissions/6a9fc4c2-487b-4e72-b3cd-c3bb6146a889

import Definitions.Def_OAICommonBasesFPRASNaturalAdderMachine

set_option autoImplicit false
set_option maxHeartbeats 800000
open OAI.CommonBasesFPRAS

theorem solution {n : ℕ} (O : IndependenceOracle n)
    (coins : ℕ → Bool) (a b : ℕ) :
    let c := naturalAdderConfig a b
    let out := execution
      (binaryStackAdderWithCall (fun _ => Instruction.halt) ⟨0, by omega⟩)
      O c coins (adderTotalSteps a.bits b.bits + 1)
    out.control = ⟨23, by omega⟩ ∧
    binaryValue (out.registers (adderReg 6)) = a + b ∧
    out.registers (adderReg 7) = [true] ∧
    out.registers (adderReg 8) = [] ∧
    out.output = none ∧ out.oracleCalls = 0 ∧
    out.bitOperations ≤ 6 * max a.bits.length b.bits.length + 10 := by
  rcases naturalAdderConfig_correct O coins a b with
    ⟨hcontrol, hvalue, hden, hscratch, houtput, hcalls⟩
  rcases naturalAdderConfig_resources O coins a b with ⟨_, hcost⟩
  exact ⟨hcontrol, hvalue, hden, hscratch, houtput, hcalls, hcost⟩
