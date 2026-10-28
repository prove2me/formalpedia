-- Prove2me | solution 1 for OAI.CommonBasesFPRAS.multiplierContinuation_return_step_reusable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T21:10:17.46211+00:00
-- url     : https://prove2.me/submissions/7ffefe09-c85e-4f23-ab81-7b4ef583f159

import Definitions.Def_OAICommonBasesFPRASMultiplierContinuation

set_option autoImplicit false
set_option maxHeartbeats 800000
open OAI.CommonBasesFPRAS

theorem solution {s n : ℕ}
    (P : Program 2 s) (O : IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 2 (s + 38))
    (hcontrol : c.control = ⟨36, by omega⟩)
    (hout : c.output = none) (hmarker : c.registers (adderReg 3) = []) :
    let out := execution (binaryStackMultiplierWithCall P) O c bits 1
    out.control = ⟨38, by omega⟩ ∧ out.registers = c.registers ∧
    out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + 1 := by
  exact binaryStackMultiplierWithCall_return_step P O bits c hcontrol hout hmarker
