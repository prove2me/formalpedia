-- Prove2me | solution 1 for OAI.CommonBasesFPRAS.naturalMultiplierConfig_machine_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T20:42:18.09752+00:00
-- url     : https://prove2.me/submissions/254f927f-0bad-4098-9a7c-5385e24b7357

import Definitions.Def_OAICommonBasesFPRASNaturalMultiplierMachineV2

set_option autoImplicit false
set_option maxHeartbeats 800000
open OAI.CommonBasesFPRAS

theorem solution {n : ℕ} (O : IndependenceOracle n)
    (coins : ℕ → Bool) (a b : ℕ) :
    let c := naturalMultiplierConfig a b
    let out := execution binaryStackMultiplierProgram O c coins
      (binaryStackMultiplierLoopSteps [] a.bits b.bits)
    out.output = some ((a * b : ℕ) : ℚ) ∧
      out.oracleCalls = 0 ∧
      out.bitOperations ≤ 100 * (b.bits.length + 1) *
        (a.bits.length + b.bits.length + 5) := by
  exact ⟨naturalMultiplierConfig_correct O coins a b,
    naturalMultiplierConfig_resources O coins a b⟩
