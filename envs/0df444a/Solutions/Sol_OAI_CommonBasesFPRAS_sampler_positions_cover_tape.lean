-- Prove2me | solution 1 for OAI.CommonBasesFPRAS.sampler_positions_cover_tape
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T02:30:56.359335+00:00
-- url     : https://prove2.me/submissions/58c462cb-8524-4a19-983b-05067c140b0a

import Definitions.Def_CountingMatroidProgramShift
import Theorems.Thm_OAI_CommonBasesFPRAS_sampleThen_afterSampling
set_option autoImplicit false
set_option maxHeartbeats 800000
open OAI.CommonBasesFPRAS

def samplerPosition (K : ℕ) (i : Fin K) : Fin (3*K+1) :=
  ⟨3 * (K - 1 - i.val) + 1, by have hi := i.isLt; omega⟩

theorem samplerPosition_injective (K : ℕ) : Function.Injective (samplerPosition K) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  dsimp [samplerPosition] at hv
  omega

theorem programSampledStack_eq_ofFn (bits : ℕ → Bool) (K : ℕ) :
    programSampledStack bits K = List.ofFn (fun i : Fin K => bits (samplerPosition K i).val) := by
  induction K with
  | zero => simp [programSampledStack]
  | succ K ih =>
    simp only [programSampledStack, List.ofFn_succ, List.cons.injEq]
    constructor
    · change bits (3*K+1) = bits (samplerPosition (K+1) 0).val
      congr 1
    · change programSampledStack bits K =
        List.ofFn (fun i : Fin K => bits (samplerPosition (K+1) i.succ).val)
      rw [ih]
      congr 1
      funext i
      congr 1
      simp [samplerPosition]
      omega

theorem solution {s n : ℕ} (P : Program 2 s)
    (O : IndependenceOracle n) (c : MachineConfig 2 s)
    (bits : ℕ → Bool) (K : ℕ) (hreg9 : c.registers 9 = []) :
    ∃ positions : Fin K ↪ Fin (3*K+1),
      (∀ i, (positions i).val = 3 * (K - 1 - i.val) + 1) ∧
      (execution (sampleThenProgram P) O (sampledProgramConfig c bits K 0)
        bits (3*K+1)).registers 9 =
        List.ofFn (fun i : Fin K => bits (positions i).val) := by
  let positions : Fin K ↪ Fin (3*K+1) :=
    ⟨samplerPosition K, samplerPosition_injective K⟩
  refine ⟨positions, ?_, ?_⟩
  · intro i
    rfl
  · have hrun := OAI.CommonBasesFPRAS.sampleThen_afterSampling P O c bits K 0
    rw [hrun]
    simp [execution, afterSampleConfig, embedConfig, positions, hreg9,
      programSampledStack_eq_ofFn]
