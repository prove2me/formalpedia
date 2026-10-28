-- Prove2me | solution 1 for MFOTLMon.Monitor.observation_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T21:31:27.490659+00:00
-- url     : https://prove2.me/submissions/929c1466-d8b3-4b3c-9350-2c3fb7d3353f

import Definitions.Def_MFOTLMon_Monitor_Algorithm

namespace MFOTLMon.Monitor

namespace QueueProof

variable {S : Signature}

theorem run_zero (D : TempStruct S) (Φ : Formula S) : run D Φ 0 = init Φ := rfl

theorem run_succ (D : TempStruct S) (Φ : Formula S) (k : ℕ) :
    run D Φ (k + 1) = iteration D Φ (run D Φ k) := by
  exact Function.iterate_succ_apply' (iteration D Φ) k (init Φ)

theorem evalLoop_ell (D : TempStruct S) (Φ : Formula S) (fuel : ℕ) (s : State S) :
    (evalLoop D Φ fuel s).ell = s.ell := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
      rw [evalLoop]
      split
      · exact ih _
      · rfl

theorem evalLoop_Q (D : TempStruct S) (Φ : Formula S) (fuel : ℕ) (s : State S) :
    (evalLoop D Φ fuel s).Q = s.Q := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
      rw [evalLoop]
      split
      · exact ih _
      · rfl

theorem iteration_ell (D : TempStruct S) (Φ : Formula S) (s : State S) :
    (iteration D Φ s).ell = s.ell + 1 := by
  exact congrArg (fun n : ℕ ↦ n + 1) (evalLoop_ell D Φ (s.ell + 2) (afterBuild D s))

theorem iteration_Q (D : TempStruct S) (Φ : Formula S) (s : State S) :
    (iteration D Φ s).Q = updateQ D Φ s := by
  change updateQ D Φ (evalLoop D Φ (s.ell + 2) (afterBuild D s)) = updateQ D Φ s
  simp only [updateQ, evalLoop_Q, evalLoop_ell]
  rfl

theorem run_ell (D : TempStruct S) (Φ : Formula S) (k : ℕ) :
    (run D Φ k).ell = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [run_succ, iteration_ell, ih]

theorem mem_updateQ_fresh (D : TempStruct S) (Φ : Formula S) (s : State S)
    (α : Formula S) (hα : α ∈ tempSubs Φ) :
    (α, s.ell + 1, waitfor α) ∈ updateQ D Φ s := by
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨α, hα, rfl⟩

theorem mem_iteration_fresh (D : TempStruct S) (Φ : Formula S) (s : State S)
    (α : Formula S) (hα : α ∈ tempSubs Φ) :
    (α, s.ell + 1, waitfor α) ∈ (iteration D Φ s).Q := by
  change (α, s.ell + 1, waitfor α) ∈
    updateQ D Φ (evalLoop D Φ (s.ell + 2) (afterBuild D s))
  have hell : (evalLoop D Φ (s.ell + 2) (afterBuild D s)).ell = s.ell :=
    evalLoop_ell D Φ (s.ell + 2) (afterBuild D s)
  simpa only [hell] using
    mem_updateQ_fresh D Φ (evalLoop D Φ (s.ell + 2) (afterBuild D s)) α hα

theorem observation_one (D : TempStruct S) (Φ : Formula S) :
    ∀ α ∈ tempSubs Φ, ∀ k : ℕ, (α, k, waitfor α) ∈ (run D Φ k).Q := by
  intro α hα k
  cases k with
  | zero =>
      change (α, 0, waitfor α) ∈ (tempSubs Φ).map (fun β ↦ (β, 0, waitfor β))
      exact List.mem_map.mpr ⟨α, hα, rfl⟩
  | succ k =>
      rw [run_succ]
      simpa only [run_ell] using mem_iteration_fresh D Φ (run D Φ k) α hα

end QueueProof

end MFOTLMon.Monitor

open MFOTLMon.Monitor

theorem solution {S : Signature} (D : TempStruct S) (Φ : Formula S) :
    ∀ α ∈ tempSubs Φ, ∀ k : ℕ, (α, k, waitfor α) ∈ (run D Φ k).Q := by
  exact QueueProof.observation_one D Φ
