-- Prove2me | solution 1 for HeisenbergRep.Knill.heisenberg_update
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:52:19.014474+00:00
-- url     : https://prove2.me/submissions/32713a67-861d-4e8a-baab-c38380667edf

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Stabilizer

open QAlgorithms
open scoped Matrix

theorem solution {n : ℕ} (U : Matrix (Qubits n) (Qubits n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Qubits n) ℂ) (M N : Matrix (Qubits n) (Qubits n) ℂ)
    (ψ : EuclideanSpace ℂ (Qubits n)) :
    act U (act N ψ) = act (U * N * Uᴴ) (act U ψ) ∧
      U * (M * N) * Uᴴ = (U * M * Uᴴ) * (U * N * Uᴴ) := by
  have hUU : Uᴴ * U = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp hU
    rwa [Matrix.star_eq_conjTranspose] at this
  have key : U * N * Uᴴ * U = U * N := by
    rw [Matrix.mul_assoc (U * N), hUU, Matrix.mul_one]
  refine ⟨?_, ?_⟩
  · unfold act
    simp only [WithLp.ofLp_toLp, Matrix.mulVec_mulVec, key]
  · calc U * (M * N) * Uᴴ = U * M * (Uᴴ * U) * N * Uᴴ := by
          rw [hUU, Matrix.mul_one, Matrix.mul_assoc U M N]
      _ = (U * M * Uᴴ) * (U * N * Uᴴ) := by
          simp only [Matrix.mul_assoc]
