-- Prove2me | solution 1 for HeisenbergRep.Knill.measurement_correction
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T03:47:22.962064+00:00
-- url     : https://prove2.me/submissions/f27b37be-4664-4a1a-9bf7-ec65c77b37c7

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QECC

open QAlgorithms
open scoped Matrix

theorem solution {n : ℕ} (M : Matrix.unitaryGroup (Qubits n) ℂ)
    (hM : M ∈ pauliGroup n) (A : Matrix (Qubits n) (Qubits n) ℂ)
    (hMA : (M : Matrix (Qubits n) (Qubits n) ℂ) * A = -(A * (M : Matrix (Qubits n) (Qubits n) ℂ))) :
    (M : Matrix (Qubits n) (Qubits n) ℂ) * ((2⁻¹ : ℂ) • (1 - A)) *
        (M : Matrix (Qubits n) (Qubits n) ℂ)ᴴ = (2⁻¹ : ℂ) • (1 + A) ∧
    ∀ ψ : EuclideanSpace ℂ (Qubits n), act (M : Matrix (Qubits n) (Qubits n) ℂ) ψ = ψ →
      act (M : Matrix (Qubits n) (Qubits n) ℂ) (act ((2⁻¹ : ℂ) • (1 - A)) ψ) =
        act ((2⁻¹ : ℂ) • (1 + A)) ψ := by
  have hU : (M : Matrix (Qubits n) (Qubits n) ℂ) * (M : Matrix (Qubits n) (Qubits n) ℂ)ᴴ = 1 := by
    have := M.2
    rw [Matrix.mem_unitaryGroup_iff] at this
    exact this
  have hact : ∀ (B C : Matrix (Qubits n) (Qubits n) ℂ) (φ : EuclideanSpace ℂ (Qubits n)),
      act B (act C φ) = act (B * C) φ := by
    intro B C φ
    unfold act
    rw [WithLp.ofLp_toLp, Matrix.mulVec_mulVec]
  refine ⟨?_, fun ψ hψ => ?_⟩
  · rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hU, hMA,
      Matrix.neg_mul, Matrix.mul_assoc, hU, Matrix.mul_one, sub_neg_eq_add]
  · have e : (M : Matrix (Qubits n) (Qubits n) ℂ) * ((2⁻¹ : ℂ) • (1 - A))
        = ((2⁻¹ : ℂ) • (1 + A)) * (M : Matrix (Qubits n) (Qubits n) ℂ) := by
      rw [Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one, hMA, sub_neg_eq_add, Matrix.smul_mul,
        Matrix.add_mul, Matrix.one_mul]
    rw [hact, e, ← hact, hψ]
