-- Prove2me | solution 1 for HeisenbergRep.Knill.anticommute_conj_neg
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:53:51.140584+00:00
-- url     : https://prove2.me/submissions/73eb427f-882a-433c-aaa5-15f6f447a110

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QECC

open QAlgorithms
open scoped Matrix

theorem solution {n : ℕ} (E : Matrix.unitaryGroup (Qubits n) ℂ)
    (hE : E ∈ pauliGroup n) (M : Matrix (Qubits n) (Qubits n) ℂ)
    (hEM : (E : Matrix (Qubits n) (Qubits n) ℂ) * M = -(M * (E : Matrix (Qubits n) (Qubits n) ℂ))) :
    (E : Matrix (Qubits n) (Qubits n) ℂ) * M * (E : Matrix (Qubits n) (Qubits n) ℂ)ᴴ = -M := by
  have hEE : (E : Matrix (Qubits n) (Qubits n) ℂ) * (E : Matrix (Qubits n) (Qubits n) ℂ)ᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp E.2
    rwa [Matrix.star_eq_conjTranspose] at this
  rw [hEM, Matrix.neg_mul, Matrix.mul_assoc, hEE, Matrix.mul_one]
