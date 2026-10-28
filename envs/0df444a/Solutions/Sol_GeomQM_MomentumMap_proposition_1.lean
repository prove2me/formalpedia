-- Prove2me | solution 1 for GeomQM.MomentumMap.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T10:49:54.073476+00:00
-- url     : https://prove2.me/submissions/bd9cde27-b234-49c0-a941-cd7d8f64115c

import Mathlib
import Definitions.Def_GeomQM_MomentumMap_Defs

open Matrix

open GeomQM.MomentumMap in
theorem solution (n : ℕ) (A B C : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hC : C.IsHermitian) :
    scal (lieO A B) C = scal A (lieO B C) ∧
    scal (jordan A B) C = scal A (jordan B C) ∧
    lieO A (jordan B C) = jordan (lieO A B) C + jordan B (lieO A C) := by
  have hcyc : (B * A * C).trace = (A * C * B).trace := by
    rw [trace_mul_cycle A C B]
  refine ⟨?_, ?_, ?_⟩
  · simp only [scal, lieO, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
      trace_smul, trace_sub, smul_eq_mul, ← Matrix.mul_assoc, hcyc]
  · simp only [scal, jordan, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
      trace_smul, trace_add, smul_eq_mul, ← Matrix.mul_assoc, hcyc]
  · simp only [lieO, jordan, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.sub_mul, Matrix.mul_sub, smul_add, smul_sub, smul_smul, ← Matrix.mul_assoc]
    module
