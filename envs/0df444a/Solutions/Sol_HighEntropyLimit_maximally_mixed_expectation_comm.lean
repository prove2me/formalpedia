-- Prove2me | solution 1 for HighEntropyLimit.maximally_mixed_expectation_comm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T05:36:11.266843+00:00
-- url     : https://prove2.me/submissions/5cdd6b34-ded0-4491-8b25-86cb05a5dffc

import Mathlib

theorem solution (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (A * B * ((n : ℂ)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℂ))) =
      Matrix.trace (B * A * ((n : ℂ)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℂ))) := by
  simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, Matrix.trace_mul_comm A B]
