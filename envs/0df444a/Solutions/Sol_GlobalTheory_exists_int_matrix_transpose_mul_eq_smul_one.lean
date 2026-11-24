-- Prove2me | solution 1 for GlobalTheory.exists_int_matrix_transpose_mul_eq_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:42:35.471044+00:00
-- url     : https://prove2.me/submissions/27d18212-d3c2-4300-9295-d8e815a5e448

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIntMatrixTransposeMulEqSmulOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (s : ℕ) :
    ∃ x : Matrix (Fin 4) (Fin 4) ℤ, x.transpose * x = (s : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) ∧
      x * x.transpose = (s : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares s
  have h' : ((a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c : ℤ) ^ 2 + (d : ℤ) ^ 2) = (s : ℤ) := by
    exact_mod_cast h
  refine ⟨!![(a:ℤ), -b, -c, -d; b, a, -d, c; c, d, a, -b; d, -c, b, a], ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;>
      first | linear_combination h' | ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;>
      first | linear_combination h' | ring
end GlobalTheory
