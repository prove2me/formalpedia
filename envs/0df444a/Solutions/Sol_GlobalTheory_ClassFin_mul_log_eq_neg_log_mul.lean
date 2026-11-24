-- Prove2me | solution 1 for GlobalTheory.ClassFin.mul_log_eq_neg_log_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:27:44.290285+00:00
-- url     : https://prove2.me/submissions/4fa94e3e-c6c3-4444-9235-c0d5a1553481

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MulLogEqNegLogMul
import Theorems.Thm_GlobalTheory_ClassFin_mul_diagonal_eq_neg_of_exp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.ClassFin
namespace GlobalTheory.ClassFin
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (x x' H H' : Matrix ι ι ℂ), IsLog H (xᴴ * x) → IsLog H' (x'ᴴ * x') → x' * x = 1 → x * H = -(H' * x) := by
  intro ι _ _ x x' H H' ⟨U, d, hU, hH, hA⟩ ⟨V, d', hV, hH', hA'⟩ hx
  have hx' : x * x' = 1 := mul_eq_one_comm.mp hx
  have hU' : Uᴴ * U = 1 := mul_eq_one_comm.mp hU
  have hV' : Vᴴ * V = 1 := mul_eq_one_comm.mp hV
  have key : (x'ᴴ * x') * x * (xᴴ * x) = x := by
    calc (x'ᴴ * x') * x * (xᴴ * x) = x'ᴴ * (x' * x) * xᴴ * x := by simp only [Matrix.mul_assoc]
      _ = (x * x')ᴴ * x := by rw [hx, Matrix.mul_one, conjTranspose_mul]
      _ = x := by rw [hx', conjTranspose_one, Matrix.one_mul]
  rw [hA, hA'] at key
  have hy := mul_diagonal_eq_neg_of_exp (Vᴴ * x * U) d d' (by
    calc _ = (Vᴴ * V) * diagonal (fun i => (Real.exp (d' i) : ℂ)) * (Vᴴ * x * U) *
            diagonal (fun i => (Real.exp (d i) : ℂ)) * (Uᴴ * U) := by
          rw [hV', hU', Matrix.one_mul, Matrix.mul_one]
      _ = Vᴴ * (V * diagonal (fun i => (Real.exp (d' i) : ℂ)) * Vᴴ * x *
            (U * diagonal (fun i => (Real.exp (d i) : ℂ)) * Uᴴ)) * U := by
          simp only [Matrix.mul_assoc]
      _ = Vᴴ * x * U := by rw [key])
  calc x * H = (V * Vᴴ) * x * H := by rw [hV, Matrix.one_mul]
    _ = V * (Vᴴ * x * U * diagonal (fun i => (d i : ℂ))) * Uᴴ := by
        rw [hH]; simp only [Matrix.mul_assoc]
    _ = -(H' * x * (U * Uᴴ)) := by
        rw [hy, hH']; simp only [Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul]
    _ = -(H' * x) := by rw [hU, Matrix.mul_one]
end GlobalTheory.ClassFin
