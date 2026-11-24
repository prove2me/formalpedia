-- Prove2me | solution 1 for GlobalTheory.matrix_exp_mul_eq_mul_exp_of_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:26:57.967682+00:00
-- url     : https://prove2.me/submissions/71e4caf5-d7e7-472d-9a47-cb28801bfc31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixExpSmulMulEqMulExpSmulOfIntertwine
import Theorems.Thm_GlobalTheory_matrix_pow_mul_eq_mul_pow_of_intertwine
import Theorems.Thm_GlobalTheory_matrix_hasSum_exp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {m r : ℕ} (X : Matrix (Fin m) (Fin m) ℂ)
    (ε : Matrix (Fin m) (Fin r) ℂ) (β : Matrix (Fin r) (Fin r) ℂ) (h : X * ε = ε * β) :
    NormedSpace.exp X * ε = ε * NormedSpace.exp β := by
  let g : Matrix (Fin m) (Fin m) ℂ →+ Matrix (Fin m) (Fin r) ℂ :=
    AddMonoidHom.mk' (fun A => A * ε) (fun A B => Matrix.add_mul A B ε)
  have hg : Continuous g := Continuous.matrix_mul continuous_id continuous_const
  let g' : Matrix (Fin r) (Fin r) ℂ →+ Matrix (Fin m) (Fin r) ℂ :=
    AddMonoidHom.mk' (fun A => ε * A) (fun A B => Matrix.mul_add ε A B)
  have hg' : Continuous g' := Continuous.matrix_mul continuous_const continuous_id
  have hL := (matrix_hasSum_exp X).map g hg
  have hR := (matrix_hasSum_exp β).map g' hg'
  have key : (g ∘ fun n : ℕ => ((n.factorial : ℂ)⁻¹) • X ^ n) =
      (g' ∘ fun n : ℕ => ((n.factorial : ℂ)⁻¹) • β ^ n) := by
    funext n
    simp only [Function.comp, g, g', AddMonoidHom.mk'_apply, Matrix.smul_mul, Matrix.mul_smul,
      matrix_pow_mul_eq_mul_pow_of_intertwine X ε β h n]
  rw [key] at hL
  exact hL.unique hR
end GlobalTheory
