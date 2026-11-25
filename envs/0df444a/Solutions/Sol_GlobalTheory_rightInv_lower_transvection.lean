-- Prove2me | solution 1 for GlobalTheory.rightInv_lower_transvection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:49:47.168877+00:00
-- url     : https://prove2.me/submissions/3aee36b7-1e64-4f17-bbd4-b517b84e4af4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RightInvariantGLOfUpperTriangularRightInvariant
import Theorems.Thm_GlobalTheory_poly_eval_eq_eval_zero_of_eq_inv
import Theorems.Thm_GlobalTheory_upperFactor_isUpper
import Theorems.Thm_GlobalTheory_upperFactor_det
import Theorems.Thm_GlobalTheory_transvection_mul_upperFactor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory
variable {k : Type} [Field k] [Infinite k] {m : ℕ}
namespace GlobalTheory
theorem _root_.solution (ψ Φ : Matrix (Fin m) (Fin m) k → k) (r : k → k)
    (hΦ : ∀ A₀ D : Matrix (Fin m) (Fin m) k, ∃ p : Polynomial k, ∀ x : k, Φ (A₀ + x • D) = p.eval x)
    (hψ : ∀ A : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → ψ A = r A.det * Φ A)
    (hT : ∀ A T : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → T.det ≠ 0 → T.BlockTriangular id →
      ψ (A * T) = ψ A)
    (A : Matrix (Fin m) (Fin m) k) (hA : A.det ≠ 0) {i j : Fin m} (hji : j < i) (x : k) :
    ψ (A * transvection i j x) = ψ A := by
  have hij : i ≠ j := ne_of_gt hji
  have hl : ∀ y : k, (transvection i j y).det = 1 := fun y => det_transvection_of_ne i j hij y
  have hAl : ∀ y : k, (A * transvection i j y).det = A.det := fun y => by
    rw [det_mul, hl, mul_one]
  obtain ⟨p, hp⟩ := hΦ A (A * single i j 1)
  obtain ⟨q, hq⟩ := hΦ (A * (1 - single j j 1 - single i i 1 + single j i 1 + single i j 1))
    (A * single j j 1)
  have e1 : ∀ y : k, ψ (A * transvection i j y) = r A.det * p.eval y := by
    intro y
    rw [hψ _ (by rw [hAl]; exact hA), hAl, ← hp]
    congr 2
    rw [transvection, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_smul, smul_single, smul_eq_mul,
      mul_one]
  have e2 : ∀ y : k, y ≠ 0 → r A.det * p.eval y = r (-A.det) * q.eval y⁻¹ := by
    intro y hy
    have hdT : (upperFactor i j y).det ≠ 0 := by rw [upperFactor_det hji hy]; norm_num
    rw [← e1, ← hT _ _ (by rw [hAl]; exact hA) hdT (upperFactor_isUpper hji y), Matrix.mul_assoc,
      transvection_mul_upperFactor hji hy]
    have hdM : (A * swapLine i j y⁻¹).det = -A.det := by
      rw [← transvection_mul_upperFactor hji hy, ← Matrix.mul_assoc, det_mul, hAl,
        upperFactor_det hji hy, mul_neg_one]
    rw [hψ _ (by rw [hdM]; exact neg_ne_zero.mpr hA), hdM, ← hq, swapLine, Matrix.mul_add,
      Matrix.mul_smul]
  by_cases hr : r A.det = 0
  · rw [e1, hr, zero_mul, hψ A hA, hr, zero_mul]
  have hconst := poly_eval_eq_eval_zero_of_eq_inv p q (r (-A.det) / r A.det) (fun y hy => by
    rw [div_mul_eq_mul_div, eq_div_iff hr, mul_comm, e2 y hy])
  rw [e1, hconst x, hψ A hA, ← hp, zero_smul, add_zero]
end GlobalTheory
