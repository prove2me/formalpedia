-- Prove2me | solution 1 for GlobalTheory.TransposeMulCommute.mul_transpose_eq_of_transpose_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:39:06.820572+00:00
-- url     : https://prove2.me/submissions/7f6d1fd5-8486-47a1-8230-1c3d18659957

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MulTransposeEqOfTransposeMulEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TransposeMulCommute
namespace GlobalTheory.TransposeMulCommute
theorem _root_.solution :
    ∀ {al : Matrix (Fin (4 : ℕ)) (Fin (4 : ℕ)) ℤ} {m : ℕ}, (1 : ℕ) ≤ m →
      Matrix.transpose al * al = (↑m : ℤ) • (1 : Matrix (Fin (4 : ℕ)) (Fin (4 : ℕ)) ℤ) →
      al * Matrix.transpose al = (↑m : ℤ) • (1 : Matrix (Fin (4 : ℕ)) (Fin (4 : ℕ)) ℤ) := by
  intro al m hm h
  have hm0 : (m : ℤ) ≠ 0 := by
    have : m ≠ 0 := by omega
    exact_mod_cast this
  have hdet : al.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det h
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_smul, Matrix.det_one, mul_one] at h1
    exact pow_ne_zero _ hm0 h1.symm
  have h2 : (al * al.transpose) * al = ((m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) * al := by
    rw [Matrix.mul_assoc, h, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  have h3 := congrArg (fun X => X * al.adjugate) h2
  simp only [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at h3
  ext i j
  have h4 := congrFun (congrFun h3 i) j
  rw [Matrix.smul_apply, Matrix.smul_apply al.det, smul_eq_mul, smul_eq_mul al.det] at h4
  exact mul_left_cancel₀ hdet h4
end GlobalTheory.TransposeMulCommute
