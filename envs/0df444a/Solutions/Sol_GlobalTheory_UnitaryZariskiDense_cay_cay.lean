-- Prove2me | solution 1 for GlobalTheory.UnitaryZariskiDense.cay_cay
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:07:24.883842+00:00
-- url     : https://prove2.me/submissions/93fb2631-4446-4540-bb0f-f68881e3395d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetGNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupFamilyZariskiDense

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical MvPolynomial
open scoped Matrix ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.UnitaryZariskiDense
variable {ι : Type} {a : ℕ}
namespace GlobalTheory.UnitaryZariskiDense
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] (B : Matrix n n ℂ) (hB : (1 + B).det ≠ 0) :
    (1 + cay B).det ≠ 0 ∧ cay (cay B) = B := by
  have hu : IsUnit (1 + B).det := isUnit_iff_ne_zero.2 hB
  have e1 : 1 + cay B = (2 : ℂ) • (1 + B)⁻¹ := by
    have h3 : (1 + B + (1 - B)) = (2 : ℂ) • (1 : Matrix n n ℂ) := by rw [two_smul]; abel
    calc 1 + cay B = (1 + B) * (1 + B)⁻¹ + (1 - B) * (1 + B)⁻¹ := by
          rw [Matrix.mul_nonsing_inv _ hu, cay]
      _ = (2 : ℂ) • (1 + B)⁻¹ := by rw [← Matrix.add_mul, h3, Matrix.smul_mul, Matrix.one_mul]
  have e2 : 1 - cay B = (2 : ℂ) • (B * (1 + B)⁻¹) := by
    have h3 : (1 + B - (1 - B)) = (2 : ℂ) • B := by rw [two_smul]; abel
    calc 1 - cay B = (1 + B) * (1 + B)⁻¹ - (1 - B) * (1 + B)⁻¹ := by
          rw [Matrix.mul_nonsing_inv _ hu, cay]
      _ = (2 : ℂ) • (B * (1 + B)⁻¹) := by rw [← Matrix.sub_mul, h3, Matrix.smul_mul]
  have hinv : ((2 : ℂ) • (1 + B)⁻¹)⁻¹ = (2 : ℂ)⁻¹ • (1 + B) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.nonsing_inv_mul _ hu]
    norm_num
  refine ⟨?_, ?_⟩
  · rw [e1, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ two_ne_zero) (isUnit_iff_ne_zero.1 (Matrix.isUnit_nonsing_inv_det _ hu))
  · rw [cay, e1, e2, hinv, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
    norm_num
end GlobalTheory.UnitaryZariskiDense
