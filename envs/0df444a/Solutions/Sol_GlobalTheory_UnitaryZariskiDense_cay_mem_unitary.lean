-- Prove2me | solution 1 for GlobalTheory.UnitaryZariskiDense.cay_mem_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:07:25.560894+00:00
-- url     : https://prove2.me/submissions/a21235d5-760d-4977-9821-7a1d5d09b841

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetGNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupFamilyZariskiDense
import Theorems.Thm_GlobalTheory_UnitaryZariskiDense_det_one_add_ne_zero
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open Classical MvPolynomial
open scoped Matrix ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.UnitaryZariskiDense
variable {ι : Type} {a : ℕ}
namespace GlobalTheory.UnitaryZariskiDense
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : Aᴴ = -A) :
    cay A ∈ Matrix.unitaryGroup n ℂ := by
  have h1 : IsUnit (1 + A).det := isUnit_iff_ne_zero.2 (det_one_add_ne_zero A hA)
  have h2 : IsUnit (1 - A).det := by
    have := det_one_add_ne_zero (-A) (by rw [Matrix.conjTranspose_neg, hA])
    rw [← sub_eq_add_neg] at this
    exact isUnit_iff_ne_zero.2 this
  rw [Matrix.mem_unitaryGroup_iff', cay, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one, hA, ← sub_eq_add_neg, sub_neg_eq_add]
  have comm : (1 + A) * (1 - A) = (1 - A) * (1 + A) := by noncomm_ring
  calc (1 - A)⁻¹ * (1 + A) * ((1 - A) * (1 + A)⁻¹)
      = (1 - A)⁻¹ * ((1 + A) * (1 - A)) * (1 + A)⁻¹ := by simp only [Matrix.mul_assoc]
    _ = ((1 - A)⁻¹ * (1 - A)) * ((1 + A) * (1 + A)⁻¹) := by rw [comm]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [Matrix.nonsing_inv_mul _ h2, Matrix.mul_nonsing_inv _ h1, Matrix.one_mul]
end GlobalTheory.UnitaryZariskiDense
