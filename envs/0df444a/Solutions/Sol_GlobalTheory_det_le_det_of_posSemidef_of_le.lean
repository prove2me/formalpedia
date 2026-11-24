-- Prove2me | solution 1 for GlobalTheory.det_le_det_of_posSemidef_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:36:14.03713+00:00
-- url     : https://prove2.me/submissions/06e899ed-f102-42c7-b342-8dff609c01c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_OneLeDetOneAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Theorems.Thm_GlobalTheory_posSemidef_of_le
import Theorems.Thm_GlobalTheory_one_le_det_one_add_of_posSemidef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder MatrixOrder
open GlobalTheory
variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n]
variable [DecidableEq n]
namespace GlobalTheory
theorem _root_.solution {A B : Matrix n n 𝕜} (hA : A.PosSemidef) (h : A ≤ B) :
    A.det ≤ B.det := by
  by_cases h0 : A.det = 0
  · rw [h0]; exact (posSemidef_of_le hA h).det_nonneg
  have hA' := hA.posDef_iff_det_ne_zero.mpr h0
  obtain ⟨C, hC, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp
    hA'.isStrictlyPositive
  let _ := hC.invertible
  have hD := (le_iff.mp h).conjTranspose_mul_mul_same C⁻¹
  have hB : B = star C * (1 + C⁻¹ᴴ * (B - star C * C) * C⁻¹) * C := by
    have e1 : star C * C⁻¹ᴴ = 1 := by
      rw [star_eq_conjTranspose, ← conjTranspose_mul, inv_mul_of_invertible, conjTranspose_one]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e1,
      Matrix.one_mul, Matrix.mul_assoc, inv_mul_of_invertible, Matrix.mul_one, add_sub_cancel]
  have h1 := one_le_det_one_add_of_posSemidef hD
  rw [hB, det_mul_right_comm, det_mul (star C * C)]
  exact le_mul_of_one_le_right hA.det_nonneg h1
end GlobalTheory
