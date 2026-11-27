-- Prove2me | solution 1 for GlobalTheory.le_re_trace_mul_smul_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:41:56.818817+00:00
-- url     : https://prove2.me/submissions/d99102f1-e4c3-4bd3-81d4-e8a2e4c55c29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_OneLeDetOneAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Theorems.Thm_GlobalTheory_conjTranspose_mul_mul_le_of_le
import Theorems.Thm_GlobalTheory_le_re_trace_smul_one_of_posSemidef

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
theorem _root_.solution {l b : Matrix n n 𝕜} (hl : l.PosDef) (hb : b.PosSemidef) :
    b ≤ RCLike.re (l * b).trace • l⁻¹ := by
  obtain ⟨C, hC, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp
    hl.isStrictlyPositive
  let _ := hC.invertible
  have h1 := le_re_trace_smul_one_of_posSemidef (hb.mul_mul_conjTranspose_same C)
  have h2 := conjTranspose_mul_mul_le_of_le h1 C⁻¹ᴴ
  have e1 : Cᴴ * C⁻¹ᴴ = 1 := by
    rw [← conjTranspose_mul, inv_mul_of_invertible, conjTranspose_one]
  rw [conjTranspose_conjTranspose, ← Matrix.mul_assoc, ← Matrix.mul_assoc, inv_mul_of_invertible,
    Matrix.one_mul, Matrix.mul_assoc, e1, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, trace_mul_cycle] at h2
  rwa [star_eq_conjTranspose, Matrix.mul_inv_rev, ← conjTranspose_nonsing_inv]
end GlobalTheory
