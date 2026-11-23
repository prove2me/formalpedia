-- Prove2me | solution 1 for GlobalTheory.inv_le_inv_of_posDef_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:27.646268+00:00
-- url     : https://prove2.me/submissions/2c0ccc6c-7bff-40d1-b285-42f2c254f82d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_OneLeDetOneAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Theorems.Thm_GlobalTheory_posDef_of_le

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
theorem _root_.solution {A B : Matrix n n 𝕜} (hA : A.PosDef) (h : A ≤ B) :
    B⁻¹ ≤ A⁻¹ := by
  have hB := posDef_of_le hA h
  have hAi := hA.inv
  let _ := hB.isUnit.invertible
  let _ := hA.isUnit.invertible
  let _ := hAi.isUnit.invertible
  have h1 := PosDef.fromBlocks₁₁ (1 : Matrix n n 𝕜) B hAi
  have h2 := PosDef.fromBlocks₂₂ A⁻¹ (1 : Matrix n n 𝕜) hB
  simp only [conjTranspose_one, Matrix.mul_one, Matrix.one_mul, inv_inv_of_invertible] at h1 h2
  exact h2.mp (h1.mpr h)
end GlobalTheory
