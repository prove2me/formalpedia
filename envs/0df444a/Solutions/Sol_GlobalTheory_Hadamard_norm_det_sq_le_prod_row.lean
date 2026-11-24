-- Prove2me | solution 1 for GlobalTheory.Hadamard.norm_det_sq_le_prod_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:07:04.527213+00:00
-- url     : https://prove2.me/submissions/3a7589d8-eee9-4dce-bb3c-4e32629515c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsOrthonormalOfLinearIndependent
import Theorems.Thm_GlobalTheory_Hadamard_norm_det_sq_le_prod_col

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module
open scoped InnerProductSpace ComplexOrder
open GlobalTheory GlobalTheory.Hadamard
variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
namespace GlobalTheory.Hadamard
theorem _root_.solution (A : Matrix ι ι 𝕜) :
    ‖A.det‖ ^ 2 ≤ ∏ i, ∑ j, ‖A i j‖ ^ 2 := by
  rw [← det_transpose]
  exact norm_det_sq_le_prod_col Aᵀ
end GlobalTheory.Hadamard
