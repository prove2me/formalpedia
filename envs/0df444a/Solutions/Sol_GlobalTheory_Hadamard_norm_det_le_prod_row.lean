-- Prove2me | solution 1 for GlobalTheory.Hadamard.norm_det_le_prod_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:54:43.975287+00:00
-- url     : https://prove2.me/submissions/d1ae47ef-0ac9-42e3-89df-d8f4a220597f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsOrthonormalOfLinearIndependent
import Theorems.Thm_GlobalTheory_Hadamard_norm_det_le_prod_col

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
    ‖A.det‖ ≤ ∏ i, √(∑ j, ‖A i j‖ ^ 2) := by
  rw [← det_transpose]
  exact norm_det_le_prod_col Aᵀ
end GlobalTheory.Hadamard
