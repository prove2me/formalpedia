-- Prove2me | solution 1 for GlobalTheory.Hadamard.norm_det_sq_le_prod_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:49:34.915831+00:00
-- url     : https://prove2.me/submissions/5cf657fd-b734-4a35-99c1-ef94343e6c69

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
    ‖A.det‖ ^ 2 ≤ ∏ j, ∑ i, ‖A i j‖ ^ 2 := by
  refine (pow_le_pow_left₀ (norm_nonneg _) (norm_det_le_prod_col A) 2).trans_eq ?_
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl fun j _ => Real.sq_sqrt (by positivity)
end GlobalTheory.Hadamard
