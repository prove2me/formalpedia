-- Prove2me | solution 1 for GlobalTheory.Hadamard.norm_det_le_prod_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:33:48.305337+00:00
-- url     : https://prove2.me/submissions/2ca2e17e-aec2-42ae-95a4-61f2b32e5aa9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsOrthonormalOfLinearIndependent
import Theorems.Thm_GlobalTheory_Hadamard_norm_orthonormalBasis_det_le

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
    ‖A.det‖ ≤ ∏ j, √(∑ i, ‖A i j‖ ^ 2) := by
  have h := norm_orthonormalBasis_det_le (EuclideanSpace.basisFun ι 𝕜)
    (fun j => (WithLp.toLp 2 fun i => A i j : EuclideanSpace 𝕜 ι))
  simp only [EuclideanSpace.norm_eq] at h
  convert h using 2
  rw [Basis.det_apply]
  congr 1
end GlobalTheory.Hadamard
