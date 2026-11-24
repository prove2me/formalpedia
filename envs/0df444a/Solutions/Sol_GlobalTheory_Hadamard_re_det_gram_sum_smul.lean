-- Prove2me | solution 1 for GlobalTheory.Hadamard.re_det_gram_sum_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:32:21.532835+00:00
-- url     : https://prove2.me/submissions/2dbc77fb-10ab-4d87-95b0-bec95177d44b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsOrthonormalOfLinearIndependent
import Theorems.Thm_GlobalTheory_Hadamard_gram_sum_smul

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
theorem _root_.solution (e : ι → E) (m : Matrix ι ι 𝕜) :
    RCLike.re (gram 𝕜 (fun j => ∑ i, m i j • e i)).det
      = ‖m.det‖ ^ 2 * RCLike.re (gram 𝕜 e).det := by
  rw [gram_sum_smul, det_mul, det_mul, det_conjTranspose, mul_right_comm, RCLike.star_def,
    RCLike.conj_mul]
  norm_cast
  rw [RCLike.re_ofReal_mul]
end GlobalTheory.Hadamard
