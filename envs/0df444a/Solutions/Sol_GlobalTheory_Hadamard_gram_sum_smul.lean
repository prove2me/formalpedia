-- Prove2me | solution 1 for GlobalTheory.Hadamard.gram_sum_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:12:53.435668+00:00
-- url     : https://prove2.me/submissions/dabfa2af-5d1f-4077-a763-a01f102fc001

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsOrthonormalOfLinearIndependent

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
omit [DecidableEq ι] [Fintype κ] [DecidableEq κ]
namespace GlobalTheory.Hadamard
theorem _root_.solution [Fintype κ] (e : ι → E) (m : Matrix ι κ 𝕜) :
    gram 𝕜 (fun j => ∑ i, m i j • e i) = mᴴ * gram 𝕜 e * m := by
  ext j k
  simp only [gram_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right, mul_apply,
    conjTranspose_apply, Finset.sum_mul, Finset.mul_sum, RCLike.star_def]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
end GlobalTheory.Hadamard
