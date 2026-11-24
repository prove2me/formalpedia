-- Prove2me | solution 1 for GlobalTheory.Hadamard.sum_norm_apply_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:15:54.061138+00:00
-- url     : https://prove2.me/submissions/468bce3a-db38-46ed-815d-27af386b6ff1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsOrthonormalOfLinearIndependent
import Theorems.Thm_GlobalTheory_Hadamard_norm_sum_smul_sq

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
theorem _root_.solution {e : ι → E} (he : Orthonormal 𝕜 e) (φ : E →L[𝕜] 𝕜) :
    ∑ i, ‖φ (e i)‖ ^ 2 ≤ ‖φ‖ ^ 2 := by
  set s := ∑ i, ‖φ (e i)‖ ^ 2 with hs
  set v := ∑ i, (starRingEnd 𝕜) (φ (e i)) • e i with hv
  have hs0 : 0 ≤ s := by positivity
  have h1 : ‖v‖ ^ 2 = s := by simp [hv, norm_sum_smul_sq he, hs]
  have h2 : φ v = (s : 𝕜) := by
    simp [hv, hs, RCLike.conj_mul]
  have h3 : s ≤ ‖φ‖ * ‖v‖ := by
    have := φ.le_opNorm v
    rwa [h2, RCLike.norm_ofReal, abs_of_nonneg hs0] at this
  nlinarith [sq_nonneg (‖φ‖ - ‖v‖)]
end GlobalTheory.Hadamard
