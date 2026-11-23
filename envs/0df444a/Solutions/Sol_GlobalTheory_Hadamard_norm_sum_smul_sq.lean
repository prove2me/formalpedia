-- Prove2me | solution 1 for GlobalTheory.Hadamard.norm_sum_smul_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:04.7528+00:00
-- url     : https://prove2.me/submissions/ac6f993e-87a6-4329-9c14-c9aa6d5cdc5a

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
theorem _root_.solution {e : ι → E} (he : Orthonormal 𝕜 e) (c : ι → 𝕜) :
    ‖∑ i, c i • e i‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by
  have h := he.inner_sum c c Finset.univ
  rw [inner_self_eq_norm_sq_to_K] at h
  simp only [RCLike.conj_mul] at h
  exact_mod_cast h
end GlobalTheory.Hadamard
