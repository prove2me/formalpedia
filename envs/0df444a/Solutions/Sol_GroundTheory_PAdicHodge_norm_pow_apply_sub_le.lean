-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_pow_apply_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:29:33.100195+00:00
-- url     : https://prove2.me/submissions/2ef8f891-5b71-4edc-8f8c-34ee1a7a3738

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Theorems.Thm_GroundTheory_PAdicHodge_norm_algEquiv_apply
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_zero
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.normTrace_zero
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial Module
noncomputable section
variable {p : ℕ} [Fact p.Prime]
namespace GroundTheory.PAdicHodge
theorem _root_.solution (γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (y : PadicAlgCl p)
    (N : ℕ) : ‖(γ ^ N) y - y‖ ≤ ‖γ y - y‖ := by
  induction N with
  | zero => simp
  | succ N ih =>
    have e : (γ ^ (N + 1)) y - y = (γ ^ N) (γ y - y) + ((γ ^ N) y - y) := by
      rw [pow_succ, AlgEquiv.mul_apply, map_sub]; ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ih)
    rw [norm_algEquiv_apply]
end GroundTheory.PAdicHodge
