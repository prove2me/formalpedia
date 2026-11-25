-- Prove2me | solution 1 for GroundTheory.Automorphic.norm_sub_finProj_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:45:10.838215+00:00
-- url     : https://prove2.me/submissions/e00f0fc3-59e1-47b5-b146-9bd97f1f74e5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TraceNormComp
import Definitions.Def_GroundTheory_AutomorphicForms_TraceStrongLimit
import Theorems.Thm_GroundTheory_Automorphic_finProj_mem_span
import Theorems.Thm_GroundTheory_Automorphic_inner_sub_finProj_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped InnerProductSpace ENNReal Topology
open ContinuousLinearMap InnerProductSpace Filter
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {ι : Type*} [Fintype ι]
variable {u : ι → H}
namespace GroundTheory.Automorphic
theorem _root_.solution (hu : Orthonormal ℂ u) (x : H) {g : H}
    (hg : g ∈ Submodule.span ℂ (Set.range u)) : ‖x - finProj u x‖ ≤ ‖x - g‖ := by
  have hmem : finProj u x - g ∈ Submodule.span ℂ (Set.range u) :=
    Submodule.sub_mem _ (finProj_mem_span u x) hg
  have h0 : ⟪x - finProj u x, finProj u x - g⟫_ℂ = 0 := by
    rw [← inner_conj_symm, inner_sub_finProj_eq_zero hu x hmem, map_zero]
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h0
  rw [sub_add_sub_cancel] at h
  rw [mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _), h]
  exact le_add_of_nonneg_right (mul_self_nonneg _)
end GroundTheory.Automorphic
