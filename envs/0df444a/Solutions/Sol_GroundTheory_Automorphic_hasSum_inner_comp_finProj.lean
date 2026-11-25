-- Prove2me | solution 1 for GroundTheory.Automorphic.hasSum_inner_comp_finProj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:23:45.886603+00:00
-- url     : https://prove2.me/submissions/28717781-7b0a-4667-a049-9d84da076557

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TraceNormComp
import Definitions.Def_GroundTheory_AutomorphicForms_TraceStrongLimit
import Theorems.Thm_GroundTheory_Automorphic_finProj_apply

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
theorem _root_.solution (u : ι → H) (S : H →L[ℂ] H) {κ : Type*}
    (b : HilbertBasis κ ℂ H) :
    HasSum (fun β => ⟪b β, S (finProj u (b β))⟫_ℂ) (∑ i, ⟪u i, S (u i)⟫_ℂ) := by
  have h : (fun β => ⟪b β, S (finProj u (b β))⟫_ℂ) =
      fun β => ∑ i, ⟪u i, b β⟫_ℂ * ⟪b β, S (u i)⟫_ℂ := by
    ext β
    rw [finProj_apply, map_sum, inner_sum]
    simp only [map_smul, inner_smul_right]
  rw [h]
  exact hasSum_sum fun i _ => b.hasSum_inner_mul_inner (u i) (S (u i))
end GroundTheory.Automorphic
