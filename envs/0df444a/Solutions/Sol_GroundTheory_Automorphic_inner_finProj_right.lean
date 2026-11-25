-- Prove2me | solution 1 for GroundTheory.Automorphic.inner_finProj_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:23:48.798145+00:00
-- url     : https://prove2.me/submissions/d7d4fd5f-87ee-48f6-808b-1ff546b418dc

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
theorem _root_.solution (hu : Orthonormal ℂ u) (x : H) (j : ι) :
    ⟪u j, finProj u x⟫_ℂ = ⟪u j, x⟫_ℂ := by
  rw [finProj_apply]
  exact hu.inner_right_fintype _ j
end GroundTheory.Automorphic
