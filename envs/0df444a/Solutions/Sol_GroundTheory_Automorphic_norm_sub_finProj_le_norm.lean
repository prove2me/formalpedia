-- Prove2me | solution 1 for GroundTheory.Automorphic.norm_sub_finProj_le_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:53:52.368689+00:00
-- url     : https://prove2.me/submissions/d41a4ec7-65ec-4346-9ad6-22e624c1e29a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TraceNormComp
import Definitions.Def_GroundTheory_AutomorphicForms_TraceStrongLimit
import Theorems.Thm_GroundTheory_Automorphic_norm_sub_finProj_le

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
theorem _root_.solution (hu : Orthonormal ℂ u) (x : H) : ‖x - finProj u x‖ ≤ ‖x‖ := by
  simpa using norm_sub_finProj_le hu x (Submodule.zero_mem _)
end GroundTheory.Automorphic
