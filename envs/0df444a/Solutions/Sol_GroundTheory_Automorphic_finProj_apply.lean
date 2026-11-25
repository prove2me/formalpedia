-- Prove2me | solution 1 for GroundTheory.Automorphic.finProj_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:54:23.268339+00:00
-- url     : https://prove2.me/submissions/62a4b13b-5ff9-4be0-85ae-3187ada0caf8

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TraceNormComp
import Definitions.Def_GroundTheory_AutomorphicForms_TraceStrongLimit

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
namespace GroundTheory.Automorphic
theorem _root_.solution (u : ι → H) (x : H) : finProj u x = ∑ i, ⟪u i, x⟫_ℂ • u i := by
  simp [finProj, rankOne_apply]
end GroundTheory.Automorphic
