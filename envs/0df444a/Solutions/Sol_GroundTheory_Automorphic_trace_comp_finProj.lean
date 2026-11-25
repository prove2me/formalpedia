-- Prove2me | solution 1 for GroundTheory.Automorphic.trace_comp_finProj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:37:56.854598+00:00
-- url     : https://prove2.me/submissions/b8f570f1-1b68-464d-b209-51e89efbb8a2

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TraceNormComp
import Definitions.Def_GroundTheory_AutomorphicForms_TraceStrongLimit
import Theorems.Thm_GroundTheory_Automorphic_hasSum_inner_comp_finProj

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
theorem _root_.solution [CompleteSpace H] (u : ι → H) (S : H →L[ℂ] H) :
    trace (S.comp (finProj u)) = ∑ i, ⟪u i, S (u i)⟫_ℂ :=
  (hasSum_inner_comp_finProj u S (stdHilbertBasis ℂ H)).tsum_eq
end GroundTheory.Automorphic
