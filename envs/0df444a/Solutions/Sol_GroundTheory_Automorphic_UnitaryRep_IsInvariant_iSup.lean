-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.IsInvariant.iSup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:28:29.113741+00:00
-- url     : https://prove2.me/submissions/04cac228-16e5-4004-8681-9d4518e3a63c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_ExistsEqAlgebraMapOfIsSelfAdjoint
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_DirectSum
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_Integrated
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_directSum_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.directSum_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.UnitaryRep
open scoped InnerProductSpace
open ContinuousLinearMap Submodule
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable {π : UnitaryRep G H}
namespace GroundTheory.Automorphic.UnitaryRep
namespace IsInvariant
theorem _root_.solution {ι : Sort*} {V : ι → Submodule ℂ H} (h : ∀ i, π.IsInvariant (V i)) :
    π.IsInvariant (⨆ i, V i) := by
  intro g v hv
  exact Submodule.iSup_induction V (motive := fun x => π g x ∈ ⨆ i, V i) hv
    (fun i x hx => Submodule.mem_iSup_of_mem i (h i g x hx)) (by simp)
    (fun x y hx hy => by simpa using add_mem hx hy)
end IsInvariant
end GroundTheory.Automorphic.UnitaryRep
