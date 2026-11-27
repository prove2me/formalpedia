-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.singleL_mem_intertwiners
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:45:16.057774+00:00
-- url     : https://prove2.me/submissions/658dec1c-aaf3-4791-bd16-2a0d4b517054

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_DirectSum
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_directSum_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_singleL_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
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
open scoped InnerProductSpace ENNReal
open ContinuousLinearMap
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℂ (E i)] [∀ i, CompleteSpace (E i)]
variable (ρ : ∀ i, UnitaryRep G (E i))
namespace GroundTheory.Automorphic.UnitaryRep
theorem _root_.solution [DecidableEq ι] (i : ι) :
    singleL i ∈ (ρ i).intertwiners (directSum ρ) := by
  intro g a
  refine lp.ext (funext fun j => ?_)
  rw [singleL_apply, directSum_apply, singleL_apply]
  by_cases h : j = i
  · subst h
    simp
  · rw [lp.single_apply_ne 2 i _ h, lp.single_apply_ne 2 i _ h, map_zero]
end GroundTheory.Automorphic.UnitaryRep
