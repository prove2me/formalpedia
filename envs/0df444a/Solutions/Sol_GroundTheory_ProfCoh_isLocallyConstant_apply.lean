-- Prove2me | solution 1 for GroundTheory.ProfCoh.isLocallyConstant_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:17:35.912814+00:00
-- url     : https://prove2.me/submissions/f0ae6df6-b043-4ba2-afe0-c320f6928883

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_DiscreteModules
import Definitions.Def_GroundTheory_ProfiniteCohomology_DiscreteModules_IsDiscreteRepIffForallExistsOpenNormalSubgroup
import Theorems.Thm_GroundTheory_ProfCoh_isDiscreteRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_isOpen_stabilizer
import Theorems.Thm_GroundTheory_ProfCoh_mem_stabilizer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.isDiscreteRep_apply
attribute [local simp] GroundTheory.ProfCoh.mem_stabilizer



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory Limits Topology
universe w u v
variable {k : Type u} {G : Type v} [CommRing k] [Group G]
variable [TopologicalSpace G]
variable [IsTopologicalGroup G]
namespace GroundTheory.ProfCoh
theorem _root_.solution (A : Rep.{w} k G) [IsDiscreteRep A] (a : A) :
    IsLocallyConstant fun g : G => A.ρ g a := by
  rw [IsLocallyConstant.iff_isOpen_fiber]
  intro b
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun h => g⁻¹ * h) ⁻¹' (stabilizer A.ρ a : Set G), ?_,
    (isOpen_stabilizer A a).preimage (continuous_const.mul continuous_id), by simp⟩
  intro h hh
  simp only [Set.mem_preimage, SetLike.mem_coe, mem_stabilizer, Set.mem_singleton_iff] at hh hg ⊢
  rw [← hg, show h = g * (g⁻¹ * h) by group, map_mul, Module.End.mul_apply, hh]
end GroundTheory.ProfCoh
