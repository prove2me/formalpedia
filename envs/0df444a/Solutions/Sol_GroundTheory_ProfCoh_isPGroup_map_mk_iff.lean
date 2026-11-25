-- Prove2me | solution 1 for GroundTheory.ProfCoh.isPGroup_map_mk_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:24:43.412188+00:00
-- url     : https://prove2.me/submissions/25a8caa2-367a-4956-9c71-5fef5217c022

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_OpenNormal
import Definitions.Def_GroundTheory_ProfiniteCohomology_OfNatRelIndexSupAntitone
import Definitions.Def_GroundTheory_ProfiniteCohomology_IsProPGroupSubgroupIffIsPGroupMap
import Theorems.Thm_GroundTheory_ProfCoh_Supernatural_exp_ofNat
import Theorems.Thm_GroundTheory_ProfCoh_Supernatural_ofNat_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.Supernatural.exp_ofNat
attribute [local simp] GroundTheory.ProfCoh.Supernatural.ofNat_one



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
variable {G : Type*} [Group G] [TopologicalSpace G]
omit [TopologicalSpace G]
namespace GroundTheory.ProfCoh
theorem _root_.solution {p : ℕ} (H U : Subgroup G) [U.Normal] :
    IsPGroup p (H.map (QuotientGroup.mk' U)) ↔ ∀ h ∈ H, ∃ k : ℕ, h ^ p ^ k ∈ U := by
  constructor
  · intro hp h hh
    obtain ⟨k, hk⟩ := hp ⟨QuotientGroup.mk' U h, Subgroup.mem_map_of_mem _ hh⟩
    refine ⟨k, ?_⟩
    have hk' := congrArg Subtype.val hk
    simp only [Subgroup.coe_pow, OneMemClass.coe_one, QuotientGroup.mk'_apply] at hk'
    rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk'
  · rintro h ⟨x, hx⟩
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨k, hk⟩ := h g hg
    refine ⟨k, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, OneMemClass.coe_one, QuotientGroup.mk'_apply]
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hk
end GroundTheory.ProfCoh
