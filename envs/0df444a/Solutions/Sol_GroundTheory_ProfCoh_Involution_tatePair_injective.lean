-- Prove2me | solution 1 for GroundTheory.ProfCoh.Involution.tatePair_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:56:26.122644+00:00
-- url     : https://prove2.me/submissions/377c798b-a7ee-4154-b8d9-cc8226ab8f5f

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_TorsionDualFinite
import Definitions.Def_GroundTheory_ProfiniteCohomology_RealPlaces_InvolutionDuality
import Theorems.Thm_GroundTheory_ProfCoh_QZ_mk_surjective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open GroundTheory.ProfCoh.Involution
variable {M : Type*} [AddCommGroup M]
variable {σ : M →+ M}
namespace GroundTheory.ProfCoh.Involution
theorem _root_.solution : Function.Injective (tatePair σ) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  by_contra hne
  have hne' : (QuotientAddGroup.mk (x : M) : M ⧸ traceSub σ) ≠ 0 := by
    rwa [Ne, QuotientAddGroup.eq_zero_iff]
  obtain ⟨χ, hχ⟩ := QZ.exists_apply_ne_zero hne'
  set f : M →+ QZ := χ.comp (QuotientAddGroup.mk' (traceSub σ)) with hf_def
  have hf : f ∈ fixedSub (dualInv σ) := by
    rw [mem_fixedSub_dualInv_iff]
    intro y
    rw [hf_def, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply,
      (QuotientAddGroup.eq_zero_iff _).2 (mem_traceSub.2 ⟨y, rfl⟩), map_zero]
  apply hχ
  exact DFunLike.congr_fun hx (((⟨f, hf⟩ : fixedSub (dualInv σ))) : tateQuot (dualInv σ))
end GroundTheory.ProfCoh.Involution
