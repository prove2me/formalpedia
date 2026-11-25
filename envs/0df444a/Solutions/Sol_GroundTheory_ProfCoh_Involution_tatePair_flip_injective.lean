-- Prove2me | solution 1 for GroundTheory.ProfCoh.Involution.tatePair_flip_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:56:23.275859+00:00
-- url     : https://prove2.me/submissions/400b0ab2-1ae9-4cc2-ab23-b022c20f39b1

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_TorsionDualFinite
import Definitions.Def_GroundTheory_ProfiniteCohomology_RealPlaces_InvolutionDuality
import Theorems.Thm_GroundTheory_ProfCoh_QZDual_addCharEquiv_apply
import Theorems.Thm_GroundTheory_ProfCoh_QZDual_eval_apply
import Theorems.Thm_GroundTheory_ProfCoh_QZ_addCharEquiv_apply
import Theorems.Thm_GroundTheory_ProfCoh_QZ_evalHom_apply
import Theorems.Thm_GroundTheory_ProfCoh_QZ_exists_comp_eq_of_ker_le
import Theorems.Thm_GroundTheory_ProfCoh_QZ_mk_surjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.QZ.addCharEquiv_apply
attribute [local simp] GroundTheory.ProfCoh.QZ.evalHom_apply
attribute [local simp] GroundTheory.ProfCoh.QZDual.addCharEquiv_apply
attribute [local simp] GroundTheory.ProfCoh.QZDual.eval_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open GroundTheory.ProfCoh.Involution
variable {M : Type*} [AddCommGroup M]
variable {σ : M →+ M}
namespace GroundTheory.ProfCoh.Involution
theorem _root_.solution : Function.Injective (tatePair σ).flip := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  obtain ⟨f, rfl⟩ := QuotientAddGroup.mk_surjective f
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  have hker : (AddMonoidHom.id M - σ).ker ≤ (f : M →+ QZ).ker := by
    intro x hx
    have hx' : (x : M) ∈ fixedSub σ := by
      rw [mem_fixedSub]
      rw [AddMonoidHom.mem_ker, AddMonoidHom.sub_apply, AddMonoidHom.id_apply, sub_eq_zero] at hx
      exact hx.symm
    exact DFunLike.congr_fun hf (((⟨x, hx'⟩ : fixedSub σ)) : tateQuot σ)
  obtain ⟨ψ, hψ⟩ := QZ.exists_comp_eq_of_ker_le _ _ hker
  refine mem_traceSub.2 ⟨ψ, ?_⟩
  rw [← hψ]
  ext x
  simp [sub_eq_add_neg]
end GroundTheory.ProfCoh.Involution
