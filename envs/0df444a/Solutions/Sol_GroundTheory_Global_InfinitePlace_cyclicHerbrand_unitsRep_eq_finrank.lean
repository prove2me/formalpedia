-- Prove2me | solution 1 for GroundTheory.Global.InfinitePlace.cyclicHerbrand_unitsRep_eq_finrank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:24:00.776909+00:00
-- url     : https://prove2.me/submissions/d3a5c44e-81df-443e-aaf6-ca94d4a4ef47

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_CoeGalRootsOfUnityHomApply
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Infinite
import Definitions.Def_GroundTheory_GlobalFields_InfiniteNormIndex_LocalSymbol
import Theorems.Thm_GroundTheory_Global_natCard_kerModRange_eq_one
import Theorems.Thm_GroundTheory_Global_InfinitePlace_cyclicHerbrand_unitsRep_eq_two
import Theorems.Thm_GroundTheory_Global_cycSub_apply
import Theorems.Thm_GroundTheory_Global_normHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.cycSub_apply
attribute [local simp] GroundTheory.Global.normHom_apply



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion GroundTheory.ProfCoh
  GroundTheory.GroupCoh
open scoped NumberField.LiesOver ComplexConjugate
open GroundTheory.Global.InfinitePlace
variable {K L : Type*} [Field K] [Field L] [Algebra K L] {v : InfinitePlace K}
  (w : InfinitePlace L) [w.LiesOver v]
variable (v)
variable {v w}
variable (v w)
namespace GroundTheory.Global.InfinitePlace
theorem _root_.solution (σ : Gal(w.Completion/v.Completion))
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    cyclicHerbrand (unitsRep v w) σ = Module.finrank v.Completion w.Completion := by
  by_cases h2 : v.IsReal ∧ w.IsComplex
  · obtain ⟨hv, hw⟩ := h2
    have hσc : σ = completionConj hv := by
      rcases eq_one_or_eq_completionConj hv hw σ with h | h
      · exfalso
        have := hσ (completionConj hv)
        rw [h, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at this
        exact completionConj_ne_one hv hw this
      · exact h
    rw [hσc, cyclicHerbrand_unitsRep_eq_two v w hv hw, (finrank_completion_eq_two_iff w).2 ⟨hv, hw⟩]
    norm_num
  · rw [(finrank_completion_eq_one_iff w).2 h2]
    have := subsingleton_gal w h2
    have hsub : ∀ x, cycSub (unitsRep v w) σ x = 0 := fun x => by
      rw [Subsingleton.elim σ 1, cycSub_apply, map_one, Module.End.one_apply, sub_self]
    have hnorm : ∀ x, normHom (unitsRep v w) x = x := fun x => by
      rw [normHom_apply, Fintype.sum_subsingleton _ 1, map_one, Module.End.one_apply]
    rw [cyclicHerbrand, herbrandQuotient, natCard_kerModRange_eq_one (fun x _ => ⟨x, hnorm x⟩),
      natCard_kerModRange_eq_one (fun x hx => ⟨0, by
        rw [map_zero]; rw [AddMonoidHom.mem_ker, hnorm] at hx; exact hx.symm⟩)]
    norm_num
end GroundTheory.Global.InfinitePlace
