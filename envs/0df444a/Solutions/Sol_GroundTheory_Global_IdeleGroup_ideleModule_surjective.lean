-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.ideleModule_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:07:21.787615+00:00
-- url     : https://prove2.me/submissions/a0aa9e1b-daae-4fdd-8f9e-5e7d892120cb

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Theorems.Thm_GroundTheory_Global_IdeleGroup_ideleModule_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding



set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Topology Filter
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
variable {K}
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution : Function.Surjective (ideleModule K) := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
  rintro ⟨t, ht⟩
  obtain ⟨z, hz0, hz⟩ : ∃ z : w.Completion, z ≠ 0 ∧ ‖z‖ ^ w.mult = t := by
    rcases w.isReal_or_isComplex with hw | hw
    · let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
      refine ⟨e.symm t, (map_ne_zero_iff _ e.symm.injective).2 ht.ne', ?_⟩
      have hn : ‖e.symm t‖ = ‖e (e.symm t)‖ := by
        rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
        exact ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
          (map_zero _) _).symm
      rw [hn, RingEquiv.apply_symm_apply, Real.norm_of_nonneg ht.le]
      simp [InfinitePlace.mult, hw]
    · let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
      refine ⟨e.symm (Real.sqrt t : ℂ), (map_ne_zero_iff _ e.symm.injective).2
        (Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 ht)), ?_⟩
      have hn : ‖e.symm (Real.sqrt t : ℂ)‖ = ‖e (e.symm (Real.sqrt t : ℂ))‖ := by
        rw [InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply]
        exact ((InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
          (map_zero _) _).symm
      have hw' : ¬ w.IsReal := InfinitePlace.not_isReal_iff_isComplex.2 hw
      rw [hn, RingEquiv.apply_symm_apply, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg t)]
      simp [InfinitePlace.mult, hw', Real.sq_sqrt ht.le]
  refine ⟨infiniteEmbedding w (Units.mk0 z hz0), Subtype.ext ?_⟩
  rw [ideleModule_infiniteEmbedding, Units.val_mk0, hz]
end GroundTheory.Global.IdeleGroup
