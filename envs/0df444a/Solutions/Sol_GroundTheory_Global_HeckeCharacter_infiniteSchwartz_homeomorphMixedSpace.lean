-- Prove2me | solution 1 for GroundTheory.Global.HeckeCharacter.infiniteSchwartz_homeomorphMixedSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:37:12.519054+00:00
-- url     : https://prove2.me/submissions/e11903c9-03e9-4466-b63a-34b91632a434

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_EulerFactorsArch
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceFourier
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeCharRayClass
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_EulerFactorsInfinite
import Theorems.Thm_GroundTheory_Global_HeckeCharacter_infiniteSchwartz_apply
import Theorems.Thm_GroundTheory_Global_HeckeCharacter_toIdele_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_ideleModule_mk
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteComponent
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_standardOpenSubgroupEquiv_symm_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_unitsToUnits
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteComponent_finiteUnitsSingle
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_IdeleGroup_standardOpenSubgroupEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_standardOpenSubgroupEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_IdeleGroup_toFinite_ofFinite
import Theorems.Thm_GroundTheory_Global_IdeleGroup_toInfinite_ofFinite
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_coe_circleToUnits
import Theorems.Thm_GroundTheory_Global_gaussianSchwartz_apply
import Theorems.Thm_GroundTheory_Global_homeomorphMixedSpace_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
import Theorems.Thm_P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.HeckeCharacter.toIdele_diagonal
attribute [local simp] GroundTheory.Global.IdeleClassGroup.ideleModule_mk
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteComponent
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_standardOpenSubgroupEquiv_symm_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_unitsToUnits
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteComponent_finiteUnitsSingle
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.IdeleGroup.standardOpenSubgroupEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.standardOpenSubgroupEquiv_apply_snd
attribute [local simp] GroundTheory.Global.IdeleGroup.toFinite_ofFinite
attribute [local simp] GroundTheory.Global.IdeleGroup.toInfinite_ofFinite
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.coe_circleToUnits
attribute [local simp] GroundTheory.Global.gaussianSchwartz_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk
attribute [local simp] P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf



set_option autoImplicit false
open NumberField InfinitePlace InfinitePlace.Completion MeasureTheory Complex ComplexConjugate
  NumberField.mixedEmbedding Function
open scoped Real SchwartzMap Classical RealInnerProductSpace
open GroundTheory GroundTheory.Global
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Global.HeckeCharacter
variable (χ : HeckeCharacter K)
namespace GroundTheory.Global.HeckeCharacter
theorem _root_.solution (x : InfiniteAdeleRing K) :
    χ.infiniteSchwartz (homeomorphMixedSpace K x) = ∏ w, χ.infiniteTest w (x w) := by
  rw [infiniteSchwartz_apply, prod_eq_prod_mul_prod, homeomorphMixedSpace_apply,
    InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  simp only [infinitePoly, infiniteTest, Finset.prod_mul_distrib]
  have hr : ∀ w : {w // IsReal w}, (if 0 < χ.infiniteWeight w.1 then
      conj (extensionEmbedding w.1 (x w.1)) else extensionEmbedding w.1 (x w.1)) =
        ((extensionEmbeddingOfIsReal w.2 (x w.1) : ℝ) : ℂ) := fun w ↦ by
    rw [extensionEmbeddingOfIsReal_apply]
    split_ifs
    · rw [← extensionEmbeddingOfIsReal_apply w.2, conj_ofReal]
    · rfl
  have hnr : ∀ w : {w // IsReal w}, (extensionEmbeddingOfIsReal w.2 (x w.1)) ^ 2 = ‖x w.1‖ ^ 2 :=
    fun w ↦ by
      rw [← (isometry_extensionEmbeddingOfIsReal w.2).norm_map_of_map_zero (map_zero _),
        Real.norm_eq_abs, sq_abs]
  have hnc : ∀ w : {w // IsComplex w}, ‖extensionEmbedding w.1 (x w.1)‖ = ‖x w.1‖ := fun w ↦
    (isometry_extensionEmbedding w.1).norm_map_of_map_zero (map_zero _) _
  simp only [hr, hnr, hnc, mult_isReal, mult_isComplex]
  have hexp : ((Real.exp (-π * (∑ w : {w // IsReal w}, ‖x w.1‖ ^ 2 +
      2 * ∑ w : {w // IsComplex w}, ‖x w.1‖ ^ 2)) : ℝ) : ℂ) =
      (∏ w : {w // IsReal w}, ((Real.exp (-(π * ((1 : ℕ) : ℝ) * ‖x w.1‖ ^ 2)) : ℝ) : ℂ)) *
        ∏ w : {w // IsComplex w}, ((Real.exp (-(π * ((2 : ℕ) : ℝ) * ‖x w.1‖ ^ 2)) : ℝ) : ℂ) := by
    rw [← ofReal_prod, ← ofReal_prod, ← ofReal_mul, ← Real.exp_sum, ← Real.exp_sum, ← Real.exp_add]
    congr 2
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun w _ ↦ by push_cast; ring
  rw [hexp]
  ring
end GroundTheory.Global.HeckeCharacter
