-- Prove2me | solution 1 for GroundTheory.LocalField.dense_zpowers_maximalUnramifiedExtensionFrobenius
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:01:29.659952+00:00
-- url     : https://prove2.me/submissions/118bd2e5-6e8b-4563-b0e2-b03497c7fc11

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_LocalFields_UnramifiedGalois
import Definitions.Def_GroundTheory_LocalFields_UnramifiedExistence
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Frobenius
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramified
import Theorems.Thm_GroundTheory_LocalField_maximalUnramifiedExtensionGaloisEquiv_apply
import Theorems.Thm_GroundTheory_LocalField_dense_zpowers_ofAdd_one
import Theorems.Thm_GroundTheory_LocalField_Abstract_cosetConj_mk
import Theorems.Thm_GroundTheory_LocalField_galoisEquivResidue_apply
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.Abstract.cosetConj_mk
attribute [local simp] GroundTheory.LocalField.galoisEquivResidue_apply
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


attribute [local simp] GroundTheory.LocalField.maximalUnramifiedExtensionGaloisEquiv_apply

set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel IntermediateField GroundTheory.LocalField.Abstract GroundTheory.LocalField.Abstract.ProfiniteInteger
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω]
variable [HasUnramifiedRoots K Ω]
variable [IsGalois K Ω]
namespace GroundTheory.LocalField
theorem _root_.solution :
    Dense (Subgroup.zpowers (maximalUnramifiedExtensionFrobenius K Ω) :
      Set (maximalUnramifiedExtension K Ω ≃ₐ[K] maximalUnramifiedExtension K Ω)) := by
  have h : (Subgroup.zpowers (maximalUnramifiedExtensionFrobenius K Ω) :
      Set (maximalUnramifiedExtension K Ω ≃ₐ[K] maximalUnramifiedExtension K Ω)) =
      (maximalUnramifiedExtensionGaloisEquiv K Ω).symm ''
        (Subgroup.zpowers (Multiplicative.ofAdd (1 : ℤ̂)) : Set (Multiplicative ℤ̂)) := by
    ext ρ
    simp only [SetLike.mem_coe, Subgroup.mem_zpowers_iff, Set.mem_image]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨_, ⟨k, rfl⟩, by rw [map_zpow]; rfl⟩
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, by rw [map_zpow]; rfl⟩
  rw [h]
  exact (maximalUnramifiedExtensionGaloisEquiv K Ω).symm.surjective.denseRange.dense_image
    (maximalUnramifiedExtensionGaloisEquiv K Ω).symm.continuous dense_zpowers_ofAdd_one
end GroundTheory.LocalField
