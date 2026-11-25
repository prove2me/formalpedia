-- Prove2me | solution 1 for GroundTheory.LocalField.map_unramifiedDegree_fixingSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:01:44.717181+00:00
-- url     : https://prove2.me/submissions/33e110a3-9944-49b7-a20b-30152422ad74

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
import Theorems.Thm_GroundTheory_LocalField_unramifiedDegree_fixingSubgroup
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
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosed Ω]
  (L : IntermediateField K Ω) [FiniteDimensional K L]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
variable [IsGalois K Ω]
namespace GroundTheory.LocalField
theorem _root_.solution :
    L.fixingSubgroup.map (unramifiedDegree K Ω) =
      (powMonoidHom (residueDegree K L) : Multiplicative ℤ̂ →* Multiplicative ℤ̂).range := by
  have := IsGalois.tower_top_of_isGalois K L Ω
  ext x
  simp only [Subgroup.mem_map, MonoidHom.mem_range, powMonoidHom_apply]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨_, (unramifiedDegree_fixingSubgroup L ⟨σ, hσ⟩).symm⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨τ, rfl⟩ := unramifiedDegree_surjective (K := L) (Ω := Ω) y
    obtain ⟨σ, rfl⟩ := (fixingSubgroupEquiv L).surjective τ
    exact ⟨σ, σ.2, (unramifiedDegree_fixingSubgroup L σ)⟩
end GroundTheory.LocalField
