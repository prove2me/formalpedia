-- Prove2me | solution 1 for GroundTheory.LocalField.normal_extendScalars
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:49:36.296943+00:00
-- url     : https://prove2.me/submissions/32c9bdb5-37fe-4c58-bf7a-480c1405b864

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_LocalFields_LocalAxiomTransport
import Definitions.Def_GroundTheory_LocalFields_LocalAxiomDictionary
import Theorems.Thm_GroundTheory_LocalField_StableFiltration_coe_smul_F
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_ord_zero
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
attribute [local simp] GroundTheory.LocalField.StableFiltration.coe_smul_F
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open Abstract IntermediateField
variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
variable (K' L' : Subgroup (Ω ≃ₐ[K] Ω)) {E F : IntermediateField K Ω} (hEF : E ≤ F)
  (hK : E.fixingSubgroup = K') (hL : F.fixingSubgroup = L')
include hK hL
namespace GroundTheory.LocalField
theorem _root_.solution [(L'.subgroupOf K').Normal] :
    Normal E (extendScalars hEF) := by
  subst hK hL
  refine IntermediateField.normal_iff_forall_map_le'.2 fun σ' => ?_
  rintro _ ⟨x, hx, rfl⟩
  replace hx : ∀ τ ∈ F.fixingSubgroup, τ x = x := (mem_iff_forall_fixingSubgroup F x).1 hx
  show σ' x ∈ F
  rw [mem_iff_forall_fixingSubgroup]
  let σ : E.fixingSubgroup := (IntermediateField.fixingSubgroupEquiv E).symm σ'
  have hσ : ∀ y, (σ : Ω ≃ₐ[K] Ω) y = σ' y := fun _ => rfl
  intro τ hτ
  have hc : (σ : Ω ≃ₐ[K] Ω)⁻¹ * τ * σ ∈ F.fixingSubgroup := by
    have hτE : τ ∈ E.fixingSubgroup := IntermediateField.fixingSubgroup_antitone hEF hτ
    have := (inferInstance : (F.fixingSubgroup.subgroupOf E.fixingSubgroup).Normal).conj_mem
      ⟨τ, hτE⟩ (by simpa [Subgroup.mem_subgroupOf] using hτ) σ⁻¹
    simpa [Subgroup.mem_subgroupOf, mul_assoc] using this
  have h1 := hx _ hc
  simp only [AlgEquiv.mul_apply] at h1
  change τ (σ' x) = σ' x
  have h2 := congrArg (σ : Ω ≃ₐ[K] Ω) h1
  rwa [AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply] at h2
end GroundTheory.LocalField
