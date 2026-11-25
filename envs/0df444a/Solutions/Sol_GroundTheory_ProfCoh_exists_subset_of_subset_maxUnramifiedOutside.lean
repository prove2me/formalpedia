-- Prove2me | solution 1 for GroundTheory.ProfCoh.exists_subset_of_subset_maxUnramifiedOutside
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:36:34.772123+00:00
-- url     : https://prove2.me/submissions/5a3a86d4-7b8e-48ae-b106-e27062543eaf

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_Discrete
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_Unramified
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Theorems.Thm_GroundTheory_ProfCoh_IsUnramifiedOutside_sup
import Theorems.Thm_GroundTheory_ProfCoh_coe_galRootsOfUnityHom_apply
import Theorems.Thm_GroundTheory_ProfCoh_coe_openNormalSubgroupEquiv_symm_apply
import Theorems.Thm_GroundTheory_ProfCoh_isDiscreteRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_isUnramifiedOutside_bot
import Theorems.Thm_GroundTheory_ProfCoh_mem_stabilizer
import Theorems.Thm_GroundTheory_ProfCoh_openNormalSubgroupEquiv_apply
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAddInt___apply_e3c2bd0048b0
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAddZ___apply_9150def5d083
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAdd___apply_d57b0a2a1b9a
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galRootsOfUnityZ___apply_40a7d6b8f2a7
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galRootsOfUnity___apply_600492b04171
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galUnitsZ___apply_2d4ee74d5783
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galUnits___apply_5e27268f2c21
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.coe_galRootsOfUnityHom_apply
attribute [local simp] GroundTheory.ProfCoh.coe_openNormalSubgroupEquiv_symm_apply
attribute [local simp] GroundTheory.ProfCoh.isDiscreteRep_apply
attribute [local simp] GroundTheory.ProfCoh.mem_stabilizer
attribute [local simp] GroundTheory.ProfCoh.openNormalSubgroupEquiv_apply
attribute [local simp] P2M_GroundTheory_ProfCoh_galAddInt___apply_e3c2bd0048b0
attribute [local simp] P2M_GroundTheory_ProfCoh_galAddZ___apply_9150def5d083
attribute [local simp] P2M_GroundTheory_ProfCoh_galAdd___apply_d57b0a2a1b9a
attribute [local simp] P2M_GroundTheory_ProfCoh_galRootsOfUnityZ___apply_40a7d6b8f2a7
attribute [local simp] P2M_GroundTheory_ProfCoh_galRootsOfUnity___apply_600492b04171
attribute [local simp] P2M_GroundTheory_ProfCoh_galUnitsZ___apply_2d4ee74d5783
attribute [local simp] P2M_GroundTheory_ProfCoh_galUnits___apply_5e27268f2c21



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open NumberField IsDedekindDomain
variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))
variable [NumberField F] [IsGalois F Ω]
namespace GroundTheory.ProfCoh
theorem _root_.solution (s : Finset Ω)
    (hs : ∀ x ∈ s, x ∈ maxUnramifiedOutside F Ω S) :
    ∃ E : IntermediateField F Ω, FiniteDimensional F E ∧ IsUnramifiedOutside S E ∧
      ∀ x ∈ s, x ∈ E := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨⊥, inferInstance, isUnramifiedOutside_bot S, by simp⟩
  | insert a s _ ih =>
    obtain ⟨E₁, hf₁, hu₁, ha⟩ :=
      (mem_maxUnramifiedOutside_iff S).1 (hs a (Finset.mem_insert_self a s))
    obtain ⟨E₂, hf₂, hu₂, hs₂⟩ := ih fun x hx => hs x (Finset.mem_insert_of_mem hx)
    refine ⟨E₁ ⊔ E₂, inferInstance, hu₁.sup hu₂, fun x hx => ?_⟩
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact le_sup_left (α := IntermediateField F Ω) ha
    · exact le_sup_right (α := IntermediateField F Ω) (hs₂ x hx)
end GroundTheory.ProfCoh
