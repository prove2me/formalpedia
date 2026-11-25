-- Prove2me | solution 1 for GroundTheory.ProfCoh.isUnramifiedIn_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:29:38.989227+00:00
-- url     : https://prove2.me/submissions/3ded1e6b-2491-4b2a-942c-aa47ddb75be5

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_FixedField
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_MaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_Ramification
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_Unramified
import Theorems.Thm_GroundTheory_ProfCoh_isUnramifiedIn_iff_inertia
import Theorems.Thm_GroundTheory_ProfCoh_coe_galRootsOfUnityHom_apply
import Theorems.Thm_GroundTheory_ProfCoh_coe_openNormalSubgroupEquiv_symm_apply
import Theorems.Thm_GroundTheory_ProfCoh_exists_finiteGalois_le
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
attribute [local simp] GroundTheory.ProfCoh.openNormalSubgroupEquiv_apply
attribute [local simp] P2M_GroundTheory_ProfCoh_galAddInt___apply_e3c2bd0048b0
attribute [local simp] P2M_GroundTheory_ProfCoh_galAddZ___apply_9150def5d083
attribute [local simp] P2M_GroundTheory_ProfCoh_galAdd___apply_d57b0a2a1b9a
attribute [local simp] P2M_GroundTheory_ProfCoh_galRootsOfUnityZ___apply_40a7d6b8f2a7
attribute [local simp] P2M_GroundTheory_ProfCoh_galRootsOfUnity___apply_600492b04171
attribute [local simp] P2M_GroundTheory_ProfCoh_galUnitsZ___apply_2d4ee74d5783
attribute [local simp] P2M_GroundTheory_ProfCoh_galUnits___apply_5e27268f2c21



set_option autoImplicit false
open GroundTheory GroundTheory.ProfCoh
open NumberField IsDedekindDomain
open scoped Pointwise
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
variable [IsGalois F Ω]
namespace GroundTheory.ProfCoh
theorem _root_.solution {E : IntermediateField F Ω} [FiniteDimensional F E]
    (v : HeightOneSpectrum (𝓞 F)) (hE : Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal) (τ : Gal(Ω/F)) :
    Algebra.IsUnramifiedIn (𝓞 ↥(E.map (τ : Ω →ₐ[F] Ω))) v.asIdeal := by
  obtain ⟨M, hM⟩ := exists_finiteGalois_le E
  set M' : IntermediateField F Ω := M.toIntermediateField with hM'
  set ρ : Gal(M'/F) := τ.restrictNormal M' with hρ
  have hρapp : ∀ y (hy : y ∈ M'), ((ρ ⟨y, hy⟩ : M') : Ω) = τ y := fun y hy =>
    AlgEquiv.restrictNormal_commutes τ M' ⟨y, hy⟩
  have hτM : E.map (τ : Ω →ₐ[F] Ω) ≤ M' := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (IntermediateField.mem_map _).1 hx
    have := (ρ ⟨y, hM hy⟩).2
    rwa [hρapp] at this
  rw [isUnramifiedIn_iff_inertia hM] at hE
  rw [isUnramifiedIn_iff_inertia hτM]
  intro Q hQ hQv σ hσ x hx
  obtain ⟨y, hy, rfl⟩ := (IntermediateField.mem_map _).1 hx
  have hconj : ρ⁻¹ * σ * ρ ∈ (ρ⁻¹ • Q).inertia Gal(M'/F) := by
    rw [Ideal.inertia, AddSubgroup.mem_inertia]
    intro z
    rw [Submodule.mem_toAddSubgroup, Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_inv,
      smul_sub, ← mul_smul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, mul_smul]
    exact (AddSubgroup.mem_inertia.1 hσ) (ρ • z)
  have := NumberField.of_module_finite F M'
  have : IsGaloisGroup Gal(M'/F) (𝓞 F) (𝓞 M') := IsGaloisGroup.of_isFractionRing _ _ _ F M'
  have hfix := hE (ρ⁻¹ • Q) inferInstance inferInstance _ hconj y hy
  have hρy : ρ ⟨y, hM hy⟩ = ⟨(τ : Ω →ₐ[F] Ω) y, hτM hx⟩ := Subtype.ext (hρapp y (hM hy))
  rw [← hρy]
  calc σ (ρ ⟨y, hM hy⟩) = ρ ((ρ⁻¹ * σ * ρ) ⟨y, hM hy⟩) := by
        simp only [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
    _ = ρ ⟨y, hM hy⟩ := by rw [hfix]
end GroundTheory.ProfCoh
