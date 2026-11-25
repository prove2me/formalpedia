-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Glob.InertiaLift.exists_inertia_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:44:29.926562+00:00
-- url     : https://prove2.me/submissions/5d2f6d97-fa45-42e8-96a0-780fbabd95a2

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_GaloisUnramifiedOutsideCohomology
import Theorems.Thm_GlobalTheory_CompanionTheory_Glob_InertiaLift_restrictScalars_smul
import Theorems.Thm_GlobalTheory_CompanionTheory_Glob_InertiaLift_mem_inertia_of_integers
import Theorems.Thm_GlobalTheory_CompanionTheory_Glob_InertiaLift_exists_residue_correction
import Theorems.Thm_GroundTheory_ProfCoh_coe_galRootsOfUnityHom_apply
import Theorems.Thm_GroundTheory_ProfCoh_coe_openNormalSubgroupEquiv_symm_apply
import Theorems.Thm_GroundTheory_ProfCoh_isDiscreteRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_mem_stabilizer
import Theorems.Thm_GroundTheory_ProfCoh_openNormalSubgroupEquiv_apply
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAddInt___apply_e3c2bd0048b0
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAddZ___apply_9150def5d083
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAdd___apply_d57b0a2a1b9a
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galRootsOfUnityZ___apply_40a7d6b8f2a7
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galRootsOfUnity___apply_600492b04171
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galUnitsZ___apply_2d4ee74d5783
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galUnits___apply_5e27268f2c21
import Theorems.Thm_ReciprocityTheory_Gal_exists_smul_eq_of_over
import Theorems.Thm_ReciprocityTheory_Gal_exists_valuationSubring_over
import Theorems.Thm_ReciprocityTheory_Gal_smul_valuation_lt_one_iff
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
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual
open scoped Pointwise IntermediateField
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Glob GlobalTheory.CompanionTheory.Glob.InertiaLift
variable {F K Ω : Type*} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  [Field Ω] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω]
namespace GlobalTheory.CompanionTheory.Glob.InertiaLift
theorem _root_.solution [IsAlgClosure F Ω] [IsAlgClosure K Ω] [Normal F K]
    (w : HeightOneSpectrum (𝓞 K)) {τ : K ≃ₐ[F] K} (hτ : τ ∈ w.asIdeal.inertia (K ≃ₐ[F] K)) :
    ∃ (A : ValuationSubring Ω) (σ : Ω ≃ₐ[F] Ω),
      (∀ x : 𝓞 K, A.valuation (algebraMap K Ω (x : K)) < 1 ↔ x ∈ w.asIdeal) ∧
      σ ∈ Inertia (F := F) A ∧ ∀ x : K, σ (algebraMap K Ω x) = algebraMap K Ω (τ x) := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap ℚ F).injective
  have : IsGalois K Ω := {}
  have : IsGalois F Ω := {}
  obtain ⟨A, hA⟩ := exists_valuationSubring_over (Ω := Ω) w
  let σ₀ : Ω ≃ₐ[F] Ω := τ.liftNormal Ω
  have hσ₀ : ∀ x : K, σ₀ (algebraMap K Ω x) = algebraMap K Ω (τ x) := fun x =>
    AlgEquiv.liftNormal_commutes τ Ω x
  have hτ' : ∀ z : 𝓞 K, τ • z - z ∈ w.asIdeal := fun z => AddSubgroup.mem_inertia.1 hτ z
  have hτi : ∀ z : 𝓞 K, τ⁻¹ • z - z ∈ w.asIdeal := fun z =>
    AddSubgroup.mem_inertia.1 (Subgroup.inv_mem _ hτ) z
  have hσ₀i : ∀ x : K, (σ₀⁻¹ : Ω ≃ₐ[F] Ω) (algebraMap K Ω x) = algebraMap K Ω ((τ⁻¹ : K ≃ₐ[F] K) x) := by
    intro x
    have h1 : algebraMap K Ω x = σ₀ (algebraMap K Ω ((τ⁻¹ : K ≃ₐ[F] K) x)) := by
      rw [hσ₀]
      congr 1
      show x = (τ * τ⁻¹) x
      simp
    rw [h1]
    show (σ₀⁻¹ * σ₀) _ = _
    simp
  have hA' : ∀ x : 𝓞 K, (σ₀ • A).valuation (algebraMap K Ω (x : K)) < 1 ↔ x ∈ w.asIdeal := by
    intro x
    rw [smul_valuation_lt_one_iff, hσ₀i]
    have := hA (τ⁻¹ • x)
    refine (Iff.trans (by exact this) ?_)
    constructor
    · intro h
      have := w.asIdeal.sub_mem h (hτi x)
      simpa using this
    · intro h
      have := w.asIdeal.add_mem (hτi x) h
      simpa using this
  obtain ⟨h, hh⟩ := exists_smul_eq_of_over hA' hA
  let σ₁ : Ω ≃ₐ[F] Ω := h.restrictScalars F * σ₀
  have hσ₁ : ∀ x : K, σ₁ (algebraMap K Ω x) = algebraMap K Ω (τ x) := by
    intro x
    show (h.restrictScalars F) (σ₀ (algebraMap K Ω x)) = _
    rw [hσ₀]
    exact h.commutes _
  have hd : σ₁ ∈ Dec (F := F) A := by
    show σ₁ • A = A
    rw [mul_smul, restrictScalars_smul, hh]
  have hz : ∀ z : 𝓞 K, A.valuation (σ₁ (algebraMap K Ω (z : K)) - algebraMap K Ω (z : K)) < 1 := by
    intro z
    rw [hσ₁, ← map_sub]
    exact (hA (τ • z - z)).2 (hτ' z)
  obtain ⟨g, hgA, hg⟩ := exists_residue_correction (F := F) w hA hd hz
  let g' : Ω ≃ₐ[F] Ω := g.restrictScalars F
  have hgD : g' ∈ Dec (F := F) A := by
    show g' • A = A
    rw [restrictScalars_smul, hgA]
  refine ⟨A, g'⁻¹ * σ₁, hA, ?_, fun x => ?_⟩
  · refine mem_inertia_of_integers ((Dec (F := F) A).mul_mem ((Dec (F := F) A).inv_mem hgD) hd) ?_
    intro b hb
    have e : (g'⁻¹ * σ₁) b - b = (g'⁻¹ : Ω ≃ₐ[F] Ω) (σ₁ b - g' b) := by
      rw [map_sub]
      have : (g'⁻¹ : Ω ≃ₐ[F] Ω) (g' b) = b := by
        show (g'⁻¹ * g') b = b
        simp
      rw [this]
      rfl
    rw [e, valuation_apply_lt_one_iff ((Dec (F := F) A).inv_mem hgD), Valuation.map_sub_swap]
    exact hg ⟨b, hb.tower_top⟩
  · show (g'⁻¹ : Ω ≃ₐ[F] Ω) (σ₁ (algebraMap K Ω x)) = _
    rw [hσ₁]
    have : g' (algebraMap K Ω (τ x)) = algebraMap K Ω (τ x) := g.commutes _
    conv_lhs => rw [← this]
    show (g'⁻¹ * g') _ = _
    simp
end GlobalTheory.CompanionTheory.Glob.InertiaLift
