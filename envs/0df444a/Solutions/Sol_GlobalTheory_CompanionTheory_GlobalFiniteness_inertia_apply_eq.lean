-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GlobalFiniteness.inertia_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:44:21.286505+00:00
-- url     : https://prove2.me/submissions/9dfdb8f8-e6a3-4b88-b4a6-e94d4ac5735e

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_NormalSubgroupLeUnramifiedFixing
import Theorems.Thm_GlobalTheory_CompanionTheory_GlobalFiniteness_mem_cutPrime_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_GlobalFiniteness_cutPrime_liesOver
import Theorems.Thm_GroundTheory_ProfCoh_IsUnramifiedOutside_map
import Theorems.Thm_GroundTheory_ProfCoh_coe_galRootsOfUnityHom_apply
import Theorems.Thm_GroundTheory_ProfCoh_coe_openNormalSubgroupEquiv_symm_apply
import Theorems.Thm_GroundTheory_ProfCoh_isDiscreteRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_isUnramifiedOutside_iff_le_maxUnramifiedOutside
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
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GlobalFiniteness
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
namespace GlobalTheory.CompanionTheory.GlobalFiniteness
theorem _root_.solution [IsGalois F Ω] {S : Set (HeightOneSpectrum (𝓞 F))}
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) {A : ValuationSubring Ω} (hA : IsPlaceOver A v)
    {σ : G F Ω} (hσ : σ ∈ Inertia (F := F) A) {x : Ω} (hx : x ∈ maxUnramifiedOutside F Ω S) :
    σ x = x := by
  classical
  haveI hM : IsGalois F (maxUnramifiedOutside F Ω S) := isGalois_maxUnramifiedOutside S
  haveI : FiniteDimensional F (IntermediateField.adjoin F ({x} : Set Ω)) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  set E : IntermediateField F Ω := IntermediateField.normalClosure F (IntermediateField.adjoin F ({x} : Set Ω)) Ω with hE
  haveI : FiniteDimensional F E := normalClosure.is_finiteDimensional F (IntermediateField.adjoin F ({x} : Set Ω)) Ω
  haveI : Normal F E := normalClosure.normal F (IntermediateField.adjoin F ({x} : Set Ω)) Ω
  haveI : Algebra.IsSeparable F E := Algebra.IsSeparable.of_algHom F Ω E.val
  haveI : IsGalois F E := ⟨⟩
  have hxE : x ∈ E := IntermediateField.le_normalClosure (IntermediateField.adjoin F ({x} : Set Ω)) (IntermediateField.mem_adjoin_simple_self F x)
  have hEM : E ≤ maxUnramifiedOutside F Ω S := by
    rw [hE, IntermediateField.normalClosure_le_iff_of_normal]
    exact IntermediateField.adjoin_simple_le_iff.2 hx
  have hEun : IsUnramifiedOutside S E := (isUnramifiedOutside_iff_le_maxUnramifiedOutside S).2 hEM
  haveI hPl : (cutPrime A E).LiesOver v.asIdeal := cutPrime_liesOver hA E
  haveI : NumberField E := NumberField.of_module_finite F E
  haveI : Module.Finite (𝓞 F) (𝓞 E) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 F) (𝓞 E)
  haveI : Algebra.FiniteType (𝓞 F) (𝓞 E) := Algebra.FiniteType.of_restrictScalars_finiteType ℤ (𝓞 F) (𝓞 E)
  haveI : IsGaloisGroup Gal(E/F) (𝓞 F) (𝓞 E) := IsGaloisGroup.of_isFractionRing (G := Gal(E/F)) (A := 𝓞 F) (B := 𝓞 E) (K := F) (L := E)
  have he : (cutPrime A E).ramificationIdx (𝓞 F) = 1 :=
    Algebra.IsUnramifiedIn.ramificationIdx_eq_one (hEun v hv) hPl
  have hcard : Nat.card ((cutPrime A E).inertia Gal(E/F)) = 1 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(E/F)) v.asIdeal (cutPrime A E),
      Ideal.ramificationIdxIn_eq_ramificationIdx (G := Gal(E/F)) v.asIdeal (cutPrime A E), he]
  set σ' : Gal(E/F) := σ.restrictNormal E with hσ'
  have hmem : σ' ∈ (cutPrime A E).inertia Gal(E/F) := by
    intro z
    show σ' • z - z ∈ cutPrime A E
    rw [mem_cutPrime_iff]
    obtain ⟨-, hσ2⟩ := hσ
    have hy : ((z : E) : Ω) ∈ A :=
      mem_of_isIntegral_int A ((RingOfIntegers.isIntegral_coe z).map (IsScalarTower.toAlgHom ℤ E Ω))
    have hc : (((σ' • z - z : 𝓞 E) : E) : Ω) = σ ((z : E) : Ω) - ((z : E) : Ω) := by
      have h1 := AlgEquiv.restrictNormal_commutes σ E (z : E)
      simp only [IntermediateField.algebraMap_apply] at h1
      rw [← h1, hσ']
      rfl
    rw [hc]
    exact hσ2 _ (A.valuation_le_one ⟨_, hy⟩)
  have hσ'1 : σ' = 1 := by
    haveI hsub : Subsingleton ((cutPrime A E).inertia Gal(E/F)) := (Nat.card_eq_one_iff_unique.1 hcard).1
    have := Subsingleton.elim (⟨σ', hmem⟩ : (cutPrime A E).inertia Gal(E/F)) ⟨1, Subgroup.one_mem _⟩
    exact congrArg Subtype.val this
  have h1 := AlgEquiv.restrictNormal_commutes σ E ⟨x, hxE⟩
  rw [← hσ', hσ'1] at h1
  exact h1.symm
end GlobalTheory.CompanionTheory.GlobalFiniteness
