-- Prove2me | solution 1 for M4aHerbrand.GenuineDescent.finite_setOf_monoidHom_comp_idelicNorm_genuineBaseChange_eq_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/3a749b3b-21fd-54c7-9c79-a9473cc1b88e

import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_NumberField_PrimeNormIndex_ideleClass_normCoset_index_dvd_of_finrank_eq_prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_GenuineDescent_finite_setOf_monoidHom_comp_idelicNorm_genuineBaseChange_eq_of_prime
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero"

set_option autoImplicit false

open NumberField

private theorem finite_monoidHom_units_of_finite (G : Type) [Group G] [Finite G] : Finite (G →* ℂˣ) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have hmem : ∀ (χ : G →* ℂˣ) (g : G), χ g ∈ rootsOfUnity (Fintype.card G) ℂ := by
    intro χ g
    rw [mem_rootsOfUnity, ← map_pow, pow_card_eq_one, map_one]
  let Φ : (G →* ℂˣ) → (G → rootsOfUnity (Fintype.card G) ℂ) := fun χ g => ⟨χ g, hmem χ g⟩
  have hΦ : Function.Injective Φ := by
    intro χ₁ χ₂ h
    ext g
    have h1 := congrArg (fun f : G → rootsOfUnity (Fintype.card G) ℂ => (f g : ℂˣ)) h
    exact congrArg Units.val h1
  exact Finite.of_injective Φ hΦ

private def charOfTopSubgroup {A : Type} [CommGroup A] (ξ : (⊤ : Subgroup A) →* ℂˣ) : A →* ℂˣ :=
  ξ.comp (Subgroup.topEquiv (G := A)).symm.toMonoidHom

private theorem charOfTopSubgroup_apply {A : Type} [CommGroup A] (ξ : (⊤ : Subgroup A) →* ℂˣ) (z : A) :
    charOfTopSubgroup ξ z = ξ ⟨z, Subgroup.mem_top z⟩ := rfl

private theorem charOfTopSubgroup_injective {A : Type} [CommGroup A] :
    Function.Injective (charOfTopSubgroup (A := A)) := by
  intro ξ₁ ξ₂ h
  refine MonoidHom.ext fun w => ?_
  exact congrArg (fun f : A →* ℂˣ => f (w : A)) h

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L]
    (hdeg : (Module.finrank K L).Prime)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) :
    Set.Finite {ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ |
      ((Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
            ξ ⟨z, Subgroup.mem_top z⟩ = 1) ∧
        ∀ z : (AdeleRing (𝓞 L) L)ˣ,
          ξ ⟨(M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z, Subgroup.mem_top _⟩ =
            ξL ⟨z, Subgroup.mem_top z⟩) } := by
  classical

  have hidx : (M4aHerbrand.principalIdeles (𝓞 K) K ⊔
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm.range).index ≠ 0 := by
    intro h0
    have hdvd := NumberField.PrimeNormIndex.ideleClass_normCoset_index_dvd_of_finrank_eq_prime K L
      (Module.finrank K L) hdeg rfl (M4aHerbrand.GenuineDescent.genuineBaseChange K L)
    rw [h0] at hdvd
    exact hdeg.ne_zero (zero_dvd_iff.mp hdvd)
  set H : Subgroup (AdeleRing (𝓞 K) K)ˣ :=
    M4aHerbrand.principalIdeles (𝓞 K) K ⊔
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm.range with hH
  haveI : H.FiniteIndex := Subgroup.finiteIndex_iff.mpr hidx
  set S := {ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ |
      ((Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
            ξ ⟨z, Subgroup.mem_top z⟩ = 1) ∧
        ∀ z : (AdeleRing (𝓞 L) L)ˣ,
          ξ ⟨(M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z, Subgroup.mem_top _⟩ =
            ξL ⟨z, Subgroup.mem_top z⟩) } with hS
  by_cases hne : S.Nonempty
  · obtain ⟨ξ₀, hξ₀⟩ := hne

    obtain ⟨-, hξ₀P, hξ₀N⟩ := hξ₀
    have hker : ∀ ξ ∈ S, H ≤ (charOfTopSubgroup ξ * (charOfTopSubgroup ξ₀)⁻¹).ker := by
      intro ξ hξ
      obtain ⟨-, hξP, hξN⟩ := hξ
      rw [hH]
      refine sup_le ?_ ?_
      · intro z hz
        rw [MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.inv_apply, charOfTopSubgroup_apply,
          charOfTopSubgroup_apply,
          hξP z hz, hξ₀P z hz, inv_one, mul_one]
      · rintro _ ⟨w, rfl⟩
        rw [MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.inv_apply, charOfTopSubgroup_apply,
          charOfTopSubgroup_apply,
          hξN w, hξ₀N w, mul_inv_cancel]
    let Φ : S → ((AdeleRing (𝓞 K) K)ˣ ⧸ H →* ℂˣ) := fun ξ =>
      QuotientGroup.lift H (charOfTopSubgroup ξ.1 * (charOfTopSubgroup ξ₀)⁻¹) (hker ξ.1 ξ.2)
    have hΦ : Function.Injective Φ := by
      intro ξ₁ ξ₂ h
      apply Subtype.ext
      apply charOfTopSubgroup_injective
      refine MonoidHom.ext fun z => ?_
      have h1 := congrArg (fun f : (AdeleRing (𝓞 K) K)ˣ ⧸ H →* ℂˣ => f (z : (AdeleRing (𝓞 K) K)ˣ ⧸ H)) h
      simp only [Φ, QuotientGroup.lift_mk, MonoidHom.mul_apply, MonoidHom.inv_apply] at h1
      exact mul_right_cancel h1
    haveI : Finite ((AdeleRing (𝓞 K) K)ˣ ⧸ H →* ℂˣ) :=
      finite_monoidHom_units_of_finite ((AdeleRing (𝓞 K) K)ˣ ⧸ H)
    haveI : Finite S := Finite.of_injective Φ hΦ
    exact Set.toFinite S
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    exact Set.finite_empty

#print axioms solution

end S_M4aHerbrand_GenuineDescent_finite_setOf_monoidHom_comp_idelicNorm_genuineBaseChange_eq_of_prime
end P2MW
export P2MW.S_M4aHerbrand_GenuineDescent_finite_setOf_monoidHom_comp_idelicNorm_genuineBaseChange_eq_of_prime (solution)
