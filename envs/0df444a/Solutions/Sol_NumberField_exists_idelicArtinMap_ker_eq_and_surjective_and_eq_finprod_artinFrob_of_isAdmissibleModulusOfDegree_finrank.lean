-- Prove2me | solution 1 for NumberField.exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/5a4020f4-e8cf-52f8-b7a7-9fd402fa3c2e

import Mathlib
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Theorems.Thm_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree
import Theorems.Thm_LanglandsTunnell_P2_Artin_exists_mulEquiv_quotient_normRaySubgroup_apply_eq_contents_of_anchors
import Theorems.Thm_HeckeCharacter_isAdjuster_idelicNorm_of_isAdjuster
import Theorems.Thm_HeckeCharacter_fadContentHom_projFin_idelicNorm_eq_fracRelNormUnit
import Theorems.Thm_LanglandsTunnell_P2_Artin_unitIdeles_le_range_idelicNorm_of_isAdmissibleModulusOfDegree
import Theorems.Thm_HeckeCharacter_fadContentHom_projFin_mem_coprimeToModulus_of_isAdjuster_one
import Theorems.Thm_LanglandsTunnell_P2_Artin_artinSymbol_fadContentHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank
p2m_attr_erase "instance" "LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero"

set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin Deep.NTSupply
open scoped IsMulCommutative

theorem solution
    (E F : Type*) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsMulCommutative (F ≃ₐ[E] F)]
    (𝔣 : Ideal (𝓞 E)) (hadm : NumberField.NormIndex.IsAdmissibleModulusOfDegree E F (Module.finrank E F) 𝔣) :
    ∃ r : (AdeleRing (𝓞 E) E)ˣ →* (F ≃ₐ[E] F),
      principalIdeles (𝓞 E) E ≤ r.ker ∧
      r.ker = principalIdeles (𝓞 E) E ⊔ (genuineBaseChange E F).idelicNorm.range ∧
      Function.Surjective r ∧
      ∀ u : (AdeleRing (𝓞 E) E)ˣ, IsAdjuster E 𝔣 u 1 →
        r u = ∏ᶠ v : HeightOneSpectrum (𝓞 E), artinFrob E F v ^ placeOrd E (projFin E u) v := by
  classical

  have hn : Module.finrank E F ≠ 0 := Module.finrank_pos.ne'
  have hexp : ∀ x : F ≃ₐ[E] F, x ^ Module.finrank E F = 1 := fun x => by
    rw [← IsGalois.card_aut_eq_finrank]; exact pow_card_eq_one'
  obtain ⟨hsurj, hker⟩ := LanglandsTunnell.Artin.artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree E F (Module.finrank E F) hn hexp 𝔣 hadm

  obtain ⟨φ, hφ⟩ :=
    LanglandsTunnell.P2.Artin.exists_mulEquiv_quotient_normRaySubgroup_apply_eq_contents_of_anchors E F 𝔣 hadm.1
      (genuineBaseChange E F).idelicNorm
      (fun h => HeckeCharacter.isAdjuster_idelicNorm_of_isAdjuster E F 𝔣 h)
      (fun u => HeckeCharacter.fadContentHom_projFin_idelicNorm_eq_fracRelNormUnit E F u)
      (LanglandsTunnell.P2.Artin.unitIdeles_le_range_idelicNorm_of_isAdmissibleModulusOfDegree E F 𝔣 hadm)

  have hle : normRaySubgroup E F 𝔣 ≤ (artinSymbol E F 𝔣).ker := le_of_eq hker.symm
  let ψ₀ : (↥(Deep.NTSupply.coprimeToModulus E 𝔣) ⧸ normRaySubgroup E F 𝔣) →* (F ≃ₐ[E] F) :=
    QuotientGroup.lift _ (artinSymbol E F 𝔣) hle
  have hψ₀mk : ∀ J, ψ₀ (QuotientGroup.mk J) = artinSymbol E F 𝔣 J := fun J => QuotientGroup.lift_mk _ hle J
  have hψ₀inj : Function.Injective ψ₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_lift, hker, eq_bot_iff]
    rintro _ ⟨J, hJ, rfl⟩
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hJ

  let π : (AdeleRing (𝓞 E) E)ˣ →* (AdeleRing (𝓞 E) E)ˣ ⧸ (principalIdeles (𝓞 E) E ⊔ (genuineBaseChange E F).idelicNorm.range) :=
    QuotientGroup.mk' _
  let r : (AdeleRing (𝓞 E) E)ˣ →* (F ≃ₐ[E] F) := ψ₀.comp (φ.toMonoidHom.comp π)
  have hr : ∀ u, r u = ψ₀ (φ (QuotientGroup.mk u)) := fun _ => rfl

  have hker_r : r.ker = principalIdeles (𝓞 E) E ⊔ (genuineBaseChange E F).idelicNorm.range := by
    ext u
    rw [MonoidHom.mem_ker, hr, map_eq_one_iff ψ₀ hψ₀inj, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  refine ⟨r, ?_, hker_r, ?_, ?_⟩
  ·
    rw [hker_r]
    exact le_sup_left
  ·
    intro g
    obtain ⟨J, hJ⟩ := hsurj g
    obtain ⟨c, hc⟩ := φ.surjective (QuotientGroup.mk J)
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective c
    exact ⟨u, by rw [hr, hc, hψ₀mk, hJ]⟩
  ·
    intro u hu
    have hc := HeckeCharacter.fadContentHom_projFin_mem_coprimeToModulus_of_isAdjuster_one E 𝔣 u hu
    rw [hr, hφ u hu hc, hψ₀mk]
    exact LanglandsTunnell.P2.Artin.artinSymbol_fadContentHom E F 𝔣 u hc

end S_NumberField_exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank
end P2MW
export P2MW.S_NumberField_exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank (solution)
