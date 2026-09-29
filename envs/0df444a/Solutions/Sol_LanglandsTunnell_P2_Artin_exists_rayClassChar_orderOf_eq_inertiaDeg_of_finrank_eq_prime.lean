-- Prove2me | solution 1 for LanglandsTunnell.P2.Artin.exists_rayClassChar_orderOf_eq_inertiaDeg_of_finrank_eq_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/6f8fd35f-7390-5e95-b9b8-29c0bc35d836

import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Theorems.Thm_LanglandsTunnell_P2_Artin_exists_admissibleModulus_supported
import Theorems.Thm_LanglandsTunnell_P2_Artin_exists_dvd_and_isAdmissibleModulusOfDegree_of_ramified_dvd
import Theorems.Thm_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree
import Theorems.Thm_P2M_Dup_ArithFrobResidue_orderOf_arithFrob_eq_finrank_of_inertia_eq_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_P2_Artin_exists_rayClassChar_orderOf_eq_inertiaDeg_of_finrank_eq_prime
p2m_attr_erase "instance" "LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero"

set_option autoImplicit false

open NumberField IsDedekindDomain
open Deep.NTSupply
open LanglandsTunnell.P2.Artin

theorem solution
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E]
    [IsGalois F E]
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hdeg : Module.finrank F E = ℓ) :
    ∃ 𝔣 : Ideal (𝓞 F), IsAdmissibleModulus F E 𝔣 ∧
      ∃ η : NarrowRayClassGroup F 𝔣 →* ℂˣ,
        ∀ (w : HeightOneSpectrum (𝓞 E)) (hw : ¬ ((w.under (𝓞 F)).asIdeal ∣ 𝔣)),
          orderOf (η (primeClass F 𝔣 (w.under (𝓞 F)) hw)) =
            (w.under (𝓞 F)).asIdeal.inertiaDeg' w.asIdeal := by

  obtain ⟨𝔣₀, hadm₀, -⟩ := exists_admissibleModulus_supported F E
  have hexp0 : ∀ v : HeightOneSpectrum (𝓞 F), admissibleExp F v ≠ 0 := fun v => by
    unfold admissibleExp; omega
  have hram : ∀ v : HeightOneSpectrum (𝓞 F),
      (primeAbove F E v).inertia (E ≃ₐ[F] E) ≠ ⊥ → v.asIdeal ∣ 𝔣₀ :=
    fun v hv => (dvd_pow_self v.asIdeal (hexp0 v)).trans (hadm₀.2 v hv)
  obtain ⟨𝔣, hdvd, -, hdeg'⟩ :=
    exists_dvd_and_isAdmissibleModulusOfDegree_of_ramified_dvd F E 𝔣₀ hadm₀.1 hram ℓ
  have hadm : IsAdmissibleModulus F E 𝔣 := ⟨hdeg'.1, fun v hv => (hadm₀.2 v hv).trans hdvd⟩

  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hcard : Nat.card (E ≃ₐ[F] E) = ℓ := (IsGalois.card_aut_eq_finrank F E).trans hdeg
  haveI : IsCyclic (E ≃ₐ[F] E) := isCyclic_of_prime_card hcard
  have hexp : ∀ x : E ≃ₐ[F] E, x ^ ℓ = 1 := fun x => by
    rw [← hcard]
    exact pow_card_eq_one'

  have hker : (artinSymbol F E 𝔣).ker = normRaySubgroup F E 𝔣 :=
    open LanglandsTunnell.Artin in
    (artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree
      F E ℓ hℓ.ne_zero hexp 𝔣 hdeg').2

  have hroots : Nat.card (rootsOfUnity ℓ ℂ) = ℓ := by
    exact Complex.card_rootsOfUnity ℓ
  let χ : (E ≃ₐ[F] E) →* ℂˣ :=
    (rootsOfUnity ℓ ℂ).subtype.comp (mulEquivOfPrimeCardEq hcard hroots).toMonoidHom
  have hχ : Function.Injective χ :=
    Subtype.val_injective.comp (mulEquivOfPrimeCardEq hcard hroots).injective

  have hle : (narrowRaySubgroup F 𝔣).subgroupOf (coprimeToModulus F 𝔣) ≤
      (χ.comp (artinSymbol F E 𝔣)).ker := by
    intro x hx
    have hx' : x ∈ (artinSymbol F E 𝔣).ker := by
      rw [hker]
      exact Subgroup.mem_sup_left hx
    rw [MonoidHom.mem_ker] at hx' ⊢
    rw [MonoidHom.comp_apply, hx', map_one]
  let η : NarrowRayClassGroup F 𝔣 →* ℂˣ := QuotientGroup.lift _ (χ.comp (artinSymbol F E 𝔣)) hle
  refine ⟨𝔣, hadm, η, fun w hw => ?_⟩

  have hηv : η (primeClass F 𝔣 (w.under (𝓞 F)) hw) = χ (artinFrob F E (w.under (𝓞 F))) := by
    show (QuotientGroup.lift _ (χ.comp (artinSymbol F E 𝔣)) hle)
        (NarrowRayClassGroup.mk F 𝔣 ⟨primeUnit F (w.under (𝓞 F)),
          primeUnit_mem_coprimeToModulus F hw⟩) = _
    rw [NarrowRayClassGroup.mk, QuotientGroup.mk'_apply, QuotientGroup.lift_mk,
      MonoidHom.comp_apply, artinSymbol_prime F E hw]
  rw [hηv, orderOf_injective χ hχ]

  have hP : (primeAbove F E (w.under (𝓞 F))).inertia (E ≃ₐ[F] E) = ⊥ := by
    by_contra h
    exact hw ((dvd_pow_self _ (hexp0 _)).trans (hadm.2 _ h))
  haveI : Finite (𝓞 F ⧸ (primeAbove F E (w.under (𝓞 F))).under (𝓞 F)) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by
      rw [under_primeAbove]
      exact (w.under (𝓞 F)).ne_bot)
  haveI : Fintype (𝓞 F ⧸ (primeAbove F E (w.under (𝓞 F))).under (𝓞 F)) := Fintype.ofFinite _
  have h78 : orderOf (artinFrob F E (w.under (𝓞 F))) =
      Module.finrank (𝓞 F ⧸ (primeAbove F E (w.under (𝓞 F))).under (𝓞 F))
        (𝓞 E ⧸ primeAbove F E (w.under (𝓞 F))) :=
    ArithFrobResidue.orderOf_arithFrob_eq_finrank_of_inertia_eq_bot hP
      ⟨artinFrob F E (w.under (𝓞 F)), (isArithFrobAt_artinFrob F E (w.under (𝓞 F))).mem_stabilizer⟩
      (isArithFrobAt_artinFrob F E (w.under (𝓞 F)))

  have hf : ((primeAbove F E (w.under (𝓞 F))).under (𝓞 F)).inertiaDeg'
      (primeAbove F E (w.under (𝓞 F))) = (w.under (𝓞 F)).asIdeal.inertiaDeg' w.asIdeal := by
    rw [under_primeAbove]
    haveI : w.asIdeal.IsPrime := w.isPrime
    haveI : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
    haveI := (w.under (𝓞 F)).isMaximal
    haveI := w.isMaximal
    rw [Ideal.inertiaDeg'_eq_inertiaDeg (w.under (𝓞 F)).asIdeal (primeAbove F E (w.under (𝓞 F))),
      Ideal.inertiaDeg'_eq_inertiaDeg (w.under (𝓞 F)).asIdeal w.asIdeal]
    exact Ideal.inertiaDeg_eq_of_isGaloisGroup (w.under (𝓞 F)).asIdeal
      (primeAbove F E (w.under (𝓞 F))) w.asIdeal (E ≃ₐ[F] E)
  exact h78.trans ((Ideal.inertiaDeg_algebraMap _ _).symm.trans hf)

end S_LanglandsTunnell_P2_Artin_exists_rayClassChar_orderOf_eq_inertiaDeg_of_finrank_eq_prime
end P2MW
export P2MW.S_LanglandsTunnell_P2_Artin_exists_rayClassChar_orderOf_eq_inertiaDeg_of_finrank_eq_prime (solution)
