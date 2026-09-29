-- Prove2me | solution 1 for NumberField.pow_map_genuineBaseChange_mem_principalIdeles_sup_range_idelicNorm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/f6ca64a6-8b92-5dad-9e40-1a97ce23c15b

import Mathlib
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_NumberField_exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_unitIdeles_le
import Theorems.Thm_HeckeCharacter_exists_isAdjuster
import Theorems.Thm_LanglandsTunnell_P2_Artin_exists_ne_bot_and_unitIdeles_le_range_idelicNorm
import Theorems.Thm_LanglandsTunnell_P2_Artin_exists_ne_bot_forall_inertia_ne_bot_dvd
import Theorems.Thm_LanglandsTunnell_P2_Artin_unitIdeles_le_unitIdeles_of_dvd
import Theorems.Thm_HeckeCharacter_isAdjuster_unitsMap_genuineBaseChange_one_of_isAdjuster_one
import Theorems.Thm_LanglandsTunnell_P2_Artin_resHom_finprod_artinFrob_pow_placeOrd_map_eq_finprod_pow_finrank
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_pow_map_genuineBaseChange_mem_principalIdeles_sup_range_idelicNorm
p2m_attr_erase "instance" "LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero"

set_option autoImplicit false

open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin Deep.NTSupply
open scoped IsMulCommutative

theorem solution
    (E F N L' : Type*) [Field E] [NumberField E] [Field F] [NumberField F] [Field N] [NumberField N]
    [Field L'] [NumberField L']
    [Algebra E F] [Algebra E N] [Algebra F N] [Algebra E L'] [Algebra L' N]
    [IsScalarTower E F N] [IsScalarTower E L' N]
    [IsGalois F N] [IsMulCommutative (N ≃ₐ[F] N)] [IsGalois E L'] [IsMulCommutative (L' ≃ₐ[E] L')]
    (hinj : Function.Injective (resHom E L' F N))
    (n' : ℕ) (hexp : ∀ g : L' ≃ₐ[E] L', g ^ n' = 1) (hn : Module.finrank E F ∣ n')
    (u : (AdeleRing (𝓞 E) E)ˣ) :
    (Units.map (genuineBaseChange E F).β.toMonoidHom u) ^ (n' / Module.finrank E F) ∈
      principalIdeles (𝓞 F) F ⊔ (genuineBaseChange F N).idelicNorm.range := by
  classical
  set B := genuineBaseChange E F with hB
  set βu : (AdeleRing (𝓞 E) E)ˣ →* (AdeleRing (𝓞 F) F)ˣ := Units.map B.β.toMonoidHom with hβu
  set q : ℕ := n' / Module.finrank E F with hq

  obtain ⟨𝔪, h𝔪0, h𝔪ram, h𝔪units⟩ := LanglandsTunnell.P2.Artin.exists_ne_bot_and_unitIdeles_le_range_idelicNorm F N
  obtain ⟨𝔯, h𝔯0, h𝔯ram⟩ := LanglandsTunnell.P2.Artin.exists_ne_bot_forall_inertia_ne_bot_dvd E L'
  set 𝔣 : Ideal (𝓞 E) := 𝔪.comap (algebraMap (𝓞 E) (𝓞 F)) * 𝔯 with h𝔣
  have h𝔪E : 𝔪.comap (algebraMap (𝓞 E) (𝓞 F)) ≠ ⊥ := fun h => h𝔪0 (Ideal.eq_bot_of_comap_eq_bot h)
  have h𝔣0 : 𝔣 ≠ ⊥ := mul_ne_zero h𝔪E h𝔯0
  have h𝔯𝔣 : 𝔯 ∣ 𝔣 := Dvd.intro_left _ rfl
  have h𝔣F0 : modulusExt E F 𝔣 ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective (algebraMap_ringOfIntegers_injective E F)]
    exact h𝔣0
  have h𝔪𝔣 : 𝔪 ∣ modulusExt E F 𝔣 := by
    rw [Ideal.dvd_iff_le]
    refine (Ideal.map_mono (Ideal.mul_le_left : 𝔣 ≤ 𝔪.comap (algebraMap (𝓞 E) (𝓞 F)))).trans ?_
    exact Ideal.map_comap_le

  obtain ⟨r, -, hker, -, hr⟩ := NumberField.exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_unitIdeles_le F N (modulusExt E F 𝔣) h𝔣F0
    (fun w hw => dvd_trans (h𝔪ram w hw) h𝔪𝔣)
    ((LanglandsTunnell.P2.Artin.unitIdeles_le_unitIdeles_of_dvd F h𝔣F0 h𝔪𝔣).trans h𝔪units)

  obtain ⟨α, hα⟩ := HeckeCharacter.exists_isAdjuster E 𝔣 h𝔣0 u
  set pE : Eˣ →* (AdeleRing (𝓞 E) E)ˣ := Units.map (algebraMap E (AdeleRing (𝓞 E) E) : E →* AdeleRing (𝓞 E) E) with hpE
  set u₁ : (AdeleRing (𝓞 E) E)ˣ := u * (pE α)⁻¹ with hu₁
  have hu₁adj : IsAdjuster E 𝔣 u₁ 1 := by
    refine ⟨fun v hv => ?_, fun τ => ?_⟩
    · have h := hα.cong v hv; rwa [map_one, inv_one, mul_one]
    · have h := hα.sign τ; rwa [map_one, inv_one, mul_one]
  have hprinc : βu (pE α) ∈ principalIdeles (𝓞 F) F := by
    refine ⟨Units.map (algebraMap E F : E →* F) α, Units.ext ?_⟩
    simp only [hβu, hpE, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
    exact (B.β_compat (α : E)).symm
  have hu : u = u₁ * pE α := by rw [hu₁, inv_mul_cancel_right]

  have hker1 : (βu u₁) ^ q ∈ r.ker := by
    rw [MonoidHom.mem_ker, map_pow, hr _ (HeckeCharacter.isAdjuster_unitsMap_genuineBaseChange_one_of_isAdjuster_one E F 𝔣 u₁ hu₁adj)]
    apply hinj
    rw [map_pow, map_one, LanglandsTunnell.P2.Artin.resHom_finprod_artinFrob_pow_placeOrd_map_eq_finprod_pow_finrank E F N L' u₁ ?_, ← pow_mul, Nat.mul_div_cancel' hn]
    ·
      exact hexp _
    ·
      intro v hv Q hQ hQv
      by_contra hne
      have hvf : v.asIdeal ∣ 𝔣 := dvd_trans (h𝔯ram v Q hQ hQv hne) h𝔯𝔣
      exact hv ((placeOrd_eq_zero_iff E (projFin E u₁) v).mpr (by
        have h := (hu₁adj.cong v hvf).1
        rwa [map_one, inv_one, mul_one] at h))

  rw [hker] at hker1
  rw [hu, map_mul, mul_pow]
  exact Subgroup.mul_mem _ hker1 (Subgroup.mem_sup_left (Subgroup.pow_mem _ hprinc q))

end S_NumberField_pow_map_genuineBaseChange_mem_principalIdeles_sup_range_idelicNorm
end P2MW
export P2MW.S_NumberField_pow_map_genuineBaseChange_mem_principalIdeles_sup_range_idelicNorm (solution)
