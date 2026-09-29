-- Prove2me | solution 1 for NumberField.PlaceDecomp.iSup_decomp_eq_top_of_isCyclic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/7d588fb7-4526-5d01-8062-dd4976cb080f

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_NumberField_exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank
import Theorems.Thm_HeckeCharacter_exists_isAdjuster
import Theorems.Thm_LanglandsTunnell_P2_Artin_exists_dvd_and_isAdmissibleModulusOfDegree_of_ramified_dvd
import Theorems.Thm_LanglandsTunnell_P2_Artin_exists_ne_bot_forall_inertia_primeAbove_ne_bot_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceDecomp_iSup_decomp_eq_top_of_isCyclic
p2m_attr_erase "instance" "LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero"
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped NumberField.PlaceDecomp

section EngP2Decomp
open scoped Pointwise

namespace M4aHerbrand
p2m_export "M4aHerbrand" "principalIdeles"
namespace LocDec
p2m_open "M4aHerbrand"

variable (E F : Type*) [Field E] [Field F] [NumberField F] [Algebra E F] (w : HeightOneSpectrum (𝓞 F))

example (σ : F ≃ₐ[E] F) : Ideal (𝓞 F) := σ • w.asIdeal
example (σ : F ≃ₐ[E] F) (x : 𝓞 F) : ((σ • x : 𝓞 F) : F) = σ x := rfl
example (σ : F ≃ₐ[E] F) (x : F) : σ • x = σ x := rfl
example (a : 𝓞 F) : algebraMap (𝓞 F) F a = (a : F) := rfl

theorem smul_valuationSubring_le (σ : F ≃ₐ[E] F) (hσ : σ • w.asIdeal = w.asIdeal) :
    σ • (w.valuation F).valuationSubring ≤ (w.valuation F).valuationSubring := by
  intro x hx
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem] at hx
  rw [← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring] at hx ⊢
  obtain ⟨a, s, hs, h⟩ := hx
  have hs' : σ • s ∈ w.asIdeal.primeCompl := by
    intro (hmem : σ • s ∈ w.asIdeal)
    rw [← hσ, Ideal.smul_mem_pointwise_smul_iff] at hmem
    exact hs hmem
  refine ⟨σ • a, σ • s, hs', ?_⟩
  have hx' : x = σ • (σ⁻¹ • x) := (smul_inv_smul σ x).symm
  rw [hx', h, smul_mul', smul_inv'']
  rfl

theorem mem_decomp_of_smul_asIdeal_eq (σ : F ≃ₐ[E] F) (hσ : σ • w.asIdeal = w.asIdeal) :
    σ ∈ NumberField.PlaceDecomp.decomp E F w := by
  rw [MulAction.mem_stabilizer_iff]
  apply le_antisymm (smul_valuationSubring_le E F w σ hσ)
  rw [ValuationSubring.subset_pointwise_smul_iff]
  apply smul_valuationSubring_le E F w σ⁻¹
  rw [← hσ, inv_smul_smul]
  exact hσ.symm

theorem stabilizer_le_decomp :
    MulAction.stabilizer (F ≃ₐ[E] F) w.asIdeal ≤ NumberField.PlaceDecomp.decomp E F w :=
  fun σ hσ => mem_decomp_of_smul_asIdeal_eq E F w σ hσ

theorem inertia_le_decomp :
    w.asIdeal.inertia (F ≃ₐ[E] F) ≤ NumberField.PlaceDecomp.decomp E F w :=
  (Ideal.inertia_le_stabilizer w.asIdeal).trans (stabilizer_le_decomp E F w)

theorem mem_decomp_of_isArithFrobAt [NumberField E] [IsGalois E F] {φ : F ≃ₐ[E] F} (hφ : IsArithFrobAt (𝓞 E) φ w.asIdeal) :
    φ ∈ NumberField.PlaceDecomp.decomp E F w :=
  stabilizer_le_decomp E F w (hφ.mem_stabilizer)

end M4aHerbrand.LocDec

end EngP2Decomp

open scoped IsMulCommutative in
open M4aHerbrand.LocDec _root_.M4aHerbrand _root_.P2MW.S_NumberField_PlaceDecomp_iSup_decomp_eq_top_of_isCyclic.M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin in
theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsCyclic (F ≃ₐ[E] F)] :
    (⨆ w : HeightOneSpectrum (𝓞 F), NumberField.PlaceDecomp.decomp E F w) = ⊤ := by
  classical
  haveI : IsMulCommutative (F ≃ₐ[E] F) := ⟨⟨fun a b => IsCyclic.commGroup.mul_comm a b⟩⟩
  obtain ⟨𝔯, h𝔯, hram⟩ := LanglandsTunnell.P2.Artin.exists_ne_bot_forall_inertia_primeAbove_ne_bot_dvd E F
  obtain ⟨𝔣, -, -, hadm⟩ :=
    LanglandsTunnell.P2.Artin.exists_dvd_and_isAdmissibleModulusOfDegree_of_ramified_dvd E F 𝔯 h𝔯 hram (Module.finrank E F)
  obtain ⟨r, hker, -, hsurj, hfrob⟩ :=
    NumberField.exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank E F 𝔣 hadm
  rw [eq_top_iff]
  rintro g -
  obtain ⟨u, rfl⟩ := hsurj g
  obtain ⟨α, hα⟩ := HeckeCharacter.exists_isAdjuster E 𝔣 hadm.1 u
  set pα : (AdeleRing (𝓞 E) E)ˣ := Units.map (algebraMap E (AdeleRing (𝓞 E) E) : E →* AdeleRing (𝓞 E) E) α with hpα
  have hmem : pα ∈ principalIdeles (𝓞 E) E := ⟨α, rfl⟩
  have hu' : IsAdjuster E 𝔣 (u * pα⁻¹) 1 := by
    have key : u * pα⁻¹ * (Units.map (algebraMap E (AdeleRing (𝓞 E) E) : E →* AdeleRing (𝓞 E) E) 1)⁻¹ = u * pα⁻¹ := by
      rw [map_one, inv_one, mul_one]
    exact ⟨fun v hv => by rw [key]; exact hα.cong v hv, fun τ => by rw [key]; exact hα.sign τ⟩
  have hru : r u = r (u * pα⁻¹) := by
    rw [map_mul, map_inv, show r pα = 1 from hker hmem, inv_one, mul_one]
  rw [hru, hfrob _ hu']
  refine finprod_induction (fun x => x ∈ ⨆ w : HeightOneSpectrum (𝓞 F), NumberField.PlaceDecomp.decomp E F w)
    (Subgroup.one_mem _) (fun x y hx hy => Subgroup.mul_mem _ hx hy) (fun v => ?_)
  apply Subgroup.zpow_mem
  let wv : HeightOneSpectrum (𝓞 F) :=
    ⟨primeAbove E F v, inferInstance, primeAbove_ne_bot E F v⟩
  exact Subgroup.mem_iSup_of_mem wv (mem_decomp_of_isArithFrobAt E F wv (isArithFrobAt_artinFrob E F v))

end S_NumberField_PlaceDecomp_iSup_decomp_eq_top_of_isCyclic
end P2MW
export P2MW.S_NumberField_PlaceDecomp_iSup_decomp_eq_top_of_isCyclic (solution)
