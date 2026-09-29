-- Prove2me | solution 1 for NumberField.LevelArith.exists_level_sUnitsRep_val_d_eq_of_sIdele_coboundary_of_map_eq_add_d
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/2d24c7ab-dcf6-5ef8-9c64-acca5807bb9b

import Mathlib
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelInflation
import Definitions.Def_GroupCohomology_ContinuousH2Inflation
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_NumberField_LevelArith_exists_le_unitsMap_genuineBaseChange_mem_sup_of_pow_mem
import Theorems.Thm_groupCohomology_exists_pow_smul_sub_d_mem_of_isPGroup_of_d_mem
import Theorems.Thm_NumberField_LevelArith_unitsMap_genuineBaseChange_mem_unitIdelesOutside_of_le
import Theorems.Thm_groupCohomology_inhomogeneousCochains_d_comp_res_apply
import Theorems.Thm_groupCohomology_inhomogeneousCochains_d_comp_apply
import Theorems.Thm_groupCohomology_inhomogeneousCochains_d_d_apply
import Theorems.Thm_M4aHerbrand_exists_hom_res_ideles_and_ideleClassGroup_injective_range_eq_invariants_of_isScalarTower
import Theorems.Thm_NumberField_SIdele_exists_hom_classObj_ideleClassGroup_injective_range_eq
import Theorems.Thm_M4aHerbrand_nonempty_ideleGaloisDescent
import Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_exists_mulDistribMulAction_smul_eq_classAct
import Theorems.Thm_NumberField_LevelArith_isGalois_levelField
import Theorems.Thm_NumberField_AdeleRing_finiteIndex_principalIdeles_sup_unitIdelesOutside
import Theorems.Thm_NumberField_AdeleRing_principalIdeles_inf_unitIdelesOutside_eq_map_unit
import Theorems.Thm_NumberField_SUnits_sUnits_eq_unit
import Theorems.Thm_NumberField_LevelArith_isPGroup_levelGal_of_isPGroup_quotient
import Theorems.Thm_NumberField_SIdele_exists_hom_ideles_apply_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_exists_level_sUnitsRep_val_d_eq_of_sIdele_coboundary_of_map_eq_add_d
p2m_attr_erase "instance" "NumberField.LevelArith.instCommGroupUnitsModPow instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "groupCohomology.coe_continuousH1SrMap_apply groupCohomology.continuousH2SrMap_continuousH2Srπ groupCohomology.coe_levelCocyclesSr₂Map NumberField.LevelArith.smul_mk NumberField.LevelArith.selmerRepInt_ρ_apply NumberField.LevelArith.selmerRepField_ρ_apply NumberField.LevelArith.unitsModPowMap_mk"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory groupCohomology ExtCitation NumberField IsDedekindDomain M4aHerbrand NumberField.LevelArith
open scoped NumberField.LevelArith NumberField.PlaceDecomp
open scoped NumberField.InfPlaceDecomp

set_option maxHeartbeats 51200000 in
theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥L]
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F]
    [IsGalois ↥L ↥(levelField L F hLF)] (hF : F.IsUnramifiedOutside S)
    (hG : IsPGroup p (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))

    (D : IdeleGaloisDescent (𝓞 ↥(levelField L F hLF)) ↥L ↥(levelField L F hLF))
    [MulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ]
    (hactI : ∀ (g : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) (x : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ), g • x = D.unitsAct g x)
    [MulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (IdeleClassGroup (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))]
    (hact : ∀ (g : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) (x : (IdeleClassGroup (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))), g • x = D.classAct g x)

    (π : (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ) ⟶ (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (IdeleClassGroup (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))))
    (hπ : ∀ x : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ, π.hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk x : (IdeleClassGroup (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))))

    (Φ : (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)) →+ Additive (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)
    (hΦinj : Function.Injective Φ)
    (hΦrange : Φ.range = (NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF) {w | w.under (𝓞 ↥L) ∈ (placesOverPrimesFinset ↥L S)}).toAddSubgroup)
    (hΦρ : ∀ (g : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) (y : (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))), Φ ((NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)).ρ g y) = Additive.ofMul (D.unitsAct g (Additive.toMul (Φ y))))
    (hΦdiag : ∀ x : (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)), Φ ((NumberField.SIdele.diag ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)).hom x) =
      Additive.ofMul (Units.map (algebraMap ↥(levelField L F hLF) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) : ↥(levelField L F hLF) →* AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) (NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) x)))

    (f₁ : (Fin 3 → (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) → (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)))
    (u : (Fin 2 → (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) → (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)))
    (hu : ((inhomogeneousCochains (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))).d 2 3).hom u = fun g => (NumberField.SIdele.diag ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)).hom (f₁ g))

    (ξ : (Fin 2 → (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) → (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ))
    (hξ : ((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)).d 2 3).hom ξ = 0)
    (hξS : ∀ g : Fin 2 → (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)), (Additive.toMul (ξ g) : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ) ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF) {w | w.under (𝓞 ↥L) ∈ (placesOverPrimesFinset ↥L S)})
    (ν : (Fin 1 → (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) → (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (IdeleClassGroup (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))))
    (hkill : ∀ g : Fin 2 → (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)), π.hom (Φ (u g)) = π.hom (ξ g) + ((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (IdeleClassGroup (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)))).d 1 2).hom ν g) :
    ∃ (F₂ : IntermediateField ℚ (AlgebraicClosure ℚ)) (hfd : FiniteDimensional ℚ ↥F₂) (_ : F₂.IsUnramifiedOutside S) (_ : IsGalois ℚ ↥F₂)
      (hFF₂ : F ≤ F₂),
      haveI := hfd
      ∃ e₂ : (Fin 2 → (↥(levelField L F₂ (hLF.trans hFF₂)) ≃ₐ[↥L] ↥(levelField L F₂ (hLF.trans hFF₂)))) → (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S)),
        ∀ (g₂ : Fin 3 → (↥(levelField L F₂ (hLF.trans hFF₂)) ≃ₐ[↥L] ↥(levelField L F₂ (hLF.trans hFF₂)))) (g₀ : Fin 3 → ↥L.fixingSubgroup),
          (∀ (i : Fin 3) (x : ↥(levelField L F₂ (hLF.trans hFF₂))), (((g₂ i) x : ↥(levelField L F₂ (hLF.trans hFF₂))) : AlgebraicClosure ℚ) = ((g₀ i : ↥L.fixingSubgroup) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : AlgebraicClosure ℚ)) →
          ((NumberField.SUnits.val ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S) (((inhomogeneousCochains (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S))).d 2 3).hom e₂ (fun i => g₂ i)) : ↥(levelField L F₂ (hLF.trans hFF₂))) : AlgebraicClosure ℚ)
            = ((NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) (f₁ (fun i => levelGal L F hLF (g₀ i))) : ↥(levelField L F hLF)) : AlgebraicClosure ℚ) := by
  classical

  obtain ⟨F₂, hfd₂, hF₂, hgal₂, hFF₂, hcap⟩ :=
    NumberField.LevelArith.exists_le_unitsMap_genuineBaseChange_mem_sup_of_pow_mem S hpS L F hLF hF
  haveI := hfd₂
  haveI := hgal₂
  refine ⟨F₂, hfd₂, hF₂, hgal₂, hFF₂, ?_⟩

  have hKK₂ : ∀ x : ↥(levelField L F hLF), (x : AlgebraicClosure ℚ) ∈ levelField L F₂ (hLF.trans hFF₂) := fun x =>
    (IntermediateField.mem_extendScalars (hLF.trans hFF₂)).2 (hFF₂ ((IntermediateField.mem_extendScalars hLF).1 x.2))
  letI algKK₂ : Algebra ↥(levelField L F hLF) ↥(levelField L F₂ (hLF.trans hFF₂)) :=
    (({ toFun := fun x => ⟨(x : AlgebraicClosure ℚ), hKK₂ x⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
        map_zero' := rfl, map_add' := fun _ _ => rfl } : ↥(levelField L F hLF) →+* ↥(levelField L F₂ (hLF.trans hFF₂)))).toAlgebra
  haveI towLKK₂ : IsScalarTower ↥L ↥(levelField L F hLF) ↥(levelField L F₂ (hLF.trans hFF₂)) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have halg0 : ∀ x : ↥(levelField L F hLF), ((algebraMap ↥(levelField L F hLF) ↥(levelField L F₂ (hLF.trans hFF₂)) x : ↥(levelField L F₂ (hLF.trans hFF₂))) : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ) := fun _ => rfl
  haveI galLK₂ : IsGalois ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) := NumberField.LevelArith.isGalois_levelField L F₂ (hLF.trans hFF₂)

  obtain ⟨DM⟩ := M4aHerbrand.nonempty_ideleGaloisDescent ↥L ↥(levelField L F₂ (hLF.trans hFF₂))
  letI instIM : MulDistribMulAction (↥(levelField L F₂ (hLF.trans hFF₂)) ≃ₐ[↥L] ↥(levelField L F₂ (hLF.trans hFF₂))) (AdeleRing (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂))) ↥(levelField L F₂ (hLF.trans hFF₂)))ˣ := MulDistribMulAction.compHom _ DM.unitsAct
  have hactIM : ∀ (g : ↥(levelField L F₂ (hLF.trans hFF₂)) ≃ₐ[↥L] ↥(levelField L F₂ (hLF.trans hFF₂))) (x : (AdeleRing (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂))) ↥(levelField L F₂ (hLF.trans hFF₂)))ˣ), g • x = DM.unitsAct g x := fun _ _ => rfl
  obtain ⟨instCM, hactM⟩ := M4aHerbrand.IdeleGaloisDescent.exists_mulDistribMulAction_smul_eq_classAct ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) DM
  letI := instCM
  let rN : (↥(levelField L F₂ (hLF.trans hFF₂)) ≃ₐ[↥L] ↥(levelField L F₂ (hLF.trans hFF₂))) →* (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) := AlgEquiv.restrictNormalHom ↥(levelField L F hLF)
  have hrN : Function.Surjective rN := AlgEquiv.restrictNormalHom_surjective ↥(levelField L F₂ (hLF.trans hFF₂))
  haveI : rN.ker.Normal := MonoidHom.normal_ker rN
  let ιq : (↥(levelField L F₂ (hLF.trans hFF₂)) ≃ₐ[↥L] ↥(levelField L F₂ (hLF.trans hFF₂))) ⧸ rN.ker ≃* (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) := QuotientGroup.quotientKerEquivOfSurjective rN hrN
  have hιq : ∀ (g : ↥(levelField L F₂ (hLF.trans hFF₂)) ≃ₐ[↥L] ↥(levelField L F₂ (hLF.trans hFF₂))) (x : ↥(levelField L F hLF)), algebraMap ↥(levelField L F hLF) ↥(levelField L F₂ (hLF.trans hFF₂)) (ιq (QuotientGroup.mk g) x) = g (algebraMap ↥(levelField L F hLF) ↥(levelField L F₂ (hLF.trans hFF₂)) x) := by
    intro g x
    have : ιq (QuotientGroup.mk g) = rN g := QuotientGroup.kerLift_mk rN g
    rw [this]
    exact AlgEquiv.restrictNormal_commutes g ↥(levelField L F hLF) x
  obtain ⟨J, j, hJ, hj, hjinj, hjrange⟩ :=
    M4aHerbrand.exists_hom_res_ideles_and_ideleClassGroup_injective_range_eq_invariants_of_isScalarTower ↥L ↥(levelField L F hLF) ↥(levelField L F₂ (hLF.trans hFF₂))
      D DM hactI hact hactIM hactM rN.ker ιq hιq

  obtain ⟨Φ₂, -, hΦ₂inj, hΦ₂range, hΦ₂ρ, hΦ₂diag, -, -, -⟩ :=
    NumberField.SIdele.exists_hom_classObj_ideleClassGroup_injective_range_eq ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S) DM hactM
  obtain ⟨hpresI, hpresU⟩ :=
    NumberField.LevelArith.unitsMap_genuineBaseChange_mem_unitIdelesOutside_of_le S L F hLF L F₂ le_rfl (hLF.trans hFF₂) hFF₂ halg0

  have hmemT : ∀ y : (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)), J.hom (Φ y) ∈ Φ₂.range := fun y => by
    have hy : Additive.toMul (Φ y) ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF) {w | w.under (𝓞 ↥L) ∈ (placesOverPrimesFinset ↥L S)} := by
      have : Φ y ∈ Φ.range := ⟨y, rfl⟩
      rw [hΦrange] at this
      exact this
    have h2 := hpresI (Additive.toMul (Φ y)) hy
    rw [hΦ₂range]
    have h3 : J.hom (Φ y) = Additive.ofMul (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange ↥(levelField L F hLF) ↥(levelField L F₂ (hLF.trans hFF₂))).β.toMonoidHom (Additive.toMul (Φ y))) := hJ _
    rw [h3]
    exact h2
  obtain ⟨T, hT⟩ : ∃ T : (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)) →+ (NumberField.SIdele.obj ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S)), ∀ y, Φ₂ (T y) = J.hom (Φ y) :=
    ⟨(AddMonoidHom.ofInjective hΦ₂inj).symm.toAddMonoidHom.comp ((J.hom.toAddMonoidHom.comp Φ).codRestrict Φ₂.range hmemT),
      fun y => AddMonoidHom.apply_ofInjective_symm hΦ₂inj ⟨_, hmemT y⟩⟩
  choose incl hincl using hpresU
  have hιqr : ∀ g : (↥(levelField L F₂ (hLF.trans hFF₂)) ≃ₐ[↥L] ↥(levelField L F₂ (hLF.trans hFF₂))), (ιq.toMonoidHom.comp (QuotientGroup.mk' rN.ker)) g = rN g := fun g => QuotientGroup.kerLift_mk rN g
  have hTρ : ∀ (g : (↥(levelField L F₂ (hLF.trans hFF₂)) ≃ₐ[↥L] ↥(levelField L F₂ (hLF.trans hFF₂)))) (y : (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))), T ((NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)).ρ (rN g) y) = (NumberField.SIdele.obj ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S)).ρ g (T y) := by
    intro g y
    apply hΦ₂inj
    rw [hT, hΦρ, hΦ₂ρ, hT]
    have h1 : J.hom ((Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ).ρ (rN g) (Φ y)) =
        (Rep.ofMulDistribMulAction (↥(levelField L F₂ (hLF.trans hFF₂)) ≃ₐ[↥L] ↥(levelField L F₂ (hLF.trans hFF₂))) (AdeleRing (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂))) ↥(levelField L F₂ (hLF.trans hFF₂)))ˣ).ρ g (J.hom (Φ y)) := Rep.hom_comm_apply J g (Φ y)
    have h2 : (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ).ρ (rN g) (Φ y) =
        Additive.ofMul (D.unitsAct (rN g) (Additive.toMul (Φ y))) := by
      rw [Rep.ofMulDistribMulAction_ρ_apply_apply, hactI]
    have h3 : (Rep.ofMulDistribMulAction (↥(levelField L F₂ (hLF.trans hFF₂)) ≃ₐ[↥L] ↥(levelField L F₂ (hLF.trans hFF₂))) (AdeleRing (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂))) ↥(levelField L F₂ (hLF.trans hFF₂)))ˣ).ρ g (J.hom (Φ y)) = Additive.ofMul (DM.unitsAct g (Additive.toMul (J.hom (Φ y)))) := by
      rw [Rep.ofMulDistribMulAction_ρ_apply_apply]; rfl
    rw [← h2, h1, h3]
  have hTdiag : ∀ x : (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)), T ((NumberField.SIdele.diag ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)).hom x) = (NumberField.SIdele.diag ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S)).hom (incl x) := by
    intro x
    apply hΦ₂inj
    rw [hT, hΦdiag]
    refine (hJ _).trans ?_
    rw [hΦ₂diag, hincl]
    congr 1
    ext
    change (M4aHerbrand.GenuineDescent.genuineBaseChange ↥(levelField L F hLF) ↥(levelField L F₂ (hLF.trans hFF₂))).β (algebraMap ↥(levelField L F hLF) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) (NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) x : ↥(levelField L F hLF))) = _
    rw [(M4aHerbrand.GenuineDescent.genuineBaseChange ↥(levelField L F hLF) ↥(levelField L F₂ (hLF.trans hFF₂))).β_compat]
    rfl

  have hπsurj : Function.Surjective π.hom := fun c => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective (Additive.toMul c)
    exact ⟨Additive.ofMul x, hπ x⟩
  choose νt hνt using fun g : Fin 1 → (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) => hπsurj (ν g)
  have hker : ∀ g : Fin 2 → (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)), ∃ a : (↥(levelField L F hLF))ˣ,
      Additive.toMul (Φ (u g)) = (Additive.toMul (ξ g) : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ) * (Additive.toMul (((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)).d 1 2).hom νt g) : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ) *
        Units.map (algebraMap ↥(levelField L F hLF) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) : ↥(levelField L F hLF) →* AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) a := by
    intro g
    let ΦR : (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)) →+ (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ) := Φ
    have hΦR : ∀ y, ΦR y = Φ y := fun _ => rfl
    have hνfun : (fun g => π.hom (νt g)) = ν := funext hνt
    have hdπ : π.hom (((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)).d 1 2).hom νt g) = ((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (IdeleClassGroup (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)))).d 1 2).hom ν g := by
      have := congrFun (groupCohomology.inhomogeneousCochains_d_comp_apply π 1 νt) g
      rw [hνfun] at this
      exact this.symm
    have hz : π.hom (ΦR (u g) - ξ g - ((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)).d 1 2).hom νt g) = 0 := by
      rw [map_sub, map_sub]
      have hk := hkill g
      change π.hom (ΦR (u g)) = _ at hk
      rw [hk, hdπ, add_sub_cancel_left, sub_self]

    set z : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ := Additive.toMul (ΦR (u g) - ξ g - ((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)).d 1 2).hom νt g) with hzdef
    have hz1 : (QuotientGroup.mk z : (IdeleClassGroup (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))) = 1 := by
      have h0 : Additive.ofMul (QuotientGroup.mk z : (IdeleClassGroup (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))) = 0 := (hπ z).symm.trans hz
      exact Additive.ofMul.injective (h0.trans ofMul_one.symm)
    obtain ⟨c, hc⟩ := (QuotientGroup.eq_one_iff z).1 hz1
    refine ⟨c, ?_⟩
    have : (Additive.toMul (Φ (u g)) : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ) = z * ((Additive.toMul (ξ g) : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ) * (Additive.toMul (((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)).d 1 2).hom νt g) : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)) := by
      apply Additive.ofMul.injective
      simp only [hzdef, ofMul_mul, ofMul_toMul, ← hΦR]
      abel
    rw [this, ← hc, mul_comm]
  choose a ha using hker

  have hWst : ∀ (g : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) (x : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ), x ∈ (M4aHerbrand.principalIdeles (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF) ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF) {w | w.under (𝓞 ↥L) ∈ (placesOverPrimesFinset ↥L S)}) → D.unitsAct g x ∈ (M4aHerbrand.principalIdeles (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF) ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF) {w | w.under (𝓞 ↥L) ∈ (placesOverPrimesFinset ↥L S)}) := by
    intro g x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hx
    rw [map_mul]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ?_)
    · rw [← D.map_principalIdeles g]
      exact Subgroup.mem_map_of_mem _ hy
    · have hz' : Additive.ofMul z ∈ Φ.range := by rw [hΦrange]; exact hz
      obtain ⟨w, hw⟩ := hz'
      have : Φ ((NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)).ρ g w) ∈ Φ.range := ⟨_, rfl⟩
      rw [hΦρ, hw, hΦrange] at this
      exact this
  have hUS : ∀ y : (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)), (Additive.toMul (Φ y) : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ) ∈ (M4aHerbrand.principalIdeles (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF) ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF) {w | w.under (𝓞 ↥L) ∈ (placesOverPrimesFinset ↥L S)}) := fun y => by
    apply Subgroup.mem_sup_right
    have : Φ y ∈ Φ.range := ⟨y, rfl⟩
    rw [hΦrange] at this
    exact this
  have hνW : ∀ g : Fin 2 → (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)), (Additive.toMul (((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)).d 1 2).hom νt g) : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ) ∈ (M4aHerbrand.principalIdeles (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF) ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF) {w | w.under (𝓞 ↥L) ∈ (placesOverPrimesFinset ↥L S)}) := by
    intro g
    have h1 := ha g
    have h2 : (Additive.toMul (((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)).d 1 2).hom νt g) : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ) =
        Additive.toMul (Φ (u g)) * ((Additive.toMul (ξ g) : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ) *
          Units.map (algebraMap ↥(levelField L F hLF) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) : ↥(levelField L F hLF) →* AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) (a g))⁻¹ := by
      apply Additive.ofMul.injective
      have h1' := congrArg Additive.ofMul h1
      simp only [ofMul_mul, ofMul_inv] at h1' ⊢
      rw [h1']; abel
    rw [h2]
    refine Subgroup.mul_mem _ (hUS _) (Subgroup.inv_mem _ (Subgroup.mul_mem _ ?_ ?_))
    · exact Subgroup.mem_sup_right (hξS g)
    · exact Subgroup.mem_sup_left ⟨a g, rfl⟩

  haveI hfin : (M4aHerbrand.principalIdeles (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF) ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF) {w | w.under (𝓞 ↥L) ∈ (placesOverPrimesFinset ↥L S)}).FiniteIndex :=
    NumberField.AdeleRing.finiteIndex_principalIdeles_sup_unitIdelesOutside ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)
  let WA : AddSubgroup (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ) := (Subgroup.toAddSubgroup (M4aHerbrand.principalIdeles (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF) ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF) {w | w.under (𝓞 ↥L) ∈ (placesOverPrimesFinset ↥L S)}) : AddSubgroup (Additive (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ))
  have hWA : ∀ x : (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ), x ∈ WA ↔ (Additive.toMul x : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ) ∈ (M4aHerbrand.principalIdeles (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF) ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF) {w | w.under (𝓞 ↥L) ∈ (placesOverPrimesFinset ↥L S)}) := fun _ => Iff.rfl
  haveI hfin' : WA.FiniteIndex := ⟨hfin.index_ne_zero⟩
  have hGK : IsPGroup p (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) := NumberField.LevelArith.isPGroup_levelGal_of_isPGroup_quotient p L F hLF hG
  obtain ⟨m, k, hm⟩ := groupCohomology.exists_pow_smul_sub_d_mem_of_isPGroup_of_d_mem p hGK (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ) WA
    (fun g x hx => by
      rw [hWA] at hx ⊢
      rw [Rep.ofMulDistribMulAction_ρ_apply_apply, hactI]
      exact hWst g _ hx) νt (fun g => (hWA _).2 (hνW g))

  have hcapν : ∀ g : Fin 1 → (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)),
      Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange ↥(levelField L F hLF) ↥(levelField L F₂ (hLF.trans hFF₂))).β.toMonoidHom (Additive.toMul (νt g - ((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)).d 0 1).hom m g)) ∈ (M4aHerbrand.principalIdeles (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂))) ↥(levelField L F₂ (hLF.trans hFF₂)) ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂))) ↥(levelField L F₂ (hLF.trans hFF₂)) {w | w.under (𝓞 ↥L) ∈ (placesOverPrimesFinset ↥L S)}) := fun g =>
    hcap halg0 _ ⟨k, by
      have h1 := hm g
      rw [hWA] at h1
      have e : ∀ (zz : ℤ) (y : (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)), (Additive.toMul (zz • y) : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ) = (Additive.toMul y : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ) ^ zz :=
        fun zz y => toMul_zsmul (α := (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ) zz y
      rw [e] at h1
      exact_mod_cast h1⟩

  have hν'cap : ∀ g : Fin 1 → (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)), ∃ (kk : (↥(levelField L F₂ (hLF.trans hFF₂)))ˣ) (jj : (NumberField.SIdele.obj ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S))),
      Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange ↥(levelField L F hLF) ↥(levelField L F₂ (hLF.trans hFF₂))).β.toMonoidHom (Additive.toMul (νt g - ((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)).d 0 1).hom m g)) =
        (Units.map (algebraMap ↥(levelField L F₂ (hLF.trans hFF₂)) (AdeleRing (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂))) ↥(levelField L F₂ (hLF.trans hFF₂))) : ↥(levelField L F₂ (hLF.trans hFF₂)) →* AdeleRing (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂))) ↥(levelField L F₂ (hLF.trans hFF₂)))) kk * Additive.toMul (Φ₂ jj) := fun g => by
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.1 (hcapν g)
    obtain ⟨kk, rfl⟩ := hy
    have hz' : Additive.ofMul z ∈ Φ₂.range := by rw [hΦ₂range]; exact hz
    obtain ⟨jj, hjj⟩ := hz'
    exact ⟨kk, jj, by rw [← hyz, hjj]; rfl⟩
  choose kk jj hkj using hν'cap

  have hξJ : ∀ g : Fin 2 → (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)), ∃ y : (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)), Φ y = ξ g := fun g => by
    have : Additive.ofMul (Additive.toMul (ξ g) : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ) ∈ Φ.range := by rw [hΦrange]; exact hξS g
    obtain ⟨y, hy⟩ := this
    exact ⟨y, hy⟩
  choose ξJ hξJ' using hξJ

  have hJρ : ∀ (g : (↥(levelField L F₂ (hLF.trans hFF₂)) ≃ₐ[↥L] ↥(levelField L F₂ (hLF.trans hFF₂)))) (x : (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)), J.hom ((Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ).ρ (rN g) x) = (Rep.ofMulDistribMulAction (↥(levelField L F₂ (hLF.trans hFF₂)) ≃ₐ[↥L] ↥(levelField L F₂ (hLF.trans hFF₂))) (AdeleRing (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂))) ↥(levelField L F₂ (hLF.trans hFF₂)))ˣ).ρ g (J.hom x) := fun g x =>
    Rep.hom_comm_apply J g x

  have hstar : ∀ g : Fin 2 → (↥(levelField L F₂ (hLF.trans hFF₂)) ≃ₐ[↥L] ↥(levelField L F₂ (hLF.trans hFF₂))),
      Φ₂ (T (u (rN ∘ g))) = J.hom (ξ (rN ∘ g)) + ((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(levelField L F₂ (hLF.trans hFF₂)) ≃ₐ[↥L] ↥(levelField L F₂ (hLF.trans hFF₂))) (AdeleRing (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂))) ↥(levelField L F₂ (hLF.trans hFF₂)))ˣ)).d 1 2).hom (fun g₁ => J.hom (νt (rN ∘ g₁) - ((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)).d 0 1).hom m (rN ∘ g₁))) g +
        J.hom (Additive.ofMul ((Units.map (algebraMap ↥(levelField L F hLF) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) : ↥(levelField L F hLF) →* AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))) (a (rN ∘ g)))) := by
    intro g

    have hdm : ((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)).d 1 2).hom (fun g₁ => νt g₁ - ((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)).d 0 1).hom m g₁) = ((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)).d 1 2).hom νt := by
      change ((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)).d 1 2).hom (νt - ((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)).d 0 1).hom m) = _
      rw [map_sub]
      have : ((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)).d 1 2).hom (((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)).d 0 1).hom m) = 0 :=
        groupCohomology.inhomogeneousCochains_d_d_apply (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ) 0 m
      rw [this, sub_zero]
    have hnat : ((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(levelField L F₂ (hLF.trans hFF₂)) ≃ₐ[↥L] ↥(levelField L F₂ (hLF.trans hFF₂))) (AdeleRing (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂))) ↥(levelField L F₂ (hLF.trans hFF₂)))ˣ)).d 1 2).hom (fun g₁ => J.hom (νt (rN ∘ g₁) - ((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)).d 0 1).hom m (rN ∘ g₁))) g =
        J.hom (((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)).d 1 2).hom (fun g₁ => νt g₁ - ((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)).d 0 1).hom m g₁) (rN ∘ g)) :=
      congrFun (groupCohomology.inhomogeneousCochains_d_comp_res_apply rN J.hom.toAddMonoidHom
        (fun h x => hJρ h x) 1 (fun g₁ => νt g₁ - ((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)).d 0 1).hom m g₁)) g
    rw [hnat, hdm, hT]
    have h1 := congrArg Additive.ofMul (ha (rN ∘ g))
    simp only [ofMul_mul, ofMul_toMul] at h1

    rw [← map_add, ← map_add]
    congr 1

  let ofU : (↥(levelField L F₂ (hLF.trans hFF₂)))ˣ → (Rep.ofMulDistribMulAction (↥(levelField L F₂ (hLF.trans hFF₂)) ≃ₐ[↥L] ↥(levelField L F₂ (hLF.trans hFF₂))) (↥(levelField L F₂ (hLF.trans hFF₂)))ˣ) := fun c => Additive.ofMul c
  let Φ₂A : (NumberField.SIdele.obj ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S)) →+ (Rep.ofMulDistribMulAction (↥(levelField L F₂ (hLF.trans hFF₂)) ≃ₐ[↥L] ↥(levelField L F₂ (hLF.trans hFF₂))) (AdeleRing (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂))) ↥(levelField L F₂ (hLF.trans hFF₂)))ˣ) := Φ₂
  have hΦ₂A : ∀ y, Φ₂A y = Φ₂ y := fun _ => rfl
  let princA : (Rep.ofMulDistribMulAction (↥(levelField L F₂ (hLF.trans hFF₂)) ≃ₐ[↥L] ↥(levelField L F₂ (hLF.trans hFF₂))) (↥(levelField L F₂ (hLF.trans hFF₂)))ˣ) →+ (Rep.ofMulDistribMulAction (↥(levelField L F₂ (hLF.trans hFF₂)) ≃ₐ[↥L] ↥(levelField L F₂ (hLF.trans hFF₂))) (AdeleRing (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂))) ↥(levelField L F₂ (hLF.trans hFF₂)))ˣ) := (MonoidHom.toAdditive (Units.map (algebraMap ↥(levelField L F₂ (hLF.trans hFF₂)) (AdeleRing (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂))) ↥(levelField L F₂ (hLF.trans hFF₂))) : ↥(levelField L F₂ (hLF.trans hFF₂)) →* AdeleRing (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂))) ↥(levelField L F₂ (hLF.trans hFF₂)))) : Additive (↥(levelField L F₂ (hLF.trans hFF₂)))ˣ →+ Additive (AdeleRing (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂))) ↥(levelField L F₂ (hLF.trans hFF₂)))ˣ)
  have hprincA : ∀ c : (↥(levelField L F₂ (hLF.trans hFF₂)))ˣ, princA (ofU c) = Additive.ofMul ((Units.map (algebraMap ↥(levelField L F₂ (hLF.trans hFF₂)) (AdeleRing (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂))) ↥(levelField L F₂ (hLF.trans hFF₂))) : ↥(levelField L F₂ (hLF.trans hFF₂)) →* AdeleRing (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂))) ↥(levelField L F₂ (hLF.trans hFF₂)))) c) := fun _ => rfl
  have hPρ : ∀ (g : (↥(levelField L F₂ (hLF.trans hFF₂)) ≃ₐ[↥L] ↥(levelField L F₂ (hLF.trans hFF₂)))) (c : (Rep.ofMulDistribMulAction (↥(levelField L F₂ (hLF.trans hFF₂)) ≃ₐ[↥L] ↥(levelField L F₂ (hLF.trans hFF₂))) (↥(levelField L F₂ (hLF.trans hFF₂)))ˣ)), princA ((Rep.ofMulDistribMulAction (↥(levelField L F₂ (hLF.trans hFF₂)) ≃ₐ[↥L] ↥(levelField L F₂ (hLF.trans hFF₂))) (↥(levelField L F₂ (hLF.trans hFF₂)))ˣ).ρ g c) = (Rep.ofMulDistribMulAction (↥(levelField L F₂ (hLF.trans hFF₂)) ≃ₐ[↥L] ↥(levelField L F₂ (hLF.trans hFF₂))) (AdeleRing (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂))) ↥(levelField L F₂ (hLF.trans hFF₂)))ˣ).ρ g (princA c) := by
    intro g c
    rw [Rep.ofMulDistribMulAction_ρ_apply_apply, Rep.ofMulDistribMulAction_ρ_apply_apply, hactIM]
    change Additive.ofMul ((Units.map (algebraMap ↥(levelField L F₂ (hLF.trans hFF₂)) (AdeleRing (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂))) ↥(levelField L F₂ (hLF.trans hFF₂))) : ↥(levelField L F₂ (hLF.trans hFF₂)) →* AdeleRing (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂))) ↥(levelField L F₂ (hLF.trans hFF₂)))) (g • (Additive.toMul c : (↥(levelField L F₂ (hLF.trans hFF₂)))ˣ))) = Additive.ofMul (DM.unitsAct g ((Units.map (algebraMap ↥(levelField L F₂ (hLF.trans hFF₂)) (AdeleRing (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂))) ↥(levelField L F₂ (hLF.trans hFF₂))) : ↥(levelField L F₂ (hLF.trans hFF₂)) →* AdeleRing (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂))) ↥(levelField L F₂ (hLF.trans hFF₂)))) (Additive.toMul c : (↥(levelField L F₂ (hLF.trans hFF₂)))ˣ)))
    congr 1
    ext
    exact (DM.compat g _).symm
  have hΦ₂ρ' : ∀ (g : (↥(levelField L F₂ (hLF.trans hFF₂)) ≃ₐ[↥L] ↥(levelField L F₂ (hLF.trans hFF₂)))) (y : (NumberField.SIdele.obj ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S))), Φ₂A ((NumberField.SIdele.obj ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S)).ρ g y) = (Rep.ofMulDistribMulAction (↥(levelField L F₂ (hLF.trans hFF₂)) ≃ₐ[↥L] ↥(levelField L F₂ (hLF.trans hFF₂))) (AdeleRing (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂))) ↥(levelField L F₂ (hLF.trans hFF₂)))ˣ).ρ g (Φ₂A y) := by
    intro g y
    rw [hΦ₂A, hΦ₂A, hΦ₂ρ, Rep.ofMulDistribMulAction_ρ_apply_apply, hactIM]
  let princR : (Rep.ofMulDistribMulAction (↥(levelField L F₂ (hLF.trans hFF₂)) ≃ₐ[↥L] ↥(levelField L F₂ (hLF.trans hFF₂))) (↥(levelField L F₂ (hLF.trans hFF₂)))ˣ) ⟶ (Rep.ofMulDistribMulAction (↥(levelField L F₂ (hLF.trans hFF₂)) ≃ₐ[↥L] ↥(levelField L F₂ (hLF.trans hFF₂))) (AdeleRing (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂))) ↥(levelField L F₂ (hLF.trans hFF₂)))ˣ) := Rep.ofHom ⟨princA.toIntLinearMap, fun g => LinearMap.ext fun c => hPρ g c⟩
  have hprincR : ∀ c, princR.hom c = princA c := fun _ => rfl
  obtain ⟨Φ₂R, hΦ₂R⟩ := NumberField.SIdele.exists_hom_ideles_apply_eq ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S) DM hactIM Φ₂ hΦ₂ρ

  have hN₂ : (fun g₁ : Fin 1 → (↥(levelField L F₂ (hLF.trans hFF₂)) ≃ₐ[↥L] ↥(levelField L F₂ (hLF.trans hFF₂))) => J.hom (νt (rN ∘ g₁) - ((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)).d 0 1).hom m (rN ∘ g₁))) =
      (fun g₁ => princR.hom (ofU (kk (rN ∘ g₁)))) + fun g₁ => Φ₂R.hom (jj (rN ∘ g₁)) := by
    funext g₁
    simp only [Pi.add_apply]
    have e1 : J.hom (νt (rN ∘ g₁) - ((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)).d 0 1).hom m (rN ∘ g₁)) =
        Additive.ofMul ((Units.map (algebraMap ↥(levelField L F₂ (hLF.trans hFF₂)) (AdeleRing (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂))) ↥(levelField L F₂ (hLF.trans hFF₂))) : ↥(levelField L F₂ (hLF.trans hFF₂)) →* AdeleRing (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂))) ↥(levelField L F₂ (hLF.trans hFF₂)))) (kk (rN ∘ g₁)) * Additive.toMul (Φ₂ (jj (rN ∘ g₁)))) :=
      (hJ _).trans (congrArg Additive.ofMul (hkj (rN ∘ g₁)))
    rw [e1, ofMul_mul, hΦ₂R, hprincR, hprincA]
    rfl

  have hJprinc : ∀ c : (↥(levelField L F hLF))ˣ, J.hom (Additive.ofMul ((Units.map (algebraMap ↥(levelField L F hLF) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) : ↥(levelField L F hLF) →* AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))) c)) =
      princR.hom (ofU (Units.map (algebraMap ↥(levelField L F hLF) ↥(levelField L F₂ (hLF.trans hFF₂)) : ↥(levelField L F hLF) →* ↥(levelField L F₂ (hLF.trans hFF₂))) c)) := fun c => by
    rw [hJ, hprincR, hprincA]
    congr 1
    ext
    change (M4aHerbrand.GenuineDescent.genuineBaseChange ↥(levelField L F hLF) ↥(levelField L F₂ (hLF.trans hFF₂))).β (algebraMap ↥(levelField L F hLF) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) (c : ↥(levelField L F hLF))) = _
    rw [(M4aHerbrand.GenuineDescent.genuineBaseChange ↥(levelField L F hLF) ↥(levelField L F₂ (hLF.trans hFF₂))).β_compat]
    rfl

  have hstar2 : ∀ g : Fin 2 → (↥(levelField L F₂ (hLF.trans hFF₂)) ≃ₐ[↥L] ↥(levelField L F₂ (hLF.trans hFF₂))),
      Φ₂R.hom (T (u (rN ∘ g)) - T (ξJ (rN ∘ g)) - ((inhomogeneousCochains (NumberField.SIdele.obj ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S))).d 1 2).hom (fun g₁ => jj (rN ∘ g₁)) g) =
        princR.hom (((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(levelField L F₂ (hLF.trans hFF₂)) ≃ₐ[↥L] ↥(levelField L F₂ (hLF.trans hFF₂))) (↥(levelField L F₂ (hLF.trans hFF₂)))ˣ)).d 1 2).hom (fun g₁ => ofU (kk (rN ∘ g₁))) g +
          ofU (Units.map (algebraMap ↥(levelField L F hLF) ↥(levelField L F₂ (hLF.trans hFF₂)) : ↥(levelField L F hLF) →* ↥(levelField L F₂ (hLF.trans hFF₂))) (a (rN ∘ g)))) := by
    intro g
    have e2 : J.hom (ξ (rN ∘ g)) = Φ₂R.hom (T (ξJ (rN ∘ g))) := by
      rw [hΦ₂R, hT, hξJ']
    have e3 := hJprinc (a (rN ∘ g))
    have e4 : ((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(levelField L F₂ (hLF.trans hFF₂)) ≃ₐ[↥L] ↥(levelField L F₂ (hLF.trans hFF₂))) (AdeleRing (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂))) ↥(levelField L F₂ (hLF.trans hFF₂)))ˣ)).d 1 2).hom (fun g₁ => J.hom (νt (rN ∘ g₁) - ((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)).d 0 1).hom m (rN ∘ g₁))) g =
        princR.hom (((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(levelField L F₂ (hLF.trans hFF₂)) ≃ₐ[↥L] ↥(levelField L F₂ (hLF.trans hFF₂))) (↥(levelField L F₂ (hLF.trans hFF₂)))ˣ)).d 1 2).hom (fun g₁ => ofU (kk (rN ∘ g₁))) g) +
          Φ₂R.hom (((inhomogeneousCochains (NumberField.SIdele.obj ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S))).d 1 2).hom (fun g₁ => jj (rN ∘ g₁)) g) := by
      rw [hN₂, map_add, Pi.add_apply,
        groupCohomology.inhomogeneousCochains_d_comp_apply princR 1 (fun g₁ => ofU (kk (rN ∘ g₁))),
        groupCohomology.inhomogeneousCochains_d_comp_apply Φ₂R 1 (fun g₁ => jj (rN ∘ g₁))]
    have h := hstar g
    rw [e2, e3, e4] at h
    rw [map_sub, map_sub, hΦ₂R (T (u (rN ∘ g))), h, map_add]
    abel

  have hEex : ∀ g : Fin 2 → (↥(levelField L F₂ (hLF.trans hFF₂)) ≃ₐ[↥L] ↥(levelField L F₂ (hLF.trans hFF₂))), ∃ ee : (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S)),
      (NumberField.SIdele.diag ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S)).hom ee = T (u (rN ∘ g)) - T (ξJ (rN ∘ g)) - ((inhomogeneousCochains (NumberField.SIdele.obj ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S))).d 1 2).hom (fun g₁ => jj (rN ∘ g₁)) g := by
    intro g
    have h1 := congrArg (fun z : (Rep.ofMulDistribMulAction (↥(levelField L F₂ (hLF.trans hFF₂)) ≃ₐ[↥L] ↥(levelField L F₂ (hLF.trans hFF₂))) (AdeleRing (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂))) ↥(levelField L F₂ (hLF.trans hFF₂)))ˣ) => (Additive.toMul z : (AdeleRing (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂))) ↥(levelField L F₂ (hLF.trans hFF₂)))ˣ)) (hstar2 g)
    simp only [hΦ₂R, hprincR] at h1

    have h2 : (Additive.toMul (Φ₂ (T (u (rN ∘ g)) - T (ξJ (rN ∘ g)) - ((inhomogeneousCochains (NumberField.SIdele.obj ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S))).d 1 2).hom (fun g₁ => jj (rN ∘ g₁)) g)) : (AdeleRing (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂))) ↥(levelField L F₂ (hLF.trans hFF₂)))ˣ) ∈
        M4aHerbrand.principalIdeles (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂))) ↥(levelField L F₂ (hLF.trans hFF₂)) ⊓ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂))) ↥(levelField L F₂ (hLF.trans hFF₂)) {w | w.under (𝓞 ↥L) ∈ (placesOverPrimesFinset ↥L S)} := by
      refine ⟨?_, ?_⟩
      · rw [h1]; exact ⟨_, rfl⟩
      · have : Φ₂ (T (u (rN ∘ g)) - T (ξJ (rN ∘ g)) - ((inhomogeneousCochains (NumberField.SIdele.obj ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S))).d 1 2).hom (fun g₁ => jj (rN ∘ g₁)) g) ∈ Φ₂.range := ⟨_, rfl⟩
        rw [hΦ₂range] at this
        exact this
    rw [NumberField.AdeleRing.principalIdeles_inf_unitIdelesOutside_eq_map_unit (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂))) ↥(levelField L F₂ (hLF.trans hFF₂)) {w | w.under (𝓞 ↥L) ∈ (placesOverPrimesFinset ↥L S)}] at h2
    obtain ⟨s, hs, hseq⟩ := h2
    have hsU : s ∈ NumberField.SUnits.sUnits ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S) := by
      rw [NumberField.SUnits.sUnits_eq_unit]
      exact hs
    refine ⟨⟨Additive.ofMul s, (NumberField.SUnits.mem_sUnitsSubmodule ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S) _).2 hsU⟩, ?_⟩
    apply hΦ₂inj
    rw [hΦ₂diag]
    exact congrArg Additive.ofMul hseq
  choose ee hee using hEex

  have hdi : Function.Injective (NumberField.SIdele.diag ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S)).hom := fun x y hxy => by
    have h1 : Φ₂ ((NumberField.SIdele.diag ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S)).hom x) = Φ₂ ((NumberField.SIdele.diag ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S)).hom y) := congrArg Φ₂ hxy
    rw [hΦ₂diag, hΦ₂diag] at h1
    have h2 := Units.ext_iff.1 (Additive.ofMul.injective h1)
    rw [Units.coe_map, Units.coe_map, MonoidHom.coe_coe] at h2
    have h3 := NumberField.AdeleRing.algebraMap_injective (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂))) ↥(levelField L F₂ (hLF.trans hFF₂)) h2
    exact Subtype.ext (Additive.toMul.injective (Units.ext h3))
  obtain ⟨ΦRK, hΦRK⟩ := NumberField.SIdele.exists_hom_ideles_apply_eq ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) D hactI Φ hΦρ
  have hdξJ : ∀ g : Fin 3 → (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)), ((inhomogeneousCochains (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))).d 2 3).hom ξJ g = 0 := by
    have h1 := groupCohomology.inhomogeneousCochains_d_comp_apply ΦRK 2 ξJ
    have h2 : (fun g => ΦRK.hom (ξJ g)) = ξ := funext fun g => (hΦRK _).trans (hξJ' g)
    intro g
    apply hΦinj
    have e1 : Φ (((inhomogeneousCochains (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))).d 2 3).hom ξJ g) = ((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)).d 2 3).hom (fun g => ΦRK.hom (ξJ g)) g :=
      (hΦRK _).symm.trans (congrFun h1 g).symm
    have e2 : ((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)).d 2 3).hom (fun g => ΦRK.hom (ξJ g)) g = ((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)).d 2 3).hom ξ g :=
      congrArg (fun f => ((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)).d 2 3).hom f g) h2
    exact e1.trans (e2.trans ((congrFun hξ g).trans (map_zero Φ).symm))
  have hde : ∀ g₃ : Fin 3 → (↥(levelField L F₂ (hLF.trans hFF₂)) ≃ₐ[↥L] ↥(levelField L F₂ (hLF.trans hFF₂))), ((inhomogeneousCochains (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S))).d 2 3).hom ee g₃ = incl (f₁ (rN ∘ g₃)) := by
    let Ecoch : ((inhomogeneousCochains (NumberField.SIdele.obj ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S))).X 2) := fun g => (NumberField.SIdele.diag ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S)).hom (ee g)
    let Acoch : ((inhomogeneousCochains (NumberField.SIdele.obj ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S))).X 2) := fun g => T (u (rN ∘ g))
    let Bcoch : ((inhomogeneousCochains (NumberField.SIdele.obj ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S))).X 2) := fun g => T (ξJ (rN ∘ g))
    let Ccoch : ((inhomogeneousCochains (NumberField.SIdele.obj ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S))).X 2) := ((inhomogeneousCochains (NumberField.SIdele.obj ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S))).d 1 2).hom (fun g₁ => jj (rN ∘ g₁))
    have hE : Ecoch = Acoch - Bcoch - Ccoch := funext fun g => hee g
    have hd : ((inhomogeneousCochains (NumberField.SIdele.obj ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S))).d 2 3).hom Ecoch = ((inhomogeneousCochains (NumberField.SIdele.obj ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S))).d 2 3).hom Acoch - ((inhomogeneousCochains (NumberField.SIdele.obj ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S))).d 2 3).hom Bcoch - ((inhomogeneousCochains (NumberField.SIdele.obj ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S))).d 2 3).hom Ccoch := by
      rw [hE, map_sub, map_sub]
    have h00 : ((inhomogeneousCochains (NumberField.SIdele.obj ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S))).d 2 3).hom (((inhomogeneousCochains (NumberField.SIdele.obj ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S))).d 1 2).hom (fun g₁ => jj (rN ∘ g₁))) = 0 :=
      groupCohomology.inhomogeneousCochains_d_d_apply (NumberField.SIdele.obj ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S)) 1 _
    intro g₃
    apply hdi
    have s1 : (NumberField.SIdele.diag ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S)).hom (((inhomogeneousCochains (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S))).d 2 3).hom ee g₃) =
        ((inhomogeneousCochains (NumberField.SIdele.obj ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S))).d 2 3).hom Acoch g₃ - ((inhomogeneousCochains (NumberField.SIdele.obj ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S))).d 2 3).hom Bcoch g₃ - ((inhomogeneousCochains (NumberField.SIdele.obj ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S))).d 2 3).hom Ccoch g₃ :=
      (congrFun (groupCohomology.inhomogeneousCochains_d_comp_apply (NumberField.SIdele.diag ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S)) 2 ee) g₃).symm.trans (congrFun hd g₃)
    have sA : ((inhomogeneousCochains (NumberField.SIdele.obj ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S))).d 2 3).hom Acoch g₃ = (NumberField.SIdele.diag ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S)).hom (incl (f₁ (rN ∘ g₃))) :=
      (congrFun (groupCohomology.inhomogeneousCochains_d_comp_res_apply rN T hTρ 2 u) g₃).trans
        ((congrArg T (congrFun hu (rN ∘ g₃))).trans (hTdiag _))
    have sB : ((inhomogeneousCochains (NumberField.SIdele.obj ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S))).d 2 3).hom Bcoch g₃ = 0 :=
      (congrFun (groupCohomology.inhomogeneousCochains_d_comp_res_apply rN T hTρ 2 ξJ) g₃).trans
        ((congrArg T (hdξJ (rN ∘ g₃))).trans (map_zero T))
    have sC : ((inhomogeneousCochains (NumberField.SIdele.obj ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S))).d 2 3).hom Ccoch g₃ = 0 := by
      show ((inhomogeneousCochains (NumberField.SIdele.obj ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S))).d 2 3).hom (((inhomogeneousCochains (NumberField.SIdele.obj ↥L ↥(levelField L F₂ (hLF.trans hFF₂)) (placesOverPrimesFinset ↥L S))).d 1 2).hom (fun g₁ => jj (rN ∘ g₁))) g₃ = 0
      rw [h00]; rfl
    rw [sA, sB, sC, sub_zero, sub_zero] at s1
    exact s1

  refine ⟨ee, fun g₂ g₀ hlink => ?_⟩
  rw [hde g₂, hincl]
  have hg : (fun j => rN (g₂ j)) = fun i => levelGal L F hLF (g₀ i) := by
    funext i
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    rw [NumberField.LevelArith.levelGal_apply_coe, ← halg0 ((rN (g₂ i)) x)]
    have h1 : algebraMap ↥(levelField L F hLF) ↥(levelField L F₂ (hLF.trans hFF₂)) ((rN (g₂ i)) x) = (g₂ i) (algebraMap ↥(levelField L F hLF) ↥(levelField L F₂ (hLF.trans hFF₂)) x) :=
      AlgEquiv.restrictNormal_commutes (g₂ i) ↥(levelField L F hLF) x
    rw [h1, hlink i, halg0]
  simp only [Units.coe_map, MonoidHom.coe_coe, halg0]
  rw [show (rN ∘ g₂) = fun i => levelGal L F hLF (g₀ i) from hg]

end S_NumberField_LevelArith_exists_level_sUnitsRep_val_d_eq_of_sIdele_coboundary_of_map_eq_add_d
end P2MW
export P2MW.S_NumberField_LevelArith_exists_level_sUnitsRep_val_d_eq_of_sIdele_coboundary_of_map_eq_add_d (solution)
