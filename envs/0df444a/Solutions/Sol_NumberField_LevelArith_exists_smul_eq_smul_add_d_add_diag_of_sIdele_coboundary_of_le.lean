-- Prove2me | solution 1 for NumberField.LevelArith.exists_smul_eq_smul_add_d_add_diag_of_sIdele_coboundary_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/71ff2b5a-b4c5-5e59-90e3-5a417ba13d9a

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
import Theorems.Thm_M4aHerbrand_exists_hom_res_ideles_and_ideleClassGroup_injective_range_eq_invariants_of_isScalarTower
import Theorems.Thm_NumberField_SIdele_exists_hom_classObj_ideleClassGroup_injective_range_eq
import Theorems.Thm_M4aHerbrand_nonempty_ideleGaloisDescent
import Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_exists_mulDistribMulAction_smul_eq_classAct
import Theorems.Thm_NumberField_LevelArith_levelGal_surjective_and_ker
import Theorems.Thm_NumberField_LevelArith_isGalois_levelField
import Theorems.Thm_groupCohomology_inhomogeneousCochains_d_comp_res_apply
import Theorems.Thm_NumberField_LevelArith_unitsMap_genuineBaseChange_mem_unitIdelesOutside_of_le
import Theorems.Thm_NumberField_SIdele_exists_smul_eq_d_add_diag_of_d_eq_diag
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_exists_smul_eq_smul_add_d_add_diag_of_sIdele_coboundary_of_le
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory groupCohomology ExtCitation NumberField IsDedekindDomain M4aHerbrand NumberField.LevelArith
open scoped NumberField.LevelArith NumberField.PlaceDecomp
open scoped NumberField.InfPlaceDecomp

set_option maxHeartbeats 25600000 in
theorem solution
    (S : Finset Nat.Primes)
    (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F]
    [IsGalois ↥L ↥(levelField L F hLF)]
    (L₁ F₁ : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLL₁ : L ≤ L₁) (hL₁F₁ : L₁ ≤ F₁) (hFF₁ : F ≤ F₁)
    [FiniteDimensional ℚ ↥L₁] [FiniteDimensional ℚ ↥F₁] [Normal ℚ ↥F₁] [IsGalois ↥L₁ ↥(levelField L₁ F₁ hL₁F₁)]
    (n : ℕ) (hn : Nat.card (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype) ∣ n)

    (f₁ : (Fin 3 → (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) → (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)))
    (c : (Fin 2 → (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) → (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)))
    (hc : ((inhomogeneousCochains (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))).d 2 3).hom c = fun g => (NumberField.SIdele.diag ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)).hom (f₁ g))

    (f₁' : (Fin 3 → (↥(levelField L₁ F₁ hL₁F₁) ≃ₐ[↥L₁] ↥(levelField L₁ F₁ hL₁F₁))) → (NumberField.SUnits.sUnitsRep ↥L₁ ↥(levelField L₁ F₁ hL₁F₁) (placesOverPrimesFinset ↥L₁ S)))
    (hff' : ∀ (g : Fin 3 → ↥L₁.fixingSubgroup) (g₀ : Fin 3 → ↥L.fixingSubgroup),
      (∀ i, ((g₀ i : ↥L.fixingSubgroup) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = ((g i : ↥L₁.fixingSubgroup) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) →
      ((NumberField.SUnits.val ↥L₁ ↥(levelField L₁ F₁ hL₁F₁) (placesOverPrimesFinset ↥L₁ S) (f₁' (fun i => levelGal L₁ F₁ hL₁F₁ (g i))) : ↥(levelField L₁ F₁ hL₁F₁)) : AlgebraicClosure ℚ)
        = ((NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) (f₁ (fun i => levelGal L F hLF (g₀ i))) : ↥(levelField L F hLF)) : AlgebraicClosure ℚ))
    (c₁ : (Fin 2 → (↥(levelField L₁ F₁ hL₁F₁) ≃ₐ[↥L₁] ↥(levelField L₁ F₁ hL₁F₁))) → (NumberField.SIdele.obj ↥L₁ ↥(levelField L₁ F₁ hL₁F₁) (placesOverPrimesFinset ↥L₁ S)))
    (hc₁ : ((inhomogeneousCochains (NumberField.SIdele.obj ↥L₁ ↥(levelField L₁ F₁ hL₁F₁) (placesOverPrimesFinset ↥L₁ S))).d 2 3).hom c₁ = fun g => (NumberField.SIdele.diag ↥L₁ ↥(levelField L₁ F₁ hL₁F₁) (placesOverPrimesFinset ↥L₁ S)).hom (f₁' g)) :
    ∃ (ζ : (Fin 2 → (↥(levelField L₁ F₁ hL₁F₁) ≃ₐ[↥L₁] ↥(levelField L₁ F₁ hL₁F₁))) → (NumberField.SIdele.obj ↥L₁ ↥(levelField L₁ F₁ hL₁F₁) (placesOverPrimesFinset ↥L₁ S))) (ω : (Fin 1 → (↥(levelField L₁ F₁ hL₁F₁) ≃ₐ[↥L₁] ↥(levelField L₁ F₁ hL₁F₁))) → (NumberField.SIdele.obj ↥L₁ ↥(levelField L₁ F₁ hL₁F₁) (placesOverPrimesFinset ↥L₁ S))) (e : (Fin 2 → (↥(levelField L₁ F₁ hL₁F₁) ≃ₐ[↥L₁] ↥(levelField L₁ F₁ hL₁F₁))) → (NumberField.SUnits.sUnitsRep ↥L₁ ↥(levelField L₁ F₁ hL₁F₁) (placesOverPrimesFinset ↥L₁ S))),
      ((inhomogeneousCochains (NumberField.SIdele.obj ↥L₁ ↥(levelField L₁ F₁ hL₁F₁) (placesOverPrimesFinset ↥L₁ S))).d 2 3).hom ζ = 0 ∧
      (n : ℤ) • c₁ = (n : ℤ) • ζ + ((inhomogeneousCochains (NumberField.SIdele.obj ↥L₁ ↥(levelField L₁ F₁ hL₁F₁) (placesOverPrimesFinset ↥L₁ S))).d 1 2).hom ω + fun g => (NumberField.SIdele.diag ↥L₁ ↥(levelField L₁ F₁ hL₁F₁) (placesOverPrimesFinset ↥L₁ S)).hom (e g) := by
  classical

  letI algLL₁ : Algebra ↥L ↥L₁ := (IntermediateField.inclusion hLL₁).toRingHom.toAlgebra
  letI algLK₁ : Algebra ↥L ↥(levelField L₁ F₁ hL₁F₁) := ((algebraMap ↥L₁ ↥(levelField L₁ F₁ hL₁F₁)).comp (algebraMap ↥L ↥L₁)).toAlgebra
  haveI towLL₁K₁ : IsScalarTower ↥L ↥L₁ ↥(levelField L₁ F₁ hL₁F₁) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hKK₁ : ∀ x : ↥(levelField L F hLF), (x : AlgebraicClosure ℚ) ∈ levelField L₁ F₁ hL₁F₁ := fun x =>
    (IntermediateField.mem_extendScalars hL₁F₁).2 (hFF₁ ((IntermediateField.mem_extendScalars hLF).1 x.2))
  letI algKK₁ : Algebra ↥(levelField L F hLF) ↥(levelField L₁ F₁ hL₁F₁) :=
    (({ toFun := fun x => ⟨(x : AlgebraicClosure ℚ), hKK₁ x⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
        map_zero' := rfl, map_add' := fun _ _ => rfl } : ↥(levelField L F hLF) →+* ↥(levelField L₁ F₁ hL₁F₁))).toAlgebra
  haveI towLKK₁ : IsScalarTower ↥L ↥(levelField L F hLF) ↥(levelField L₁ F₁ hL₁F₁) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have halg0 : ∀ x : ↥(levelField L F hLF), ((algebraMap ↥(levelField L F hLF) ↥(levelField L₁ F₁ hL₁F₁) x : ↥(levelField L₁ F₁ hL₁F₁)) : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ) := fun _ => rfl
  haveI galLK₁ : IsGalois ↥L ↥(levelField L₁ F₁ hL₁F₁) := by
    haveI := NumberField.LevelArith.isGalois_levelField L F₁ (hLL₁.trans hL₁F₁)
    let e : ↥(levelField L F₁ (hLL₁.trans hL₁F₁)) ≃ₐ[↥L] ↥(levelField L₁ F₁ hL₁F₁) :=
      { toFun := fun x => ⟨(x : AlgebraicClosure ℚ),
          (IntermediateField.mem_extendScalars hL₁F₁).2 ((IntermediateField.mem_extendScalars (hLL₁.trans hL₁F₁)).1 x.2)⟩
        invFun := fun y => ⟨(y : AlgebraicClosure ℚ),
          (IntermediateField.mem_extendScalars (hLL₁.trans hL₁F₁)).2 ((IntermediateField.mem_extendScalars hL₁F₁).1 y.2)⟩
        left_inv := fun _ => rfl, right_inv := fun _ => rfl, map_mul' := fun _ _ => rfl, map_add' := fun _ _ => rfl,
        commutes' := fun _ => rfl }
    exact IsGalois.of_algEquiv e

  obtain ⟨D⟩ := M4aHerbrand.nonempty_ideleGaloisDescent ↥L ↥(levelField L F hLF)
  obtain ⟨DM⟩ := M4aHerbrand.nonempty_ideleGaloisDescent ↥L ↥(levelField L₁ F₁ hL₁F₁)
  letI instI : MulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ := MulDistribMulAction.compHom _ D.unitsAct
  have hactI : ∀ (g : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) (x : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ), g • x = D.unitsAct g x := fun _ _ => rfl
  obtain ⟨instC, hact⟩ := M4aHerbrand.IdeleGaloisDescent.exists_mulDistribMulAction_smul_eq_classAct ↥L ↥(levelField L F hLF) D
  letI := instC
  letI instIM : MulDistribMulAction (↥(levelField L₁ F₁ hL₁F₁) ≃ₐ[↥L] ↥(levelField L₁ F₁ hL₁F₁)) (AdeleRing (𝓞 ↥(levelField L₁ F₁ hL₁F₁)) ↥(levelField L₁ F₁ hL₁F₁))ˣ := MulDistribMulAction.compHom _ DM.unitsAct
  have hactIM : ∀ (g : ↥(levelField L₁ F₁ hL₁F₁) ≃ₐ[↥L] ↥(levelField L₁ F₁ hL₁F₁)) (x : (AdeleRing (𝓞 ↥(levelField L₁ F₁ hL₁F₁)) ↥(levelField L₁ F₁ hL₁F₁))ˣ), g • x = DM.unitsAct g x := fun _ _ => rfl
  obtain ⟨instCM, hactM⟩ := M4aHerbrand.IdeleGaloisDescent.exists_mulDistribMulAction_smul_eq_classAct ↥L ↥(levelField L₁ F₁ hL₁F₁) DM
  letI := instCM
  let rN : (↥(levelField L₁ F₁ hL₁F₁) ≃ₐ[↥L] ↥(levelField L₁ F₁ hL₁F₁)) →* (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) := AlgEquiv.restrictNormalHom ↥(levelField L F hLF)
  have hrN : Function.Surjective rN := AlgEquiv.restrictNormalHom_surjective ↥(levelField L₁ F₁ hL₁F₁)
  haveI : rN.ker.Normal := MonoidHom.normal_ker rN
  let ιq : (↥(levelField L₁ F₁ hL₁F₁) ≃ₐ[↥L] ↥(levelField L₁ F₁ hL₁F₁)) ⧸ rN.ker ≃* (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) := QuotientGroup.quotientKerEquivOfSurjective rN hrN
  have hιq : ∀ (g : ↥(levelField L₁ F₁ hL₁F₁) ≃ₐ[↥L] ↥(levelField L₁ F₁ hL₁F₁)) (x : ↥(levelField L F hLF)), algebraMap ↥(levelField L F hLF) ↥(levelField L₁ F₁ hL₁F₁) (ιq (QuotientGroup.mk g) x) = g (algebraMap ↥(levelField L F hLF) ↥(levelField L₁ F₁ hL₁F₁) x) := by
    intro g x
    have : ιq (QuotientGroup.mk g) = rN g := QuotientGroup.kerLift_mk rN g
    rw [this]
    exact AlgEquiv.restrictNormal_commutes g ↥(levelField L F hLF) x
  obtain ⟨J, j, hJ, hj, hjinj, hjrange⟩ :=
    M4aHerbrand.exists_hom_res_ideles_and_ideleClassGroup_injective_range_eq_invariants_of_isScalarTower ↥L ↥(levelField L F hLF) ↥(levelField L₁ F₁ hL₁F₁)
      D DM hactI hact hactIM hactM rN.ker ιq hιq

  obtain ⟨Φ, ιC, hΦinj, hΦrange, hΦρ, hΦdiag, -, -, -⟩ :=
    NumberField.SIdele.exists_hom_classObj_ideleClassGroup_injective_range_eq ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) D hact
  let r : (↥(levelField L₁ F₁ hL₁F₁) ≃ₐ[↥L₁] ↥(levelField L₁ F₁ hL₁F₁)) →* (↥(levelField L₁ F₁ hL₁F₁) ≃ₐ[↥L] ↥(levelField L₁ F₁ hL₁F₁)) :=
    { toFun := fun g => g.restrictScalars ↥L, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hr : ∀ (g : (↥(levelField L₁ F₁ hL₁F₁) ≃ₐ[↥L₁] ↥(levelField L₁ F₁ hL₁F₁))) (x : ↥(levelField L₁ F₁ hL₁F₁)), r g x = g x := fun _ _ => rfl
  let D' : IdeleGaloisDescent (𝓞 ↥(levelField L₁ F₁ hL₁F₁)) ↥L₁ ↥(levelField L₁ F₁ hL₁F₁) :=
    { act := DM.act.comp r
      compat := fun g x => DM.compat (r g) x
      continuous_act := fun g => DM.continuous_act (r g) }
  letI instI' : MulDistribMulAction (↥(levelField L₁ F₁ hL₁F₁) ≃ₐ[↥L₁] ↥(levelField L₁ F₁ hL₁F₁)) (AdeleRing (𝓞 ↥(levelField L₁ F₁ hL₁F₁)) ↥(levelField L₁ F₁ hL₁F₁))ˣ := MulDistribMulAction.compHom _ D'.unitsAct
  have hactI' : ∀ (g : (↥(levelField L₁ F₁ hL₁F₁) ≃ₐ[↥L₁] ↥(levelField L₁ F₁ hL₁F₁))) (x : (AdeleRing (𝓞 ↥(levelField L₁ F₁ hL₁F₁)) ↥(levelField L₁ F₁ hL₁F₁))ˣ), g • x = D'.unitsAct g x := fun _ _ => rfl
  have hactI'r : ∀ (g : (↥(levelField L₁ F₁ hL₁F₁) ≃ₐ[↥L₁] ↥(levelField L₁ F₁ hL₁F₁))) (x : (AdeleRing (𝓞 ↥(levelField L₁ F₁ hL₁F₁)) ↥(levelField L₁ F₁ hL₁F₁))ˣ), D'.unitsAct g x = DM.unitsAct (r g) x := fun _ _ => rfl
  obtain ⟨instC', hact'⟩ := M4aHerbrand.IdeleGaloisDescent.exists_mulDistribMulAction_smul_eq_classAct ↥L₁ ↥(levelField L₁ F₁ hL₁F₁) D'
  letI := instC'
  obtain ⟨Φ', ιC', hΦ'inj, hΦ'range, hΦ'ρ, hΦ'diag, -, -, -⟩ :=
    NumberField.SIdele.exists_hom_classObj_ideleClassGroup_injective_range_eq ↥L₁ ↥(levelField L₁ F₁ hL₁F₁) (placesOverPrimesFinset ↥L₁ S) D' hact'

  let ρ : (↥(levelField L₁ F₁ hL₁F₁) ≃ₐ[↥L₁] ↥(levelField L₁ F₁ hL₁F₁)) →* (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) := rN.comp r
  have hρ : ∀ (γ : ↥L₁.fixingSubgroup), ρ (levelGal L₁ F₁ hL₁F₁ γ) = levelGal L F hLF ⟨(γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), fun x => γ.2 ⟨(x : AlgebraicClosure ℚ), hLL₁ x.2⟩⟩ := by
    intro γ
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    rw [NumberField.LevelArith.levelGal_apply_coe]
    have h1 : ((algebraMap ↥(levelField L F hLF) ↥(levelField L₁ F₁ hL₁F₁) ((rN (r (levelGal L₁ F₁ hL₁F₁ γ))) x) : ↥(levelField L₁ F₁ hL₁F₁)) : AlgebraicClosure ℚ) =
        (((r (levelGal L₁ F₁ hL₁F₁ γ)) (algebraMap ↥(levelField L F hLF) ↥(levelField L₁ F₁ hL₁F₁) x) : ↥(levelField L₁ F₁ hL₁F₁)) : AlgebraicClosure ℚ) :=
      congrArg (fun y : ↥(levelField L₁ F₁ hL₁F₁) => (y : AlgebraicClosure ℚ)) (AlgEquiv.restrictNormal_commutes (r (levelGal L₁ F₁ hL₁F₁ γ)) ↥(levelField L F hLF) x)
    rw [halg0] at h1
    show (((rN (r (levelGal L₁ F₁ hL₁F₁ γ))) x : ↥(levelField L F hLF)) : AlgebraicClosure ℚ) = _
    rw [h1, hr, NumberField.LevelArith.levelGal_apply_coe]
    rfl

  have halg : ∀ x : ↥(levelField L F hLF), ((algebraMap ↥(levelField L F hLF) ↥(levelField L₁ F₁ hL₁F₁) x : ↥(levelField L₁ F₁ hL₁F₁)) : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ) := fun _ => rfl
  obtain ⟨hpresI, hpresU⟩ :=
    NumberField.LevelArith.unitsMap_genuineBaseChange_mem_unitIdelesOutside_of_le S L F hLF L₁ F₁ hLL₁ hL₁F₁ hFF₁ halg
  have hmemT : ∀ y : (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)), J.hom (Φ y) ∈ Φ'.range := fun y => by
    have hy : Additive.toMul (Φ y) ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF) {w | w.under (𝓞 ↥L) ∈ (placesOverPrimesFinset ↥L S)} := by
      have : Φ y ∈ Φ.range := ⟨y, rfl⟩
      rw [hΦrange] at this
      exact this
    have h2 := hpresI (Additive.toMul (Φ y)) hy
    rw [hΦ'range]
    have h3 : J.hom (Φ y) = Additive.ofMul (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange ↥(levelField L F hLF) ↥(levelField L₁ F₁ hL₁F₁)).β.toMonoidHom (Additive.toMul (Φ y))) := hJ _
    rw [h3]
    exact h2
  have hT_ex : ∃ T : (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)) →+ (NumberField.SIdele.obj ↥L₁ ↥(levelField L₁ F₁ hL₁F₁) (placesOverPrimesFinset ↥L₁ S)), ∀ y, Φ' (T y) = J.hom (Φ y) := by
    refine ⟨(AddMonoidHom.ofInjective hΦ'inj).symm.toAddMonoidHom.comp
      ((J.hom.toAddMonoidHom.comp Φ).codRestrict Φ'.range hmemT), fun y => ?_⟩
    exact AddMonoidHom.apply_ofInjective_symm hΦ'inj ⟨_, hmemT y⟩
  obtain ⟨T, hT⟩ := hT_ex
  choose incl hincl using hpresU

  have hιqr : ∀ g : (↥(levelField L₁ F₁ hL₁F₁) ≃ₐ[↥L₁] ↥(levelField L₁ F₁ hL₁F₁)), (ιq.toMonoidHom.comp (QuotientGroup.mk' rN.ker)) (r g) = ρ g := fun g =>
    QuotientGroup.kerLift_mk rN (r g)
  have hTρ : ∀ (g : (↥(levelField L₁ F₁ hL₁F₁) ≃ₐ[↥L₁] ↥(levelField L₁ F₁ hL₁F₁))) (y : (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))), T ((NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)).ρ (ρ g) y) = (NumberField.SIdele.obj ↥L₁ ↥(levelField L₁ F₁ hL₁F₁) (placesOverPrimesFinset ↥L₁ S)).ρ g (T y) := by
    intro g y
    apply hΦ'inj
    rw [hT, hΦρ, hΦ'ρ, hT, hactI'r]
    have h1 : J.hom ((Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ).ρ (ρ g) (Φ y)) =
        (Rep.ofMulDistribMulAction (↥(levelField L₁ F₁ hL₁F₁) ≃ₐ[↥L] ↥(levelField L₁ F₁ hL₁F₁)) (AdeleRing (𝓞 ↥(levelField L₁ F₁ hL₁F₁)) ↥(levelField L₁ F₁ hL₁F₁))ˣ).ρ (r g) (J.hom (Φ y)) := Rep.hom_comm_apply J (r g) (Φ y)
    have h2 : (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ).ρ (ρ g) (Φ y) =
        Additive.ofMul (D.unitsAct (ρ g) (Additive.toMul (Φ y))) := by
      rw [Rep.ofMulDistribMulAction_ρ_apply_apply]; rfl
    have h3 : (Rep.ofMulDistribMulAction (↥(levelField L₁ F₁ hL₁F₁) ≃ₐ[↥L] ↥(levelField L₁ F₁ hL₁F₁)) (AdeleRing (𝓞 ↥(levelField L₁ F₁ hL₁F₁)) ↥(levelField L₁ F₁ hL₁F₁))ˣ).ρ (r g) (J.hom (Φ y)) = Additive.ofMul (DM.unitsAct (r g) (Additive.toMul (J.hom (Φ y)))) := by
      rw [Rep.ofMulDistribMulAction_ρ_apply_apply]; rfl
    rw [← h2, h1, h3]

  have hTdiag : ∀ x : (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)), T ((NumberField.SIdele.diag ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)).hom x) = (NumberField.SIdele.diag ↥L₁ ↥(levelField L₁ F₁ hL₁F₁) (placesOverPrimesFinset ↥L₁ S)).hom (incl x) := by
    intro x
    apply hΦ'inj
    rw [hT, hΦdiag]
    refine (hJ _).trans ?_
    rw [hΦ'diag, hincl]
    congr 1
    ext
    change (M4aHerbrand.GenuineDescent.genuineBaseChange ↥(levelField L F hLF) ↥(levelField L₁ F₁ hL₁F₁)).β (algebraMap ↥(levelField L F hLF) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) (NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) x : ↥(levelField L F hLF))) = _
    rw [(M4aHerbrand.GenuineDescent.genuineBaseChange ↥(levelField L F hLF) ↥(levelField L₁ F₁ hL₁F₁)).β_compat]
    rfl

  have hcardG : Nat.card (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) ∣ n := by
    obtain ⟨hsurjL, hkerL⟩ := NumberField.LevelArith.levelGal_surjective_and_ker L F hLF
    have e1 := (QuotientGroup.quotientKerEquivOfSurjective (levelGal L F hLF) hsurjL).toEquiv
    have e2 := (QuotientGroup.quotientMulEquivOfEq hkerL).toEquiv
    rw [← Nat.card_congr e1, Nat.card_congr e2]
    exact hn
  obtain ⟨ω₀, e₀, hω₀⟩ := NumberField.SIdele.exists_smul_eq_d_add_diag_of_d_eq_diag ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) n hcardG f₁ c hc

  have hρval : ∀ g : Fin 3 → (↥(levelField L₁ F₁ hL₁F₁) ≃ₐ[↥L₁] ↥(levelField L₁ F₁ hL₁F₁)), incl (f₁ (fun j => ρ (g j))) = f₁' g := by
    intro g
    obtain ⟨hsurj₁, -⟩ := NumberField.LevelArith.levelGal_surjective_and_ker L₁ F₁ hL₁F₁
    choose γ hγ using fun i => hsurj₁ (g i)
    have hg : g = fun i => levelGal L₁ F₁ hL₁F₁ (γ i) := funext fun i => (hγ i).symm
    subst hg
    apply Subtype.ext
    apply Additive.toMul.injective
    change NumberField.SUnits.val ↥L₁ ↥(levelField L₁ F₁ hL₁F₁) (placesOverPrimesFinset ↥L₁ S) (incl _) = NumberField.SUnits.val ↥L₁ ↥(levelField L₁ F₁ hL₁F₁) (placesOverPrimesFinset ↥L₁ S) (f₁' _)
    apply Units.ext
    apply Subtype.ext
    rw [hincl]
    have hval := hff' γ (fun i => ⟨(γ i : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), fun x => (γ i).2 ⟨(x : AlgebraicClosure ℚ), hLL₁ x.2⟩⟩) (fun _ => rfl)
    rw [hval]
    simp only [Units.coe_map, MonoidHom.coe_coe, halg0]
    rw [show (fun j => ρ (levelGal L₁ F₁ hL₁F₁ (γ j))) =
        (fun i => levelGal L F hLF ⟨(γ i : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), fun x => (γ i).2 ⟨(x : AlgebraicClosure ℚ), hLL₁ x.2⟩⟩)
      from funext fun j => hρ (γ j)]
  have hdc₁ : ((inhomogeneousCochains (NumberField.SIdele.obj ↥L₁ ↥(levelField L₁ F₁ hL₁F₁) (placesOverPrimesFinset ↥L₁ S))).d 2 3).hom (fun g => T (c (ρ ∘ g))) = fun g => (NumberField.SIdele.diag ↥L₁ ↥(levelField L₁ F₁ hL₁F₁) (placesOverPrimesFinset ↥L₁ S)).hom (f₁' g) := by
    rw [groupCohomology.inhomogeneousCochains_d_comp_res_apply ρ T hTρ 2 c, hc]
    funext g
    show T ((NumberField.SIdele.diag ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)).hom (f₁ (ρ ∘ g))) = _
    rw [hTdiag, ← hρval g]
    rfl

  refine ⟨c₁ - fun g => T (c (ρ ∘ g)), fun g => T (ω₀ (ρ ∘ g)), fun g => incl (e₀ (ρ ∘ g)), ?_, ?_⟩
  · rw [map_sub, hc₁, hdc₁, sub_self]
  · have hnc : ((n : ℤ) • fun g : Fin 2 → (↥(levelField L₁ F₁ hL₁F₁) ≃ₐ[↥L₁] ↥(levelField L₁ F₁ hL₁F₁)) => T (c (ρ ∘ g))) =
        ((inhomogeneousCochains (NumberField.SIdele.obj ↥L₁ ↥(levelField L₁ F₁ hL₁F₁) (placesOverPrimesFinset ↥L₁ S))).d 1 2).hom (fun g => T (ω₀ (ρ ∘ g))) + fun g => (NumberField.SIdele.diag ↥L₁ ↥(levelField L₁ F₁ hL₁F₁) (placesOverPrimesFinset ↥L₁ S)).hom (incl (e₀ (ρ ∘ g))) := by
      rw [groupCohomology.inhomogeneousCochains_d_comp_res_apply ρ T hTρ 1 ω₀]
      funext g
      simp only [Pi.smul_apply, Pi.add_apply]
      rw [← map_zsmul T, show (n : ℤ) • c (ρ ∘ g) = ((n : ℤ) • c) (ρ ∘ g) from rfl, hω₀, Pi.add_apply, map_add, hTdiag]
    rw [smul_sub, hnc]
    abel

end S_NumberField_LevelArith_exists_smul_eq_smul_add_d_add_diag_of_sIdele_coboundary_of_le
end P2MW
export P2MW.S_NumberField_LevelArith_exists_smul_eq_smul_add_d_add_diag_of_sIdele_coboundary_of_le (solution)
