-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.residue_comp_section_smul_eq_of_mem_inertia
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/e8bba0ae-19ff-5241-8ebd-fd6e865b01f6

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple

import Theorems.Thm_ModularCurve_DRModelPackageLevel_existsUnique_section_comp_eq_pointEquivPlace_symm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_residue_comp_section_smul_eq_of_mem_inertia

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve IsLocalRing ModularCurve ModularCurve.DRLevel ModularCurve.JZeroNeronObjectAtP"

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

namespace GALSEC
variable {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
theorem fix_algebraMap (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (r : DRLevel.R p) :
    σ (algebraMap (DRLevel.R p) (AlgebraicClosure ℚ) r) = algebraMap (DRLevel.R p) (AlgebraicClosure ℚ) r := by
  rw [IsScalarTower.algebraMap_apply (DRLevel.R p) ℚ (AlgebraicClosure ℚ), AlgEquiv.commutes]

omit [Fact p.Prime] in
theorem specMap_comp_genPt (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ genPt p = genPt p := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  exact fix_algebraMap σ r

variable {A : ValuationSubring (AlgebraicClosure ℚ)}

theorem residue_comp_toRingHom_of_mem_inertia (τ : ↥(A.decompositionSubgroup ℚ)) (hτ : τ ∈ A.inertiaSubgroup ℚ) :
    (IsLocalRing.residue ↥A).comp (MulSemiringAction.toRingHom _ (↥A) τ) = IsLocalRing.residue ↥A := by
  ext a
  rw [RingHom.comp_apply, MulSemiringAction.toRingHom_apply, IsLocalRing.ResidueField.residue_smul]
  have h : MulSemiringAction.toRingAut (↥(A.decompositionSubgroup ℚ)) (IsLocalRing.ResidueField ↥A) τ = 1 :=
    (MonoidHom.mem_ker).mp hτ
  have := RingEquiv.congr_fun h (IsLocalRing.residue (↥A) a)
  simpa [MulSemiringAction.toRingAut_apply] using this

theorem subtype_comp_toRingHom (τ : ↥(A.decompositionSubgroup ℚ)) :
    A.subtype.comp (MulSemiringAction.toRingHom _ (↥A) τ) =
      ((τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp A.subtype := by
  ext a
  rfl

omit [Fact p.Prime] in
theorem toRingHom_comp_eq (τ : ↥(A.decompositionSubgroup ℚ)) (ρ : DRLevel.R p →+* ↥A)
    (hρ : A.subtype.comp ρ = algebraMap (DRLevel.R p) (AlgebraicClosure ℚ)) :
    (MulSemiringAction.toRingHom _ (↥A) τ).comp ρ = ρ := by
  apply RingHom.ext
  intro r
  apply Subtype.ext
  have h1 := RingHom.congr_fun (subtype_comp_toRingHom τ) (ρ r)
  have h2 := RingHom.congr_fun hρ r
  simp only [RingHom.comp_apply] at h1 h2 ⊢
  rw [show ((MulSemiringAction.toRingHom _ (↥A) τ) (ρ r) : AlgebraicClosure ℚ) = A.subtype ((MulSemiringAction.toRingHom _ (↥A) τ) (ρ r)) from rfl,
    h1, RingHom.coe_coe, show (A.subtype (ρ r)) = algebraMap (DRLevel.R p) (AlgebraicClosure ℚ) r from h2, fix_algebraMap]
  exact h2.symm

end GALSEC

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    [IsProper (toBase N₀ p)]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) :
    ∀ σ ∈ A.inertiaSubgroupIn ℚ,
      ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p)))
        (s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
        (_hs : Spec.map (CommRingCat.ofHom A.subtype) ≫ s.1 =
          ((𝔓.Meta.pointEquivPlace).symm V).1 ≫ 𝔓.eeta ≫
            pullback.fst (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R p) (AlgebraicClosure ℚ)))))
        (s' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
        (_hs' : Spec.map (CommRingCat.ofHom A.subtype) ≫ s'.1 =
          ((𝔓.Meta.pointEquivPlace).symm (arithmeticGalois (modularFunctionFieldFull (N₀ * p)) σ • V)).1 ≫ 𝔓.eeta ≫
            pullback.fst (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R p) (AlgebraicClosure ℚ))))),
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ s'.1 =
          Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ s.1 := by
  intro σ hσ V s hs s' hs'
  haveI : IsIso 𝔓.eeta := 𝔓.eeta_iso
  obtain ⟨τ, hτ, hτσ⟩ := Subgroup.mem_map.mp hσ
  have hτσ' : ((τ : ↥(A.decompositionSubgroup ℚ)) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = σ := hτσ
  subst hτσ'
  set σA : ↥A →+* ↥A := MulSemiringAction.toRingHom _ (↥A) τ with hσAdef

  have hover : (Spec.map (CommRingCat.ofHom σA) ≫ s.1) ≫ toBase N₀ p = Spec.map (CommRingCat.ofHom ρ) := by
    rw [Category.assoc, s.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp, GALSEC.toRingHom_comp_eq τ ρ hρ]
  let t : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p) := ⟨Spec.map (CommRingCat.ofHom σA) ≫ s.1, hover⟩

  set x := (𝔓.Meta.pointEquivPlace).symm V with hx
  have hPbase : x.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p)
      (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R p) (AlgebraicClosure ℚ)))) ≫ toBase N₀ p = genPt p := by
    rw [pullback.condition, ← Category.assoc 𝔓.eeta, 𝔓.heeta, ← Category.assoc, x.2, Category.id_comp]
  have hq : (Spec.map (CommRingCat.ofHom ((τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
        AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ x.1 ≫ 𝔓.eeta ≫ pullback.fst _ _) ≫ toBase N₀ p =
      𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R p) (AlgebraicClosure ℚ))) := by
    rw [Category.id_comp, Category.assoc, Category.assoc, Category.assoc, hPbase]
    exact GALSEC.specMap_comp_genPt _
  let x' : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // s ≫ 𝔓.Meta.toBase = 𝟙 _} :=
    ⟨pullback.lift _ _ hq ≫ inv 𝔓.eeta, by
      have h1 : inv 𝔓.eeta ≫ 𝔓.Meta.toBase = pullback.snd _ _ := by
        rw [← 𝔓.heeta, IsIso.inv_hom_id_assoc]
      rw [Category.assoc, h1, pullback.lift_snd]⟩
  have hx' : x'.1 ≫ 𝔓.eeta ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom ((τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
        AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ x.1 ≫ 𝔓.eeta ≫ pullback.fst _ _ := by
    show (pullback.lift _ _ hq ≫ inv 𝔓.eeta) ≫ 𝔓.eeta ≫ _ = _
    rw [Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst]
  have hgal := 𝔓.hgal (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) x x' hx'
  have hx'' : x' = (𝔓.Meta.pointEquivPlace).symm
      (arithmeticGalois (modularFunctionFieldFull (N₀ * p)) (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • V) := by
    rw [Equiv.eq_symm_apply, hgal, hx, Equiv.apply_symm_apply]

  have ht : Spec.map (CommRingCat.ofHom A.subtype) ≫ t.1 =
      ((𝔓.Meta.pointEquivPlace).symm (arithmeticGalois (modularFunctionFieldFull (N₀ * p))
        (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • V)).1 ≫ 𝔓.eeta ≫
          pullback.fst (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R p) (AlgebraicClosure ℚ)))) := by
    rw [← hx'', hx']
    show Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map (CommRingCat.ofHom σA) ≫ s.1 = _
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, GALSEC.subtype_comp_toRingHom τ,
      CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hs]

  obtain ⟨s₀, -, huniq⟩ := ModularCurve.DRModelPackageLevel.existsUnique_section_comp_eq_pointEquivPlace_symm
    N₀ p hpN₀ 𝔓 A ρ hρ (arithmeticGalois (modularFunctionFieldFull (N₀ * p)) (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • V)
  have e1 : s' = s₀ := huniq s' hs'
  have e2 : t = s₀ := huniq t ht
  have hst : s'.1 = Spec.map (CommRingCat.ofHom σA) ≫ s.1 := by rw [e1, ← e2]
  rw [hst, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, GALSEC.residue_comp_toRingHom_of_mem_inertia τ hτ]

end S_ModularCurve_DRModelPackageLevel_residue_comp_section_smul_eq_of_mem_inertia
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_residue_comp_section_smul_eq_of_mem_inertia (solution)
