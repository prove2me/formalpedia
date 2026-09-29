-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.dualNumber_eq_comp_of_ker_ribetMatrix
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/e05d21c4-53d0-5384-bb43-ab7b729aae6f

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_dualNumber_eq_comp_of_ker_ribetMatrix
set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_dualNumber_eq_comp_of_ker_ribetMatrix.GoodReductionJacobian AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve ModularCurve.DRLevel"

universe u

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "pointGroup one_natural one mul_natural inv inv_mul_cancel mul"
namespace KerTan
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

variable {κ : Type u} [Field κ] {B : Scheme.{u}} {sB : B ⟶ Spec (CommRingCat.of κ)} (L : RelativeGroupLaw κ sB)

theorem eq_inv_of_mul_eq_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ)) (x y : SchemeHomOver t sB)
    (h : L.mul t x y = L.one t) : x = L.inv t y := by
  letI := L.pointGroup t
  exact eq_inv_of_mul_eq_one_left h

theorem eq_inv_of_mul_eq_one' {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ)) (x y : SchemeHomOver t sB)
    (h : L.mul t x y = L.one t) : y = L.inv t x := by
  letI := L.pointGroup t
  exact eq_inv_of_mul_eq_one_right h

theorem inv_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ)) (t' : T' ⟶ Spec (CommRingCat.of κ))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t sB) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x) = L.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  apply eq_inv_of_mul_eq_one
  rw [← L.mul_natural, L.inv_mul_cancel, L.one_natural]

end GoodReductionJacobian.RelativeGroupLaw.KerTan

open GoodReductionJacobian.RelativeGroupLaw.KerTan in

theorem solution
    {κ : Type u} [Field κ] {B : Scheme.{u}} (sB : B ⟶ Spec (CommRingCat.of κ)) (L : RelativeGroupLaw κ sB)
    (F : SchemeHomOver sB sB)
    (hF : ∀ (v : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ)))) sB)
        (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of κ))) sB)
        (_ : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom κ κ κ).toRingHom) ≫ v.1 = x.1),
      NeronModelInfra.schemeHomOverComp v F =
        NeronModelInfra.schemeHomOverComp
          (⟨Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ))) ≫ x.1,
            by rw [Category.assoc, x.2, Category.comp_id]⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ)))) sB) F) :

    let tBB : pullback sB sB ⟶ Spec (CommRingCat.of κ) := pullback.fst sB sB ≫ sB
    let xBB : SchemeHomOver tBB sB := ⟨pullback.fst sB sB, rfl⟩
    let yBB : SchemeHomOver tBB sB := ⟨pullback.snd sB sB, pullback.condition.symm⟩
    let m₀ := L.mul tBB xBB (NeronModelInfra.schemeHomOverComp yBB F)
    let m₁ := L.mul tBB (NeronModelInfra.schemeHomOverComp xBB F) yBB
    let Mx : pullback sB sB ⟶ pullback sB sB := pullback.lift m₀.1 m₁.1 (m₀.2.trans m₁.2.symm)
    let eBB : Spec (CommRingCat.of κ) ⟶ pullback sB sB := pullback.lift (L.one (𝟙 _)).1 (L.one (𝟙 _)).1 rfl
    ∀ w : Spec (CommRingCat.of (DualNumber κ)) ⟶ pullback Mx eBB,
      w ≫ pullback.snd Mx eBB = Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ))) →
      w = Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ))) ≫
            Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom κ κ κ).toRingHom) ≫ w  := by
  intro tBB xBB yBB m₀ m₁ Mx eBB w hw

  have hιpr : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom κ κ κ).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ))) = 𝟙 _ := by
    have h : CommRingCat.ofHom (algebraMap κ (DualNumber κ)) ≫
        CommRingCat.ofHom (TrivSqZeroExt.fstHom κ κ κ).toRingHom = 𝟙 _ := by
      apply CommRingCat.hom_ext
      ext r
      exact (TrivSqZeroExt.fstHom κ κ κ).commutes r
    rw [← Spec.map_comp, h, Spec.map_id]

  have hMt : Mx ≫ tBB = tBB := by
    dsimp only [Mx, tBB]
    rw [pullback.lift_fst_assoc]
    exact m₀.2
  have heBt : eBB ≫ tBB = 𝟙 _ := by
    dsimp only [eBB, tBB]
    rw [pullback.lift_fst_assoc]
    exact (L.one (𝟙 _)).2

  have hbt : (w ≫ pullback.fst Mx eBB) ≫ tBB = Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ))) := by
    calc (w ≫ pullback.fst Mx eBB) ≫ tBB
        = w ≫ (pullback.fst Mx eBB ≫ Mx) ≫ tBB := by rw [Category.assoc, Category.assoc, hMt]
      _ = w ≫ (pullback.snd Mx eBB ≫ eBB) ≫ tBB := by rw [pullback.condition]
      _ = Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ))) := by
          rw [Category.assoc, heBt, Category.comp_id, hw]
  have hbM : (w ≫ pullback.fst Mx eBB) ≫ Mx = Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ))) ≫ eBB := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hw]

  let B₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ)))) sB :=
    GoodReductionJacobian.schemeHomOverComp (w ≫ pullback.fst Mx eBB) hbt xBB
  let B₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ)))) sB :=
    GoodReductionJacobian.schemeHomOverComp (w ≫ pullback.fst Mx eBB) hbt yBB
  have hB₁ : B₁.1 = (w ≫ pullback.fst Mx eBB) ≫ pullback.fst sB sB := rfl
  have hB₂ : B₂.1 = (w ≫ pullback.fst Mx eBB) ≫ pullback.snd sB sB := rfl

  have hone : (L.one (Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ))))).1 =
      Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ))) ≫ (L.one (𝟙 _)).1 := by
    rw [← L.one_natural (𝟙 _) (Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ))))
      (Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ)))) (Category.comp_id _)]
    rfl

  have hm₀ : L.mul _ B₁ (NeronModelInfra.schemeHomOverComp B₂ F) = L.one _ := by
    have h : GoodReductionJacobian.schemeHomOverComp (w ≫ pullback.fst Mx eBB) hbt m₀ = L.one _ := by
      apply Subtype.ext
      rw [GoodReductionJacobian.schemeHomOverComp_coe, hone]
      have e1 : m₀.1 = Mx ≫ pullback.fst sB sB := (pullback.lift_fst _ _ _).symm
      rw [e1, ← Category.assoc, hbM, Category.assoc]
      congr 1
      exact pullback.lift_fst _ _ _
    rw [L.mul_natural] at h
    exact h
  have hm₁ : L.mul _ (NeronModelInfra.schemeHomOverComp B₁ F) B₂ = L.one _ := by
    have h : GoodReductionJacobian.schemeHomOverComp (w ≫ pullback.fst Mx eBB) hbt m₁ = L.one _ := by
      apply Subtype.ext
      rw [GoodReductionJacobian.schemeHomOverComp_coe, hone]
      have e1 : m₁.1 = Mx ≫ pullback.snd sB sB := (pullback.lift_snd _ _ _).symm
      rw [e1, ← Category.assoc, hbM, Category.assoc]
      congr 1
      exact pullback.lift_snd _ _ _
    rw [L.mul_natural] at h
    exact h

  let x₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of κ))) sB :=
    ⟨Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom κ κ κ).toRingHom) ≫ B₁.1, by
      rw [Category.assoc, B₁.2, hιpr]⟩
  let x₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of κ))) sB :=
    ⟨Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom κ κ κ).toRingHom) ≫ B₂.1, by
      rw [Category.assoc, B₂.2, hιpr]⟩

  have hF₁ : NeronModelInfra.schemeHomOverComp B₁ F =
      GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ)))) (Category.comp_id _)
        (NeronModelInfra.schemeHomOverComp x₁ F) := by
    rw [hF B₁ x₁ rfl]
    apply Subtype.ext
    simp only [NeronModelInfra.schemeHomOverComp_coe, GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc]
  have hF₂ : NeronModelInfra.schemeHomOverComp B₂ F =
      GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ)))) (Category.comp_id _)
        (NeronModelInfra.schemeHomOverComp x₂ F) := by
    rw [hF B₂ x₂ rfl]
    apply Subtype.ext
    simp only [NeronModelInfra.schemeHomOverComp_coe, GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc]

  have hb₁ : B₁ = GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ)))) (Category.comp_id _)
      (L.inv (𝟙 _) (NeronModelInfra.schemeHomOverComp x₂ F)) := by
    rw [eq_inv_of_mul_eq_one L _ _ _ hm₀, hF₂, inv_natural]
  have hb₂ : B₂ = GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ)))) (Category.comp_id _)
      (L.inv (𝟙 _) (NeronModelInfra.schemeHomOverComp x₁ F)) := by
    rw [eq_inv_of_mul_eq_one' L _ _ _ hm₁, hF₁, inv_natural]
  have hb₁' : B₁.1 = Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ))) ≫
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom κ κ κ).toRingHom) ≫ B₁.1 := by
    conv_lhs => rw [hb₁]
    conv_rhs => rw [hb₁]
    simp only [GoodReductionJacobian.schemeHomOverComp_coe]
    rw [reassoc_of% hιpr]
  have hb₂' : B₂.1 = Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ))) ≫
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom κ κ κ).toRingHom) ≫ B₂.1 := by
    conv_lhs => rw [hb₂]
    conv_rhs => rw [hb₂]
    simp only [GoodReductionJacobian.schemeHomOverComp_coe]
    rw [reassoc_of% hιpr]

  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [Category.assoc] at hb₁' ⊢
      exact hb₁'
    · simp only [Category.assoc] at hb₂' ⊢
      exact hb₂'
  · rw [Category.assoc, Category.assoc, hw, hιpr, Category.comp_id]

end S_GoodReductionJacobian_RelativeGroupLaw_dualNumber_eq_comp_of_ker_ribetMatrix
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_dualNumber_eq_comp_of_ker_ribetMatrix (solution)
