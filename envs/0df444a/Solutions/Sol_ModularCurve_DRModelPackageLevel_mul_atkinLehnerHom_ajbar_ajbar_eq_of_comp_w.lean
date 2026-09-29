-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.mul_atkinLehnerHom_ajbar_ajbar_eq_of_comp_w
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/96525538-7869-520a-9194-ace5fdf898d0

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
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_LevelModel
import Definitions.Def_ModularCurve_ToricDescentData
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_ModularCurve_DegeneracyVp
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_ModularCurve_GeometricBaseChange

import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_mul_comp_eq_of_classifies_rigidify_pullback_of_ofPoint_of_isIso
import Theorems.Thm_ModularCurve_DRModelPackageLevel_nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_mul_atkinLehnerHom_ajbar_ajbar_eq_of_comp_w
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection"
set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve ModularCurve.DRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicCurve"

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    [IsProper (toBase N₀ p)]

    (D : RelativePic0Designation (R p) (toBase N₀ p))
    (hD : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) D)

    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)) (D.baseChange ℚ))
    (hPQ : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase N₀ p) 𝔓.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) ℚ), pullback.condition⟩)).L))

    (ajQ : SchemeHomOver (baseChange (R p) (toBase N₀ p) ℚ) (D.baseChange ℚ).toBase)
    (hajQε : (sectionBaseChange ℚ 𝔓.εinf).1 ≫ ajQ.1 = (D.baseChange ℚ).zeroSection)
    (hajQ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (R p) (toBase N₀ p) ℚ)),
      Nonempty ((hDQ.poincare.pullbackAlong
          ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase N₀ p) ℚ) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase N₀ p) ℚ) (t ≫ (sectionBaseChange ℚ 𝔓.εinf).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔓.εinf).2).trans
              (Category.comp_id t)))).idealModule))

    (kQ : pullback (toBase N₀ p) (genPt p) ⟶ pullback (toBase N₀ p) (specMap (R p) ℚ))
    (hkQ₁ : kQ ≫ pullback.fst (toBase N₀ p) (specMap (R p) ℚ) = pullback.fst (toBase N₀ p) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase N₀ p) (specMap (R p) ℚ) = pullback.snd (toBase N₀ p) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))

    (ajbar : 𝔓.Meta.C ⟶ D.P) (hajbar : ajbar = 𝔓.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (R p) ℚ))
    (hajbar_over : ajbar ≫ D.toBase = 𝔓.Meta.toBase ≫ genPt p)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
    (hεbar : εbar.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1) (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ D.zeroSection)

    (pts : JZero (N₀ * p) ≃ SchemeHomOver (genPt p) D.toBase)
    (hpts_add : ∀ x y : JZero (N₀ * p),
      pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (pts x) (pts y))
    (hpts_galois : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero (N₀ * p)),
      (pts (σ • x)).1 = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1)
    (hpts_aj : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _}),
      s.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar (N₀ * p)),
        (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) =
          Finsupp.single (𝔓.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔓.Meta.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)

    (wstar : SchemeHomOver D.toBase D.toBase)
    (hw : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (a : SchemeHomOver t D.toBase),
      Nonempty ((hD.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a wstar)).L ≅
        Scheme.Modules.rigidify (rigSection (toBase N₀ p) t 𝔓.εinf) (pullback.snd (toBase N₀ p) t)
          ((Scheme.Modules.pullback (curveChange 𝔓.w.hom 𝔓.w_over t)).obj (hD.poincare.pullbackAlong a).L)))
    (hwhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (x y : SchemeHomOver t D.toBase),
      NeronModelInfra.schemeHomOverComp
          ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul t x y) wstar =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul t
          (NeronModelInfra.schemeHomOverComp x wstar) (NeronModelInfra.schemeHomOverComp y wstar))

    (y y' ε' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
    (hy' : y'.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) ≫ 𝔓.w.hom = y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))
    (hε' : ε'.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) ≫ 𝔓.w.hom = εbar.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))

    (a b c : SchemeHomOver (genPt p) D.toBase)
    (ha : a.1 = (y.1 ≫ ajbar) ≫ wstar.1) (hb : b.1 = ε'.1 ≫ ajbar) (hc : c.1 = y'.1 ≫ ajbar) :
    (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul (genPt p) a b = c := by

  haveI : SmoothOfRelativeDimension 1 (pullback.snd (toBase N₀ p) (genPt p)) := by
    have e : pullback.snd (toBase N₀ p) (genPt p) = inv 𝔓.eeta ≫ 𝔓.Meta.toBase := by
      rw [← 𝔓.heeta, IsIso.inv_hom_id_assoc]
    rw [e]; exact MorphismProperty.RespectsIso.precomp (P := @SmoothOfRelativeDimension 1) _ _ inferInstance

  let bar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _} → SchemeHomOver (genPt p) (toBase N₀ p) := fun z =>
    ⟨z.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p), by
      simp only [Category.assoc, pullback.condition]; rw [reassoc_of% 𝔓.heeta, reassoc_of% z.2]⟩
  have hbar : ∀ z, (bar z).1 = z.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) := fun z => rfl
  have hy'bar : (bar y').1 ≫ 𝔓.w.hom = (bar y).1 := by
    rw [hbar, hbar]; simp only [Category.assoc]; exact hy'
  have hε'bar : (bar ε').1 ≫ 𝔓.w.hom = genPt p ≫ 𝔓.εinf.1 := by
    rw [hbar]; simp only [Category.assoc]; rw [hε', hεbar]

  let a' : SchemeHomOver (genPt p) D.toBase := ⟨y.1 ≫ ajbar, by rw [Category.assoc, hajbar_over, reassoc_of% y.2]⟩
  have haa' : a = NeronModelInfra.schemeHomOverComp a' wstar := Subtype.ext (by rw [ha]; rfl)

  have ha' := DRModelPackageLevel.nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar
    N₀ p hpN₀ 𝔓 D hD hDQ hPQ ajQ hajQ kQ hkQ₁ hkQ₂ ajbar hajbar y (bar y) rfl a' rfl
  have hb' := DRModelPackageLevel.nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar
    N₀ p hpN₀ 𝔓 D hD hDQ hPQ ajQ hajQ kQ hkQ₁ hkQ₂ ajbar hajbar ε' (bar ε') rfl b hb
  have hc' := DRModelPackageLevel.nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar
    N₀ p hpN₀ 𝔓 D hD hDQ hPQ ajQ hajQ kQ hkQ₁ hkQ₂ ajbar hajbar y' (bar y') rfl c hc
  rw [haa']
  exact RepresentsRelSubPic.mul_comp_eq_of_classifies_rigidify_pullback_of_ofPoint_of_isIso
    hD hD 𝔓.w.hom 𝔓.w_over wstar (fun t a => hw t a) (genPt p) (bar y) (bar y') (bar ε') hy'bar hε'bar a' ha' b c hb' hc'

end S_ModularCurve_DRModelPackageLevel_mul_atkinLehnerHom_ajbar_ajbar_eq_of_comp_w
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_mul_atkinLehnerHom_ajbar_ajbar_eq_of_comp_w (solution)
