-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/42e325a0-215d-5c83-875e-f0d0b1feab5b

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

import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve ModularCurve.DRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicCurve"

namespace P3bKit

universe u

theorem smoothOfRelativeDimension_one_of_iso {S X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} (e : X ≅ Y)
    (he : e.inv ≫ f = g) [SmoothOfRelativeDimension 1 f] : SmoothOfRelativeDimension 1 g := by
  rw [← he]
  exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1) e.inv f).mpr ‹_›

theorem nonempty_pullback_ker_invModule_iso_of_isIso {X Y T : Scheme.{u}} (f : Y ⟶ X) [IsIso f] (p : T ⟶ X)
    [IsClosedImmersion p] (p' : T ⟶ Y) (hp : p' ≫ f = p) (hI : p.ker.IsInvertible) (hI' : p'.ker.IsInvertible) :
    Nonempty ((Scheme.Modules.pullback f).obj p.ker.invModule ≅ p'.ker.invModule) ∧
      Nonempty ((Scheme.Modules.pullback f).obj p.ker.module ≅ p'.ker.module) := by
  obtain ⟨⟨e₁⟩, ⟨e₂⟩⟩ := Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso f p p' hp hI hI' 1
  refine ⟨⟨?_ ≪≫ e₁ ≪≫ eqToIso (by rw [pow_one])⟩, ⟨?_ ≪≫ e₂ ≪≫ eqToIso (by rw [pow_one])⟩⟩
  · exact eqToIso (by rw [pow_one])
  · exact eqToIso (by rw [pow_one])

end P3bKit

attribute [reassoc] AlgebraicGeometry.RelPicard.BaseChange.baseChangeSnd_fst' AlgebraicGeometry.RelPicard.BaseChange.baseChangeSnd_snd'
  AlgebraicGeometry.RelPicard.BaseChange.κ_hom_fst AlgebraicGeometry.RelPicard.BaseChange.κ_hom_snd

open ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard.BaseChange in
theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    [IsProper (toBase N₀ p)]
    (D : RelativePic0Designation (R p) (toBase N₀ p))
    (hD : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) D)
    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)) (D.baseChange ℚ))
    (hPQ : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase N₀ p) 𝔓.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) ℚ), pullback.condition⟩)).L))
    (ajQ : SchemeHomOver (baseChange (R p) (toBase N₀ p) ℚ) (D.baseChange ℚ).toBase)
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
    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
    (ybar : SchemeHomOver (genPt p) (toBase N₀ p)) (hybar : ybar.1 = y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))
    (a : SchemeHomOver (genPt p) D.toBase) (ha : a.1 = y.1 ≫ ajbar) :
    Nonempty ((hD.poincare.pullbackAlong a).L ≅
      (RelEffCartierDiv.ofPoint (toBase N₀ p) ybar.1 ybar.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint (toBase N₀ p) (genPt p ≫ 𝔓.εinf.1)
          ((Category.assoc _ _ _).trans ((congrArg (genPt p ≫ ·) 𝔓.εinf.2).trans (Category.comp_id _)))).idealModule) := by
  obtain ⟨ePQ⟩ := hPQ
  have heeta : 𝔓.eeta ≫ pullback.snd (toBase N₀ p) (genPt p) = 𝔓.Meta.toBase := 𝔓.heeta

  have hgen : genPt p = specMap ℚ (AlgebraicClosure ℚ) ≫ specMap (R p) ℚ := by
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    first
      | rfl
      | (congr 2; exact IsScalarTower.algebraMap_eq _ _ _)
      | (congr 2; ext x; simp [IsScalarTower.algebraMap_apply])

  have hΦinv : (pullback.fst (baseChange (R p) (toBase N₀ p) ℚ) (specMap ℚ (AlgebraicClosure ℚ)) ≫
      pullback.fst (toBase N₀ p) (specMap (R p) ℚ)) ≫ toBase N₀ p =
      pullback.snd (baseChange (R p) (toBase N₀ p) ℚ) (specMap ℚ (AlgebraicClosure ℚ)) ≫ genPt p := by
    rw [Category.assoc, pullback.condition, hgen]
    exact pullback.condition_assoc _
  let Φ : pullback (toBase N₀ p) (genPt p) ≅ pullback (baseChange (R p) (toBase N₀ p) ℚ) (specMap ℚ (AlgebraicClosure ℚ)) :=
    { hom := pullback.lift kQ (pullback.snd (toBase N₀ p) (genPt p)) hkQ₂
      inv := pullback.lift (pullback.fst _ _ ≫ pullback.fst (toBase N₀ p) (specMap (R p) ℚ)) (pullback.snd _ _) hΦinv
      hom_inv_id := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, hkQ₁, Category.id_comp]
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp]
      inv_hom_id := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, Category.id_comp]
          apply pullback.hom_ext
          · rw [Category.assoc, hkQ₁, pullback.lift_fst]
          · rw [Category.assoc, hkQ₂, pullback.lift_snd_assoc]
            exact (pullback.condition).symm
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp] }
  have hΦfst : Φ.hom ≫ pullback.fst _ _ = kQ := pullback.lift_fst _ _ _
  have hΦsnd : Φ.hom ≫ pullback.snd _ _ = pullback.snd (toBase N₀ p) (genPt p) := pullback.lift_snd _ _ _
  clear_value Φ
  haveI hΦiso : IsIso Φ.hom := inferInstance

  haveI := 𝔓.smooth_generic
  haveI : SmoothOfRelativeDimension 1
      (pullback.snd (baseChange (R p) (toBase N₀ p) ℚ) (specMap ℚ (AlgebraicClosure ℚ))) := inferInstance
  haveI hsY : SmoothOfRelativeDimension 1 (pullback.snd (toBase N₀ p) (genPt p)) :=
    P3bKit.smoothOfRelativeDimension_one_of_iso Φ.symm hΦsnd
  haveI : IsSeparated (pullback.snd (toBase N₀ p) (genPt p)) := inferInstance
  haveI : IsSeparated (pullback.snd (baseChange (R p) (toBase N₀ p) ℚ) (specMap ℚ (AlgebraicClosure ℚ))) := inferInstance

  have hx : (y.1 ≫ 𝔓.eeta ≫ kQ) ≫ baseChange (R p) (toBase N₀ p) ℚ = specMap ℚ (AlgebraicClosure ℚ) := by
    simp only [Category.assoc]
    rw [hkQ₂, reassoc_of% heeta, reassoc_of% y.2]
  obtain ⟨eAJ⟩ := hajQ (AlgebraicClosure ℚ) (specMap ℚ (AlgebraicClosure ℚ)) ⟨y.1 ≫ 𝔓.eeta ≫ kQ, hx⟩

  have hgy : graphOver (toBase N₀ p) ybar.1 ybar.2 = y.1 ≫ 𝔓.eeta := by
    apply pullback.hom_ext
    · rw [graphOver_fst, hybar, Category.assoc]
    · rw [graphOver_snd, Category.assoc, heeta, y.2]
  have hgraphA : graphOver (toBase N₀ p) ybar.1 ybar.2 ≫ Φ.hom =
      graphOver (baseChange (R p) (toBase N₀ p) ℚ) (y.1 ≫ 𝔓.eeta ≫ kQ) hx := by
    apply pullback.hom_ext
    · rw [Category.assoc, hΦfst, graphOver_fst, hgy, Category.assoc]
    · rw [Category.assoc, hΦsnd, graphOver_snd, graphOver_snd]
  have hεQ : (specMap ℚ (AlgebraicClosure ℚ) ≫ (sectionBaseChange ℚ 𝔓.εinf).1) ≫ baseChange (R p) (toBase N₀ p) ℚ =
      specMap ℚ (AlgebraicClosure ℚ) :=
    (Category.assoc _ _ _).trans ((congrArg (specMap ℚ (AlgebraicClosure ℚ) ≫ ·) (sectionBaseChange ℚ 𝔓.εinf).2).trans
      (Category.comp_id _))
  have hε : (genPt p ≫ 𝔓.εinf.1) ≫ toBase N₀ p = genPt p :=
    (Category.assoc _ _ _).trans ((congrArg (genPt p ≫ ·) 𝔓.εinf.2).trans (Category.comp_id _))
  have hgraphB : graphOver (toBase N₀ p) (genPt p ≫ 𝔓.εinf.1) hε ≫ Φ.hom =
      graphOver (baseChange (R p) (toBase N₀ p) ℚ) (specMap ℚ (AlgebraicClosure ℚ) ≫ (sectionBaseChange ℚ 𝔓.εinf).1) hεQ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hΦfst, graphOver_fst]
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, hkQ₁, graphOver_fst, sectionBaseChange_coe_fst, hgen, Category.assoc]
      · rw [Category.assoc, Category.assoc, hkQ₂, graphOver_snd_assoc, sectionBaseChange_coe_snd, Category.comp_id]
    · rw [Category.assoc, hΦsnd, graphOver_snd, graphOver_snd]

  have hIA := Scheme.Hom.isInvertible_ker_of_comp_eq_id
    (p := pullback.snd (baseChange (R p) (toBase N₀ p) ℚ) (specMap ℚ (AlgebraicClosure ℚ)))
    (graphOver (baseChange (R p) (toBase N₀ p) ℚ) (y.1 ≫ 𝔓.eeta ≫ kQ) hx) (graphOver_snd _ _ _)
  have hIA' := Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd (toBase N₀ p) (genPt p))
    (graphOver (toBase N₀ p) ybar.1 ybar.2) (graphOver_snd _ _ _)
  have hIB := Scheme.Hom.isInvertible_ker_of_comp_eq_id
    (p := pullback.snd (baseChange (R p) (toBase N₀ p) ℚ) (specMap ℚ (AlgebraicClosure ℚ)))
    (graphOver (baseChange (R p) (toBase N₀ p) ℚ) (specMap ℚ (AlgebraicClosure ℚ) ≫ (sectionBaseChange ℚ 𝔓.εinf).1) hεQ)
    (graphOver_snd _ _ _)
  have hIB' := Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd (toBase N₀ p) (genPt p))
    (graphOver (toBase N₀ p) (genPt p ≫ 𝔓.εinf.1) hε) (graphOver_snd _ _ _)
  obtain ⟨⟨jA⟩, -⟩ := P3bKit.nonempty_pullback_ker_invModule_iso_of_isIso Φ.hom _ _ hgraphA hIA hIA'
  obtain ⟨-, ⟨jB⟩⟩ := P3bKit.nonempty_pullback_ker_invModule_iso_of_isIso Φ.hom _ _ hgraphB hIB hIB'

  have haQ : ((y.1 ≫ 𝔓.eeta ≫ kQ) ≫ ajQ.1) ≫ (D.baseChange ℚ).toBase = specMap ℚ (AlgebraicClosure ℚ) :=
    (Category.assoc _ _ _).trans ((congrArg ((y.1 ≫ 𝔓.eeta ≫ kQ) ≫ ·) ajQ.2).trans hx)
  have hcomp : baseChangeSnd (toBase N₀ p) a =
      Φ.hom ≫ baseChangeSnd (baseChange (R p) (toBase N₀ p) ℚ)
          (⟨(y.1 ≫ 𝔓.eeta ≫ kQ) ≫ ajQ.1, haQ⟩ : SchemeHomOver (specMap ℚ (AlgebraicClosure ℚ)) (D.baseChange ℚ).toBase) ≫
        (κ (toBase N₀ p) ℚ (D.baseChange ℚ).toBase).hom ≫
        baseChangeSnd (toBase N₀ p) (⟨pullback.fst D.toBase (specMap (R p) ℚ), pullback.condition⟩ :
          SchemeHomOver ((D.baseChange ℚ).toBase ≫ specMap (R p) ℚ) D.toBase) := by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, baseChangeSnd_fst', baseChangeSnd_snd', baseChangeSnd_fst'_assoc,
        baseChangeSnd_snd'_assoc, κ_hom_fst, κ_hom_snd_assoc, reassoc_of% hΦfst,
        reassoc_of% hΦsnd, hkQ₁, ha, hajbar]

  refine ⟨(Scheme.Modules.pullbackCongr hcomp).app hD.poincare.L ≪≫
    ((Scheme.Modules.pullbackComp Φ.hom _).app _).symm ≪≫
    (Scheme.Modules.pullback Φ.hom).mapIso
      (((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
        (Scheme.Modules.pullback _).mapIso (((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫ ePQ.symm) ≪≫ eAJ) ≪≫
    Scheme.Modules.pullbackTensorObjIso Φ.hom _ _ ≪≫ (jA ⊗ᵢ jB)⟩

end S_ModularCurve_DRModelPackageLevel_nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar (solution)
