-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/d47dd590-d0d1-53e0-be79-109e7369f47f

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_ModularCurve_ComponentGroup

import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve"

open ModularCurve.JHNeronObjectAtP (Fbar)
open scoped MatrixGroups

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

section ReassocKit
open AlgebraicGeometry.RelPicard AlgebraicGeometry.RelPicard.BaseChange
universe v
variable {R R' : Type v} [CommRing R] [CommRing R'] [Algebra R R'] {C : Scheme.{v}}

theorem baseChangeSnd_fst'_assoc {T T' : Scheme.{v}} (cc : C ⟶ Spec (CommRingCat.of R'))
    {t : T ⟶ Spec (CommRingCat.of R')} {t' : T' ⟶ Spec (CommRingCat.of R')} (ψ : SchemeHomOver t' t)
    {Z : Scheme.{v}} (h : C ⟶ Z) :
    baseChangeSnd cc ψ ≫ pullback.fst cc t ≫ h = pullback.fst cc t' ≫ h := by
  rw [← Category.assoc, baseChangeSnd_fst']

theorem baseChangeSnd_snd'_assoc {T T' : Scheme.{v}} (cc : C ⟶ Spec (CommRingCat.of R'))
    {t : T ⟶ Spec (CommRingCat.of R')} {t' : T' ⟶ Spec (CommRingCat.of R')} (ψ : SchemeHomOver t' t)
    {Z : Scheme.{v}} (h : T ⟶ Z) :
    baseChangeSnd cc ψ ≫ pullback.snd cc t ≫ h = pullback.snd cc t' ≫ ψ.1 ≫ h := by
  rw [← Category.assoc, baseChangeSnd_snd', Category.assoc]

theorem κ_hom_snd_assoc (c : C ⟶ Spec (CommRingCat.of R)) {T : Scheme.{v}} (t' : T ⟶ Spec (CommRingCat.of R'))
    {Z : Scheme.{v}} (h : T ⟶ Z) :
    (κ c R' t').hom ≫ pullback.snd c (t' ≫ specMap R R') ≫ h = pullback.snd (baseChange R c R') t' ≫ h := by
  rw [← Category.assoc, κ_hom_snd]

end ReassocKit

end P3bKit

open AlgebraicGeometry.RelPicard.BaseChange P3bKit in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    [IsSeparated (toBase p (ΓM M H) hj)] [IsSeparated (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)]
    (D : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) D)

    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
          (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (D.baseChange ℚ))
    (ajQ : SchemeHomOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (D.baseChange ℚ).toBase)
    (kQ : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ℚ))
    (ajbar : 𝔛.Meta.C ⟶ D.P)
    (hPQ : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) ℚ), pullback.condition⟩)).L))
    (hajcl : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
          (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)),
        Nonempty ((hDQ.poincare.pullbackAlong
            ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
                (Category.comp_id t)))).idealModule))
    (hkQ₁ : kQ ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))
    (hajbar : ajbar = 𝔛.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (R p) ℚ))

    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (ybar : SchemeHomOver (genPt p) (toBase p (ΓM M H) hj))
    (hybar : ybar.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (a : SchemeHomOver (genPt p) D.toBase) (ha : a.1 = y.1 ≫ ajbar) :
    Nonempty ((hD.poincare.pullbackAlong a).L ≅
      (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) ybar.1 ybar.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) (genPt p ≫ 𝔛.εinf.1)
          ((Category.assoc _ _ _).trans ((congrArg (genPt p ≫ ·) 𝔛.εinf.2).trans (Category.comp_id _)))).idealModule) := by
  obtain ⟨ePQ⟩ := hPQ
  have heeta : 𝔛.eeta ≫ pullback.snd (toBase p (ΓM M H) hj) (genPt p) = 𝔛.Meta.toBase := 𝔛.heeta

  have hgen : genPt p = specMap ℚ (AlgebraicClosure ℚ) ≫ specMap (R p) ℚ := by
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    first | rfl | (congr 2; exact IsScalarTower.algebraMap_eq _ _ _)

  have hΦinv : (pullback.fst (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (specMap ℚ (AlgebraicClosure ℚ)) ≫
      pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ)) ≫ toBase p (ΓM M H) hj =
      pullback.snd (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (specMap ℚ (AlgebraicClosure ℚ)) ≫ genPt p := by
    rw [Category.assoc, pullback.condition, hgen]
    exact pullback.condition_assoc _
  let Φ : pullback (toBase p (ΓM M H) hj) (genPt p) ≅ pullback (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (specMap ℚ (AlgebraicClosure ℚ)) :=
    { hom := pullback.lift kQ (pullback.snd (toBase p (ΓM M H) hj) (genPt p)) hkQ₂
      inv := pullback.lift (pullback.fst _ _ ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ)) (pullback.snd _ _) hΦinv
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
  have hΦsnd : Φ.hom ≫ pullback.snd _ _ = pullback.snd (toBase p (ΓM M H) hj) (genPt p) := pullback.lift_snd _ _ _
  clear_value Φ
  haveI hΦiso : IsIso Φ.hom := inferInstance

  haveI := 𝔛.smooth_generic
  haveI : SmoothOfRelativeDimension 1
      (pullback.snd (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (specMap ℚ (AlgebraicClosure ℚ))) := inferInstance
  haveI hsY : SmoothOfRelativeDimension 1 (pullback.snd (toBase p (ΓM M H) hj) (genPt p)) :=
    P3bKit.smoothOfRelativeDimension_one_of_iso Φ.symm hΦsnd
  haveI : IsSeparated (pullback.snd (toBase p (ΓM M H) hj) (genPt p)) := inferInstance
  haveI : IsSeparated (pullback.snd (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (specMap ℚ (AlgebraicClosure ℚ))) := inferInstance

  have hx : (y.1 ≫ 𝔛.eeta ≫ kQ) ≫ baseChange (R p) (toBase p (ΓM M H) hj) ℚ = specMap ℚ (AlgebraicClosure ℚ) := by
    simp only [Category.assoc]
    rw [hkQ₂, reassoc_of% heeta, reassoc_of% y.2]
  obtain ⟨eAJ⟩ := hajcl (AlgebraicClosure ℚ) (specMap ℚ (AlgebraicClosure ℚ)) ⟨y.1 ≫ 𝔛.eeta ≫ kQ, hx⟩

  have hgy : graphOver (toBase p (ΓM M H) hj) ybar.1 ybar.2 = y.1 ≫ 𝔛.eeta := by
    apply pullback.hom_ext
    · rw [graphOver_fst, hybar, Category.assoc]
    · rw [graphOver_snd, Category.assoc, heeta, y.2]
  have hgraphA : graphOver (toBase p (ΓM M H) hj) ybar.1 ybar.2 ≫ Φ.hom =
      graphOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (y.1 ≫ 𝔛.eeta ≫ kQ) hx := by
    apply pullback.hom_ext
    · rw [Category.assoc, hΦfst, graphOver_fst, hgy, Category.assoc]
    · rw [Category.assoc, hΦsnd, graphOver_snd, graphOver_snd]
  have hεQ : (specMap ℚ (AlgebraicClosure ℚ) ≫ (sectionBaseChange ℚ 𝔛.εinf).1) ≫ baseChange (R p) (toBase p (ΓM M H) hj) ℚ =
      specMap ℚ (AlgebraicClosure ℚ) :=
    (Category.assoc _ _ _).trans ((congrArg (specMap ℚ (AlgebraicClosure ℚ) ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
      (Category.comp_id _))
  have hε : (genPt p ≫ 𝔛.εinf.1) ≫ toBase p (ΓM M H) hj = genPt p :=
    (Category.assoc _ _ _).trans ((congrArg (genPt p ≫ ·) 𝔛.εinf.2).trans (Category.comp_id _))
  have hgraphB : graphOver (toBase p (ΓM M H) hj) (genPt p ≫ 𝔛.εinf.1) hε ≫ Φ.hom =
      graphOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (specMap ℚ (AlgebraicClosure ℚ) ≫ (sectionBaseChange ℚ 𝔛.εinf).1) hεQ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hΦfst, graphOver_fst]
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, hkQ₁, graphOver_fst, sectionBaseChange_coe_fst, hgen, Category.assoc]
      · rw [Category.assoc, Category.assoc, hkQ₂, graphOver_snd_assoc, sectionBaseChange_coe_snd, Category.comp_id]
    · rw [Category.assoc, hΦsnd, graphOver_snd, graphOver_snd]

  have hIA := Scheme.Hom.isInvertible_ker_of_comp_eq_id
    (p := pullback.snd (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (specMap ℚ (AlgebraicClosure ℚ)))
    (graphOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (y.1 ≫ 𝔛.eeta ≫ kQ) hx) (graphOver_snd _ _ _)
  have hIA' := Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd (toBase p (ΓM M H) hj) (genPt p))
    (graphOver (toBase p (ΓM M H) hj) ybar.1 ybar.2) (graphOver_snd _ _ _)
  have hIB := Scheme.Hom.isInvertible_ker_of_comp_eq_id
    (p := pullback.snd (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (specMap ℚ (AlgebraicClosure ℚ)))
    (graphOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (specMap ℚ (AlgebraicClosure ℚ) ≫ (sectionBaseChange ℚ 𝔛.εinf).1) hεQ)
    (graphOver_snd _ _ _)
  have hIB' := Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd (toBase p (ΓM M H) hj) (genPt p))
    (graphOver (toBase p (ΓM M H) hj) (genPt p ≫ 𝔛.εinf.1) hε) (graphOver_snd _ _ _)
  obtain ⟨⟨jA⟩, -⟩ := P3bKit.nonempty_pullback_ker_invModule_iso_of_isIso Φ.hom _ _ hgraphA hIA hIA'
  obtain ⟨-, ⟨jB⟩⟩ := P3bKit.nonempty_pullback_ker_invModule_iso_of_isIso Φ.hom _ _ hgraphB hIB hIB'

  have haQ : ((y.1 ≫ 𝔛.eeta ≫ kQ) ≫ ajQ.1) ≫ (D.baseChange ℚ).toBase = specMap ℚ (AlgebraicClosure ℚ) :=
    (Category.assoc _ _ _).trans ((congrArg ((y.1 ≫ 𝔛.eeta ≫ kQ) ≫ ·) ajQ.2).trans hx)
  have hcomp : baseChangeSnd (toBase p (ΓM M H) hj) a =
      Φ.hom ≫ baseChangeSnd (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)
          (⟨(y.1 ≫ 𝔛.eeta ≫ kQ) ≫ ajQ.1, haQ⟩ : SchemeHomOver (specMap ℚ (AlgebraicClosure ℚ)) (D.baseChange ℚ).toBase) ≫
        (κ (toBase p (ΓM M H) hj) ℚ (D.baseChange ℚ).toBase).hom ≫
        baseChangeSnd (toBase p (ΓM M H) hj) (⟨pullback.fst D.toBase (specMap (R p) ℚ), pullback.condition⟩ :
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

end S_ModularCurve_XHDRModelAtP_nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar (solution)
