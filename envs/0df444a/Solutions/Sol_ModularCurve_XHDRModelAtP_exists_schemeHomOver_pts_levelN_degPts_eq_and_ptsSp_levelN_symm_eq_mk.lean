-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_schemeHomOver_pts_levelN_degPts_eq_and_ptsSp_levelN_symm_eq_mk
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/5dc965f9-6424-55d3-a941-78de2f56e289

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_DivisorPushPull
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
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_JacJ1Iface

import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_module_tensor_invModule_iso
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_nonempty_pullback_ofPoint_lineBundle_iso_and_idealModule_iso_of_range_subset
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_one_iso
import Theorems.Thm_ModularCurve_inertiaDegAlong_eq_one_laurentBaseChange_qExpFunctionFieldC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_schemeHomOver_pts_levelN_degPts_eq_and_ptsSp_levelN_symm_eq_mk
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve"

open ModularCurve.JHNeronObjectAtP (Fbar)
open scoped MatrixGroups

namespace G2Kit

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

noncomputable def monoidalCancel {C : Type*} [Category C] [MonoidalCategory C] {M M' N N' : C}
    (eN : N ⊗ N' ≅ 𝟙_ C) (e : M ⊗ N ≅ M' ⊗ N) : M ≅ M' :=
  (ρ_ M).symm ≪≫ (whiskerLeftIso M eN.symm) ≪≫ (α_ M N N').symm ≪≫ (whiskerRightIso e N') ≪≫ α_ M' N N' ≪≫
    whiskerLeftIso M' eN ≪≫ ρ_ M'

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

end G2Kit

namespace G2Body

open AlgebraicGeometry.RelPicard.BaseChange G2Kit in

theorem ajRead
    (p : ℕ) [Fact p.Prime] (Γ : Subgroup SL(2, ℤ))
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (ε : SchemeHomOver (𝟙 _) (toBase p Γ hj))
    [IsSeparated (toBase p Γ hj)] [IsSeparated (baseChange (R p) (toBase p Γ hj) ℚ)]
    [SmoothOfRelativeDimension 1 (baseChange (R p) (toBase p Γ hj) ℚ)]
    {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]
    (Meta : CurveModel (AlgebraicClosure ℚ) F)
    (eeta : Meta.C ⟶ pullback (toBase p Γ hj) (genPt p)) [IsIso eeta]
    (heeta : eeta ≫ pullback.snd (toBase p Γ hj) (genPt p) = Meta.toBase)
    (D : RelativePic0Designation (R p) (toBase p Γ hj))
    (hD : RepresentsRelSubPic (toBase p Γ hj) ε (algEquivZeroCut (toBase p Γ hj) ε) D)
    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p Γ hj) ℚ) (sectionBaseChange ℚ ε)
          (algEquivZeroCut (baseChange (R p) (toBase p Γ hj) ℚ) (sectionBaseChange ℚ ε)) (D.baseChange ℚ))
    (ajQ : SchemeHomOver (baseChange (R p) (toBase p Γ hj) ℚ) (D.baseChange ℚ).toBase)
    (kQ : pullback (toBase p Γ hj) (genPt p) ⟶ pullback (toBase p Γ hj) (specMap (R p) ℚ))
    (ajbar : Meta.C ⟶ D.P)
    (hPQ : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p Γ hj) ε ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) ℚ), pullback.condition⟩)).L))
    (hajcl : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
          (x : SchemeHomOver t (baseChange (R p) (toBase p Γ hj) ℚ)),
        Nonempty ((hDQ.poincare.pullbackAlong
            ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p Γ hj) ℚ) x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p Γ hj) ℚ) (t ≫ (sectionBaseChange ℚ ε).1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ ε).2).trans
                (Category.comp_id t)))).idealModule))
    (hkQ₁ : kQ ≫ pullback.fst (toBase p Γ hj) (specMap (R p) ℚ) = pullback.fst (toBase p Γ hj) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase p Γ hj) (specMap (R p) ℚ) = pullback.snd (toBase p Γ hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))
    (hajbar : ajbar = eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (R p) ℚ))
    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta.C // q ≫ Meta.toBase = 𝟙 _})
    (ybar : SchemeHomOver (genPt p) (toBase p Γ hj))
    (hybar : ybar.1 = y.1 ≫ eeta ≫ pullback.fst (toBase p Γ hj) (genPt p))
    (a : SchemeHomOver (genPt p) D.toBase) (ha : a.1 = y.1 ≫ ajbar) :
    Nonempty ((hD.poincare.pullbackAlong a).L ≅
      (RelEffCartierDiv.ofPoint (toBase p Γ hj) ybar.1 ybar.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint (toBase p Γ hj) (genPt p ≫ ε.1)
          ((Category.assoc _ _ _).trans ((congrArg (genPt p ≫ ·) ε.2).trans (Category.comp_id _)))).idealModule) := by
  obtain ⟨ePQ⟩ := hPQ

  have hgen : genPt p = specMap ℚ (AlgebraicClosure ℚ) ≫ specMap (R p) ℚ := by
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl

  have hΦinv : (pullback.fst (baseChange (R p) (toBase p Γ hj) ℚ) (specMap ℚ (AlgebraicClosure ℚ)) ≫
      pullback.fst (toBase p Γ hj) (specMap (R p) ℚ)) ≫ toBase p Γ hj =
      pullback.snd (baseChange (R p) (toBase p Γ hj) ℚ) (specMap ℚ (AlgebraicClosure ℚ)) ≫ genPt p := by
    rw [Category.assoc, pullback.condition, hgen]
    exact pullback.condition_assoc _
  let Φ : pullback (toBase p Γ hj) (genPt p) ≅ pullback (baseChange (R p) (toBase p Γ hj) ℚ) (specMap ℚ (AlgebraicClosure ℚ)) :=
    { hom := pullback.lift kQ (pullback.snd (toBase p Γ hj) (genPt p)) hkQ₂
      inv := pullback.lift (pullback.fst _ _ ≫ pullback.fst (toBase p Γ hj) (specMap (R p) ℚ)) (pullback.snd _ _) hΦinv
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
  have hΦsnd : Φ.hom ≫ pullback.snd _ _ = pullback.snd (toBase p Γ hj) (genPt p) := pullback.lift_snd _ _ _
  clear_value Φ
  haveI hΦiso : IsIso Φ.hom := inferInstance

  haveI : SmoothOfRelativeDimension 1
      (pullback.snd (baseChange (R p) (toBase p Γ hj) ℚ) (specMap ℚ (AlgebraicClosure ℚ))) := inferInstance
  haveI hsY : SmoothOfRelativeDimension 1 (pullback.snd (toBase p Γ hj) (genPt p)) :=
    G2Kit.smoothOfRelativeDimension_one_of_iso Φ.symm hΦsnd
  haveI : IsSeparated (pullback.snd (toBase p Γ hj) (genPt p)) := inferInstance
  haveI : IsSeparated (pullback.snd (baseChange (R p) (toBase p Γ hj) ℚ) (specMap ℚ (AlgebraicClosure ℚ))) := inferInstance

  have hx : (y.1 ≫ eeta ≫ kQ) ≫ baseChange (R p) (toBase p Γ hj) ℚ = specMap ℚ (AlgebraicClosure ℚ) := by
    simp only [Category.assoc]
    rw [hkQ₂, reassoc_of% heeta, reassoc_of% y.2]
  obtain ⟨eAJ⟩ := hajcl (AlgebraicClosure ℚ) (specMap ℚ (AlgebraicClosure ℚ)) ⟨y.1 ≫ eeta ≫ kQ, hx⟩

  have hgy : graphOver (toBase p Γ hj) ybar.1 ybar.2 = y.1 ≫ eeta := by
    apply pullback.hom_ext
    · rw [graphOver_fst, hybar, Category.assoc]
    · rw [graphOver_snd, Category.assoc, heeta, y.2]
  have hgraphA : graphOver (toBase p Γ hj) ybar.1 ybar.2 ≫ Φ.hom =
      graphOver (baseChange (R p) (toBase p Γ hj) ℚ) (y.1 ≫ eeta ≫ kQ) hx := by
    apply pullback.hom_ext
    · rw [Category.assoc, hΦfst, graphOver_fst, hgy, Category.assoc]
    · rw [Category.assoc, hΦsnd, graphOver_snd, graphOver_snd]
  have hεQ : (specMap ℚ (AlgebraicClosure ℚ) ≫ (sectionBaseChange ℚ ε).1) ≫ baseChange (R p) (toBase p Γ hj) ℚ =
      specMap ℚ (AlgebraicClosure ℚ) :=
    (Category.assoc _ _ _).trans ((congrArg (specMap ℚ (AlgebraicClosure ℚ) ≫ ·) (sectionBaseChange ℚ ε).2).trans
      (Category.comp_id _))
  have hε : (genPt p ≫ ε.1) ≫ toBase p Γ hj = genPt p :=
    (Category.assoc _ _ _).trans ((congrArg (genPt p ≫ ·) ε.2).trans (Category.comp_id _))
  have hgraphB : graphOver (toBase p Γ hj) (genPt p ≫ ε.1) hε ≫ Φ.hom =
      graphOver (baseChange (R p) (toBase p Γ hj) ℚ) (specMap ℚ (AlgebraicClosure ℚ) ≫ (sectionBaseChange ℚ ε).1) hεQ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hΦfst, graphOver_fst]
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, hkQ₁, graphOver_fst, sectionBaseChange_coe_fst, hgen, Category.assoc]
      · rw [Category.assoc, Category.assoc, hkQ₂, graphOver_snd_assoc, sectionBaseChange_coe_snd, Category.comp_id]
    · rw [Category.assoc, hΦsnd, graphOver_snd, graphOver_snd]

  have hIA := Scheme.Hom.isInvertible_ker_of_comp_eq_id
    (p := pullback.snd (baseChange (R p) (toBase p Γ hj) ℚ) (specMap ℚ (AlgebraicClosure ℚ)))
    (graphOver (baseChange (R p) (toBase p Γ hj) ℚ) (y.1 ≫ eeta ≫ kQ) hx) (graphOver_snd _ _ _)
  have hIA' := Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd (toBase p Γ hj) (genPt p))
    (graphOver (toBase p Γ hj) ybar.1 ybar.2) (graphOver_snd _ _ _)
  have hIB := Scheme.Hom.isInvertible_ker_of_comp_eq_id
    (p := pullback.snd (baseChange (R p) (toBase p Γ hj) ℚ) (specMap ℚ (AlgebraicClosure ℚ)))
    (graphOver (baseChange (R p) (toBase p Γ hj) ℚ) (specMap ℚ (AlgebraicClosure ℚ) ≫ (sectionBaseChange ℚ ε).1) hεQ)
    (graphOver_snd _ _ _)
  have hIB' := Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd (toBase p Γ hj) (genPt p))
    (graphOver (toBase p Γ hj) (genPt p ≫ ε.1) hε) (graphOver_snd _ _ _)
  obtain ⟨⟨jA⟩, -⟩ := G2Kit.nonempty_pullback_ker_invModule_iso_of_isIso Φ.hom _ _ hgraphA hIA hIA'
  obtain ⟨-, ⟨jB⟩⟩ := G2Kit.nonempty_pullback_ker_invModule_iso_of_isIso Φ.hom _ _ hgraphB hIB hIB'

  have haQ : ((y.1 ≫ eeta ≫ kQ) ≫ ajQ.1) ≫ (D.baseChange ℚ).toBase = specMap ℚ (AlgebraicClosure ℚ) :=
    (Category.assoc _ _ _).trans ((congrArg ((y.1 ≫ eeta ≫ kQ) ≫ ·) ajQ.2).trans hx)
  have hcomp : baseChangeSnd (toBase p Γ hj) a =
      Φ.hom ≫ baseChangeSnd (baseChange (R p) (toBase p Γ hj) ℚ)
          (⟨(y.1 ≫ eeta ≫ kQ) ≫ ajQ.1, haQ⟩ : SchemeHomOver (specMap ℚ (AlgebraicClosure ℚ)) (D.baseChange ℚ).toBase) ≫
        (κ (toBase p Γ hj) ℚ (D.baseChange ℚ).toBase).hom ≫
        baseChangeSnd (toBase p Γ hj) (⟨pullback.fst D.toBase (specMap (R p) ℚ), pullback.condition⟩ :
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

end G2Body

open G2Body in
open AlgebraicGeometry.RelPicard.BaseChange in
set_option maxHeartbeats 1600000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    [IsProper (toBase p (ΓM M H) hj)]
    [IsProper (toBase p (ΓN p M H hpM) hj)] [IsSeparated (toBase p (ΓN p M H hpM) hj)]

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (D₀ : RelativePic0Designation (R p) (toBase p (ΓN p M H hpM) hj))
    (hD₀ : RepresentsRelSubPic (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)
      (algEquivZeroCut (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)) D₀)

    (αH βH : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hαint : αH.toRingHom.IsIntegral) (hβint : βH.toRingHom.IsIntegral)
    (Meta₀ : CurveModel (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
    (eeta₀ : Meta₀.C ⟶ pullback (toBase p (XHDRLevel.ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))))
    [IsIso eeta₀]
    (heeta₀ : eeta₀ ≫ pullback.snd _ _ = Meta₀.toBase)
    (hMeta₀π : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}) (y₀ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _}),
      y₀.1 ≫ eeta₀ ≫ pullback.fst _ _ = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1 →
      Meta₀.pointEquivPlace y₀ = Place.restrictAlong αH hαint (𝔛.Meta.pointEquivPlace y))
    (hMeta₀πw : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}) (y₀ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _}),
      y₀.1 ≫ eeta₀ ≫ pullback.fst _ _ = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom ≫ 𝔛.π.1 →
      Meta₀.pointEquivPlace y₀ = Place.restrictAlong βH hβint (𝔛.Meta.pointEquivPlace y))
    (degPts : Fin 2 → (JH M H →+ JH (M / p) (infSubgroup p M H hpM)))
    (hdeg0 : ∀ (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))) (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))),
      (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) = Divisor.pushforwardAlong αH hαint (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) →
      degPts 0 (Pic0.mk Dv) = Pic0.mk Dw)
    (hdeg1 : ∀ (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))) (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))),
      (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) = Divisor.pushforwardAlong βH hβint (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) →
      degPts 1 (Pic0.mk Dv) = Pic0.mk Dw)

    (hDQ₀ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ) (sectionBaseChange ℚ (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π))
        (algEquivZeroCut (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ) (sectionBaseChange ℚ (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π))) (D₀.baseChange ℚ))
    (hPQ₀ : Nonempty (hDQ₀.poincare.L ≅ (BaseChange.ofR (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π) ℚ
        (hD₀.poincare.pullbackAlong ⟨pullback.fst D₀.toBase (specMap (R p) ℚ), pullback.condition⟩)).L))

    (ajQ₀ : SchemeHomOver (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ) (D₀.baseChange ℚ).toBase)
    (hajQ₀ε : (sectionBaseChange ℚ (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)).1 ≫ ajQ₀.1 = (D₀.baseChange ℚ).zeroSection)
    (hajQ₀ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ)),
      Nonempty ((hDQ₀.poincare.pullbackAlong
          ⟨x.1 ≫ ajQ₀.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ₀.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ) (t ≫ (sectionBaseChange ℚ (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)).2).trans
              (Category.comp_id t)))).idealModule))

    (kQ₀ : pullback (toBase p (ΓN p M H hpM) hj) (genPt p) ⟶ pullback (toBase p (ΓN p M H hpM) hj) (specMap (R p) ℚ))
    (hkQ₀₁ : kQ₀ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓN p M H hpM) hj) (genPt p))
    (hkQ₀₂ : kQ₀ ≫ pullback.snd (toBase p (ΓN p M H hpM) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓN p M H hpM) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))

    (ajbar₀ : Meta₀.C ⟶ D₀.P) (hajbar₀ : ajbar₀ = eeta₀ ≫ kQ₀ ≫ ajQ₀.1 ≫ pullback.fst D₀.toBase (specMap (R p) ℚ))
    (hajbar₀_over : ajbar₀ ≫ D₀.toBase = Meta₀.toBase ≫ genPt p)
    (εbar₀ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _})
    (hεbar₀ : εbar₀.1 ≫ eeta₀ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 ≫ 𝔛.π.1)
    (hεbar₀_aj : εbar₀.1 ≫ ajbar₀ = genPt p ≫ D₀.zeroSection)

    (pts₀ : JH (M / p) (infSubgroup p M H hpM) ≃ SchemeHomOver (genPt p) D₀.toBase)
    (hpts₀_add : ∀ x y : JH (M / p) (infSubgroup p M H hpM),
      pts₀ (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).mul _ (pts₀ x) (pts₀ y))
    (hpts₀_aj : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _}),
      s.1 ≫ eeta₀ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 ≫ 𝔛.π.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) =
          Finsupp.single (Meta₀.pointEquivPlace x) 1 - Finsupp.single (Meta₀.pointEquivPlace s) 1 ∧
        (pts₀ (Pic0.mk Dv)).1 = x.1 ≫ ajbar₀)
    (ptsSp₀ : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ≃
      SchemeHomOver (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) D₀.toBase)

    (hptsSp₀_add : ∀ a b, ptsSp₀ (a + b) =
      ofFibrePt (((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).baseChange
        (resPt A ≫ Spec.map (CommRingCat.ofHom ρ))).mul _ (toFibrePt (ptsSp₀ a)) (toFibrePt (ptsSp₀ b))))

    (hptsSp₀ : ∀ (v₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓN p M H hpM) hj))
      (vκ₁ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : vκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ v₁.1)
      (_ : vκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₁ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ).base Q₁.1 = vκ₁.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (v₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓN p M H hpM) hj))
      (vκ₂ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : vκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ v₂.1)
      (_ : vκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₂ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ).base Q₂.1 = vκ₂.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (Dw : Divisor.degZero (K := ResidueField ↥A) (F := Fbar p M H hpM (ResidueField ↥A)))
      (_ : (Dw : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) =
        Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₁) 1 - Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₂) 1),
      ∃ s₀ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D₀.toBase,
        Nonempty ((hD₀.poincare.pullbackAlong s₀).L ≅
          (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) v₁.1 v₁.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) v₂.1 v₂.2).idealModule) ∧
        ptsSp₀.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s₀) = Pic0.mk Dw) :
    ∀ (i : Fin 2)
      (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₁ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ).base Q₁.1 =
        (uκ₁ ≫ fibreMap (if i = 0 then 𝔛.π else 𝔛.πw) ((IsLocalRing.residue ↥A).comp ρ)).base
          (IsLocalRing.closedPoint (ResidueField ↥A)))
      (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₂ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ).base Q₂.1 =
        (uκ₂ ≫ fibreMap (if i = 0 then 𝔛.π else 𝔛.πw) ((IsLocalRing.residue ↥A).comp ρ)).base
          (IsLocalRing.closedPoint (ResidueField ↥A)))
      (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
      (_ : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1)
      (Dw : Divisor.degZero (K := ResidueField ↥A) (F := Fbar p M H hpM (ResidueField ↥A)))
      (_ : (Dw : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) =
        Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₂) 1),
      ∃ s₀ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D₀.toBase,
        (pts₀ (degPts i (Pic0.mk Dv))).1 = barPt A ≫ s₀.1 ∧
        ptsSp₀.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s₀) = Pic0.mk Dw := by
  intro i y₁ u₁ hu₁y uκ₁ huκ₁f huκ₁s Q₁ hQ₁ y₂ u₂ hu₂y uκ₂ huκ₂f huκ₂s Q₂ hQ₂ Dv hDv Dw hDw
  haveI : IsSeparated (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ) := by
    unfold baseChange; infer_instance
  haveI := 𝔛.smooth0
  haveI : SmoothOfRelativeDimension 1 (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ) := by
    unfold baseChange; infer_instance
  haveI : SmoothOfRelativeDimension 1 ((⊤ : (X p (ΓN p M H hpM) hj).Opens).ι ≫ toBase p (ΓN p M H hpM) hj) := by
    have h : SmoothOfRelativeDimension (0 + 1) ((⊤ : (X p (ΓN p M H hpM) hj).Opens).ι ≫ toBase p (ΓN p M H hpM) hj) :=
      AlgebraicGeometry.smoothOfRelativeDimension_comp (n := 0) (m := 1) (f := (⊤ : (X p (ΓN p M H hpM) hj).Opens).ι) (toBase p (ΓN p M H hpM) hj)
    simpa using h

  set πi : SchemeHomOver (toBase p (ΓM M H) hj) (toBase p (ΓN p M H hpM) hj) := (if i = 0 then 𝔛.π else 𝔛.πw) with hπi

  let v₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓN p M H hpM) hj) := NeronModelInfra.schemeHomOverComp u₁ πi
  let v₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓN p M H hpM) hj) := NeronModelInfra.schemeHomOverComp u₂ πi
  have hv₁ : v₁.1 = u₁.1 ≫ πi.1 := rfl
  have hv₂ : v₂.1 = u₂.1 ≫ πi.1 := rfl
  let vκ₁ := uκ₁ ≫ XHDRLevel.fibreMap πi ((IsLocalRing.residue ↥A).comp ρ)
  let vκ₂ := uκ₂ ≫ XHDRLevel.fibreMap πi ((IsLocalRing.residue ↥A).comp ρ)
  have hfm_fst : XHDRLevel.fibreMap πi ((IsLocalRing.residue ↥A).comp ρ) ≫ pullback.fst _ _ = pullback.fst _ _ ≫ πi.1 := by
    unfold XHDRLevel.fibreMap; exact pullback.lift_fst _ _ _
  have hfm_snd : XHDRLevel.fibreMap πi ((IsLocalRing.residue ↥A).comp ρ) ≫ pullback.snd _ _ = pullback.snd _ _ := by
    unfold XHDRLevel.fibreMap; rw [pullback.lift_snd, Category.comp_id]
  have hvκ₁f : vκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ v₁.1 := by
    show (uκ₁ ≫ _) ≫ _ = _ ≫ (u₁.1 ≫ πi.1)
    rw [Category.assoc, hfm_fst, ← Category.assoc, huκ₁f, Category.assoc]
  have hvκ₂f : vκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ v₂.1 := by
    show (uκ₂ ≫ _) ≫ _ = _ ≫ (u₂.1 ≫ πi.1)
    rw [Category.assoc, hfm_fst, ← Category.assoc, huκ₂f, Category.assoc]
  have hvκ₁s : vκ₁ ≫ pullback.snd _ _ = 𝟙 _ := by
    show (uκ₁ ≫ _) ≫ _ = _
    rw [Category.assoc, hfm_snd, huκ₁s]
  have hvκ₂s : vκ₂ ≫ pullback.snd _ _ = 𝟙 _ := by
    show (uκ₂ ≫ _) ≫ _ = _
    rw [Category.assoc, hfm_snd, huκ₂s]
  have hQ₁' : (𝔛.efib A hA ρ hρ).base Q₁.1 = vκ₁.base (IsLocalRing.closedPoint (ResidueField ↥A)) := hQ₁
  have hQ₂' : (𝔛.efib A hA ρ hρ).base Q₂.1 = vκ₂.base (IsLocalRing.closedPoint (ResidueField ↥A)) := hQ₂

  obtain ⟨s₀, ⟨eS⟩, hsp⟩ := hptsSp₀ v₁ vκ₁ hvκ₁f hvκ₁s Q₁ hQ₁' v₂ vκ₂ hvκ₂f hvκ₂s Q₂ hQ₂' Dw hDw
  refine ⟨s₀, ?_, hsp⟩

  have hbar : barPt A ≫ Spec.map (CommRingCat.ofHom ρ) = genPt p := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]
  let g' : SchemeHomOver (genPt p) D₀.toBase := ⟨barPt A ≫ s₀.1, by rw [Category.assoc, s₀.2, hbar]⟩

  have hinv₀ : inv eeta₀ ≫ Meta₀.toBase = pullback.snd _ _ := by
    rw [IsIso.inv_comp_eq, heeta₀]
  have hyc : ∀ y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _},
      (y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ πi.1) ≫ toBase p (ΓN p M H hpM) hj =
        𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))) := by
    intro y
    simp only [Category.assoc, πi.2]
    rw [pullback.condition, reassoc_of% 𝔛.heeta, reassoc_of% y.2, Category.id_comp]
  let dn : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _} →
      {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _} := fun y =>
    ⟨pullback.lift (y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ πi.1) (𝟙 _) (hyc y) ≫ inv eeta₀, by
      rw [Category.assoc, hinv₀, pullback.lift_snd]⟩
  have hdn : ∀ y, (dn y).1 ≫ eeta₀ ≫ pullback.fst _ _ = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ πi.1 := by
    intro y
    show (pullback.lift _ _ _ ≫ inv eeta₀) ≫ eeta₀ ≫ _ = _
    rw [Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst]
  set y₀₁ := dn y₁ with hy₀₁
  set y₀₂ := dn y₂ with hy₀₂
  have hv₁y : (⟨barPt A ≫ v₁.1, by rw [Category.assoc, v₁.2, hbar]⟩ : SchemeHomOver (genPt p) (toBase p (ΓN p M H hpM) hj)).1 =
      y₀₁.1 ≫ eeta₀ ≫ pullback.fst _ _ := by
    show barPt A ≫ u₁.1 ≫ πi.1 = _
    rw [hdn, ← Category.assoc, hu₁y]; simp only [Category.assoc]
  have hv₂y : (⟨barPt A ≫ v₂.1, by rw [Category.assoc, v₂.2, hbar]⟩ : SchemeHomOver (genPt p) (toBase p (ΓN p M H hpM) hj)).1 =
      y₀₂.1 ≫ eeta₀ ≫ pullback.fst _ _ := by
    show barPt A ≫ u₂.1 ≫ πi.1 = _
    rw [hdn, ← Category.assoc, hu₂y]; simp only [Category.assoc]

  obtain ⟨D₁, hD₁, hD₁pts⟩ := hpts₀_aj y₀₁ εbar₀ hεbar₀
  obtain ⟨D₂, hD₂, hD₂pts⟩ := hpts₀_aj y₀₂ εbar₀ hεbar₀

  have hle : CongruenceSubgroup.Gamma1 M ≤ CohCarrier.GammaH M H := by
    intro B hB
    rw [CongruenceSubgroup.Gamma1_mem] at hB
    obtain ⟨-, h11, h10⟩ := hB
    have hB0 : B ∈ CongruenceSubgroup.Gamma0 M := CongruenceSubgroup.Gamma0_mem.mpr h10
    refine CohCarrier.mem_GammaH_iff.mpr ⟨hB0, ?_⟩
    have : CohCarrier.gamma0Units M ⟨B, hB0⟩ = 1 := by
      apply Units.ext
      rw [CohCarrier.val_gamma0Units, Units.val_one]
      exact h11
    rw [this]; exact one_mem _
  haveI : (CohCarrier.GammaH M H).FiniteIndex := Subgroup.finiteIndex_of_le hle
  have hinert : ∀ (φ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
      (hφ : φ.toRingHom.IsIntegral) (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), W.inertiaDegAlong φ hφ = 1 :=
    fun φ hφ W => ModularCurve.inertiaDegAlong_eq_one_laurentBaseChange_qExpFunctionFieldC (CohCarrier.GammaH M H)
      (ModularCurve.translation_mem_GammaH M H) (xHFunctionField M H) rfl φ hφ W
  have hpush : ∀ (φ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
      (hφ : φ.toRingHom.IsIntegral),
      Meta₀.pointEquivPlace y₀₁ = Place.restrictAlong φ hφ (𝔛.Meta.pointEquivPlace y₁) →
      Meta₀.pointEquivPlace y₀₂ = Place.restrictAlong φ hφ (𝔛.Meta.pointEquivPlace y₂) →
      ((D₁ - D₂ : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))) :
          Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) =
        Divisor.pushforwardAlong φ hφ (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) := by
    intro φ hφ h1 h2
    rw [AddSubgroupClass.coe_sub, hD₁, hD₂, hDv, map_sub, Divisor.pushforwardAlong_single, Divisor.pushforwardAlong_single,
      hinert, hinert, Nat.cast_one, mul_one, ← h1, ← h2]
    abel
  have hdeg : degPts i (Pic0.mk Dv) = Pic0.mk (D₁ - D₂) := by
    revert hπi
    rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with rfl | rfl <;> intro hπi
    · refine hdeg0 Dv (D₁ - D₂) (hpush αH hαint ?_ ?_)
      · exact hMeta₀π y₁ y₀₁ (by rw [hdn]; simp [hπi])
      · exact hMeta₀π y₂ y₀₂ (by rw [hdn]; simp [hπi])
    · refine hdeg1 Dv (D₁ - D₂) (hpush βH hβint ?_ ?_)
      · exact hMeta₀πw y₁ y₀₁ (by rw [hdn]; simp [hπi, XHDRModelAtP.πw_val])
      · exact hMeta₀πw y₂ y₀₂ (by rw [hdn]; simp [hπi, XHDRModelAtP.πw_val])
  rw [hdeg]

  suffices h : pts₀ (Pic0.mk (D₁ - D₂)) = g' from congrArg (fun g : SchemeHomOver (genPt p) D₀.toBase => g.1) h
  refine hD₀.ext_of_iso (genPt p) (pts₀ (Pic0.mk (D₁ - D₂))) g' ?_
  set Dv₀ : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) := D₁ - D₂ with hDv₀def
  have hDv12 : Dv₀ = D₁ - D₂ := rfl

  let Lw := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀
  letI grp : Group (SchemeHomOver (genPt p) D₀.toBase) := Lw.pointGroup _
  letI := RepresentsRelSubPic.grpObj (P := algEquivZeroGroupCut _ _) hD₀
  have pts_mul : ∀ x y : JH (M / p) (infSubgroup p M H hpM), pts₀ (x + y) = pts₀ x * pts₀ y := fun x y => hpts₀_add x y
  have hkey : pts₀ (Pic0.mk Dv₀) * pts₀ (Pic0.mk D₂) = pts₀ (Pic0.mk D₁) := by
    rw [← pts_mul]
    congr 1
    show (QuotientAddGroup.mk' _) Dv₀ + (QuotientAddGroup.mk' _) D₂ = (QuotientAddGroup.mk' _) D₁
    rw [← map_add, hDv12, sub_add_cancel]

  have hy₁c : (barPt A ≫ v₁.1) ≫ toBase p (ΓN p M H hpM) hj = genPt p := by rw [Category.assoc, v₁.2, hbar]
  have hy₂c : (barPt A ≫ v₂.1) ≫ toBase p (ΓN p M H hpM) hj = genPt p := by rw [Category.assoc, v₂.2, hbar]
  obtain ⟨eP₁⟩ := ajRead p (ΓN p M H hpM) hj (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π) Meta₀ eeta₀ heeta₀ D₀ hD₀ hDQ₀ ajQ₀ kQ₀ ajbar₀ hPQ₀ hajQ₀ hkQ₀₁ hkQ₀₂ hajbar₀
    y₀₁ ⟨barPt A ≫ v₁.1, hy₁c⟩ hv₁y (pts₀ (Pic0.mk D₁)) hD₁pts
  obtain ⟨eP₂⟩ := ajRead p (ΓN p M H hpM) hj (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π) Meta₀ eeta₀ heeta₀ D₀ hD₀ hDQ₀ ajQ₀ kQ₀ ajbar₀ hPQ₀ hajQ₀ hkQ₀₁ hkQ₀₂ hajbar₀
    y₀₂ ⟨barPt A ≫ v₂.1, hy₂c⟩ hv₂y (pts₀ (Pic0.mk D₂)) hD₂pts
  have hPmul : ∀ a b : SchemeHomOver (genPt p) D₀.toBase,
      Nonempty ((hD₀.poincare.pullbackAlong (a * b)).L ≅ (hD₀.poincare.pullbackAlong a).L ⊗ (hD₀.poincare.pullbackAlong b).L) := by
    intro a b
    have := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso (P := algEquivZeroGroupCut _ _) hD₀
      (T := Over.mk (genPt p)) (schemeHomOverToOverHom a) (schemeHomOverToOverHom b)
    exact this
  have hPone : Nonempty ((hD₀.poincare.pullbackAlong (1 : SchemeHomOver (genPt p) D₀.toBase)).L ≅
      𝟙_ (pullback (toBase p (ΓN p M H hpM) hj) (genPt p)).Modules) := by
    have := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_one_iso (P := algEquivZeroGroupCut _ _) hD₀ (Over.mk (genPt p))
    exact this

  have hgen : genPt p = specMap ℚ (AlgebraicClosure ℚ) ≫ specMap (R p) ℚ := by
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hΦinv : (pullback.fst (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ) (specMap ℚ (AlgebraicClosure ℚ)) ≫
      pullback.fst (toBase p (ΓN p M H hpM) hj) (specMap (R p) ℚ)) ≫ toBase p (ΓN p M H hpM) hj =
      pullback.snd (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ) (specMap ℚ (AlgebraicClosure ℚ)) ≫ genPt p := by
    rw [Category.assoc, pullback.condition, hgen]
    exact pullback.condition_assoc _
  let Φ : pullback (toBase p (ΓN p M H hpM) hj) (genPt p) ≅
      pullback (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ) (specMap ℚ (AlgebraicClosure ℚ)) :=
    { hom := pullback.lift kQ₀ (pullback.snd (toBase p (ΓN p M H hpM) hj) (genPt p)) hkQ₀₂
      inv := pullback.lift (pullback.fst _ _ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (specMap (R p) ℚ)) (pullback.snd _ _) hΦinv
      hom_inv_id := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, hkQ₀₁, Category.id_comp]
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp]
      inv_hom_id := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, Category.id_comp]
          apply pullback.hom_ext
          · rw [Category.assoc, hkQ₀₁, pullback.lift_fst]
          · rw [Category.assoc, hkQ₀₂, pullback.lift_snd_assoc]
            exact (pullback.condition).symm
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp] }
  have hΦsnd : Φ.hom ≫ pullback.snd _ _ = pullback.snd (toBase p (ΓN p M H hpM) hj) (genPt p) := pullback.lift_snd _ _ _
  clear_value Φ
  haveI : SmoothOfRelativeDimension 1
      (pullback.snd (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ) (specMap ℚ (AlgebraicClosure ℚ))) := inferInstance
  haveI hsX : SmoothOfRelativeDimension 1 (pullback.snd (toBase p (ΓN p M H hpM) hj) (genPt p)) :=
    G2Kit.smoothOfRelativeDimension_one_of_iso Φ.symm hΦsnd
  haveI : IsSeparated (pullback.snd (toBase p (ΓN p M H hpM) hj) (genPt p)) := inferInstance

  have hI₂ := Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd (toBase p (ΓN p M H hpM) hj) (genPt p))
    (graphOver (toBase p (ΓN p M H hpM) hj) (barPt A ≫ v₂.1) hy₂c) (graphOver_snd _ _ _)
  obtain ⟨⟨eI₂⟩, -⟩ := hI₂.nonempty_module_tensor_invModule_iso

  obtain ⟨em⟩ := hPmul (pts₀ (Pic0.mk Dv₀)) (pts₀ (Pic0.mk D₂))
  have hba : hD₀.poincare.pullbackAlong (pts₀ (Pic0.mk Dv₀) * pts₀ (Pic0.mk D₂)) = hD₀.poincare.pullbackAlong (pts₀ (Pic0.mk D₁)) := by
    rw [hkey]
  have eL : (hD₀.poincare.pullbackAlong (pts₀ (Pic0.mk Dv₀))).L ⊗ (hD₀.poincare.pullbackAlong (pts₀ (Pic0.mk D₂))).L ≅
      (hD₀.poincare.pullbackAlong (pts₀ (Pic0.mk D₁))).L := em.symm ≪≫ eqToIso (congrArg (fun M => M.L) hba)
  obtain ⟨em2⟩ := hPmul (pts₀ (Pic0.mk D₂)) (pts₀ (Pic0.mk D₂))⁻¹
  obtain ⟨e1⟩ := hPone
  have hone : hD₀.poincare.pullbackAlong (pts₀ (Pic0.mk D₂) * (pts₀ (Pic0.mk D₂))⁻¹) = hD₀.poincare.pullbackAlong 1 := by
    rw [mul_inv_cancel]
  have eN : (hD₀.poincare.pullbackAlong (pts₀ (Pic0.mk D₂))).L ⊗ (hD₀.poincare.pullbackAlong (pts₀ (Pic0.mk D₂))⁻¹).L ≅
      𝟙_ (pullback (toBase p (ΓN p M H hpM) hj) (genPt p)).Modules := em2.symm ≪≫ eqToIso (congrArg (fun M => M.L) hone) ≪≫ e1

  let L₁ := (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) (barPt A ≫ v₁.1) hy₁c).lineBundle
  let L₂ := (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) (barPt A ≫ v₂.1) hy₂c).lineBundle
  let J₂ := (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) (barPt A ≫ v₂.1) hy₂c).idealModule
  let Jε := (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) (genPt p ≫ (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π).1)
    ((Category.assoc _ _ _).trans ((congrArg (genPt p ≫ ·) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π).2).trans (Category.comp_id _)))).idealModule
  have e' : (L₁ ⊗ J₂) ⊗ (hD₀.poincare.pullbackAlong (pts₀ (Pic0.mk D₂))).L ≅ (hD₀.poincare.pullbackAlong (pts₀ (Pic0.mk D₁))).L :=
    whiskerLeftIso (L₁ ⊗ J₂) eP₂ ≪≫ α_ L₁ J₂ (L₂ ⊗ Jε) ≪≫ whiskerLeftIso L₁ ((α_ J₂ L₂ Jε).symm ≪≫ whiskerRightIso eI₂ Jε ≪≫ λ_ Jε) ≪≫
      eP₁.symm
  have eLM : (hD₀.poincare.pullbackAlong (pts₀ (Pic0.mk Dv₀))).L ≅ L₁ ⊗ J₂ := G2Kit.monoidalCancel eN (eL ≪≫ e'.symm)

  have eR : Nonempty ((hD₀.poincare.pullbackAlong g').L ≅ L₁ ⊗ J₂) := by
    let ψ : SchemeHomOver (genPt p) (Spec.map (CommRingCat.ofHom ρ)) := ⟨barPt A, hbar⟩
    have hcomp : baseChangeSnd (toBase p (ΓN p M H hpM) hj) g' =
        baseChangeSnd (toBase p (ΓN p M H hpM) hj) ψ ≫ baseChangeSnd (toBase p (ΓN p M H hpM) hj) s₀ := by
      apply pullback.hom_ext
      · rw [Category.assoc, BaseChange.baseChangeSnd_fst', BaseChange.baseChangeSnd_fst', BaseChange.baseChangeSnd_fst']
      · rw [Category.assoc, BaseChange.baseChangeSnd_snd', BaseChange.baseChangeSnd_snd']
        simp only [← Category.assoc]
        rw [BaseChange.baseChangeSnd_snd']
        exact (Category.assoc _ _ _).symm
    obtain ⟨⟨e₁⟩, -⟩ := AlgebraicGeometry.RelEffCartierDiv.nonempty_pullback_ofPoint_lineBundle_iso_and_idealModule_iso_of_range_subset
      (R p) (toBase p (ΓN p M H hpM) hj) ⊤ v₁ (fun _ _ => trivial) ψ hy₁c
    obtain ⟨-, ⟨e₂⟩⟩ := AlgebraicGeometry.RelEffCartierDiv.nonempty_pullback_ofPoint_lineBundle_iso_and_idealModule_iso_of_range_subset
      (R p) (toBase p (ΓN p M H hpM) hj) ⊤ v₂ (fun _ _ => trivial) ψ hy₂c
    exact ⟨(Scheme.Modules.pullbackCongr hcomp).app hD₀.poincare.L ≪≫
      ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
      (Scheme.Modules.pullback (baseChangeSnd (toBase p (ΓN p M H hpM) hj) ψ)).mapIso eS ≪≫
      Scheme.Modules.pullbackTensorObjIso (baseChangeSnd (toBase p (ΓN p M H hpM) hj) ψ) _ _ ≪≫ (e₁ ⊗ᵢ e₂)⟩
  obtain ⟨eR⟩ := eR
  exact ⟨eLM ≪≫ eR.symm⟩

end S_ModularCurve_XHDRModelAtP_exists_schemeHomOver_pts_levelN_degPts_eq_and_ptsSp_levelN_symm_eq_mk
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_schemeHomOver_pts_levelN_degPts_eq_and_ptsSp_levelN_symm_eq_mk (solution)
