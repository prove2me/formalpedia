-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.pts_levelN_degPts_eq_comp_degeneracyHom_of_classifies_normModule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/af6430d4-90c6-5a29-8773-8263a15e7d7d

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_JacJ1Iface
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_XHHeckeOperator
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_module_tensor_invModule_iso
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_nonempty_pullback_ofPoint_lineBundle_iso_and_idealModule_iso_of_range_subset
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_mul_comp_eq_of_classifies_rigidify_normModule_of_ofPoint
import Theorems.Thm_ModularCurve_inertiaDegAlong_eq_one_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_pts_levelN_degPts_eq_comp_degeneracyHom_of_classifies_normModule
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free SheafOfModules.isIso_ihomModelToIhom AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP"

open ModularCurve.JHNeronObjectAtP (Fbar)
open scoped MatrixGroups

namespace DEGPTSKit

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

end DEGPTSKit

namespace DEGPTSBody

open AlgebraicGeometry.RelPicard.BaseChange DEGPTSKit in

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
    DEGPTSKit.smoothOfRelativeDimension_one_of_iso Φ.symm hΦsnd
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
  obtain ⟨⟨jA⟩, -⟩ := DEGPTSKit.nonempty_pullback_ker_invModule_iso_of_isIso Φ.hom _ _ hgraphA hIA hIA'
  obtain ⟨-, ⟨jB⟩⟩ := DEGPTSKit.nonempty_pullback_ker_invModule_iso_of_isIso Φ.hom _ _ hgraphB hIB hIB'

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

section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

noncomputable def gen (hdeg : ∀ v : Place K F, v.deg = 1) (Q₀ P : Place K F) : Divisor.degZero (K := K) (F := F) :=
  ⟨Finsupp.single P 1 - Finsupp.single Q₀ 1, by
    rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, hdeg, hdeg]; simp⟩

@[scoped simp] theorem coe_gen (hdeg : ∀ v : Place K F, v.deg = 1) (Q₀ P : Place K F) :
    (gen hdeg Q₀ P : Divisor K F) = Finsupp.single P 1 - Finsupp.single Q₀ 1 := rfl

theorem closure_range_mk_gen_eq_top (hdeg : ∀ v : Place K F, v.deg = 1) (Q₀ : Place K F) :
    AddSubgroup.closure (Set.range fun P : Place K F => Pic0.mk (gen hdeg Q₀ P)) = ⊤ := by
  classical
  set S := AddSubgroup.closure (Set.range fun P : Place K F => Pic0.mk (gen hdeg Q₀ P)) with hS

  let θ : Divisor K F →+ Divisor K F :=
    AddMonoidHom.id _ - (zmultiplesHom (Divisor K F) (Finsupp.single Q₀ 1)).comp Divisor.degree
  have hθ : ∀ E : Divisor K F, θ E = E - Divisor.degree E • Finsupp.single Q₀ 1 := fun E => by
    simp [θ]
  have hθmem : ∀ E : Divisor K F, θ E ∈ Divisor.degZero (K := K) (F := F) := by
    intro E
    rw [Divisor.mem_degZero, hθ, map_sub, map_zsmul, Divisor.degree_single, hdeg]
    simp
  let ψ : Divisor K F →+ Pic0 K F := (QuotientAddGroup.mk' _).comp (θ.codRestrict _ hθmem)
  have hψ : ∀ E : Divisor K F, ψ E = Pic0.mk ⟨θ E, hθmem E⟩ := fun E => rfl
  have hψS : ∀ E : Divisor K F, ψ E ∈ S := by
    intro E
    induction E using Finsupp.induction with
    | zero => rw [map_zero]; exact S.zero_mem
    | single_add a b f _ _ ih =>
      rw [map_add]
      refine S.add_mem ?_ ih
      have h1 : ψ (Finsupp.single a 1) = Pic0.mk (gen hdeg Q₀ a) := by
        rw [hψ]; congr 1; apply Subtype.ext
        simp only [coe_gen, hθ, Divisor.degree_single, hdeg, Nat.cast_one, mul_one, one_smul]
      have hb : Finsupp.single a b = b • Finsupp.single a (1 : ℤ) := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hb, map_zsmul, h1]
      exact S.zsmul_mem (AddSubgroup.subset_closure ⟨a, rfl⟩) b
  rw [eq_top_iff]
  rintro c -
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective c
  have hD : Pic0.mk D = ψ (D : Divisor K F) := by
    rw [hψ]; congr 1; apply Subtype.ext
    simp only [hθ, (Divisor.mem_degZero.mp D.2), zero_smul, sub_zero]
  rw [hD]; exact hψS _

theorem addMonoidHom_ext_of_gen {G : Type*} [AddGroup G] (hdeg : ∀ v : Place K F, v.deg = 1) (Q₀ : Place K F)
    {f g : Pic0 K F →+ G} (h : ∀ P : Place K F, f (Pic0.mk (gen hdeg Q₀ P)) = g (Pic0.mk (gen hdeg Q₀ P))) :
    f = g :=
  AddMonoidHom.eq_of_eqOn_dense (closure_range_mk_gen_eq_top hdeg Q₀) (by rintro _ ⟨P, rfl⟩; exact h P)

theorem gen_sub_gen (hdeg : ∀ v : Place K F, v.deg = 1) (Q₀ P P' : Place K F) :
    gen hdeg Q₀ P - gen hdeg Q₀ P' = gen hdeg P' P :=
  Subtype.ext (by rw [AddSubgroupClass.coe_sub, coe_gen, coe_gen, coe_gen, sub_sub_sub_cancel_right])

end Generic

set_option maxHeartbeats 6400000 in

theorem normRead
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) (𝔛 : XHDRModelAtP p M H hpM hj)
    [IsSeparated (toBase p (ΓM M H) hj)] [IsSeparated (toBase p (ΓN p M H hpM) hj)]
    (D : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) D)
    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (D.baseChange ℚ))
    (hPQ : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) ℚ), pullback.condition⟩)).L))

    (ajQ : SchemeHomOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (D.baseChange ℚ).toBase)
    (hajQε : (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQ.1 = (D.baseChange ℚ).zeroSection)
    (hajQ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)),
      Nonempty ((hDQ.poincare.pullbackAlong
          ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
              (Category.comp_id t)))).idealModule))

    (kQ : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ℚ))
    (hkQ₁ : kQ ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))

    (ajbar : 𝔛.Meta.C ⟶ D.P) (hajbar : ajbar = 𝔛.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (R p) ℚ))
    (hajbar_over : ajbar ≫ D.toBase = 𝔛.Meta.toBase ≫ genPt p)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (hεbar : εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1)
    (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ D.zeroSection)
    (D₀ : RelativePic0Designation (R p) (toBase p (ΓN p M H hpM) hj))
    (hD₀ : RepresentsRelSubPic (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)
      (algEquivZeroCut (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)) D₀)
    (Meta₀ : CurveModel (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
    (eeta₀ : Meta₀.C ⟶ pullback (toBase p (XHDRLevel.ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))))
    [IsIso eeta₀]
    (heeta₀ : eeta₀ ≫ pullback.snd _ _ = Meta₀.toBase)
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

    (πi : SchemeHomOver (toBase p (ΓM M H) hj) (toBase p (ΓN p M H hpM) hj))
    [IsFinite πi.1] [Flat πi.1] [LocallyOfFinitePresentation πi.1] (hrk : ∀ x, πi.1.finrank x = p + 1)
    (N : SchemeHomOver D.toBase D₀.toBase)
    (hN : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (a : SchemeHomOver t D.toBase),
      Nonempty ((hD₀.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a N)).L ≅
        Scheme.Modules.rigidify (rigSection (toBase p (ΓN p M H hpM) hj) t (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π))
            (pullback.snd (toBase p (ΓN p M H hpM) hj) t)
          (Scheme.Modules.normModule (curveChange πi.1 πi.2 t) (p + 1) (hD.poincare.pullbackAlong a).L)))

    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}) (x xinf : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _})
    (hyx : x.1 ≫ eeta₀ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (genPt p) =
      y.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) ≫ πi.1)
    (hxinf : xinf.1 ≫ eeta₀ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (genPt p) =
      εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) ≫ πi.1)
    (a b c : SchemeHomOver (genPt p) D₀.toBase)
    (ha : a.1 = (y.1 ≫ ajbar) ≫ N.1) (hb : b.1 = xinf.1 ≫ ajbar₀) (hc : c.1 = x.1 ≫ ajbar₀) :
    (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).mul (genPt p) a b = c := by

  haveI : SmoothOfRelativeDimension 1 (pullback.snd (toBase p (ΓM M H) hj) (genPt p)) := by
    have e : pullback.snd (toBase p (ΓM M H) hj) (genPt p) = inv 𝔛.eeta ≫ 𝔛.Meta.toBase := by
      rw [← 𝔛.heeta, IsIso.inv_hom_id_assoc]
    rw [e]; exact MorphismProperty.RespectsIso.precomp (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  haveI := 𝔛.smooth0
  haveI : SmoothOfRelativeDimension 1 (pullback.snd (toBase p (ΓN p M H hpM) hj) (genPt p)) := inferInstance
  haveI : IsSeparated (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) := by unfold baseChange; infer_instance
  haveI : IsSeparated (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ) := by unfold baseChange; infer_instance
  haveI : SmoothOfRelativeDimension 1 (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) := 𝔛.smooth_generic
  haveI : SmoothOfRelativeDimension 1 (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ) := by unfold baseChange; infer_instance

  let ybar : SchemeHomOver (genPt p) (toBase p (ΓM M H) hj) := ⟨y.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p), by
    simp only [Category.assoc, pullback.condition]; rw [reassoc_of% 𝔛.heeta, reassoc_of% y.2]⟩
  let a' : SchemeHomOver (genPt p) D.toBase := ⟨y.1 ≫ ajbar, by rw [Category.assoc, hajbar_over, reassoc_of% y.2]⟩
  have haa' : a = NeronModelInfra.schemeHomOverComp a' N := Subtype.ext (by rw [ha]; rfl)
  have ha' := ajRead p (ΓM M H) hj 𝔛.εinf 𝔛.Meta 𝔛.eeta 𝔛.heeta D hD hDQ ajQ kQ ajbar hPQ hajQ hkQ₁ hkQ₂ hajbar y ybar rfl a' rfl

  let xb : SchemeHomOver (genPt p) (toBase p (ΓN p M H hpM) hj) :=
    ⟨xinf.1 ≫ eeta₀ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (genPt p), by
      simp only [Category.assoc, pullback.condition]; rw [reassoc_of% heeta₀, reassoc_of% xinf.2]⟩
  let xg : SchemeHomOver (genPt p) (toBase p (ΓN p M H hpM) hj) :=
    ⟨x.1 ≫ eeta₀ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (genPt p), by
      simp only [Category.assoc, pullback.condition]; rw [reassoc_of% heeta₀, reassoc_of% x.2]⟩
  have hxb : xb.1 = ((genPt p) ≫ 𝔛.εinf.1) ≫ πi.1 := by
    show xinf.1 ≫ _ = _; rw [hxinf, reassoc_of% hεbar, Category.assoc]
  have hxg : xg.1 = ybar.1 ≫ πi.1 := by
    show x.1 ≫ _ = (y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _) ≫ πi.1; rw [hyx]; simp only [Category.assoc]
  have hb' := ajRead p (ΓN p M H hpM) hj (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π) Meta₀ eeta₀ heeta₀ D₀ hD₀ hDQ₀ ajQ₀ kQ₀ ajbar₀
    hPQ₀ hajQ₀ hkQ₀₁ hkQ₀₂ hajbar₀ xinf xb rfl b hb
  have hc' := ajRead p (ΓN p M H hpM) hj (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π) Meta₀ eeta₀ heeta₀ D₀ hD₀ hDQ₀ ajQ₀ kQ₀ ajbar₀
    hPQ₀ hajQ₀ hkQ₀₁ hkQ₀₂ hajbar₀ x xg rfl c hc
  rw [haa']
  exact RepresentsRelSubPic.mul_comp_eq_of_classifies_rigidify_normModule_of_ofPoint
    hD₀ hD πi.1 πi.2 (p + 1) hrk N (fun t a => hN t a) (genPt p) ybar xb xg hxb hxg a' ha' b c hb' hc'

set_option maxHeartbeats 6400000 in

theorem core
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) (𝔛 : XHDRModelAtP p M H hpM hj)

    {DX : Scheme.{0}} (dD : DX ⟶ Spec (CommRingCat.of (R p)))
    (mulD : SchemeHomOver (genPt p) dD → SchemeHomOver (genPt p) dD → SchemeHomOver (genPt p) dD)
    (ajbar : 𝔛.Meta.C ⟶ DX) (hajbar_over : ajbar ≫ dD = 𝔛.Meta.toBase ≫ genPt p)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (pts : JH M H ≃ SchemeHomOver (genPt p) dD)
    (hpts_add : ∀ x y : JH M H, pts (x + y) = mulD (pts x) (pts y))
    (hpts_aj : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
          Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)
    (hεbar : εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1)

    {DY : Scheme.{0}} (dD₀ : DY ⟶ Spec (CommRingCat.of (R p)))
    (mulD₀ : SchemeHomOver (genPt p) dD₀ → SchemeHomOver (genPt p) dD₀ → SchemeHomOver (genPt p) dD₀)
    (Meta₀ : CurveModel (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
    (eeta₀ : Meta₀.C ⟶ pullback (toBase p (XHDRLevel.ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))))
    [IsIso eeta₀]
    (heeta₀ : eeta₀ ≫ pullback.snd _ _ = Meta₀.toBase)
    (ajbar₀ : Meta₀.C ⟶ DY) (hajbar₀_over : ajbar₀ ≫ dD₀ = Meta₀.toBase ≫ genPt p)
    (εbar₀ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _})
    (hεbar₀ : εbar₀.1 ≫ eeta₀ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 ≫ 𝔛.π.1)
    (pts₀ : JH (M / p) (infSubgroup p M H hpM) ≃ SchemeHomOver (genPt p) dD₀)
    (hpts₀_add : ∀ x y : JH (M / p) (infSubgroup p M H hpM), pts₀ (x + y) = mulD₀ (pts₀ x) (pts₀ y))
    (hpts₀_aj : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _}),
      s.1 ≫ eeta₀ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 ≫ 𝔛.π.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) =
          Finsupp.single (Meta₀.pointEquivPlace x) 1 - Finsupp.single (Meta₀.pointEquivPlace s) 1 ∧
        (pts₀ (Pic0.mk Dv)).1 = x.1 ≫ ajbar₀)

    (φ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hφ : φ.toRingHom.IsIntegral)
    (degP : JH M H →+ JH (M / p) (infSubgroup p M H hpM))
    (hdegP : ∀ (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
        (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))),
      (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) =
        Divisor.pushforwardAlong φ hφ (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) →
      degP (Pic0.mk Dv) = Pic0.mk Dw)
    (πg : SchemeHomOver (toBase p (ΓM M H) hj) (toBase p (ΓN p M H hpM) hj))
    (d : SchemeHomOver dD dD₀)
    (hdhom : ∀ x y : SchemeHomOver (genPt p) dD,
      NeronModelInfra.schemeHomOverComp (mulD x y) d = mulD₀ (NeronModelInfra.schemeHomOverComp x d) (NeronModelInfra.schemeHomOverComp y d))

    (hplace : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}) (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _}),
      x.1 ≫ eeta₀ ≫ pullback.fst _ _ = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ πg.1 →
      Meta₀.pointEquivPlace x = Place.restrictAlong φ hφ (𝔛.Meta.pointEquivPlace y))

    (hnorm : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}) (x xinf : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _}),
      x.1 ≫ eeta₀ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (genPt p) =
        y.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) ≫ πg.1 →
      xinf.1 ≫ eeta₀ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (genPt p) =
        εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) ≫ πg.1 →
      ∀ (a b c : SchemeHomOver (genPt p) dD₀),
        a.1 = (y.1 ≫ ajbar) ≫ d.1 → b.1 = xinf.1 ≫ ajbar₀ → c.1 = x.1 ≫ ajbar₀ → mulD₀ a b = c) :
    ∀ X : JH M H, (pts₀ (degP X)).1 = (pts X).1 ≫ d.1 := by
  classical

  have hinv₀ : inv eeta₀ ≫ Meta₀.toBase = pullback.snd _ _ := by rw [IsIso.inv_comp_eq, heeta₀]
  have hyc : ∀ y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _},
      (y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ πg.1) ≫ toBase p (ΓN p M H hpM) hj =
        𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))) := by
    intro y
    simp only [Category.assoc, πg.2]
    rw [pullback.condition, reassoc_of% 𝔛.heeta, reassoc_of% y.2, Category.id_comp]
  let under : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _} → {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _} := fun y =>
    ⟨pullback.lift (y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ πg.1) (𝟙 _) (hyc y) ≫ inv eeta₀, by
      rw [Category.assoc, hinv₀, pullback.lift_snd]⟩
  have hunder : ∀ y, (under y).1 ≫ eeta₀ ≫ pullback.fst _ _ = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ πg.1 := by
    intro y
    show (pullback.lift _ _ _ ≫ inv eeta₀) ≫ eeta₀ ≫ _ = _
    rw [Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst]

  let Φ : JH M H → JH (M / p) (infSubgroup p M H hpM) := fun X => pts₀.symm (NeronModelInfra.schemeHomOverComp (pts X) d)
  have hΦ : ∀ X, pts₀ (Φ X) = NeronModelInfra.schemeHomOverComp (pts X) d := fun X => pts₀.apply_symm_apply _
  have hΦadd : ∀ X Y, Φ (X + Y) = Φ X + Φ Y := by
    intro X Y; apply pts₀.injective
    rw [hpts₀_add, hΦ, hΦ, hΦ, hpts_add, hdhom]
  let Φh : JH M H →+ JH (M / p) (infSubgroup p M H hpM) := AddMonoidHom.mk' Φ hΦadd
  suffices hfun : degP = Φh by
    intro X; rw [hfun]; show (pts₀ (Φ X)).1 = _; rw [hΦ]; rfl

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
  have hdeg : ∀ v : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), v.deg = 1 := fun v =>
    ModularCurve.place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC (AlgebraicClosure ℚ) (CohCarrier.GammaH M H)
      (ModularCurve.translation_mem_GammaH M H) (xHFunctionField M H) rfl v
  have hinert : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), W.inertiaDegAlong φ hφ = 1 := fun W =>
    ModularCurve.inertiaDegAlong_eq_one_laurentBaseChange_qExpFunctionFieldC (CohCarrier.GammaH M H)
      (ModularCurve.translation_mem_GammaH M H) (xHFunctionField M H) rfl φ hφ W
  refine addMonoidHom_ext_of_gen hdeg (𝔛.Meta.pointEquivPlace εbar) fun P => ?_
  obtain ⟨y, hPy⟩ := 𝔛.Meta.pointEquivPlace.surjective P
  subst hPy
  set x := under y with hx
  set xinf := under εbar with hxinf

  obtain ⟨Dv, hDv, hptsDv⟩ := hpts_aj y εbar hεbar
  obtain ⟨Ex, hEx, hptsEx⟩ := hpts₀_aj x εbar₀ hεbar₀
  obtain ⟨Einf, hEinf, hptsEinf⟩ := hpts₀_aj xinf εbar₀ hεbar₀
  have hgen : gen hdeg (𝔛.Meta.pointEquivPlace εbar) (𝔛.Meta.pointEquivPlace y) = Dv := Subtype.ext (by rw [coe_gen, hDv])

  have hpush : ((Ex - Einf : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))) :
        Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) =
      Divisor.pushforwardAlong φ hφ
        ((gen hdeg (𝔛.Meta.pointEquivPlace εbar) (𝔛.Meta.pointEquivPlace y) :
          Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) := by
    rw [AddSubgroupClass.coe_sub, hEx, hEinf, coe_gen, map_sub, Divisor.pushforwardAlong_single, Divisor.pushforwardAlong_single,
      hinert, hinert, Nat.cast_one, mul_one, ← hplace y x (hunder y), ← hplace εbar xinf (hunder εbar)]
    abel
  have hdegPgen : degP (Pic0.mk (gen hdeg (𝔛.Meta.pointEquivPlace εbar) (𝔛.Meta.pointEquivPlace y))) = Pic0.mk (Ex - Einf) :=
    hdegP _ _ hpush

  let a : SchemeHomOver (genPt p) dD₀ :=
    NeronModelInfra.schemeHomOverComp (⟨y.1 ≫ ajbar, by rw [Category.assoc, hajbar_over, reassoc_of% y.2]⟩ : SchemeHomOver (genPt p) dD) d
  have hmul : mulD₀ a (pts₀ (Pic0.mk Einf)) = pts₀ (Pic0.mk Ex) :=
    hnorm y x xinf (hunder y) (hunder εbar) a _ _ rfl hptsEinf hptsEx

  have hkey : pts₀ (Pic0.mk (Ex - Einf)) = a := by
    have h1 : pts₀ (Pic0.mk (Ex - Einf) + Pic0.mk Einf) = pts₀ (pts₀.symm a + Pic0.mk Einf) := by
      rw [← Pic0.mk_add, sub_add_cancel, hpts₀_add, Equiv.apply_symm_apply, hmul]
    have h2 := add_right_cancel (pts₀.injective h1)
    rw [h2, Equiv.apply_symm_apply]

  show degP _ = Φ _
  apply pts₀.injective
  rw [hΦ, hdegPgen, hkey]
  apply Subtype.ext
  rw [NeronModelInfra.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe, hgen, hptsDv]

end DEGPTSBody
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_pts_levelN_degPts_eq_comp_degeneracyHom_of_classifies_normModule.DEGPTSBody"

open DEGPTSBody

set_option maxHeartbeats 3200000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    [IsProper (toBase p (ΓM M H) hj)]
    (D : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) D)

    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (D.baseChange ℚ))
    (hPQ : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) ℚ), pullback.condition⟩)).L))

    (ajQ : SchemeHomOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (D.baseChange ℚ).toBase)
    (hajQε : (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQ.1 = (D.baseChange ℚ).zeroSection)
    (hajQ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)),
      Nonempty ((hDQ.poincare.pullbackAlong
          ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
              (Category.comp_id t)))).idealModule))

    (kQ : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ℚ))
    (hkQ₁ : kQ ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))

    (ajbar : 𝔛.Meta.C ⟶ D.P) (hajbar : ajbar = 𝔛.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (R p) ℚ))
    (hajbar_over : ajbar ≫ D.toBase = 𝔛.Meta.toBase ≫ genPt p)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (hεbar : εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1)
    (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ D.zeroSection)

    (pts : JH M H ≃ SchemeHomOver (genPt p) D.toBase)
    (hpts_add : ∀ x y : JH M H,
      pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (pts x) (pts y))
    (hpts_aj : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
          Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)
    [IsProper (toBase p (ΓN p M H hpM) hj)] [IsSeparated (toBase p (ΓN p M H hpM) hj)]
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
    [IsSeparated (toBase p (ΓM M H) hj)]

    [IsFinite 𝔛.π.1] [Flat 𝔛.π.1] [LocallyOfFinitePresentation 𝔛.π.1] (hrk : ∀ x, 𝔛.π.1.finrank x = p + 1)
    (δ : Fin 2 → SchemeHomOver D.toBase D₀.toBase)
    (hδ₀ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (a : SchemeHomOver t D.toBase),
      Nonempty ((hD₀.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a (δ 0))).L ≅
        Scheme.Modules.rigidify (rigSection (toBase p (ΓN p M H hpM) hj) t (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π))
            (pullback.snd (toBase p (ΓN p M H hpM) hj) t)
          (Scheme.Modules.normModule (curveChange 𝔛.π.1 𝔛.π.2 t) (p + 1) (hD.poincare.pullbackAlong a).L)))
    (hδ₁ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (a : SchemeHomOver t D.toBase),
      Nonempty ((hD₀.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a (δ 1))).L ≅
        Scheme.Modules.rigidify (rigSection (toBase p (ΓN p M H hpM) hj) t (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π))
            (pullback.snd (toBase p (ΓN p M H hpM) hj) t)
          (Scheme.Modules.normModule (curveChange 𝔛.πw.1 𝔛.πw.2 t) (p + 1) (hD.poincare.pullbackAlong a).L)))
    (hδmul : ∀ (i : Fin 2) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (x y : SchemeHomOver t D.toBase),
      NeronModelInfra.schemeHomOverComp
          ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul t x y) (δ i) =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).mul t
          (NeronModelInfra.schemeHomOverComp x (δ i)) (NeronModelInfra.schemeHomOverComp y (δ i))) :
    ∀ (i : Fin 2) (x : JH M H), (pts₀ (degPts i x)).1 = (pts x).1 ≫ (δ i).1 := by
  intro i

  haveI : IsFinite 𝔛.πw.1 := (inferInstance : IsFinite (𝔛.w.hom ≫ 𝔛.π.1))
  haveI : Flat 𝔛.πw.1 := (inferInstance : Flat (𝔛.w.hom ≫ 𝔛.π.1))
  haveI : LocallyOfFinitePresentation 𝔛.πw.1 := (inferInstance : LocallyOfFinitePresentation (𝔛.w.hom ≫ 𝔛.π.1))
  have hrkw : ∀ x, 𝔛.πw.1.finrank x = p + 1 := fun x => by
    rw [XHDRModelAtP.πw_val, Scheme.Hom.finrank_comp_left_of_isIso]; exact hrk x
  match i with
  | 0 =>
    exact core p M H hpM hj 𝔛 D.toBase (fun x y => (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ x y)
      ajbar hajbar_over εbar pts hpts_add hpts_aj hεbar
      D₀.toBase (fun x y => (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).mul _ x y) Meta₀ eeta₀ heeta₀ ajbar₀ hajbar₀_over εbar₀ hεbar₀ pts₀ hpts₀_add hpts₀_aj
      αH hαint (degPts 0) hdeg0 𝔛.π (δ 0) (fun x y => hδmul 0 (genPt p) x y)
      (fun y x h => hMeta₀π y x h)
      (fun y x xinf hyx hxinf a b c ha hb hc => normRead p M H hpM hj 𝔛 D hD hDQ hPQ ajQ hajQε hajQ kQ hkQ₁ hkQ₂ ajbar hajbar hajbar_over
        εbar hεbar hεbar_aj D₀ hD₀ Meta₀ eeta₀ heeta₀ hDQ₀ hPQ₀ ajQ₀ hajQ₀ε hajQ₀ kQ₀ hkQ₀₁ hkQ₀₂ ajbar₀ hajbar₀ hajbar₀_over εbar₀ hεbar₀ hεbar₀_aj
        𝔛.π hrk (δ 0) (fun t a => hδ₀ t a) y x xinf hyx hxinf a b c ha hb hc)
  | 1 =>
    exact core p M H hpM hj 𝔛 D.toBase (fun x y => (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ x y)
      ajbar hajbar_over εbar pts hpts_add hpts_aj hεbar
      D₀.toBase (fun x y => (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).mul _ x y) Meta₀ eeta₀ heeta₀ ajbar₀ hajbar₀_over εbar₀ hεbar₀ pts₀ hpts₀_add hpts₀_aj
      βH hβint (degPts 1) hdeg1 𝔛.πw (δ 1) (fun x y => hδmul 1 (genPt p) x y)
      (fun y x h => hMeta₀πw y x (by simpa only [XHDRModelAtP.πw_val, Category.assoc] using h))
      (fun y x xinf hyx hxinf a b c ha hb hc => normRead p M H hpM hj 𝔛 D hD hDQ hPQ ajQ hajQε hajQ kQ hkQ₁ hkQ₂ ajbar hajbar hajbar_over
        εbar hεbar hεbar_aj D₀ hD₀ Meta₀ eeta₀ heeta₀ hDQ₀ hPQ₀ ajQ₀ hajQ₀ε hajQ₀ kQ₀ hkQ₀₁ hkQ₀₂ ajbar₀ hajbar₀ hajbar₀_over εbar₀ hεbar₀ hεbar₀_aj
        𝔛.πw hrkw (δ 1) (fun t a => hδ₁ t a) y x xinf hyx hxinf a b c ha hb hc)

end S_ModularCurve_XHDRModelAtP_pts_levelN_degPts_eq_comp_degeneracyHom_of_classifies_normModule
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_pts_levelN_degPts_eq_comp_degeneracyHom_of_classifies_normModule (solution)
