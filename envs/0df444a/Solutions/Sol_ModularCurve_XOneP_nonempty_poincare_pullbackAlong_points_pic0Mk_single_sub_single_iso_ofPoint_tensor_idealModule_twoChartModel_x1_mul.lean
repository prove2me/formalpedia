-- Prove2me | solution 1 for ModularCurve.XOneP.nonempty_poincare_pullbackAlong_points_pic0Mk_single_sub_single_iso_ofPoint_tensor_idealModule_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/949a385d-f03f-5903-9571-8c97100fcc21

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JOnePGeom
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV2
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_module_tensor_invModule_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_pullbackAlong_mul_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_pullbackAlong_one_iso
import Theorems.Thm_ModularCurve_XOneP_smoothOfRelativeDimension_one_and_geometricallyIntegral_baseChange_twoChartModel_x1_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_nonempty_poincare_pullbackAlong_points_pic0Mk_single_sub_single_iso_ofPoint_tensor_idealModule_twoChartModel_x1_mul
p2m_attr_erase "instance" "AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.jqNModC_one"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

namespace GKit

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

def monoidalCancel {C : Type*} [Category C] [MonoidalCategory C] {M M' N N' : C}
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

end GKit

set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 1600000 in
open AlgebraicGeometry.RelPicard.BaseChange GKit in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)

    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (ε₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁) (ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂)
    (hε₁ : ε₁.1 ≫ i₁.1 = (sectionBaseChange k ε).1)

    (D : RelativePic0Designation A (ModularCurve.TwoChart.modelTo A (↥K) j))
    (hrep : Nonempty (RepresentsRelSubPic (ModularCurve.TwoChart.modelTo A (↥K) j) ε (algEquivZeroCut (ModularCurve.TwoChart.modelTo A (↥K) j) ε) D))

    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]

    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]

    (Mη : CurveModel (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p)))
    (eη : Mη.C ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) [IsIso eη]
    (heη : eη ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = Mη.toBase)

    (gpts : ModularCurve.JOne (M * p) ≃ SchemeHomOver (specMap A (AlgebraicClosure ℚ)) D.toBase)
    (hgadd : ∀ x y : ModularCurve.JOne (M * p), gpts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul _ (gpts x) (gpts y))

    (hDL : RepresentsRelSubPic (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (sectionBaseChange L ε)
        (algEquivZeroCut (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (sectionBaseChange L ε)) (D.baseChange L))
    (ajL : SchemeHomOver (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (D.baseChange L).toBase)
    (kL : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L))
    (ajbar : Mη.C ⟶ D.P)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
    (hPL : Nonempty (hDL.poincare.L ≅ (BaseChange.ofR (ModularCurve.TwoChart.modelTo A (↥K) j) ε L
      (hrep.some.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap A L), pullback.condition⟩)).L))
    (hajLε : (sectionBaseChange L ε).1 ≫ ajL.1 = (D.baseChange L).zeroSection)
    (hajL : (∀ (K' : Type) [Field K'] (t : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of L))
        (x : SchemeHomOver t (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L)),
      Nonempty ((hDL.poincare.pullbackAlong
          ⟨x.1 ≫ ajL.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajL.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (t ≫ (sectionBaseChange L ε).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange L ε).2).trans
              (Category.comp_id t)))).idealModule)))
    (hkL₁ : kL ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L) = pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)))
    (hkL₂ : kL ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L) = pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ≫ specMap L (AlgebraicClosure ℚ))
    (hajbar : ajbar = eη ≫ kL ≫ ajL.1 ≫ pullback.fst D.toBase (specMap A L))
    (hajbar_over : ajbar ≫ D.toBase = Mη.toBase ≫ specMap A (AlgebraicClosure ℚ))
    (hεbar : εbar.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = specMap A (AlgebraicClosure ℚ) ≫ ε.1)
    (hεbar_aj : εbar.1 ≫ ajbar = specMap A (AlgebraicClosure ℚ) ≫ D.zeroSection)
    (hpts_aj : (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      s.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = specMap A (AlgebraicClosure ℚ) ≫ ε.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ModularCurve.x1FunctionFieldBar (M * p)),
        (Dv : Divisor (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p))) =
          Finsupp.single (Mη.pointEquivPlace x) 1 - Finsupp.single (Mη.pointEquivPlace s) 1 ∧
        (gpts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)) :
    ∀ (P Q : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)))
      (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ModularCurve.x1FunctionFieldBar (M * p))),
      (Dv : Divisor (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p))) = Finsupp.single P 1 - Finsupp.single Q 1 →
      Nonempty ((hrep.some.poincare.pullbackAlong (gpts (Pic0.mk Dv))).L ≅
        (RelEffCartierDiv.ofPoint (ModularCurve.TwoChart.modelTo A (↥K) j) ((Mη.pointEquivPlace.symm P).1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)))
            (by rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc eη, heη, ← Category.assoc, (Mη.pointEquivPlace.symm P).2, Category.id_comp])).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (ModularCurve.TwoChart.modelTo A (↥K) j) ((Mη.pointEquivPlace.symm Q).1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)))
            (by rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc eη, heη, ← Category.assoc, (Mη.pointEquivPlace.symm Q).2, Category.id_comp])).idealModule) := by
  intro P Q Dv hDv
  classical
  obtain ⟨ePL⟩ := hPL
  obtain ⟨hsmL, -⟩ :=
    ModularCurve.XOneP.smoothOfRelativeDimension_one_and_geometricallyIntegral_baseChange_twoChartModel_x1_mul p M hM hpM L ζ hζ K hK A hAp hζA j hj
  let c : ModularCurve.TwoChartModel A (↥K) j ⟶ Spec (CommRingCat.of A) := ModularCurve.TwoChart.modelTo A (↥K) j
  let hD := hrep.some
  let tQ : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of A) := specMap A (AlgebraicClosure ℚ)
  have hkL₁' : kL ≫ pullback.fst c (specMap A L) = pullback.fst c tQ := hkL₁
  have hkL₂' : kL ≫ pullback.snd c (specMap A L) = pullback.snd c tQ ≫ specMap L (AlgebraicClosure ℚ) := hkL₂
  have heeta : eη ≫ pullback.snd c (tQ) = Mη.toBase := heη

  have hgen : tQ = specMap L (AlgebraicClosure ℚ) ≫ specMap A L := by
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq A L (AlgebraicClosure ℚ)]

  have hΦinv : (pullback.fst (baseChange A c L) (specMap L (AlgebraicClosure ℚ)) ≫
      pullback.fst c (specMap A L)) ≫ c =
      pullback.snd (baseChange A c L) (specMap L (AlgebraicClosure ℚ)) ≫ tQ := by
    rw [Category.assoc, pullback.condition, hgen]
    exact pullback.condition_assoc _
  let Φ : pullback c (tQ) ≅ pullback (baseChange A c L) (specMap L (AlgebraicClosure ℚ)) :=
    { hom := pullback.lift kL (pullback.snd c (tQ)) hkL₂
      inv := pullback.lift (pullback.fst _ _ ≫ pullback.fst c (specMap A L)) (pullback.snd _ _) hΦinv
      hom_inv_id := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, hkL₁, Category.id_comp]
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp]
      inv_hom_id := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, Category.id_comp]
          apply pullback.hom_ext
          · rw [Category.assoc, hkL₁, pullback.lift_fst]
          · rw [Category.assoc, hkL₂, pullback.lift_snd_assoc]
            exact (pullback.condition).symm
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp] }
  have hΦfst : Φ.hom ≫ pullback.fst _ _ = kL := pullback.lift_fst _ _ _
  have hΦsnd : Φ.hom ≫ pullback.snd _ _ = pullback.snd c (tQ) := pullback.lift_snd _ _ _
  clear_value Φ
  haveI hΦiso : IsIso Φ.hom := inferInstance

  haveI : SmoothOfRelativeDimension 1 (baseChange A c L) := hsmL
  haveI : SmoothOfRelativeDimension 1
      (pullback.snd (baseChange A c L) (specMap L (AlgebraicClosure ℚ))) := inferInstance
  haveI hsY : SmoothOfRelativeDimension 1 (pullback.snd c (tQ)) :=
    GKit.smoothOfRelativeDimension_one_of_iso Φ.symm hΦsnd
  haveI : IsSeparated (pullback.snd c (tQ)) := inferInstance
  haveI : IsSeparated (pullback.snd (baseChange A c L) (specMap L (AlgebraicClosure ℚ))) := inferInstance
  have hε : (tQ ≫ ε.1) ≫ c = tQ :=
    (Category.assoc _ _ _).trans ((congrArg (tQ ≫ ·) ε.2).trans (Category.comp_id _))

  have key : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
      (ybar : SchemeHomOver tQ c) (hybar : ybar.1 = y.1 ≫ eη ≫ pullback.fst c tQ)
      (a : SchemeHomOver tQ D.toBase) (ha : a.1 = y.1 ≫ ajbar),
      (graphOver c ybar.1 ybar.2).ker.IsInvertible ∧
      Nonempty ((hD.poincare.pullbackAlong a).L ≅
        (RelEffCartierDiv.ofPoint c ybar.1 ybar.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c (tQ ≫ ε.1) hε).idealModule) := by
    intro y ybar hybar a ha

    have hx : (y.1 ≫ eη ≫ kL) ≫ baseChange A c L = specMap L (AlgebraicClosure ℚ) := by
      simp only [Category.assoc]
      rw [hkL₂, reassoc_of% heeta, reassoc_of% y.2]
    obtain ⟨eAJ⟩ := hajL (AlgebraicClosure ℚ) (specMap L (AlgebraicClosure ℚ)) ⟨y.1 ≫ eη ≫ kL, hx⟩

    have hgy : graphOver c ybar.1 ybar.2 = y.1 ≫ eη := by
      apply pullback.hom_ext
      · rw [graphOver_fst, hybar, Category.assoc]
      · rw [graphOver_snd, Category.assoc, heeta, y.2]
    have hgraphA : graphOver c ybar.1 ybar.2 ≫ Φ.hom =
        graphOver (baseChange A c L) (y.1 ≫ eη ≫ kL) hx := by
      apply pullback.hom_ext
      · rw [Category.assoc, hΦfst, graphOver_fst, hgy, Category.assoc]
      · rw [Category.assoc, hΦsnd, graphOver_snd, graphOver_snd]
    have hεQ : (specMap L (AlgebraicClosure ℚ) ≫ (sectionBaseChange L ε).1) ≫ baseChange A c L =
        specMap L (AlgebraicClosure ℚ) :=
      (Category.assoc _ _ _).trans ((congrArg (specMap L (AlgebraicClosure ℚ) ≫ ·) (sectionBaseChange L ε).2).trans
        (Category.comp_id _))
    have hgraphB : graphOver c (tQ ≫ ε.1) hε ≫ Φ.hom =
        graphOver (baseChange A c L) (specMap L (AlgebraicClosure ℚ) ≫ (sectionBaseChange L ε).1) hεQ := by
      apply pullback.hom_ext
      · rw [Category.assoc, hΦfst, graphOver_fst]
        apply pullback.hom_ext
        · rw [Category.assoc, Category.assoc, hkL₁, graphOver_fst, sectionBaseChange_coe_fst, hgen, Category.assoc]
        · rw [Category.assoc, Category.assoc, hkL₂, graphOver_snd_assoc, sectionBaseChange_coe_snd, Category.comp_id]
      · rw [Category.assoc, hΦsnd, graphOver_snd, graphOver_snd]

    have hIA := Scheme.Hom.isInvertible_ker_of_comp_eq_id
      (p := pullback.snd (baseChange A c L) (specMap L (AlgebraicClosure ℚ)))
      (graphOver (baseChange A c L) (y.1 ≫ eη ≫ kL) hx) (graphOver_snd _ _ _)
    have hIA' := Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd c (tQ))
      (graphOver c ybar.1 ybar.2) (graphOver_snd _ _ _)
    have hIB := Scheme.Hom.isInvertible_ker_of_comp_eq_id
      (p := pullback.snd (baseChange A c L) (specMap L (AlgebraicClosure ℚ)))
      (graphOver (baseChange A c L) (specMap L (AlgebraicClosure ℚ) ≫ (sectionBaseChange L ε).1) hεQ)
      (graphOver_snd _ _ _)
    have hIB' := Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd c (tQ))
      (graphOver c (tQ ≫ ε.1) hε) (graphOver_snd _ _ _)
    obtain ⟨⟨jA⟩, -⟩ := GKit.nonempty_pullback_ker_invModule_iso_of_isIso Φ.hom _ _ hgraphA hIA hIA'
    obtain ⟨-, ⟨jB⟩⟩ := GKit.nonempty_pullback_ker_invModule_iso_of_isIso Φ.hom _ _ hgraphB hIB hIB'

    have haQ : ((y.1 ≫ eη ≫ kL) ≫ ajL.1) ≫ (D.baseChange L).toBase = specMap L (AlgebraicClosure ℚ) :=
      (Category.assoc _ _ _).trans ((congrArg ((y.1 ≫ eη ≫ kL) ≫ ·) ajL.2).trans hx)
    have hcomp : baseChangeSnd c a =
        Φ.hom ≫ baseChangeSnd (baseChange A c L)
            (⟨(y.1 ≫ eη ≫ kL) ≫ ajL.1, haQ⟩ : SchemeHomOver (specMap L (AlgebraicClosure ℚ)) (D.baseChange L).toBase) ≫
          (κ c L (D.baseChange L).toBase).hom ≫
          baseChangeSnd c (⟨pullback.fst D.toBase (specMap A L), pullback.condition⟩ :
            SchemeHomOver ((D.baseChange L).toBase ≫ specMap A L) D.toBase) := by
      apply pullback.hom_ext <;>
        simp only [Category.assoc, baseChangeSnd_fst', baseChangeSnd_snd', baseChangeSnd_fst'_assoc,
          baseChangeSnd_snd'_assoc, κ_hom_fst, κ_hom_snd_assoc, reassoc_of% hΦfst,
          reassoc_of% hΦsnd, hkL₁', ha, hajbar]

    refine ⟨hIA', ⟨(Scheme.Modules.pullbackCongr hcomp).app hD.poincare.L ≪≫
      ((Scheme.Modules.pullbackComp Φ.hom _).app _).symm ≪≫
      (Scheme.Modules.pullback Φ.hom).mapIso
        (((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
          (Scheme.Modules.pullback _).mapIso (((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫ ePL.symm) ≪≫ eAJ) ≪≫
      Scheme.Modules.pullbackTensorObjIso Φ.hom _ _ ≪≫ (jA ⊗ᵢ jB)⟩⟩

  let xP := Mη.pointEquivPlace.symm P
  let xQ := Mη.pointEquivPlace.symm Q
  obtain ⟨Dv₁, hDv₁, ha₁⟩ := hpts_aj xP εbar hεbar
  obtain ⟨Dv₂, hDv₂, ha₂⟩ := hpts_aj xQ εbar hεbar
  have hxP : Mη.pointEquivPlace xP = P := Equiv.apply_symm_apply _ _
  have hxQ : Mη.pointEquivPlace xQ = Q := Equiv.apply_symm_apply _ _
  have hDv12 : Dv = Dv₁ - Dv₂ := by
    apply Subtype.ext
    rw [AddSubgroupClass.coe_sub, hDv, hDv₁, hDv₂, hxP, hxQ]
    abel
  let ybP : SchemeHomOver tQ c := ⟨((Mη.pointEquivPlace.symm P).1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))), (by rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc eη, heη, ← Category.assoc, (Mη.pointEquivPlace.symm P).2, Category.id_comp])⟩
  let ybQ : SchemeHomOver tQ c := ⟨((Mη.pointEquivPlace.symm Q).1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))), (by rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc eη, heη, ← Category.assoc, (Mη.pointEquivPlace.symm Q).2, Category.id_comp])⟩
  obtain ⟨-, ⟨e₁⟩⟩ := key xP ybP rfl (gpts (Pic0.mk Dv₁)) ha₁
  obtain ⟨hKQ, ⟨e₂⟩⟩ := key xQ ybQ rfl (gpts (Pic0.mk Dv₂)) ha₂

  let Lw := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD
  letI grpQ : Group (SchemeHomOver tQ D.toBase) := Lw.pointGroup tQ
  have hg0 : gpts 0 = (1 : SchemeHomOver tQ D.toBase) := by
    have h := hgadd 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  let gM : Multiplicative (ModularCurve.JOne (M * p)) →* SchemeHomOver tQ D.toBase :=
    { toFun := fun x => gpts x.toAdd
      map_one' := hg0
      map_mul' := fun a b => hgadd a.toAdd b.toAdd }
  have hgM : ∀ x, gM (Multiplicative.ofAdd x) = gpts x := fun _ => rfl
  set g₁ := gpts (Pic0.mk Dv₁) with hg₁
  set g₂ := gpts (Pic0.mk Dv₂) with hg₂
  have hg : gpts (Pic0.mk Dv) = g₁ * g₂⁻¹ := by
    rw [hDv12, ← hgM, show Pic0.mk (Dv₁ - Dv₂) = Pic0.mk Dv₁ - Pic0.mk Dv₂ from map_sub (QuotientAddGroup.mk' _) _ _,
      ofAdd_sub, map_div, hgM, hgM, div_eq_mul_inv]
  obtain ⟨em⟩ := AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_pullbackAlong_mul_iso (P := algEquivZeroGroupCut _ _) hD tQ (g₁ * g₂⁻¹) g₂
  obtain ⟨em2⟩ := AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_pullbackAlong_mul_iso (P := algEquivZeroGroupCut _ _) hD tQ g₂ g₂⁻¹
  obtain ⟨e1⟩ := AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_pullbackAlong_one_iso (P := algEquivZeroGroupCut _ _) hD tQ
  have hcancel : Lw.mul tQ (g₁ * g₂⁻¹) g₂ = g₁ := inv_mul_cancel_right g₁ g₂
  have hone : Lw.mul tQ g₂ g₂⁻¹ = Lw.one tQ := mul_inv_cancel g₂
  have eN : (hD.poincare.pullbackAlong g₂).L ⊗ (hD.poincare.pullbackAlong g₂⁻¹).L ≅ 𝟙_ _ :=
    em2.symm ≪≫ eqToIso (by rw [hone]) ≪≫ e1
  have eL : (hD.poincare.pullbackAlong (g₁ * g₂⁻¹)).L ⊗ (hD.poincare.pullbackAlong g₂).L ≅ (hD.poincare.pullbackAlong g₁).L :=
    em.symm ≪≫ eqToIso (by rw [hcancel])
  obtain ⟨eKK⟩ := hKQ.nonempty_module_tensor_invModule_iso.1
  have e : (hD.poincare.pullbackAlong (g₁ * g₂⁻¹)).L ⊗ (hD.poincare.pullbackAlong g₂).L ≅
      ((RelEffCartierDiv.ofPoint c ybP.1 ybP.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c ybQ.1 ybQ.2).idealModule) ⊗
        (hD.poincare.pullbackAlong g₂).L :=
    eL ≪≫ e₁ ≪≫
      whiskerLeftIso _ ((λ_ _).symm ≪≫ whiskerRightIso eKK.symm _ ≪≫ α_ _ _ _) ≪≫ (α_ _ _ _).symm ≪≫
      whiskerLeftIso _ e₂.symm
  rw [hg]
  exact ⟨monoidalCancel eN e⟩

end S_ModularCurve_XOneP_nonempty_poincare_pullbackAlong_points_pic0Mk_single_sub_single_iso_ofPoint_tensor_idealModule_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_nonempty_poincare_pullbackAlong_points_pic0Mk_single_sub_single_iso_ofPoint_tensor_idealModule_twoChartModel_x1_mul (solution)
