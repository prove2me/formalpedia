-- Prove2me | solution 1 for ModularCurve.heckeOperatorBar_points_eq_comp_of_transform
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/115bddce-32bd-5bb1-bc59-28f550f3613d

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_GeometricBaseChange

import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_HeckeOperator

import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_baseChange_relativeGroupLaw_mul_compat
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_normModule_tensor_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_normModule_unit_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_normModule_invModule_ker_iso
import Theorems.Thm_ModularCurve_heckeInputsAlong_of_prime
import Theorems.Thm_AlgebraicCurve_CurveModel_ker_comap_eq_prod_ker_pow_ramificationIndex
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_normModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field
import Theorems.Thm_AlgebraicCurve_exists_list_isPrincipal_sub_sum_single_sub_smul_single
import Theorems.Thm_ModularCurve_inertiaDegAlong_eq_one_laurentBaseChange
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_essFiniteType_modularFunctionFieldBar
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_normModule_iso
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_finrank_pullbackMap_of_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_heckeOperatorBar_points_eq_comp_of_transform
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion"
p2m_attr_erase "instance" "ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply"

set_option autoImplicit false
set_option linter.unusedVariables false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian ModularCurve P2MW.S_ModularCurve_heckeOperatorBar_points_eq_comp_of_transform.ModularCurve AlgebraicCurve AlgebraicGeometry.SmoothProperCurve"

noncomputable section

universe u v

local notation "ℚ̄" => AlgebraicClosure ℚ

namespace HeckeS8

section K

abbrev cls {X : Scheme.{u}} (M : X.Modules) : Skeleton X.Modules := toSkeleton M

theorem cls_eq_iff {X : Scheme.{u}} (A B : X.Modules) : cls A = cls B ↔ Nonempty (A ≅ B) :=
  ⟨fun h => Quotient.exact h, fun ⟨e⟩ => Quotient.sound ⟨e⟩⟩

theorem cls_congr {X : Scheme.{u}} {A B : X.Modules} (e : A ≅ B) : cls A = cls B :=
  (cls_eq_iff A B).2 ⟨e⟩

noncomputable def isoOfClsEq {X : Scheme.{u}} {A B : X.Modules} (h : cls A = cls B) : A ≅ B :=
  ((cls_eq_iff A B).1 h).some

theorem cls_tensor {X : Scheme.{u}} (A B : X.Modules) : cls (A ⊗ B) = cls A * cls B :=
  Skeleton.toSkeleton_tensorObj A B

theorem cls_unit (X : Scheme.{u}) : cls (𝟙_ X.Modules) = 1 := Skeleton.one_eq.symm

theorem isUnit_cls {X : Scheme.{u}} {L : X.Modules} (hL : Scheme.Modules.IsInvertible L) :
    IsUnit (cls L) := by
  obtain ⟨N, -, ⟨e⟩⟩ := hL.exists_tensor_inverse
  have h : cls L * cls N = 1 := ((cls_tensor L N).symm.trans (cls_congr e)).trans (cls_unit X)
  exact ⟨⟨cls L, cls N, h, (mul_comm _ _).trans h⟩, rfl⟩

theorem isInvertible_of_iso {X : Scheme.{u}} {L L' : X.Modules} (hL : Scheme.Modules.IsInvertible L)
    (e : L ≅ L') : Scheme.Modules.IsInvertible L' := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hx, ⟨t⟩⟩ := hL.1 x
  exact ⟨U, hx, ⟨(Scheme.Modules.pullback U.ι).mapIso e.symm ≪≫ t⟩⟩

theorem isInvertible_of_cls_eq {X : Scheme.{u}} {L L' : X.Modules} (hL : Scheme.Modules.IsInvertible L)
    (h : cls L = cls L') : Scheme.Modules.IsInvertible L' :=
  isInvertible_of_iso hL (isoOfClsEq h)

theorem cls_mul_cls_dual {X : Scheme.{u}} {L : X.Modules} (hL : Scheme.Modules.IsInvertible L) :
    cls L * cls (Scheme.Modules.dual L) = 1 :=
  ((cls_tensor _ _).symm.trans (cls_congr hL.dual.2.some)).trans (cls_unit X)

theorem cls_pullback_congr {X Y : Scheme.{u}} (f : X ⟶ Y) {A B : Y.Modules} (h : cls A = cls B) :
    cls ((Scheme.Modules.pullback f).obj A) = cls ((Scheme.Modules.pullback f).obj B) :=
  cls_congr ((Scheme.Modules.pullback f).mapIso (isoOfClsEq h))

theorem cls_pullback_tensor {X Y : Scheme.{u}} (f : X ⟶ Y) (A B : Y.Modules) :
    cls ((Scheme.Modules.pullback f).obj (A ⊗ B)) =
      cls ((Scheme.Modules.pullback f).obj A) * cls ((Scheme.Modules.pullback f).obj B) :=
  (cls_congr (Scheme.Modules.pullbackTensorObjIso f A B)).trans (cls_tensor _ _)

theorem cls_pullback_unit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    cls ((Scheme.Modules.pullback f).obj (𝟙_ Y.Modules)) = 1 :=
  (cls_congr (Scheme.Modules.pullbackTensorUnitObjIso f)).trans (cls_unit X)

theorem cls_pullback_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) :
    cls ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M)) =
      cls ((Scheme.Modules.pullback (f ≫ g)).obj M) :=
  cls_congr ((Scheme.Modules.pullbackComp f g).app M)

theorem cls_pullback_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (M : Y.Modules) :
    cls ((Scheme.Modules.pullback f).obj M) = cls ((Scheme.Modules.pullback g).obj M) := by
  subst h; rfl

theorem cls_pullback_id {X : Scheme.{u}} (M : X.Modules) :
    cls ((Scheme.Modules.pullback (𝟙 X)).obj M) = cls M :=
  cls_congr ((Scheme.Modules.pullbackId X).app M)

theorem cls_pullback_inv_hom {X Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e] (M : Y.Modules) :
    cls ((Scheme.Modules.pullback (inv e)).obj ((Scheme.Modules.pullback e).obj M)) = cls M := by
  rw [cls_pullback_comp, cls_pullback_congr_hom (IsIso.inv_hom_id e), cls_pullback_id]

theorem cls_pullback_hom_inv {X Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e] (M : X.Modules) :
    cls ((Scheme.Modules.pullback e).obj ((Scheme.Modules.pullback (inv e)).obj M)) = cls M := by
  rw [cls_pullback_comp, cls_pullback_congr_hom (IsIso.hom_inv_id e), cls_pullback_id]

theorem cls_eq_of_cls_pullback_eq {X Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e] {A B : Y.Modules}
    (h : cls ((Scheme.Modules.pullback e).obj A) = cls ((Scheme.Modules.pullback e).obj B)) :
    cls A = cls B := by
  rw [← cls_pullback_inv_hom e A, ← cls_pullback_inv_hom e B]
  exact cls_pullback_congr (inv e) h

theorem isInvertible_of_isInvertible_pullback {X Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e] {A : Y.Modules}
    (h : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback e).obj A)) : Scheme.Modules.IsInvertible A :=
  isInvertible_of_cls_eq (h.pullback (inv e)) (cls_pullback_inv_hom e A)

theorem cls_normModule_congr {X Y : Scheme.{u}} (π : X ⟶ Y) (d : ℕ) {L L' : X.Modules} (h : cls L = cls L') :
    cls (Scheme.Modules.normModule π d L) = cls (Scheme.Modules.normModule π d L') :=
  cls_congr (Scheme.Modules.normModuleMapIso π d (isoOfClsEq h))

theorem cls_normModule_tensor {X Y : Scheme.{u}} (π : X ⟶ Y) [IsFinite π] [Flat π]
    [LocallyOfFinitePresentation π] (d : ℕ) (hd : ∀ y : Y, π.finrank y = d)
    {L L' : X.Modules} (hL : Scheme.Modules.IsInvertible L) (hL' : Scheme.Modules.IsInvertible L') :
    cls (Scheme.Modules.normModule π d (L ⊗ L')) =
      cls (Scheme.Modules.normModule π d L) * cls (Scheme.Modules.normModule π d L') :=
  (cls_congr (Scheme.Modules.nonempty_normModule_tensor_iso π d hd L L' hL hL').some).trans (cls_tensor _ _)

theorem cls_normModule_unit {X Y : Scheme.{u}} (π : X ⟶ Y) [IsFinite π] [Flat π]
    [LocallyOfFinitePresentation π] (d : ℕ) (hd : ∀ y : Y, π.finrank y = d) :
    cls (Scheme.Modules.normModule π d (𝟙_ X.Modules)) = 1 :=
  (cls_congr (Scheme.Modules.nonempty_normModule_unit_iso π d hd).some).trans (cls_unit Y)

theorem isUnit_cls_normModule {X Y : Scheme.{u}} (π : X ⟶ Y) [IsFinite π] [Flat π]
    [LocallyOfFinitePresentation π] (d : ℕ) (hd : ∀ y : Y, π.finrank y = d)
    {L : X.Modules} (hL : Scheme.Modules.IsInvertible L) :
    IsUnit (cls (Scheme.Modules.normModule π d L)) :=
  isUnit_cls (hL.normModule π d hd)

theorem cls_norm_invModule_mul {X Y : Scheme.{u}} (π : X ⟶ Y) [IsFinite π] [Flat π]
    [LocallyOfFinitePresentation π] (d : ℕ) (hd : ∀ y : Y, π.finrank y = d)
    {I J : X.IdealSheafData} (hI : I.IsInvertible) (hJ : J.IsInvertible) :
    cls (Scheme.Modules.normModule π d (I * J).invModule) =
      cls (Scheme.Modules.normModule π d I.invModule) * cls (Scheme.Modules.normModule π d J.invModule) := by
  rw [cls_normModule_congr π d (cls_congr (hI.nonempty_mul_invModule_iso_tensor hJ).some),
    cls_normModule_tensor π d hd hI.isInvertible_invModule hJ.isInvertible_invModule]

theorem cls_norm_invModule_pow_mul {X Y : Scheme.{u}} (π : X ⟶ Y) [IsFinite π] [Flat π]
    [LocallyOfFinitePresentation π] (d : ℕ) (hd : ∀ y : Y, π.finrank y = d)
    {I J : X.IdealSheafData} (hI : I.IsInvertible) (hJ : J.IsInvertible) (n : ℕ) :
    cls (Scheme.Modules.normModule π d (I ^ n * J).invModule) =
      cls (Scheme.Modules.normModule π d I.invModule) ^ n * cls (Scheme.Modules.normModule π d J.invModule) := by
  induction n generalizing J with
  | zero => rw [pow_zero, one_mul, pow_zero, one_mul]
  | succ n ih =>
    rw [pow_succ, mul_assoc, ih (hI.mul hJ), cls_norm_invModule_mul π d hd hI hJ, pow_succ, mul_assoc]

theorem isInvertible_prod_pow {X : Scheme.{u}} {ι : Type*} (s : Finset ι) (I : ι → X.IdealSheafData)
    (n : ι → ℕ) (h : ∀ i ∈ s, (I i).IsInvertible) : (∏ i ∈ s, I i ^ n i).IsInvertible := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Scheme.IdealSheafData.isInvertible_top
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact ((h a (Finset.mem_insert_self a s)).pow _).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem cls_norm_invModule_prod_pow_mul {X Y : Scheme.{u}} (π : X ⟶ Y) [IsFinite π] [Flat π]
    [LocallyOfFinitePresentation π] (d : ℕ) (hd : ∀ y : Y, π.finrank y = d)
    {ι : Type*} (s : Finset ι) (I : ι → X.IdealSheafData) (n : ι → ℕ) (h : ∀ i ∈ s, (I i).IsInvertible)
    {J : X.IdealSheafData} (hJ : J.IsInvertible) :
    cls (Scheme.Modules.normModule π d ((∏ i ∈ s, I i ^ n i) * J).invModule) =
      (∏ i ∈ s, cls (Scheme.Modules.normModule π d (I i).invModule) ^ n i) *
        cls (Scheme.Modules.normModule π d J.invModule) := by
  classical
  induction s using Finset.induction_on generalizing J with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, one_mul, one_mul]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, mul_assoc,
      cls_norm_invModule_pow_mul π d hd (h a (Finset.mem_insert_self a s))
        ((isInvertible_prod_pow s I n fun i hi => h i (Finset.mem_insert_of_mem hi)).mul hJ),
      ih (fun i hi => h i (Finset.mem_insert_of_mem hi)) hJ, mul_assoc]

theorem cls_norm_invModule_prod_pow {X Y : Scheme.{u}} (π : X ⟶ Y) [IsFinite π] [Flat π]
    [LocallyOfFinitePresentation π] (d : ℕ) (hd : ∀ y : Y, π.finrank y = d)
    {ι : Type*} (s : Finset ι) (I : ι → X.IdealSheafData) (n : ι → ℕ) (h : ∀ i ∈ s, (I i).IsInvertible) :
    cls (Scheme.Modules.normModule π d (∏ i ∈ s, I i ^ n i).invModule) =
      ∏ i ∈ s, cls (Scheme.Modules.normModule π d (I i).invModule) ^ n i := by
  have hT := Scheme.IdealSheafData.isInvertible_top (X := X)
  have hP := isInvertible_prod_pow s I n h
  have h1 := cls_norm_invModule_prod_pow_mul π d hd s I n h hT
  rw [cls_norm_invModule_mul π d hd hP hT] at h1
  exact (isUnit_cls_normModule π d hd hT.isInvertible_invModule).mul_left_injective h1

theorem cls_rigidify_of_field {k : Type u} [Field k] {P : Scheme.{u}} (σ : Spec (CommRingCat.of k) ⟶ P)
    (q : P ⟶ Spec (CommRingCat.of k)) {L : P.Modules} (hL : Scheme.Modules.IsInvertible L) :
    cls (Scheme.Modules.rigidify σ q L) = cls L := by
  rw [Scheme.Modules.rigidify_def, cls_tensor]
  have h1 := (hL.pullback σ).dual.1
  obtain ⟨e⟩ := Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field k _ h1
  rw [cls_pullback_congr q (cls_congr e), cls_pullback_unit, mul_one]

end K

section P

def castBase {B Y X : Scheme.{u}} {s s' : Y ⟶ B} {f : X ⟶ B} (e : s = s') (a : SchemeHomOver s f) :
    SchemeHomOver s' f :=
  ⟨a.1, a.2.trans e⟩

@[scoped simp] theorem castBase_coe {B Y X : Scheme.{u}} {s s' : Y ⟶ B} {f : X ⟶ B} (e : s = s')
    (a : SchemeHomOver s f) : (castBase e a).1 = a.1 := rfl

theorem mul_castBase {R : Type u} [CommRing R] {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) {s s' : T ⟶ Spec (CommRingCat.of R)} (e : s = s') (a b : SchemeHomOver s f) :
    G.mul s' (castBase e a) (castBase e b) = castBase e (G.mul s a b) := by
  subst e; rfl

theorem specMap_comp_specMap (R S T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
    [Algebra S T] [Algebra R T] [IsScalarTower R S T] :
    specMap S T ≫ specMap R S = specMap R T := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq R S T]

def liftPt {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    (D : RelativePic0Designation R c) (R' : Type u) [CommRing R'] [Algebra R R']
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) (a : SchemeHomOver (t ≫ specMap R R') D.toBase) :
    SchemeHomOver t (D.baseChange R').toBase :=
  ⟨pullback.lift a.1 t a.2, pullback.lift_snd _ _ _⟩

@[scoped simp] theorem liftPt_fst {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    (D : RelativePic0Designation R c) (R' : Type u) [CommRing R'] [Algebra R R']
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) (a : SchemeHomOver (t ≫ specMap R R') D.toBase) :
    (liftPt D R' t a).1 ≫ pullback.fst D.toBase (specMap R R') = a.1 :=
  pullback.lift_fst _ _ _

theorem eq_liftPt {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    (D : RelativePic0Designation R c) (R' : Type u) [CommRing R'] [Algebra R R']
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) (z : SchemeHomOver t (D.baseChange R').toBase)
    (a : SchemeHomOver (t ≫ specMap R R') D.toBase)
    (hz : z.1 ≫ pullback.fst D.toBase (specMap R R') = a.1) : z = liftPt D R' t a := by
  apply Subtype.ext
  apply pullback.hom_ext
  · exact hz.trans (liftPt_fst D R' t a).symm
  · exact z.2.trans (pullback.lift_snd _ _ _).symm

theorem liftPt_mul {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (D : RelativePic0Designation R c)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (R' : Type u) [CommRing R'] [Algebra R R']
    (h' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'))
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε R'
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩)).L))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) (a b : SchemeHomOver (t ≫ specMap R R') D.toBase) :
    liftPt D R' t ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul
        (t ≫ specMap R R') a b) =
      (RepresentsRelSubPic.relativeGroupLaw
        (P := algEquivZeroGroupCut (baseChange R c R') (sectionBaseChange R' ε)) h').mul t
        (liftPt D R' t a) (liftPt D R' t b) := by
  symm
  apply eq_liftPt
  exact AlgebraicGeometry.RelPicard.baseChange_relativeGroupLaw_mul_compat R c ε D h R' h' hP t _ _ a b
    (liftPt_fst D R' t a).symm (liftPt_fst D R' t b).symm

theorem poincare_liftPt_iso {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (D : RelativePic0Designation R c)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (R' : Type u) [CommRing R'] [Algebra R R']
    (h' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'))
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε R'
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩)).L))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) (a : SchemeHomOver (t ≫ specMap R R') D.toBase) :
    Nonempty ((h'.poincare.pullbackAlong (liftPt D R' t a)).L ≅
      (Scheme.Modules.pullback (BaseChange.κ c R' t).hom).obj (h.poincare.pullbackAlong a).L) := by
  let ψ₀ : SchemeHomOver ((D.baseChange R').toBase ≫ specMap R R') D.toBase :=
    ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩
  have E : baseChangeSnd (baseChange R c R') (liftPt D R' t a) ≫
      (BaseChange.κ c R' (D.baseChange R').toBase).hom ≫ baseChangeSnd c ψ₀ =
      (BaseChange.κ c R' t).hom ≫ baseChangeSnd c a := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, BaseChange.baseChangeSnd_fst', BaseChange.κ_hom_fst,
        ← Category.assoc, BaseChange.baseChangeSnd_fst', Category.assoc, BaseChange.baseChangeSnd_fst',
        BaseChange.κ_hom_fst]
    · rw [Category.assoc, Category.assoc, BaseChange.baseChangeSnd_snd', ← Category.assoc ((BaseChange.κ c R' _).hom),
        BaseChange.κ_hom_snd, ← Category.assoc, BaseChange.baseChangeSnd_snd', Category.assoc, liftPt_fst,
        Category.assoc, BaseChange.baseChangeSnd_snd', ← Category.assoc, BaseChange.κ_hom_snd]
  refine ⟨(Scheme.Modules.pullback _).mapIso hP.some ≪≫ ?_⟩
  change (Scheme.Modules.pullback (baseChangeSnd _ (liftPt D R' t a))).obj
      ((Scheme.Modules.pullback (BaseChange.κ c R' (D.baseChange R').toBase).hom).obj
        ((Scheme.Modules.pullback (baseChangeSnd c ψ₀)).obj h.poincare.L)) ≅
    (Scheme.Modules.pullback (BaseChange.κ c R' t).hom).obj
      ((Scheme.Modules.pullback (baseChangeSnd c a)).obj h.poincare.L)
  exact (Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackCongr (by rw [Category.assoc]; exact E)).app _ ≪≫
    ((Scheme.Modules.pullbackComp _ _).app _).symm

theorem poincare_mul_iso {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s D.toBase) :
    Nonempty ((h.poincare.pullbackAlong
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul s x y)).L ≅
      (h.poincare.pullbackAlong x).L ⊗ (h.poincare.pullbackAlong y).L) :=
  (show RepresentsRelSubPic c ε (algEquivZeroGroupCut c ε).toSubPicCondition D from h)
    |>.nonempty_poincare_pullbackAlong_mul_iso (T := Over.mk s) (schemeHomOverToOverHom x) (schemeHomOverToOverHom y)

theorem poincare_postComp_iso {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {P : SubPicCondition c ε} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P D)
    (Φ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), RigidifiedLineBundle c ε t → RigidifiedLineBundle c ε t)
    (hcut : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t),
      P.P t M → P.P t (Φ t M))
    (φ : SchemeHomOver D.toBase D.toBase)
    (hφ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t) (hM : P.P t M),
      postComp φ (h.classify t M hM) = h.classify t (Φ t M) (hcut t M hM))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (z : SchemeHomOver t D.toBase) :
    Nonempty ((h.poincare.pullbackAlong (postComp φ z)).L ≅ (Φ t (h.poincare.pullbackAlong z)).L) := by
  have hM : P.P t (h.poincare.pullbackAlong z) := P.pullback_mem _ _ z _ h.poincare_mem
  have hz : z = h.classify t _ hM := h.classify_unique t _ hM z ⟨Iso.refl _⟩
  have key := hφ t _ hM
  rw [← hz] at key
  rw [key]
  exact h.classify_spec t _ _

end P

section N

theorem isInvertible_ker_point {k : Type u} [Field k] {L : Type v} [Field L] [Algebra k L] (M : CurveModel k L)
    (x : {q : Spec (CommRingCat.of k) ⟶ M.C // q ≫ M.toBase = 𝟙 _}) : x.1.ker.IsInvertible :=
  Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := M.toBase) x.1 x.2

theorem cls_norm_invModule_ker_point {k : Type u} [Field k] {F F' : Type v} [Field F] [Field F']
    [Algebra k F] [Algebra k F'] (M : CurveModel k F) (M' : CurveModel k F')
    (π : M'.C ⟶ M.C) (hπ : π ≫ M.toBase = M'.toBase)
    [IsFinite π] [Flat π] [LocallyOfFinitePresentation π] (d : ℕ) (hd : ∀ y : M.C, π.finrank y = d)
    (y : {q : Spec (CommRingCat.of k) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _}) :
    cls (Scheme.Modules.normModule π d (y.1.ker).invModule) = cls ((y.1 ≫ π).ker).invModule :=
  cls_congr (Scheme.Modules.nonempty_normModule_invModule_ker_iso M.toBase M'.toBase π hπ d hd y).some

theorem cls_norm_pullback_invModule_ker
    {k : Type u} [Field k] [IsAlgClosed k] {F F' : Type v} [Field F] [Field F'] [Algebra k F] [Algebra k F']
    [IsCurveOver k F] [IsCurveOver k F'] [Algebra.EssFiniteType k F] [Algebra.EssFiniteType k F']
    [Algebra F F'] [IsScalarTower k F F'] [Algebra.IsIntegral F F']
    (M : CurveModel k F) (M' : CurveModel k F')
    (πa πb : M'.C ⟶ M.C) (hπa : πa ≫ M.toBase = M'.toBase) (hπb : πb ≫ M.toBase = M'.toBase)
    [IsFinite πa] [Flat πa] [LocallyOfFinitePresentation πa]
    [IsFinite πb] [Flat πb] [LocallyOfFinitePresentation πb]
    (d : ℕ) (hda : ∀ y : M.C, πa.finrank y = d)
    (hplace : ∀ (y : {q : Spec (CommRingCat.of k) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _})
        (x : {q : Spec (CommRingCat.of k) ⟶ M.C // q ≫ M.toBase = 𝟙 _}),
      y.1 ≫ πb = x.1 → (M'.pointEquivPlace y).restrict F = M.pointEquivPlace x)
    (x : {q : Spec (CommRingCat.of k) ⟶ M.C // q ≫ M.toBase = 𝟙 _}) :
    cls (Scheme.Modules.normModule πa d ((Scheme.Modules.pullback πb).obj (x.1.ker).invModule)) =
      ∏ w ∈ (M.pointEquivPlace x).fiber F',
        cls ((((M'.pointEquivPlace.symm w).1 ≫ πa).ker).invModule) ^ (w.ramificationIndex F) := by
  have hx : x.1.ker.IsInvertible := isInvertible_ker_point M x
  have hprod := CurveModel.ker_comap_eq_prod_ker_pow_ramificationIndex M M' πb hπb hplace x
  have hinv : ((x.1.ker).comap πb).IsInvertible := by
    rw [hprod]; exact isInvertible_prod_pow _ _ _ (fun w _ => isInvertible_ker_point M' _)
  rw [cls_normModule_congr πa d (cls_congr (hx.nonempty_pullback_invModule_iso πb hinv).some), hprod,
    cls_norm_invModule_prod_pow πa d hda _ _ _ (fun w _ => isInvertible_ker_point M' _)]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [cls_norm_invModule_ker_point M M' πa hπa d hda]

theorem cls_pullback_norm_pullback_of_isos {A A' B B' : Scheme.{u}}
    (eB : A ⟶ B) [IsIso eB] (eη' : A' ⟶ B') [IsIso eη']
    (α β : B' ⟶ B) (πa πb : A' ⟶ A) (hα : πa ≫ eB = eη' ≫ α) (hβ : πb ≫ eB = eη' ≫ β)
    [IsFinite πa] [Flat πa] [LocallyOfFinitePresentation πa] (d : ℕ) (hda : ∀ y : A, πa.finrank y = d)
    {W : B.Modules} (hW : Scheme.Modules.IsInvertible W) :
    cls ((Scheme.Modules.pullback eB).obj
        (Scheme.Modules.normModule α d ((Scheme.Modules.pullback β).obj W))) =
      cls (Scheme.Modules.normModule πa d
        ((Scheme.Modules.pullback πb).obj ((Scheme.Modules.pullback eB).obj W))) := by
  have sq : IsPullback (inv eη') β πb (inv eB) := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv]
    exact hβ
  have sqa : IsPullback (inv eη') α πa (inv eB) := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv]
    exact hα
  have hL : Scheme.Modules.IsInvertible
      ((Scheme.Modules.pullback πb).obj ((Scheme.Modules.pullback eB).obj W)) := (hW.pullback eB).pullback πb
  have e1 : cls ((Scheme.Modules.pullback β).obj W) =
      cls ((Scheme.Modules.pullback (inv eη')).obj
        ((Scheme.Modules.pullback πb).obj ((Scheme.Modules.pullback eB).obj W))) := by
    rw [cls_pullback_comp, cls_pullback_comp,
      cls_pullback_congr_hom (show (inv eη' ≫ πb) ≫ eB = β by rw [Category.assoc, hβ, IsIso.inv_hom_id_assoc])]
  obtain ⟨e2⟩ := Scheme.Modules.nonempty_pullback_normModule_iso πa d hda (inv eB) α (inv eη') sqa hL
  rw [cls_pullback_congr eB (cls_normModule_congr α d e1), ← cls_pullback_congr eB (cls_congr e2),
    cls_pullback_hom_inv]

end N

section D

def genClass {K F : Type*} [Field K] [Field F] [Algebra K F] (hdeg : ∀ v : Place K F, v.deg = 1)
    (v₀ u : Place K F) : Pic0 K F :=
  Pic0.mk ⟨Finsupp.single u 1 - Finsupp.single v₀ 1, by
    rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, hdeg, hdeg]; simp⟩

theorem genClass_eq_mk {K F : Type*} [Field K] [Field F] [Algebra K F] (hdeg : ∀ v : Place K F, v.deg = 1)
    (v₀ u : Place K F) (Dv : Divisor.degZero (K := K) (F := F))
    (hDv : (Dv : Divisor K F) = Finsupp.single u 1 - Finsupp.single v₀ 1) :
    Pic0.mk Dv = genClass hdeg v₀ u := by
  unfold genClass; congr 1; exact Subtype.ext hDv

theorem sum_ramificationIndexAlong_eq_finrankAlong {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [HasPrincipalDivisors K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hFI : FundamentalIdentityAlong K φ hφ)
    (hdeg : ∀ v : Place K F, v.deg = 1) (hdeg' : ∀ w : Place K F', w.deg = 1) (v : Place K F) :
    ∑ w ∈ Place.fiberAlong φ hφ v, (w.ramificationIndexAlong φ : ℤ) = (finrankAlong K φ : ℤ) := by
  have h1 := Divisor.degree_pullbackAlong φ hφ hFI (Finsupp.single v 1)
  rw [Divisor.pullbackAlong_single, map_sum, Divisor.degree_single, hdeg] at h1
  simp only [Divisor.degree_single, hdeg', Nat.cast_one, mul_one, one_mul] at h1
  exact h1

theorem correspondence_genClass_add_sum_eq_sum {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hFI : FundamentalIdentityAlong K φ hφ) (hfin : FiniteAlong K ψ) (hN : NormFormulaAlong K ψ hfin)
    (hdeg : ∀ v : Place K F, v.deg = 1) (hdeg' : ∀ w : Place K F', w.deg = 1)
    (hinert : ∀ w : Place K F', w.inertiaDegAlong ψ hψ = 1) (v₀ v : Place K F) :
    Pic0.correspondence φ ψ hφ hψ hFI hfin hN (genClass hdeg v₀ v) +
        ∑ w ∈ Place.fiberAlong φ hφ v₀, w.ramificationIndexAlong φ • genClass hdeg v₀ (w.restrictAlong ψ hψ) =
      ∑ w ∈ Place.fiberAlong φ hφ v, w.ramificationIndexAlong φ • genClass hdeg v₀ (w.restrictAlong ψ hψ) := by
  classical

  have hmem : ∀ u : Place K F, Finsupp.single u (1 : ℤ) - Finsupp.single v₀ 1 ∈ Divisor.degZero (K := K) (F := F) := by
    intro u; rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, hdeg, hdeg]; simp
  set dgen : Place K F → Divisor.degZero (K := K) (F := F) := fun u => ⟨_, hmem u⟩ with hdgen
  have hgc : ∀ u, genClass hdeg v₀ u = Pic0.mk (dgen u) := fun u => rfl

  let G : Divisor.degZero (K := K) (F := F) →+ Pic0 K F := QuotientAddGroup.mk' _
  have hG : ∀ D, Pic0.mk D = G D := fun _ => rfl

  have hsum : ∀ u : Place K F, ∑ w ∈ Place.fiberAlong φ hφ u, (w.ramificationIndexAlong φ : ℤ) = finrankAlong K φ :=
    fun u => sum_ramificationIndexAlong_eq_finrankAlong φ hφ hFI hdeg hdeg' u
  simp only [hgc]
  rw [Pic0.correspondence_mk]
  simp only [hG, ← map_nsmul, ← map_sum, ← map_add]
  congr 1
  apply Subtype.ext
  simp only [AddSubgroup.coe_add, AddSubgroup.val_finsetSum, AddSubgroup.coe_nsmul, Pic0.coe_degZeroCorrespondence,
    hdgen, Divisor.correspondence_apply, map_sub, Divisor.pullbackAlong_single, map_sum,
    Divisor.pushforwardAlong_single, hinert, Nat.cast_one, mul_one, one_mul, smul_sub, Finset.sum_sub_distrib,
    Finsupp.smul_single, nsmul_eq_mul]
  have h1 : ∀ u : Place K F, ∑ x ∈ Place.fiberAlong φ hφ u,
      Finsupp.single v₀ ((x.ramificationIndexAlong φ : ℕ) : ℤ) = Finsupp.single v₀ ((finrankAlong K φ : ℕ) : ℤ) := by
    intro u; rw [← Finsupp.single_finsetSum, hsum u]
  rw [h1, h1]
  abel

theorem closure_range_genClass_eq_top {K : Type u} [Field K] [IsAlgClosed K] {F : Type v} [Field F]
    [Algebra K F] [IsCurveOver K F] [Algebra.EssFiniteType K F]
    (hdeg : ∀ v : Place K F, v.deg = 1) (v₀ : Place K F) :
    AddSubgroup.closure (Set.range (genClass hdeg v₀)) = ⊤ := by
  classical
  rw [eq_top_iff]
  rintro x -
  obtain ⟨Dv, rfl⟩ := Pic0.mk_surjective x
  obtain ⟨l, hl⟩ := AlgebraicCurve.exists_list_isPrincipal_sub_sum_single_sub_smul_single v₀
    (Dv : Divisor K F) (Divisor.mem_degZero.1 Dv.2)

  have hmem : ∀ u : Place K F, Finsupp.single u (1 : ℤ) - Finsupp.single v₀ 1 ∈ Divisor.degZero (K := K) (F := F) := by
    intro u; rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, hdeg, hdeg]; simp
  let dgen : Place K F → Divisor.degZero (K := K) (F := F) := fun u => ⟨_, hmem u⟩
  have hgc : ∀ u, genClass hdeg v₀ u = Pic0.mk (dgen u) := fun u => rfl
  let G : Divisor.degZero (K := K) (F := F) →+ Pic0 K F := QuotientAddGroup.mk' _
  have hG : ∀ D, Pic0.mk D = G D := fun _ => rfl

  have hval : ∀ l' : List (Place K F), ((l'.map dgen).sum : Divisor K F) =
      (l'.map fun v => Finsupp.single v (1 : ℤ)).sum - (l'.length : ℤ) • Finsupp.single v₀ 1 := by
    intro l'
    induction l' with
    | nil => simp
    | cons a l' ih =>
      simp only [List.map_cons, List.sum_cons, AddSubgroup.coe_add, ih, List.length_cons, Nat.cast_succ, dgen]
      rw [add_smul, one_smul]
      abel
  have hclass : Pic0.mk Dv = (l.map (genClass hdeg v₀)).sum := by
    have e1 : (l.map (genClass hdeg v₀)).sum = G (l.map dgen).sum := by
      rw [map_list_sum, List.map_map]
      congr 1
    rw [e1, hG]
    apply (QuotientAddGroup.eq (s := (Divisor.principal (K := K) (F := F)).addSubgroupOf _)).2
    rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add, AddSubgroup.coe_neg, hval l, neg_add_eq_sub, ← neg_sub]
    exact neg_mem (Divisor.mem_principal.2 hl)
  rw [hclass]
  refine list_sum_mem fun y hy => ?_
  obtain ⟨u, -, rfl⟩ := List.mem_map.1 hy
  exact AddSubgroup.subset_closure ⟨u, rfl⟩

end D

end HeckeS8
p2m_reactivate "P2MW.S_ModularCurve_heckeOperatorBar_points_eq_comp_of_transform.HeckeS8"

namespace HeckeS8

universe w

theorem isPullback_fst_curveChange {R : Type w} [CommRing R] {C C' T : Scheme.{w}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    (f : C' ⟶ C) (hf : f ≫ c = c') (t : T ⟶ Spec (CommRingCat.of R)) :
    IsPullback (pullback.fst c' t) (curveChange f hf t) f (pullback.fst c t) := by
  refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback c t)
  · rw [curveChange_snd, hf]
    exact IsPullback.of_hasPullback c' t
  · simp only [curveChange, pullback.lift_fst]

theorem curveChange_fst {R : Type w} [CommRing R] {C C' T : Scheme.{w}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    (f : C' ⟶ C) (hf : f ≫ c = c') (t : T ⟶ Spec (CommRingCat.of R)) :
    curveChange f hf t ≫ pullback.fst c t = pullback.fst c' t ≫ f := by
  simp only [curveChange, pullback.lift_fst]

theorem finrank_curveChange_eq {R : Type w} [CommRing R] {C C' T : Scheme.{w}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    (π : C' ⟶ C) (hπ : π ≫ c = c') [IsFinite π] [Flat π]
    (d : ℕ) (hd : ∀ y : C, π.finrank y = d)
    (t : T ⟶ Spec (CommRingCat.of R)) (y : ↑(pullback c t)) :
    (curveChange π hπ t).finrank y = d :=
  (Scheme.Hom.finrank_pullbackMap_of_comp_eq c c' t π hπ y).trans (hd _)

scoped instance isFinite_curveChange {R : Type w} [CommRing R] {C C' T : Scheme.{w}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    (f : C' ⟶ C) (hf : f ≫ c = c') (t : T ⟶ Spec (CommRingCat.of R)) [IsFinite f] :
    IsFinite (curveChange f hf t) :=
  MorphismProperty.of_isPullback (P := @IsFinite) (isPullback_fst_curveChange f hf t) inferInstance

scoped instance flat_curveChange {R : Type w} [CommRing R] {C C' T : Scheme.{w}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    (f : C' ⟶ C) (hf : f ≫ c = c') (t : T ⟶ Spec (CommRingCat.of R)) [Flat f] :
    Flat (curveChange f hf t) :=
  MorphismProperty.of_isPullback (P := @Flat) (isPullback_fst_curveChange f hf t) inferInstance

scoped instance locallyOfFinitePresentation_curveChange {R : Type w} [CommRing R] {C C' T : Scheme.{w}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    (f : C' ⟶ C) (hf : f ≫ c = c') (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFinitePresentation f] :
    LocallyOfFinitePresentation (curveChange f hf t) :=
  MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) (isPullback_fst_curveChange f hf t) inferInstance

end HeckeS8
p2m_reactivate "P2MW.S_ModularCurve_heckeOperatorBar_points_eq_comp_of_transform.HeckeS8"

namespace ModularCurve p2m_export "ModularCurve" "arithmeticGalois modularFunctionFieldBar JZero modularFunctionFieldFull heckeOperatorBar heckeOperatorBar_apply heckeOperatorAlong_eq heckeAlphaBar heckeBetaBar heckeInputsAlong_of_prime inertiaDegAlong_eq_one_laurentBaseChange deg_eq_one_modularFunctionFieldBar isCurveOver_modularFunctionFieldBar essFiniteType_modularFunctionFieldBar" namespace S8 end ModularCurve.S8
p2m_open_scoped "ModularCurve" in
set_option maxHeartbeats 3200000 in

theorem ModularCurve.S8.degeneracyBar_beta_package
    (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime]
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]

    (Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar p))
    (eη : Mη.C ⟶ pullback c (Spec.map (CommRingCat.ofHom
      (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))))) [IsIso eη]
    (heη : eη ≫ pullback.snd c _ = Mη.toBase)
    (q : Nat.Primes) [NeZero (q : ℕ)] [NeZero (p * (q : ℕ))]

    (Y : Scheme.{0}) (cY : Y ⟶ Spec (CommRingCat.of ℚ))
    (πβ : Y ⟶ pullback c (specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ))
    (hβ : πβ ≫ baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ = cY)
    [IsFinite πβ] [Flat πβ] [LocallyOfFinitePresentation πβ]

    (Mη' : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar (p * (q : ℕ))))
    (eη' : Mη'.C ⟶ pullback cY (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))) [IsIso eη']
    (heη' : eη' ≫ pullback.snd _ _ = Mη'.toBase)
    (hβI : (heckeBetaBar (AlgebraicClosure ℚ) p q).toRingHom.IsIntegral)
    (hplaceβ : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη'.C // q ≫ Mη'.toBase = 𝟙 _})
        (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      y.1 ≫ eη' ≫ pullback.fst cY _ ≫ πβ ≫ pullback.fst c _ = x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x =
        Place.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) p q) hβI (Mη'.pointEquivPlace y))

    (j : pullback (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ)
        (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) ≅
      pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))))
    (hj₁ : j.hom ≫ pullback.fst c _ =
      pullback.fst (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ)
          (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) ≫
        pullback.fst c (specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ))
    (hj₂ : j.hom ≫ pullback.snd c _ =
      pullback.snd (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ)
        (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))) :
    letI := AlgebraicCurve.algebraAlong (heckeBetaBar (AlgebraicClosure ℚ) p q)
    haveI := AlgebraicCurve.isScalarTower_along (heckeBetaBar (AlgebraicClosure ℚ) p q)
    haveI := AlgebraicCurve.isIntegral_along (heckeBetaBar (AlgebraicClosure ℚ) p q) hβI
    ∃ πbar : Mη'.C ⟶ Mη.C,
      πbar = eη' ≫ curveChange πβ hβ
          (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) ≫ j.hom ≫ inv eη ∧
      πbar ≫ Mη.toBase = Mη'.toBase ∧
      IsFinite πbar ∧ Flat πbar ∧ LocallyOfFinitePresentation πbar ∧
      ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη'.C // q ≫ Mη'.toBase = 𝟙 _})
        (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
        y.1 ≫ πbar = x.1 →
          (Mη'.pointEquivPlace y).restrict (modularFunctionFieldBar p) = Mη.pointEquivPlace x := by

  letI := AlgebraicCurve.algebraAlong (heckeBetaBar (AlgebraicClosure ℚ) p q)
  haveI := AlgebraicCurve.isScalarTower_along (heckeBetaBar (AlgebraicClosure ℚ) p q)
  haveI := AlgebraicCurve.isIntegral_along (heckeBetaBar (AlgebraicClosure ℚ) p q) hβI
  have h1 : inv eη ≫ Mη.toBase = pullback.snd c _ := by rw [← heη, IsIso.inv_hom_id_assoc]
  refine ⟨_, rfl, ?_, inferInstance, inferInstance, inferInstance, ?_⟩
  · simp only [Category.assoc]
    rw [h1, hj₂, curveChange_snd]
    exact heη'
  · intro y x hyx
    have key := hplaceβ y x (by
      rw [← hyx]
      simp only [Category.assoc, IsIso.inv_hom_id_assoc]
      rw [hj₁, ← Category.assoc (curveChange _ _ _), HeckeS8.curveChange_fst, Category.assoc])
    exact key.symm

p2m_open_scoped "ModularCurve" in
set_option maxHeartbeats 3200000 in

theorem ModularCurve.S8.degeneracyBar_alpha_package
    (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime]
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]

    (Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar p))
    (eη : Mη.C ⟶ pullback c (Spec.map (CommRingCat.ofHom
      (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))))) [IsIso eη]
    (heη : eη ≫ pullback.snd c _ = Mη.toBase)
    (q : Nat.Primes) [NeZero (q : ℕ)] [NeZero (p * (q : ℕ))]

    (Y : Scheme.{0}) (cY : Y ⟶ Spec (CommRingCat.of ℚ))
    (πα : Y ⟶ pullback c (specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ))
    (hα : πα ≫ baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ = cY)
    [IsFinite πα] [Flat πα] [LocallyOfFinitePresentation πα]
    (d : ℕ) (hdα : ∀ y, πα.finrank y = d)

    (Mη' : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar (p * (q : ℕ))))
    (eη' : Mη'.C ⟶ pullback cY (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))) [IsIso eη']
    (heη' : eη' ≫ pullback.snd _ _ = Mη'.toBase)
    (hαI : (heckeAlphaBar (AlgebraicClosure ℚ) p q).toRingHom.IsIntegral)
    (hplaceα : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη'.C // q ≫ Mη'.toBase = 𝟙 _})
        (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      y.1 ≫ eη' ≫ pullback.fst cY _ ≫ πα ≫ pullback.fst c _ = x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x =
        Place.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) p q) hαI (Mη'.pointEquivPlace y))

    (j : pullback (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ)
        (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) ≅
      pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))))
    (hj₁ : j.hom ≫ pullback.fst c _ =
      pullback.fst (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ)
          (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) ≫
        pullback.fst c (specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ))
    (hj₂ : j.hom ≫ pullback.snd c _ =
      pullback.snd (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ)
        (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))) :
    letI := AlgebraicCurve.algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) p q)
    haveI := AlgebraicCurve.isScalarTower_along (heckeAlphaBar (AlgebraicClosure ℚ) p q)
    haveI := AlgebraicCurve.isIntegral_along (heckeAlphaBar (AlgebraicClosure ℚ) p q) hαI
    ∃ πbar : Mη'.C ⟶ Mη.C,
      πbar = eη' ≫ curveChange πα hα
          (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) ≫ j.hom ≫ inv eη ∧
      πbar ≫ Mη.toBase = Mη'.toBase ∧
      IsFinite πbar ∧ Flat πbar ∧ LocallyOfFinitePresentation πbar ∧
      (∀ y : Mη.C, πbar.finrank y = d) ∧
      ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη'.C // q ≫ Mη'.toBase = 𝟙 _})
        (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
        y.1 ≫ πbar = x.1 →
          (Mη'.pointEquivPlace y).restrict (modularFunctionFieldBar p) = Mη.pointEquivPlace x := by

  letI := AlgebraicCurve.algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) p q)
  haveI := AlgebraicCurve.isScalarTower_along (heckeAlphaBar (AlgebraicClosure ℚ) p q)
  haveI := AlgebraicCurve.isIntegral_along (heckeAlphaBar (AlgebraicClosure ℚ) p q) hαI
  have h1 : inv eη ≫ Mη.toBase = pullback.snd c _ := by rw [← heη, IsIso.inv_hom_id_assoc]
  refine ⟨_, rfl, ?_, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · simp only [Category.assoc]
    rw [h1, hj₂, curveChange_snd]
    exact heη'
  · intro y
    rw [Scheme.Hom.finrank_comp_left_of_isIso]
    have sq : IsPullback (𝟙 _)
        (curveChange πα hα (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) ≫ j.hom ≫ inv eη)
        (curveChange πα hα (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))) (eη ≫ j.inv) :=
      IsPullback.of_horiz_isIso ⟨by simp only [Category.id_comp, Category.assoc, IsIso.inv_hom_id_assoc,
        Iso.hom_inv_id, Category.comp_id]⟩
    rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ sq]
    exact HeckeS8.finrank_curveChange_eq πα hα d hdα _ _
  · intro y x hyx
    have key := hplaceα y x (by
      rw [← hyx]
      simp only [Category.assoc, IsIso.inv_hom_id_assoc]
      rw [hj₁, ← Category.assoc (curveChange _ _ _), HeckeS8.curveChange_fst, Category.assoc])
    exact key.symm

namespace HeckeS8

section G

theorem toMul_map_sum_nsmul {A M ι : Type*} [AddCommMonoid A] [CommMonoid M] (χ : A →+ Additive M)
    (s : Finset ι) (n : ι → ℕ) (a : ι → A) :
    Additive.toMul (χ (∑ i ∈ s, n i • a i)) = ∏ i ∈ s, Additive.toMul (χ (a i)) ^ n i := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty, map_zero]; rfl
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj, map_add, toMul_add, ih, map_nsmul, toMul_nsmul]

theorem specMap_rat (ℓ : ℕ) [Fact ℓ.Prime] :
    specMap ℚ ℚ̄ ≫ specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ = specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ̄ :=
  specMap_comp_specMap _ _ _

noncomputable def jIso (ℓ : ℕ) [Fact ℓ.Prime] {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) :
    pullback (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (specMap ℚ ℚ̄) ≅ pullback c (specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ̄) :=
  BaseChange.κ c ℚ (specMap ℚ ℚ̄) ≪≫ pullback.congrHom rfl (specMap_rat ℓ)

theorem jIso_hom_fst (ℓ : ℕ) [Fact ℓ.Prime] {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) :
    (jIso ℓ c).hom ≫ pullback.fst c (specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ̄) =
      pullback.fst (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (specMap ℚ ℚ̄) ≫ pullback.fst c (specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ) := by
  simp only [jIso, Iso.trans_hom, pullback.congrHom_hom, Category.assoc]
  erw [pullback.lift_fst]
  rw [Category.comp_id, BaseChange.κ_hom_fst]

theorem jIso_hom_snd (ℓ : ℕ) [Fact ℓ.Prime] {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) :
    (jIso ℓ c).hom ≫ pullback.snd c (specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ̄) = pullback.snd (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (specMap ℚ ℚ̄) := by
  simp only [jIso, Iso.trans_hom, pullback.congrHom_hom, Category.assoc]
  erw [pullback.lift_snd]
  rw [Category.comp_id, BaseChange.κ_hom_snd]

noncomputable def liftPts (ℓ : ℕ) [Fact ℓ.Prime] {X : Scheme.{0}} {c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))}
    (D : RelativePic0Designation ↥(GaloisRep.ratLocalizedAt ℓ) c) (a : SchemeHomOver (specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ̄) D.toBase) :
    SchemeHomOver (specMap ℚ ℚ̄) (D.baseChange ℚ).toBase :=
  liftPt D ℚ (specMap ℚ ℚ̄) (castBase (specMap_rat ℓ).symm a)

theorem liftPts_fst (ℓ : ℕ) [Fact ℓ.Prime] {X : Scheme.{0}} {c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))}
    (D : RelativePic0Designation ↥(GaloisRep.ratLocalizedAt ℓ) c) (a : SchemeHomOver (specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ̄) D.toBase) :
    (liftPts ℓ D a).1 ≫ pullback.fst D.toBase (specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ) = a.1 :=
  liftPt_fst D ℚ _ _

theorem eq_liftPts (ℓ : ℕ) [Fact ℓ.Prime] {X : Scheme.{0}} {c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))}
    (D : RelativePic0Designation ↥(GaloisRep.ratLocalizedAt ℓ) c) (z : SchemeHomOver (specMap ℚ ℚ̄) (D.baseChange ℚ).toBase)
    (a : SchemeHomOver (specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ̄) D.toBase)
    (hz : z.1 ≫ pullback.fst D.toBase (specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ) = a.1) : z = liftPts ℓ D a :=
  eq_liftPt D ℚ _ z (castBase (specMap_rat ℓ).symm a) hz

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem liftPts_add
    (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p)
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))) c)
    (D : RelativePic0Designation ↥(GaloisRep.ratLocalizedAt ℓ) c)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (hsm : Smooth D.toBase) (hpr : IsProper D.toBase) (hgc : GeometricallyConnected D.toBase)
    (aj : SchemeHomOver c D.toBase) (hajε : ε.1 ≫ aj.1 = D.zeroSection)
    (haj : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) (x : SchemeHomOver t c),
        Nonempty ((h.poincare.pullbackAlong
            ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint c (t ≫ ε.1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule))

    (Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar p))
    (eη : Mη.C ⟶ pullback c (Spec.map (CommRingCat.ofHom
      (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))))) [IsIso eη]
    (heη : eη ≫ pullback.snd c _ = Mη.toBase)
    (hgal : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst c _ =
        Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
          x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x' =
        arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull p) g • Mη.pointEquivPlace x)
    (q : Nat.Primes) [NeZero (q : ℕ)] [NeZero (p * (q : ℕ))]

    (hℚ : RepresentsRelSubPic (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)
      (algEquivZeroCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)) (D.baseChange ℚ))
    (hP : Nonempty (hℚ.poincare.L ≅ (BaseChange.ofR c ε ℚ
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ), pullback.condition⟩)).L))

    (Y : Scheme.{0}) (cY : Y ⟶ Spec (CommRingCat.of ℚ))
    (πα πβ : Y ⟶ pullback c (specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ))
    (hα : πα ≫ baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ = cY)
    (hβ : πβ ≫ baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ = cY)
    [IsFinite πα] [Flat πα] [LocallyOfFinitePresentation πα]
    [IsFinite πβ] [Flat πβ] [LocallyOfFinitePresentation πβ]
    (d : ℕ) (hdα : ∀ y, πα.finrank y = d)

    (Φ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℚ)),
      RigidifiedLineBundle (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε) t →
        RigidifiedLineBundle (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε) t)
    (hΦ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℚ))
        (M : RigidifiedLineBundle (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε) t),
      Nonempty ((Φ t M).L ≅ Scheme.Modules.rigidify
        (rigSection (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) t (sectionBaseChange ℚ ε))
        (pullback.snd (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) t)
        (Scheme.Modules.normModule (curveChange πα hα t) d
          ((Scheme.Modules.pullback (curveChange πβ hβ t)).obj M.L))))
    (hcut : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℚ))
        (M : RigidifiedLineBundle (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε) t),
      (algEquivZeroCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)).P t M →
        (algEquivZeroCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)).P t (Φ t M))
    (φη : SchemeHomOver (D.baseChange ℚ).toBase (D.baseChange ℚ).toBase)
    (hφη : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℚ))
        (M : RigidifiedLineBundle (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε) t)
        (hM : (algEquivZeroCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)).P t M),
      postComp φη (hℚ.classify t M hM) = hℚ.classify t (Φ t M) (hcut t M hM))
    (hφadd : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ℚ)) (x y : SchemeHomOver s (D.baseChange ℚ).toBase),
      NeronModelInfra.schemeHomOverComp
          ((RepresentsRelSubPic.relativeGroupLaw
            (P := algEquivZeroGroupCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)) hℚ).mul s x y) φη =
        (RepresentsRelSubPic.relativeGroupLaw
            (P := algEquivZeroGroupCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)) hℚ).mul s
          (NeronModelInfra.schemeHomOverComp x φη) (NeronModelInfra.schemeHomOverComp y φη))

    (Mη' : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar (p * (q : ℕ))))
    (eη' : Mη'.C ⟶ pullback cY (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))) [IsIso eη']
    (heη' : eη' ≫ pullback.snd _ _ = Mη'.toBase)
    (hαI : (heckeAlphaBar (AlgebraicClosure ℚ) p q).toRingHom.IsIntegral)
    (hβI : (heckeBetaBar (AlgebraicClosure ℚ) p q).toRingHom.IsIntegral)
    (hplaceα : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη'.C // q ≫ Mη'.toBase = 𝟙 _})
        (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      y.1 ≫ eη' ≫ pullback.fst cY _ ≫ πα ≫ pullback.fst c _ = x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x =
        Place.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) p q) hαI (Mη'.pointEquivPlace y))
    (hplaceβ : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη'.C // q ≫ Mη'.toBase = 𝟙 _})
        (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      y.1 ≫ eη' ≫ pullback.fst cY _ ≫ πβ ≫ pullback.fst c _ = x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x =
        Place.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) p q) hβI (Mη'.pointEquivPlace y))

    (pts : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom
      (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) D.toBase)
    (hadd : ∀ x y : JZero p,
      pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul _ (pts x) (pts y))
    (hnorm : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      s.1 ≫ eη ≫ pullback.fst c _ =
        Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))) ≫ ε.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar p),
        (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) =
          Finsupp.single (Mη.pointEquivPlace x) 1 - Finsupp.single (Mη.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ eη ≫ pullback.fst c _ ≫ aj.1)
    (x y : JZero p) :
    liftPts ℓ D (pts (x + y)) =
      (RepresentsRelSubPic.relativeGroupLaw
        (P := algEquivZeroGroupCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)) hℚ).mul (specMap ℚ ℚ̄)
        (liftPts ℓ D (pts x)) (liftPts ℓ D (pts y)) := by
  rw [hadd]
  unfold liftPts
  rw [← mul_castBase, ← liftPt_mul c ε D h ℚ hℚ hP]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem cls_poincare_liftPts_genClass
    (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p)
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))) c)
    (D : RelativePic0Designation ↥(GaloisRep.ratLocalizedAt ℓ) c)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (hsm : Smooth D.toBase) (hpr : IsProper D.toBase) (hgc : GeometricallyConnected D.toBase)
    (aj : SchemeHomOver c D.toBase) (hajε : ε.1 ≫ aj.1 = D.zeroSection)
    (haj : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) (x : SchemeHomOver t c),
        Nonempty ((h.poincare.pullbackAlong
            ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint c (t ≫ ε.1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule))

    (Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar p))
    (eη : Mη.C ⟶ pullback c (Spec.map (CommRingCat.ofHom
      (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))))) [IsIso eη]
    (heη : eη ≫ pullback.snd c _ = Mη.toBase)
    (hgal : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst c _ =
        Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
          x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x' =
        arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull p) g • Mη.pointEquivPlace x)
    (q : Nat.Primes) [NeZero (q : ℕ)] [NeZero (p * (q : ℕ))]

    (hℚ : RepresentsRelSubPic (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)
      (algEquivZeroCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)) (D.baseChange ℚ))
    (hP : Nonempty (hℚ.poincare.L ≅ (BaseChange.ofR c ε ℚ
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ), pullback.condition⟩)).L))

    (Y : Scheme.{0}) (cY : Y ⟶ Spec (CommRingCat.of ℚ))
    (πα πβ : Y ⟶ pullback c (specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ))
    (hα : πα ≫ baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ = cY)
    (hβ : πβ ≫ baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ = cY)
    [IsFinite πα] [Flat πα] [LocallyOfFinitePresentation πα]
    [IsFinite πβ] [Flat πβ] [LocallyOfFinitePresentation πβ]
    (d : ℕ) (hdα : ∀ y, πα.finrank y = d)

    (Φ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℚ)),
      RigidifiedLineBundle (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε) t →
        RigidifiedLineBundle (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε) t)
    (hΦ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℚ))
        (M : RigidifiedLineBundle (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε) t),
      Nonempty ((Φ t M).L ≅ Scheme.Modules.rigidify
        (rigSection (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) t (sectionBaseChange ℚ ε))
        (pullback.snd (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) t)
        (Scheme.Modules.normModule (curveChange πα hα t) d
          ((Scheme.Modules.pullback (curveChange πβ hβ t)).obj M.L))))
    (hcut : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℚ))
        (M : RigidifiedLineBundle (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε) t),
      (algEquivZeroCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)).P t M →
        (algEquivZeroCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)).P t (Φ t M))
    (φη : SchemeHomOver (D.baseChange ℚ).toBase (D.baseChange ℚ).toBase)
    (hφη : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℚ))
        (M : RigidifiedLineBundle (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε) t)
        (hM : (algEquivZeroCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)).P t M),
      postComp φη (hℚ.classify t M hM) = hℚ.classify t (Φ t M) (hcut t M hM))
    (hφadd : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ℚ)) (x y : SchemeHomOver s (D.baseChange ℚ).toBase),
      NeronModelInfra.schemeHomOverComp
          ((RepresentsRelSubPic.relativeGroupLaw
            (P := algEquivZeroGroupCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)) hℚ).mul s x y) φη =
        (RepresentsRelSubPic.relativeGroupLaw
            (P := algEquivZeroGroupCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)) hℚ).mul s
          (NeronModelInfra.schemeHomOverComp x φη) (NeronModelInfra.schemeHomOverComp y φη))

    (Mη' : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar (p * (q : ℕ))))
    (eη' : Mη'.C ⟶ pullback cY (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))) [IsIso eη']
    (heη' : eη' ≫ pullback.snd _ _ = Mη'.toBase)
    (hαI : (heckeAlphaBar (AlgebraicClosure ℚ) p q).toRingHom.IsIntegral)
    (hβI : (heckeBetaBar (AlgebraicClosure ℚ) p q).toRingHom.IsIntegral)
    (hplaceα : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη'.C // q ≫ Mη'.toBase = 𝟙 _})
        (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      y.1 ≫ eη' ≫ pullback.fst cY _ ≫ πα ≫ pullback.fst c _ = x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x =
        Place.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) p q) hαI (Mη'.pointEquivPlace y))
    (hplaceβ : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη'.C // q ≫ Mη'.toBase = 𝟙 _})
        (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      y.1 ≫ eη' ≫ pullback.fst cY _ ≫ πβ ≫ pullback.fst c _ = x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x =
        Place.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) p q) hβI (Mη'.pointEquivPlace y))

    (pts : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom
      (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) D.toBase)
    (hadd : ∀ x y : JZero p,
      pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul _ (pts x) (pts y))
    (hnorm : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      s.1 ≫ eη ≫ pullback.fst c _ =
        Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))) ≫ ε.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar p),
        (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) =
          Finsupp.single (Mη.pointEquivPlace x) 1 - Finsupp.single (Mη.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ eη ≫ pullback.fst c _ ≫ aj.1)
    (s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
    (hs : s.1 ≫ eη ≫ pullback.fst c _ = specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ̄ ≫ ε.1)
    (Q : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}) :
    cls ((Scheme.Modules.pullback (eη ≫ (jIso ℓ c).inv)).obj
        (hℚ.poincare.pullbackAlong (liftPts ℓ D (pts
          (genClass (deg_eq_one_modularFunctionFieldBar p) (Mη.pointEquivPlace s) (Mη.pointEquivPlace Q))))).L) =
      cls (Q.1.ker).invModule * cls (s.1.ker).module := by

  obtain ⟨Dv, hDv, hpts⟩ := hnorm Q s hs
  rw [← genClass_eq_mk (deg_eq_one_modularFunctionFieldBar p) _ _ Dv hDv]

  have hxQ : (Q.1 ≫ eη ≫ pullback.fst c _) ≫ c = (specMap ℚ ℚ̄) ≫ specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ := by
    simp only [Category.assoc]
    rw [pullback.condition, reassoc_of% heη, reassoc_of% Q.2, specMap_rat]
  let xQ : SchemeHomOver ((specMap ℚ ℚ̄) ≫ specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ) c := ⟨Q.1 ≫ eη ≫ pullback.fst c _, hxQ⟩
  let a : SchemeHomOver ((specMap ℚ ℚ̄) ≫ specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ) D.toBase :=
    ⟨xQ.1 ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg (xQ.1 ≫ ·) aj.2).trans xQ.2)⟩
  have ha : castBase (specMap_rat ℓ).symm (pts (Pic0.mk Dv)) = a := by
    apply Subtype.ext
    simp only [castBase_coe, hpts, Category.assoc, a, xQ]
  unfold liftPts
  rw [ha]
  obtain ⟨e1⟩ := poincare_liftPt_iso c ε D h ℚ hℚ hP (specMap ℚ ℚ̄) a
  obtain ⟨e2⟩ := haj ℚ̄ ((specMap ℚ ℚ̄) ≫ specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ) xQ

  let eM : Mη.C ⟶ pullback c ((specMap ℚ ℚ̄) ≫ specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ) :=
    eη ≫ (pullback.congrHom rfl (specMap_rat ℓ)).inv
  have hEM : (eη ≫ (jIso ℓ c).inv) ≫ (BaseChange.κ c ℚ (specMap ℚ ℚ̄)).hom = eM := by
    simp only [jIso, Iso.trans_inv, Category.assoc, Iso.inv_hom_id, Category.comp_id, eM]
  have hEM_fst : eM ≫ pullback.fst c _ = eη ≫ pullback.fst c _ := by
    simp only [eM, Category.assoc, pullback.congrHom_inv]
    erw [pullback.lift_fst]
    rw [Category.comp_id]
  have hEM_snd : eM ≫ pullback.snd c _ = Mη.toBase := by
    simp only [eM, Category.assoc, pullback.congrHom_inv]
    erw [pullback.lift_snd]
    rw [Category.comp_id, heη]

  have hpQ : Q.1 ≫ eM = graphOver c xQ.1 xQ.2 := by
    apply pullback.hom_ext
    · rw [Category.assoc, hEM_fst, graphOver_fst]
    · rw [Category.assoc, hEM_snd, graphOver_snd, Q.2]
  have hε : ((specMap ℚ ℚ̄) ≫ specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ) ≫ ε.1 ≫ c = (specMap ℚ ℚ̄) ≫ specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ :=
    (congrArg (((specMap ℚ ℚ̄) ≫ specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ) ≫ ·) ε.2).trans (Category.comp_id _)
  have hps : s.1 ≫ eM = graphOver c (((specMap ℚ ℚ̄) ≫ specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ) ≫ ε.1)
      ((Category.assoc _ _ _).trans ((congrArg (((specMap ℚ ℚ̄) ≫ specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ) ≫ ·) ε.2).trans
        (Category.comp_id _))) := by
    apply pullback.hom_ext
    · rw [Category.assoc, hEM_fst, graphOver_fst, hs, specMap_rat]
    · rw [Category.assoc, hEM_snd, graphOver_snd, s.2]
  obtain ⟨iQ⟩ := (Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso eM (graphOver c xQ.1 xQ.2) Q.1 hpQ
    (RelEffCartierDiv.ofPoint c xQ.1 xQ.2).isInvertible_I (isInvertible_ker_point Mη Q) 1).1
  obtain ⟨is⟩ := (Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso eM _ s.1 hps
    (RelEffCartierDiv.ofPoint c _ _).isInvertible_I (isInvertible_ker_point Mη s) 1).2
  simp only [pow_one] at iQ is
  rw [cls_pullback_congr _ (cls_congr e1), cls_pullback_comp, cls_pullback_congr_hom hEM,
    cls_pullback_congr _ (cls_congr e2), cls_pullback_tensor]
  exact congrArg₂ (· * ·) (cls_congr iQ) (cls_congr is)

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem cls_poincare_liftPts_add
    (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p)
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))) c)
    (D : RelativePic0Designation ↥(GaloisRep.ratLocalizedAt ℓ) c)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (hsm : Smooth D.toBase) (hpr : IsProper D.toBase) (hgc : GeometricallyConnected D.toBase)
    (aj : SchemeHomOver c D.toBase) (hajε : ε.1 ≫ aj.1 = D.zeroSection)
    (haj : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) (x : SchemeHomOver t c),
        Nonempty ((h.poincare.pullbackAlong
            ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint c (t ≫ ε.1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule))

    (Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar p))
    (eη : Mη.C ⟶ pullback c (Spec.map (CommRingCat.ofHom
      (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))))) [IsIso eη]
    (heη : eη ≫ pullback.snd c _ = Mη.toBase)
    (hgal : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst c _ =
        Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
          x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x' =
        arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull p) g • Mη.pointEquivPlace x)
    (q : Nat.Primes) [NeZero (q : ℕ)] [NeZero (p * (q : ℕ))]

    (hℚ : RepresentsRelSubPic (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)
      (algEquivZeroCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)) (D.baseChange ℚ))
    (hP : Nonempty (hℚ.poincare.L ≅ (BaseChange.ofR c ε ℚ
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ), pullback.condition⟩)).L))

    (Y : Scheme.{0}) (cY : Y ⟶ Spec (CommRingCat.of ℚ))
    (πα πβ : Y ⟶ pullback c (specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ))
    (hα : πα ≫ baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ = cY)
    (hβ : πβ ≫ baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ = cY)
    [IsFinite πα] [Flat πα] [LocallyOfFinitePresentation πα]
    [IsFinite πβ] [Flat πβ] [LocallyOfFinitePresentation πβ]
    (d : ℕ) (hdα : ∀ y, πα.finrank y = d)

    (Φ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℚ)),
      RigidifiedLineBundle (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε) t →
        RigidifiedLineBundle (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε) t)
    (hΦ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℚ))
        (M : RigidifiedLineBundle (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε) t),
      Nonempty ((Φ t M).L ≅ Scheme.Modules.rigidify
        (rigSection (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) t (sectionBaseChange ℚ ε))
        (pullback.snd (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) t)
        (Scheme.Modules.normModule (curveChange πα hα t) d
          ((Scheme.Modules.pullback (curveChange πβ hβ t)).obj M.L))))
    (hcut : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℚ))
        (M : RigidifiedLineBundle (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε) t),
      (algEquivZeroCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)).P t M →
        (algEquivZeroCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)).P t (Φ t M))
    (φη : SchemeHomOver (D.baseChange ℚ).toBase (D.baseChange ℚ).toBase)
    (hφη : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℚ))
        (M : RigidifiedLineBundle (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε) t)
        (hM : (algEquivZeroCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)).P t M),
      postComp φη (hℚ.classify t M hM) = hℚ.classify t (Φ t M) (hcut t M hM))
    (hφadd : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ℚ)) (x y : SchemeHomOver s (D.baseChange ℚ).toBase),
      NeronModelInfra.schemeHomOverComp
          ((RepresentsRelSubPic.relativeGroupLaw
            (P := algEquivZeroGroupCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)) hℚ).mul s x y) φη =
        (RepresentsRelSubPic.relativeGroupLaw
            (P := algEquivZeroGroupCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)) hℚ).mul s
          (NeronModelInfra.schemeHomOverComp x φη) (NeronModelInfra.schemeHomOverComp y φη))

    (Mη' : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar (p * (q : ℕ))))
    (eη' : Mη'.C ⟶ pullback cY (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))) [IsIso eη']
    (heη' : eη' ≫ pullback.snd _ _ = Mη'.toBase)
    (hαI : (heckeAlphaBar (AlgebraicClosure ℚ) p q).toRingHom.IsIntegral)
    (hβI : (heckeBetaBar (AlgebraicClosure ℚ) p q).toRingHom.IsIntegral)
    (hplaceα : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη'.C // q ≫ Mη'.toBase = 𝟙 _})
        (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      y.1 ≫ eη' ≫ pullback.fst cY _ ≫ πα ≫ pullback.fst c _ = x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x =
        Place.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) p q) hαI (Mη'.pointEquivPlace y))
    (hplaceβ : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη'.C // q ≫ Mη'.toBase = 𝟙 _})
        (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      y.1 ≫ eη' ≫ pullback.fst cY _ ≫ πβ ≫ pullback.fst c _ = x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x =
        Place.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) p q) hβI (Mη'.pointEquivPlace y))

    (pts : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom
      (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) D.toBase)
    (hadd : ∀ x y : JZero p,
      pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul _ (pts x) (pts y))
    (hnorm : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      s.1 ≫ eη ≫ pullback.fst c _ =
        Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))) ≫ ε.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar p),
        (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) =
          Finsupp.single (Mη.pointEquivPlace x) 1 - Finsupp.single (Mη.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ eη ≫ pullback.fst c _ ≫ aj.1)
    (x y : JZero p) :
    cls ((Scheme.Modules.pullback (eη ≫ (jIso ℓ c).inv)).obj
        (hℚ.poincare.pullbackAlong (liftPts ℓ D (pts (x + y)))).L) =
      cls ((Scheme.Modules.pullback (eη ≫ (jIso ℓ c).inv)).obj
          (hℚ.poincare.pullbackAlong (liftPts ℓ D (pts x))).L) *
        cls ((Scheme.Modules.pullback (eη ≫ (jIso ℓ c).inv)).obj
          (hℚ.poincare.pullbackAlong (liftPts ℓ D (pts y))).L) := by
  rw [liftPts_add p ℓ hℓp c ε D h hsm hpr hgc aj hajε haj Mη eη heη hgal q hℚ hP Y cY πα πβ hα hβ d hdα Φ hΦ hcut
    φη hφη hφadd Mη' eη' heη' hαI hβI hplaceα hplaceβ pts hadd hnorm,
    cls_pullback_congr _ (cls_congr (poincare_mul_iso hℚ _ _ _).some), cls_pullback_tensor]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem cls_pullback_Phi
    (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p)
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))) c)
    (D : RelativePic0Designation ↥(GaloisRep.ratLocalizedAt ℓ) c)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (hsm : Smooth D.toBase) (hpr : IsProper D.toBase) (hgc : GeometricallyConnected D.toBase)
    (aj : SchemeHomOver c D.toBase) (hajε : ε.1 ≫ aj.1 = D.zeroSection)
    (haj : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) (x : SchemeHomOver t c),
        Nonempty ((h.poincare.pullbackAlong
            ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint c (t ≫ ε.1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule))

    (Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar p))
    (eη : Mη.C ⟶ pullback c (Spec.map (CommRingCat.ofHom
      (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))))) [IsIso eη]
    (heη : eη ≫ pullback.snd c _ = Mη.toBase)
    (hgal : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst c _ =
        Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
          x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x' =
        arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull p) g • Mη.pointEquivPlace x)
    (q : Nat.Primes) [NeZero (q : ℕ)] [NeZero (p * (q : ℕ))]

    (hℚ : RepresentsRelSubPic (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)
      (algEquivZeroCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)) (D.baseChange ℚ))
    (hP : Nonempty (hℚ.poincare.L ≅ (BaseChange.ofR c ε ℚ
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ), pullback.condition⟩)).L))

    (Y : Scheme.{0}) (cY : Y ⟶ Spec (CommRingCat.of ℚ))
    (πα πβ : Y ⟶ pullback c (specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ))
    (hα : πα ≫ baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ = cY)
    (hβ : πβ ≫ baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ = cY)
    [IsFinite πα] [Flat πα] [LocallyOfFinitePresentation πα]
    [IsFinite πβ] [Flat πβ] [LocallyOfFinitePresentation πβ]
    (d : ℕ) (hdα : ∀ y, πα.finrank y = d)

    (Φ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℚ)),
      RigidifiedLineBundle (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε) t →
        RigidifiedLineBundle (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε) t)
    (hΦ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℚ))
        (M : RigidifiedLineBundle (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε) t),
      Nonempty ((Φ t M).L ≅ Scheme.Modules.rigidify
        (rigSection (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) t (sectionBaseChange ℚ ε))
        (pullback.snd (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) t)
        (Scheme.Modules.normModule (curveChange πα hα t) d
          ((Scheme.Modules.pullback (curveChange πβ hβ t)).obj M.L))))
    (hcut : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℚ))
        (M : RigidifiedLineBundle (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε) t),
      (algEquivZeroCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)).P t M →
        (algEquivZeroCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)).P t (Φ t M))
    (φη : SchemeHomOver (D.baseChange ℚ).toBase (D.baseChange ℚ).toBase)
    (hφη : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℚ))
        (M : RigidifiedLineBundle (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε) t)
        (hM : (algEquivZeroCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)).P t M),
      postComp φη (hℚ.classify t M hM) = hℚ.classify t (Φ t M) (hcut t M hM))
    (hφadd : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ℚ)) (x y : SchemeHomOver s (D.baseChange ℚ).toBase),
      NeronModelInfra.schemeHomOverComp
          ((RepresentsRelSubPic.relativeGroupLaw
            (P := algEquivZeroGroupCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)) hℚ).mul s x y) φη =
        (RepresentsRelSubPic.relativeGroupLaw
            (P := algEquivZeroGroupCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)) hℚ).mul s
          (NeronModelInfra.schemeHomOverComp x φη) (NeronModelInfra.schemeHomOverComp y φη))

    (Mη' : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar (p * (q : ℕ))))
    (eη' : Mη'.C ⟶ pullback cY (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))) [IsIso eη']
    (heη' : eη' ≫ pullback.snd _ _ = Mη'.toBase)
    (hαI : (heckeAlphaBar (AlgebraicClosure ℚ) p q).toRingHom.IsIntegral)
    (hβI : (heckeBetaBar (AlgebraicClosure ℚ) p q).toRingHom.IsIntegral)
    (hplaceα : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη'.C // q ≫ Mη'.toBase = 𝟙 _})
        (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      y.1 ≫ eη' ≫ pullback.fst cY _ ≫ πα ≫ pullback.fst c _ = x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x =
        Place.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) p q) hαI (Mη'.pointEquivPlace y))
    (hplaceβ : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη'.C // q ≫ Mη'.toBase = 𝟙 _})
        (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      y.1 ≫ eη' ≫ pullback.fst cY _ ≫ πβ ≫ pullback.fst c _ = x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x =
        Place.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) p q) hβI (Mη'.pointEquivPlace y))

    (pts : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom
      (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) D.toBase)
    (hadd : ∀ x y : JZero p,
      pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul _ (pts x) (pts y))
    (hnorm : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      s.1 ≫ eη ≫ pullback.fst c _ =
        Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))) ≫ ε.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar p),
        (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) =
          Finsupp.single (Mη.pointEquivPlace x) 1 - Finsupp.single (Mη.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ eη ≫ pullback.fst c _ ≫ aj.1)
    (πa πb : Mη'.C ⟶ Mη.C)
    (hπa : πa = eη' ≫ curveChange πα hα (specMap ℚ ℚ̄) ≫ (jIso ℓ c).hom ≫ inv eη)
    (hπb : πb = eη' ≫ curveChange πβ hβ (specMap ℚ ℚ̄) ≫ (jIso ℓ c).hom ≫ inv eη)
    [IsFinite πa] [Flat πa] [LocallyOfFinitePresentation πa] (hda : ∀ y : Mη.C, πa.finrank y = d)
    (M : RigidifiedLineBundle (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε) (specMap ℚ ℚ̄)) :
    cls ((Scheme.Modules.pullback (eη ≫ (jIso ℓ c).inv)).obj (Φ (specMap ℚ ℚ̄) M).L) =
      cls (Scheme.Modules.normModule πa d ((Scheme.Modules.pullback πb).obj
        ((Scheme.Modules.pullback (eη ≫ (jIso ℓ c).inv)).obj M.L))) := by
  obtain ⟨eΦ⟩ := hΦ (specMap ℚ ℚ̄) M
  have hαe : πa ≫ (eη ≫ (jIso ℓ c).inv) = eη' ≫ curveChange πα hα (specMap ℚ ℚ̄) := by
    rw [hπa]; simp only [Category.assoc, IsIso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id]
  have hβe : πb ≫ (eη ≫ (jIso ℓ c).inv) = eη' ≫ curveChange πβ hβ (specMap ℚ ℚ̄) := by
    rw [hπb]; simp only [Category.assoc, IsIso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id]
  have key := cls_pullback_norm_pullback_of_isos (eη ≫ (jIso ℓ c).inv) eη' (curveChange πα hα (specMap ℚ ℚ̄)) (curveChange πβ hβ (specMap ℚ ℚ̄)) πa πb
    hαe hβe d hda M.isInvertible
  have hR : Scheme.Modules.IsInvertible (Scheme.Modules.normModule πa d
      ((Scheme.Modules.pullback πb).obj ((Scheme.Modules.pullback (eη ≫ (jIso ℓ c).inv)).obj M.L))) :=
    ((M.isInvertible.pullback _).pullback _).normModule πa d hda
  have hN : Scheme.Modules.IsInvertible (Scheme.Modules.normModule (curveChange πα hα (specMap ℚ ℚ̄)) d
      ((Scheme.Modules.pullback (curveChange πβ hβ (specMap ℚ ℚ̄))).obj M.L)) :=
    isInvertible_of_isInvertible_pullback (eη ≫ (jIso ℓ c).inv) (isInvertible_of_cls_eq hR key.symm)
  rw [cls_pullback_congr (eη ≫ (jIso ℓ c).inv) (cls_congr eΦ), cls_pullback_congr (eη ≫ (jIso ℓ c).inv) (cls_rigidify_of_field _ _ hN), key]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem liftPts_hecke_genClass
    (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p)
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))) c)
    (D : RelativePic0Designation ↥(GaloisRep.ratLocalizedAt ℓ) c)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (hsm : Smooth D.toBase) (hpr : IsProper D.toBase) (hgc : GeometricallyConnected D.toBase)
    (aj : SchemeHomOver c D.toBase) (hajε : ε.1 ≫ aj.1 = D.zeroSection)
    (haj : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) (x : SchemeHomOver t c),
        Nonempty ((h.poincare.pullbackAlong
            ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint c (t ≫ ε.1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule))

    (Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar p))
    (eη : Mη.C ⟶ pullback c (Spec.map (CommRingCat.ofHom
      (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))))) [IsIso eη]
    (heη : eη ≫ pullback.snd c _ = Mη.toBase)
    (hgal : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst c _ =
        Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
          x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x' =
        arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull p) g • Mη.pointEquivPlace x)
    (q : Nat.Primes) [NeZero (q : ℕ)] [NeZero (p * (q : ℕ))]

    (hℚ : RepresentsRelSubPic (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)
      (algEquivZeroCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)) (D.baseChange ℚ))
    (hP : Nonempty (hℚ.poincare.L ≅ (BaseChange.ofR c ε ℚ
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ), pullback.condition⟩)).L))

    (Y : Scheme.{0}) (cY : Y ⟶ Spec (CommRingCat.of ℚ))
    (πα πβ : Y ⟶ pullback c (specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ))
    (hα : πα ≫ baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ = cY)
    (hβ : πβ ≫ baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ = cY)
    [IsFinite πα] [Flat πα] [LocallyOfFinitePresentation πα]
    [IsFinite πβ] [Flat πβ] [LocallyOfFinitePresentation πβ]
    (d : ℕ) (hdα : ∀ y, πα.finrank y = d)

    (Φ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℚ)),
      RigidifiedLineBundle (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε) t →
        RigidifiedLineBundle (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε) t)
    (hΦ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℚ))
        (M : RigidifiedLineBundle (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε) t),
      Nonempty ((Φ t M).L ≅ Scheme.Modules.rigidify
        (rigSection (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) t (sectionBaseChange ℚ ε))
        (pullback.snd (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) t)
        (Scheme.Modules.normModule (curveChange πα hα t) d
          ((Scheme.Modules.pullback (curveChange πβ hβ t)).obj M.L))))
    (hcut : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℚ))
        (M : RigidifiedLineBundle (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε) t),
      (algEquivZeroCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)).P t M →
        (algEquivZeroCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)).P t (Φ t M))
    (φη : SchemeHomOver (D.baseChange ℚ).toBase (D.baseChange ℚ).toBase)
    (hφη : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℚ))
        (M : RigidifiedLineBundle (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε) t)
        (hM : (algEquivZeroCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)).P t M),
      postComp φη (hℚ.classify t M hM) = hℚ.classify t (Φ t M) (hcut t M hM))
    (hφadd : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ℚ)) (x y : SchemeHomOver s (D.baseChange ℚ).toBase),
      NeronModelInfra.schemeHomOverComp
          ((RepresentsRelSubPic.relativeGroupLaw
            (P := algEquivZeroGroupCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)) hℚ).mul s x y) φη =
        (RepresentsRelSubPic.relativeGroupLaw
            (P := algEquivZeroGroupCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)) hℚ).mul s
          (NeronModelInfra.schemeHomOverComp x φη) (NeronModelInfra.schemeHomOverComp y φη))

    (Mη' : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar (p * (q : ℕ))))
    (eη' : Mη'.C ⟶ pullback cY (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))) [IsIso eη']
    (heη' : eη' ≫ pullback.snd _ _ = Mη'.toBase)
    (hαI : (heckeAlphaBar (AlgebraicClosure ℚ) p q).toRingHom.IsIntegral)
    (hβI : (heckeBetaBar (AlgebraicClosure ℚ) p q).toRingHom.IsIntegral)
    (hplaceα : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη'.C // q ≫ Mη'.toBase = 𝟙 _})
        (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      y.1 ≫ eη' ≫ pullback.fst cY _ ≫ πα ≫ pullback.fst c _ = x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x =
        Place.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) p q) hαI (Mη'.pointEquivPlace y))
    (hplaceβ : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη'.C // q ≫ Mη'.toBase = 𝟙 _})
        (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      y.1 ≫ eη' ≫ pullback.fst cY _ ≫ πβ ≫ pullback.fst c _ = x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x =
        Place.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) p q) hβI (Mη'.pointEquivPlace y))

    (pts : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom
      (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) D.toBase)
    (hadd : ∀ x y : JZero p,
      pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul _ (pts x) (pts y))
    (hnorm : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      s.1 ≫ eη ≫ pullback.fst c _ =
        Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))) ≫ ε.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar p),
        (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) =
          Finsupp.single (Mη.pointEquivPlace x) 1 - Finsupp.single (Mη.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ eη ≫ pullback.fst c _ ≫ aj.1)
    (s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
    (hs : s.1 ≫ eη ≫ pullback.fst c _ = specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ̄ ≫ ε.1)
    (P : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}) :
    liftPts ℓ D (pts (heckeOperatorBar p q
        (genClass (deg_eq_one_modularFunctionFieldBar p) (Mη.pointEquivPlace s) (Mη.pointEquivPlace P)))) =
      NeronModelInfra.schemeHomOverComp
        (liftPts ℓ D (pts (genClass (deg_eq_one_modularFunctionFieldBar p) (Mη.pointEquivPlace s) (Mη.pointEquivPlace P))))
        φη := by
  classical
  haveI : Fact (q : ℕ).Prime := ⟨q.2⟩

  obtain ⟨hαI', hβI', hPD, hfin, hFI, hN⟩ := heckeInputsAlong_of_prime ℚ̄ p (q : ℕ)
  haveI := hPD
  have eα : hαI' = hαI := rfl
  have eβ : hβI' = hβI := rfl
  subst hαI'; subst hβI'
  have hdeg := deg_eq_one_modularFunctionFieldBar p
  have hdeg' := deg_eq_one_modularFunctionFieldBar (p * (q : ℕ))
  haveI := isCurveOver_modularFunctionFieldBar p
  haveI := isCurveOver_modularFunctionFieldBar (p * (q : ℕ))
  haveI := essFiniteType_modularFunctionFieldBar p
  haveI := essFiniteType_modularFunctionFieldBar (p * (q : ℕ))

  obtain ⟨πb, hπb_def, hπb, iFb, iFlb, iLb, hplb⟩ := ModularCurve.S8.degeneracyBar_beta_package p ℓ c Mη eη heη q
    Y cY πβ hβ Mη' eη' heη' hβI hplaceβ (jIso ℓ c) (jIso_hom_fst ℓ c) (jIso_hom_snd ℓ c)
  obtain ⟨πa, hπa_def, hπa, iFa, iFla, iLa, hda, hpla⟩ := ModularCurve.S8.degeneracyBar_alpha_package p ℓ c Mη eη heη q
    Y cY πα hα d hdα Mη' eη' heη' hαI hplaceα (jIso ℓ c) (jIso_hom_fst ℓ c) (jIso_hom_snd ℓ c)
  haveI := iFb; haveI := iFlb; haveI := iLb; haveI := iFa; haveI := iFla; haveI := iLa

  set α := heckeAlphaBar ℚ̄ p q with hαdef
  set β := heckeBetaBar ℚ̄ p q with hβdef
  set v₀ := Mη.pointEquivPlace s with hv₀
  set vP := Mη.pointEquivPlace P with hvP
  set g : Place ℚ̄ (modularFunctionFieldBar p) → JZero p := genClass hdeg v₀ with hg

  have hya : ∀ y : {q : Spec (CommRingCat.of ℚ̄) ⟶ Mη'.C // q ≫ Mη'.toBase = 𝟙 _}, (y.1 ≫ πa) ≫ Mη.toBase = 𝟙 _ :=
    fun y => by rw [Category.assoc, hπa, y.2]
  have hQa : ∀ y : {q : Spec (CommRingCat.of ℚ̄) ⟶ Mη'.C // q ≫ Mη'.toBase = 𝟙 _},
      Mη.pointEquivPlace ⟨y.1 ≫ πa, hya y⟩ = (Mη'.pointEquivPlace y).restrictAlong α hαI := by
    intro y
    letI := AlgebraicCurve.algebraAlong (heckeAlphaBar ℚ̄ p q)
    haveI := AlgebraicCurve.isScalarTower_along (heckeAlphaBar ℚ̄ p q)
    haveI := AlgebraicCurve.isIntegral_along (heckeAlphaBar ℚ̄ p q) hαI
    exact (hpla y ⟨y.1 ≫ πa, hya y⟩ rfl).symm

  set χf : JZero p → Skeleton (Mη.C).Modules := fun x =>
    cls ((Scheme.Modules.pullback (eη ≫ (jIso ℓ c).inv)).obj (hℚ.poincare.pullbackAlong (liftPts ℓ D (pts x))).L) with hχf
  have χmul : ∀ x y, χf (x + y) = χf x * χf y := fun x y =>
    cls_poincare_liftPts_add p ℓ hℓp c ε D h hsm hpr hgc aj hajε haj Mη eη heη hgal q hℚ hP Y cY πα πβ hα hβ d hdα Φ hΦ hcut φη hφη hφadd Mη' eη' heη' hαI hβI hplaceα hplaceβ pts hadd hnorm x y
  have χunit : ∀ x, IsUnit (χf x) := fun x =>
    isUnit_cls (((hℚ.poincare.pullbackAlong (liftPts ℓ D (pts x))).isInvertible).pullback (eη ≫ (jIso ℓ c).inv))
  have χzero : χf 0 = 1 := by
    have h1 := χmul 0 0
    rw [add_zero] at h1
    exact (χunit 0).mul_left_cancel (h1.symm.trans (mul_one _).symm)
  let χ : JZero p →+ Additive (Skeleton (Mη.C).Modules) :=
    { toFun := fun x => Additive.ofMul (χf x)
      map_zero' := by simp only [χzero, ofMul_one]
      map_add' := fun x y => by simp only [χmul, ofMul_mul] }
  have hχ : ∀ x, χ x = Additive.ofMul (χf x) := fun _ => rfl

  have hχg : ∀ w : Place ℚ̄ (modularFunctionFieldBar (p * (q : ℕ))),
      χf (g (w.restrictAlong α hαI)) = cls ((((Mη'.pointEquivPlace.symm w).1 ≫ πa).ker).invModule) * cls (s.1.ker).module := by
    intro w
    have h1 := cls_poincare_liftPts_genClass p ℓ hℓp c ε D h hsm hpr hgc aj hajε haj Mη eη heη hgal q hℚ hP Y cY πα πβ hα hβ d hdα Φ hΦ hcut φη hφη hφadd Mη' eη' heη' hαI hβI hplaceα hplaceβ pts hadd hnorm s hs ⟨(Mη'.pointEquivPlace.symm w).1 ≫ πa, hya _⟩
    rw [hQa, Equiv.apply_symm_apply] at h1
    exact h1

  have hT : heckeOperatorBar p q (g vP) +
        ∑ w ∈ Place.fiberAlong β hβI v₀, w.ramificationIndexAlong β • g (w.restrictAlong α hαI) =
      ∑ w ∈ Place.fiberAlong β hβI vP, w.ramificationIndexAlong β • g (w.restrictAlong α hαI) := by
    rw [heckeOperatorBar_apply, heckeOperatorAlong_eq hαI hβI hFI hfin hN]
    exact correspondence_genClass_add_sum_eq_sum β α hβI hαI hFI hfin hN hdeg hdeg'
      (fun w => inertiaDegAlong_eq_one_laurentBaseChange α hαI w) v₀ vP
  have hχT : χf (heckeOperatorBar p q (g vP)) *
        ∏ w ∈ Place.fiberAlong β hβI v₀, (cls ((((Mη'.pointEquivPlace.symm w).1 ≫ πa).ker).invModule) * cls (s.1.ker).module) ^ (w.ramificationIndexAlong β) =
      ∏ w ∈ Place.fiberAlong β hβI vP, (cls ((((Mη'.pointEquivPlace.symm w).1 ≫ πa).ker).invModule) * cls (s.1.ker).module) ^ (w.ramificationIndexAlong β) := by
    have h0 := congrArg (fun x => Additive.toMul (χ x)) hT
    rw [map_add, toMul_add, toMul_map_sum_nsmul, toMul_map_sum_nsmul] at h0
    have h2 : ∀ v : Place ℚ̄ (modularFunctionFieldBar p),
        ∏ w ∈ Place.fiberAlong β hβI v, Additive.toMul (χ (g (w.restrictAlong α hαI))) ^ (w.ramificationIndexAlong β) =
          ∏ w ∈ Place.fiberAlong β hβI v, (cls ((((Mη'.pointEquivPlace.symm w).1 ≫ πa).ker).invModule) * cls (s.1.ker).module) ^ (w.ramificationIndexAlong β) :=
      fun v => Finset.prod_congr rfl (fun w _ => by rw [← hχg w]; rfl)
    rw [h2, h2] at h0
    exact h0

  have normQ : ∀ Q : {q : Spec (CommRingCat.of ℚ̄) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _},
      cls (Scheme.Modules.normModule πa d ((Scheme.Modules.pullback πb).obj (Q.1.ker).invModule)) =
        ∏ w ∈ Place.fiberAlong β hβI (Mη.pointEquivPlace Q), cls ((((Mη'.pointEquivPlace.symm w).1 ≫ πa).ker).invModule) ^ (w.ramificationIndexAlong β) := by
    intro Q
    letI := AlgebraicCurve.algebraAlong (heckeBetaBar ℚ̄ p q)
    haveI := AlgebraicCurve.isScalarTower_along (heckeBetaBar ℚ̄ p q)
    haveI := AlgebraicCurve.isIntegral_along (heckeBetaBar ℚ̄ p q) hβI
    exact cls_norm_pullback_invModule_ker Mη Mη' πa πb hπa hπb d hda hplb Q
  have hsum : ∀ v : Place ℚ̄ (modularFunctionFieldBar p),
      ∑ w ∈ Place.fiberAlong β hβI v, w.ramificationIndexAlong β = finrankAlong ℚ̄ β := by
    intro v
    have h1 := sum_ramificationIndexAlong_eq_finrankAlong β hβI hFI hdeg hdeg' v
    exact_mod_cast h1

  have hMzcls : cls ((Scheme.Modules.pullback (eη ≫ (jIso ℓ c).inv)).obj (hℚ.poincare.pullbackAlong (liftPts ℓ D (pts (g vP)))).L) = cls (P.1.ker).invModule * cls (s.1.ker).module :=
    cls_poincare_liftPts_genClass p ℓ hℓp c ε D h hsm hpr hgc aj hajε haj Mη eη heη hgal q hℚ hP Y cY πα πβ hα hβ d hdα Φ hΦ hcut φη hφη hφadd Mη' eη' heη' hαI hβI hplaceα hplaceβ pts hadd hnorm s hs P
  have hΦcls : cls ((Scheme.Modules.pullback (eη ≫ (jIso ℓ c).inv)).obj (Φ (specMap ℚ ℚ̄) (hℚ.poincare.pullbackAlong (liftPts ℓ D (pts (g vP))))).L) =
      cls (Scheme.Modules.normModule πa d ((Scheme.Modules.pullback πb).obj
        ((Scheme.Modules.pullback (eη ≫ (jIso ℓ c).inv)).obj (hℚ.poincare.pullbackAlong (liftPts ℓ D (pts (g vP)))).L))) :=
    cls_pullback_Phi p ℓ hℓp c ε D h hsm hpr hgc aj hajε haj Mη eη heη hgal q hℚ hP Y cY πα πβ hα hβ d hdα Φ hΦ hcut φη hφη hφadd Mη' eη' heη' hαI hβI hplaceα hplaceβ pts hadd hnorm πa πb hπa_def hπb_def hda (hℚ.poincare.pullbackAlong (liftPts ℓ D (pts (g vP))))

  have hOP : Scheme.Modules.IsInvertible (P.1.ker).invModule := (isInvertible_ker_point Mη P).isInvertible_invModule
  have hOs : Scheme.Modules.IsInvertible (s.1.ker).invModule := (isInvertible_ker_point Mη s).isInvertible_invModule
  have hIs : Scheme.Modules.IsInvertible (s.1.ker).module := (isInvertible_ker_point Mη s).isInvertible_module

  have hR1 : cls (Scheme.Modules.normModule πa d ((Scheme.Modules.pullback πb).obj
        ((Scheme.Modules.pullback (eη ≫ (jIso ℓ c).inv)).obj (hℚ.poincare.pullbackAlong (liftPts ℓ D (pts (g vP)))).L))) = cls (Scheme.Modules.normModule πa d ((Scheme.Modules.pullback πb).obj (P.1.ker).invModule)) * cls (Scheme.Modules.normModule πa d ((Scheme.Modules.pullback πb).obj (s.1.ker).module)) := by
    rw [cls_normModule_congr πa d (((cls_pullback_congr πb (hMzcls.trans (cls_tensor _ _).symm)).trans
      (cls_pullback_tensor πb _ _)).trans (cls_tensor _ _).symm),
      cls_normModule_tensor πa d hda (hOP.pullback πb) (hIs.pullback πb)]

  have hR2 : cls (Scheme.Modules.normModule πa d ((Scheme.Modules.pullback πb).obj (s.1.ker).module)) * cls (Scheme.Modules.normModule πa d ((Scheme.Modules.pullback πb).obj (s.1.ker).invModule)) = 1 := by
    have e1 : cls ((Scheme.Modules.pullback πb).obj (s.1.ker).module ⊗ (Scheme.Modules.pullback πb).obj (s.1.ker).invModule) =
        cls ((Scheme.Modules.pullback πb).obj (𝟙_ _)) := by
      rw [cls_tensor, ← cls_pullback_tensor]
      apply cls_pullback_congr
      rw [cls_tensor, cls_unit]
      exact cls_mul_cls_dual hIs
    calc cls (Scheme.Modules.normModule πa d ((Scheme.Modules.pullback πb).obj (s.1.ker).module)) *
          cls (Scheme.Modules.normModule πa d ((Scheme.Modules.pullback πb).obj (s.1.ker).invModule))
        = cls (Scheme.Modules.normModule πa d ((Scheme.Modules.pullback πb).obj (s.1.ker).module ⊗
            (Scheme.Modules.pullback πb).obj (s.1.ker).invModule)) :=
          (cls_normModule_tensor πa d hda (hIs.pullback πb) (hOs.pullback πb)).symm
      _ = cls (Scheme.Modules.normModule πa d ((Scheme.Modules.pullback πb).obj (𝟙_ _))) := cls_normModule_congr πa d e1
      _ = cls (Scheme.Modules.normModule πa d (𝟙_ _)) :=
          cls_normModule_congr πa d ((cls_pullback_unit πb).trans (cls_unit _).symm)
      _ = 1 := cls_normModule_unit πa d hda

  have hprodP : ∏ w ∈ Place.fiberAlong β hβI vP, (cls ((((Mη'.pointEquivPlace.symm w).1 ≫ πa).ker).invModule) * cls (s.1.ker).module) ^ (w.ramificationIndexAlong β) =
      cls (Scheme.Modules.normModule πa d ((Scheme.Modules.pullback πb).obj (P.1.ker).invModule)) * cls (s.1.ker).module ^ finrankAlong ℚ̄ β := by
    rw [normQ P, ← hsum vP]
    simp only [mul_pow]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hprods : ∏ w ∈ Place.fiberAlong β hβI v₀, (cls ((((Mη'.pointEquivPlace.symm w).1 ≫ πa).ker).invModule) * cls (s.1.ker).module) ^ (w.ramificationIndexAlong β) =
      cls (Scheme.Modules.normModule πa d ((Scheme.Modules.pullback πb).obj (s.1.ker).invModule)) * cls (s.1.ker).module ^ finrankAlong ℚ̄ β := by
    rw [normQ s, ← hsum v₀]
    simp only [mul_pow]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hunit : IsUnit (cls (Scheme.Modules.normModule πa d ((Scheme.Modules.pullback πb).obj (s.1.ker).invModule)) * cls (s.1.ker).module ^ finrankAlong ℚ̄ β) :=
    (isUnit_cls_normModule πa d hda (hOs.pullback πb)).mul ((isUnit_cls hIs).pow _)
  have key : χf (heckeOperatorBar p q (g vP)) = cls ((Scheme.Modules.pullback (eη ≫ (jIso ℓ c).inv)).obj (Φ (specMap ℚ ℚ̄) (hℚ.poincare.pullbackAlong (liftPts ℓ D (pts (g vP))))).L) := by
    apply hunit.mul_left_injective
    change χf (heckeOperatorBar p q (g vP)) * (cls (Scheme.Modules.normModule πa d ((Scheme.Modules.pullback πb).obj (s.1.ker).invModule)) * cls (s.1.ker).module ^ finrankAlong ℚ̄ β) =
      cls ((Scheme.Modules.pullback (eη ≫ (jIso ℓ c).inv)).obj (Φ (specMap ℚ ℚ̄) (hℚ.poincare.pullbackAlong (liftPts ℓ D (pts (g vP))))).L) * (cls (Scheme.Modules.normModule πa d ((Scheme.Modules.pullback πb).obj (s.1.ker).invModule)) * cls (s.1.ker).module ^ finrankAlong ℚ̄ β)
    rw [← hprods, hχT, hprodP, hprods, hΦcls, hR1]
    calc cls (Scheme.Modules.normModule πa d ((Scheme.Modules.pullback πb).obj (P.1.ker).invModule)) * cls (s.1.ker).module ^ finrankAlong ℚ̄ β
        = cls (Scheme.Modules.normModule πa d ((Scheme.Modules.pullback πb).obj (P.1.ker).invModule)) * (cls (Scheme.Modules.normModule πa d ((Scheme.Modules.pullback πb).obj (s.1.ker).module)) * cls (Scheme.Modules.normModule πa d ((Scheme.Modules.pullback πb).obj (s.1.ker).invModule))) * cls (s.1.ker).module ^ finrankAlong ℚ̄ β := by rw [hR2, mul_one]
      _ = cls (Scheme.Modules.normModule πa d ((Scheme.Modules.pullback πb).obj (P.1.ker).invModule)) * cls (Scheme.Modules.normModule πa d ((Scheme.Modules.pullback πb).obj (s.1.ker).module)) * (cls (Scheme.Modules.normModule πa d ((Scheme.Modules.pullback πb).obj (s.1.ker).invModule)) * cls (s.1.ker).module ^ finrankAlong ℚ̄ β) := by simp only [mul_assoc]

  apply hℚ.ext_of_iso (specMap ℚ ℚ̄)
  obtain ⟨eφ⟩ := poincare_postComp_iso hℚ Φ hcut φη hφη (specMap ℚ ℚ̄) (liftPts ℓ D (pts (g vP)))
  change Nonempty (_ ≅ (hℚ.poincare.pullbackAlong (postComp φη (liftPts ℓ D (pts (g vP))))).L)
  refine (cls_eq_iff _ _).1 (cls_eq_of_cls_pullback_eq (eη ≫ (jIso ℓ c).inv) ?_)
  rw [cls_pullback_congr (eη ≫ (jIso ℓ c).inv) (cls_congr eφ)]
  exact key
end G
p2m_reactivate "P2MW.S_ModularCurve_heckeOperatorBar_points_eq_comp_of_transform.HeckeS8"

end HeckeS8
p2m_reactivate "P2MW.S_ModularCurve_heckeOperatorBar_points_eq_comp_of_transform.HeckeS8"

open HeckeS8 in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p)
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))) c)
    (D : RelativePic0Designation ↥(GaloisRep.ratLocalizedAt ℓ) c)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (hsm : Smooth D.toBase) (hpr : IsProper D.toBase) (hgc : GeometricallyConnected D.toBase)
    (aj : SchemeHomOver c D.toBase) (hajε : ε.1 ≫ aj.1 = D.zeroSection)
    (haj : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) (x : SchemeHomOver t c),
        Nonempty ((h.poincare.pullbackAlong
            ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint c (t ≫ ε.1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule))

    (Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar p))
    (eη : Mη.C ⟶ pullback c (Spec.map (CommRingCat.ofHom
      (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))))) [IsIso eη]
    (heη : eη ≫ pullback.snd c _ = Mη.toBase)
    (hgal : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst c _ =
        Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
          x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x' =
        arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull p) g • Mη.pointEquivPlace x)
    (q : Nat.Primes) [NeZero (q : ℕ)] [NeZero (p * (q : ℕ))]

    (hℚ : RepresentsRelSubPic (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)
      (algEquivZeroCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)) (D.baseChange ℚ))
    (hP : Nonempty (hℚ.poincare.L ≅ (BaseChange.ofR c ε ℚ
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ), pullback.condition⟩)).L))

    (Y : Scheme.{0}) (cY : Y ⟶ Spec (CommRingCat.of ℚ))
    (πα πβ : Y ⟶ pullback c (specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ))
    (hα : πα ≫ baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ = cY)
    (hβ : πβ ≫ baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ = cY)
    [IsFinite πα] [Flat πα] [LocallyOfFinitePresentation πα]
    [IsFinite πβ] [Flat πβ] [LocallyOfFinitePresentation πβ]
    (d : ℕ) (hdα : ∀ y, πα.finrank y = d)

    (Φ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℚ)),
      RigidifiedLineBundle (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε) t →
        RigidifiedLineBundle (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε) t)
    (hΦ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℚ))
        (M : RigidifiedLineBundle (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε) t),
      Nonempty ((Φ t M).L ≅ Scheme.Modules.rigidify
        (rigSection (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) t (sectionBaseChange ℚ ε))
        (pullback.snd (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) t)
        (Scheme.Modules.normModule (curveChange πα hα t) d
          ((Scheme.Modules.pullback (curveChange πβ hβ t)).obj M.L))))
    (hcut : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℚ))
        (M : RigidifiedLineBundle (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε) t),
      (algEquivZeroCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)).P t M →
        (algEquivZeroCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)).P t (Φ t M))
    (φη : SchemeHomOver (D.baseChange ℚ).toBase (D.baseChange ℚ).toBase)
    (hφη : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℚ))
        (M : RigidifiedLineBundle (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε) t)
        (hM : (algEquivZeroCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)).P t M),
      postComp φη (hℚ.classify t M hM) = hℚ.classify t (Φ t M) (hcut t M hM))
    (hφadd : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ℚ)) (x y : SchemeHomOver s (D.baseChange ℚ).toBase),
      NeronModelInfra.schemeHomOverComp
          ((RepresentsRelSubPic.relativeGroupLaw
            (P := algEquivZeroGroupCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)) hℚ).mul s x y) φη =
        (RepresentsRelSubPic.relativeGroupLaw
            (P := algEquivZeroGroupCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)) hℚ).mul s
          (NeronModelInfra.schemeHomOverComp x φη) (NeronModelInfra.schemeHomOverComp y φη))

    (Mη' : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar (p * (q : ℕ))))
    (eη' : Mη'.C ⟶ pullback cY (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))) [IsIso eη']
    (heη' : eη' ≫ pullback.snd _ _ = Mη'.toBase)
    (hαI : (heckeAlphaBar (AlgebraicClosure ℚ) p q).toRingHom.IsIntegral)
    (hβI : (heckeBetaBar (AlgebraicClosure ℚ) p q).toRingHom.IsIntegral)
    (hplaceα : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη'.C // q ≫ Mη'.toBase = 𝟙 _})
        (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      y.1 ≫ eη' ≫ pullback.fst cY _ ≫ πα ≫ pullback.fst c _ = x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x =
        Place.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) p q) hαI (Mη'.pointEquivPlace y))
    (hplaceβ : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη'.C // q ≫ Mη'.toBase = 𝟙 _})
        (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      y.1 ≫ eη' ≫ pullback.fst cY _ ≫ πβ ≫ pullback.fst c _ = x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x =
        Place.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) p q) hβI (Mη'.pointEquivPlace y))

    (pts : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom
      (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) D.toBase)
    (hadd : ∀ x y : JZero p,
      pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul _ (pts x) (pts y))
    (hnorm : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      s.1 ≫ eη ≫ pullback.fst c _ =
        Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))) ≫ ε.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar p),
        (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) =
          Finsupp.single (Mη.pointEquivPlace x) 1 - Finsupp.single (Mη.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ eη ≫ pullback.fst c _ ≫ aj.1)

    (x : JZero p)
    (z zq : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) (D.baseChange ℚ).toBase)
    (hz : z.1 ≫ pullback.fst D.toBase (specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ) = (pts x).1)
    (hzq : zq.1 ≫ pullback.fst D.toBase (specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ) = (pts (heckeOperatorBar p q x)).1) :
    zq.1 = z.1 ≫ φη.1 := by
  classical
  haveI := isCurveOver_modularFunctionFieldBar p
  haveI := essFiniteType_modularFunctionFieldBar p

  have hε : (specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ̄ ≫ ε.1) ≫ c = specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ̄ := by
    rw [Category.assoc, ε.2, Category.comp_id]
  let s : {q : Spec (CommRingCat.of ℚ̄) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _} :=
    ⟨graphOver c _ hε ≫ inv eη, by rw [Category.assoc, ← heη, IsIso.inv_hom_id_assoc, graphOver_snd]⟩
  have hs : s.1 ≫ eη ≫ pullback.fst c _ = specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ̄ ≫ ε.1 := by
    simp only [s, Category.assoc, IsIso.inv_hom_id_assoc, graphOver_fst]

  letI grp : Group (SchemeHomOver (specMap ℚ ℚ̄) (D.baseChange ℚ).toBase) :=
    (RepresentsRelSubPic.relativeGroupLaw
      (P := algEquivZeroGroupCut (baseChange ↥(GaloisRep.ratLocalizedAt ℓ) c ℚ) (sectionBaseChange ℚ ε)) hℚ).pointGroup (specMap ℚ ℚ̄)

  let F₁ : JZero p → Additive (SchemeHomOver (specMap ℚ ℚ̄) (D.baseChange ℚ).toBase) :=
    fun y => Additive.ofMul (liftPts ℓ D (pts (heckeOperatorBar p q y)))
  let F₂ : JZero p → Additive (SchemeHomOver (specMap ℚ ℚ̄) (D.baseChange ℚ).toBase) :=
    fun y => Additive.ofMul (NeronModelInfra.schemeHomOverComp (liftPts ℓ D (pts y)) φη)
  have hF₁ : ∀ a b, F₁ (a + b) = F₁ a + F₁ b := by
    intro a b
    simp only [F₁, map_add]
    rw [liftPts_add p ℓ hℓp c ε D h hsm hpr hgc aj hajε haj Mη eη heη hgal q hℚ hP Y cY πα πβ hα hβ d hdα Φ hΦ hcut φη hφη hφadd Mη' eη' heη' hαI hβI hplaceα hplaceβ pts hadd hnorm]
    rfl
  have hF₂ : ∀ a b, F₂ (a + b) = F₂ a + F₂ b := by
    intro a b
    simp only [F₂]
    rw [liftPts_add p ℓ hℓp c ε D h hsm hpr hgc aj hajε haj Mη eη heη hgal q hℚ hP Y cY πα πβ hα hβ d hdα Φ hΦ hcut φη hφη hφadd Mη' eη' heη' hαI hβI hplaceα hplaceβ pts hadd hnorm, hφadd]
    rfl
  let f₁ : JZero p →+ Additive (SchemeHomOver (specMap ℚ ℚ̄) (D.baseChange ℚ).toBase) := AddMonoidHom.mk' F₁ hF₁
  let f₂ : JZero p →+ Additive (SchemeHomOver (specMap ℚ ℚ̄) (D.baseChange ℚ).toBase) := AddMonoidHom.mk' F₂ hF₂
  have hgen := closure_range_genClass_eq_top (deg_eq_one_modularFunctionFieldBar p) (Mη.pointEquivPlace s)
  have heq : f₁ = f₂ := by
    refine AddMonoidHom.eq_of_eqOn_dense hgen ?_
    rintro _ ⟨u, rfl⟩
    obtain ⟨P, rfl⟩ := Mη.pointEquivPlace.surjective u
    exact congrArg Additive.ofMul (liftPts_hecke_genClass p ℓ hℓp c ε D h hsm hpr hgc aj hajε haj Mη eη heη hgal q hℚ hP Y cY πα πβ hα hβ d hdα Φ hΦ hcut φη hφη hφadd Mη' eη' heη' hαI hβI hplaceα hplaceβ pts hadd hnorm s hs P)
  have hx : F₁ x = F₂ x := DFunLike.congr_fun heq x
  rw [eq_liftPts ℓ D z (pts x) hz, eq_liftPts ℓ D zq (pts (heckeOperatorBar p q x)) hzq]
  exact congrArg (fun w : Additive (SchemeHomOver (specMap ℚ ℚ̄) (D.baseChange ℚ).toBase) => (Additive.toMul w).1) hx

end
end S_ModularCurve_heckeOperatorBar_points_eq_comp_of_transform
end P2MW
export P2MW.S_ModularCurve_heckeOperatorBar_points_eq_comp_of_transform (solution)
