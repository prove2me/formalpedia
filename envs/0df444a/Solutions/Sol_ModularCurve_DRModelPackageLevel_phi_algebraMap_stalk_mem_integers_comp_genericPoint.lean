-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.phi_algebraMap_stalk_mem_integers_comp_genericPoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/be306bef-39b9-5289-ac88-b6b0edb0bb95

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart
import Definitions.Def_ModularCurve_DRResolvedModelPackageLevel
import Definitions.Def_ModularCurve_X0MqResolvedTable
import Definitions.Def_ModularCurve_DRResolvedModelChartsLevelRam
import Definitions.Def_MvPolynomial_CrossingResolutionScheme

import Definitions.Def_ModularCurve_DRModelPackageLevelAPI
import Definitions.Def_ModularCurve_DRModelPackageLevelCrossingFrame
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_IgusaScheme
import Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_fst_comp_zero_genericPoint_eq_iotaFin_and_mem_asIdeal_iff
import Theorems.Thm_ModularCurve_exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd
import Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_minimalPrimes_chartAlgFin_span_eq_pair_of_valuationSubring_pair
import Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_fst_comp_genericPoint_eq_iotaFin_and_eq_iotaInf
import Theorems.Thm_ModularCurve_DRModelPackageLevel_mem_minimalPrimes_of_fst_comp_genericPoint_eq_and_fst_comp_ne
import Theorems.Thm_ModularCurve_DRModelPackageLevel_xi_mem_preimage_smoothLocus
import Theorems.Thm_ModularCurve_DRModelPackageLevel_eq_xi_of_specializes
import Theorems.Thm_AlgebraicGeometry_Smooth_isDiscreteValuationRing_stalk_of_forall_specializes
import Theorems.Thm_AlgebraicGeometry_Smooth_maximalIdeal_stalk_eq_span_of_forall_specializes
import Theorems.Thm_AlgebraicGeometry_Scheme_germ_app_appIso_inv_mem_maximalIdeal_iff
import Theorems.Thm_ModularCurve_IgusaScheme_exists_mul_mem_adjoin_jFull_jqN
import Theorems.Thm_ModularCurve_IgusaScheme_jqN_mem_chartAlgFin_and_jFull_mem_chartAlg_jqN
import Theorems.Thm_ModularCurve_DRLevel_bcMap_apply_notMem_preimage_basicOpen
import Theorems.Thm_ModularCurve_valuationSubring_eq_of_comap_eq_of_forall_exists_coeffMap_eq
import Theorems.Thm_ModularCurve_IgusaScheme_subfieldClosure_range_germToFunctionField_union_range_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_phi_algebraMap_stalk_mem_integers_comp_genericPoint
p2m_attr_erase "instance" "ModularCurve.eisensteinMaximalIdeal.isPrime ModularCurve.JZeroNeronPrimaryTorsionFFModels.instCocomm_Hff ModularCurve.JZeroNeronPrimaryTorsionFFModels.instFinite_HffBarQ ModularCurve.JZeroNeronPrimaryTorsionFFModels.instFinite_Hff ModularCurve.JZeroNeronPrimaryTorsionFFModels.instHopfAlgebra_HffBarQ ModularCurve.JZeroNeronPrimaryTorsionCore.instCommRing_H ModularCurve.JZeroNeronPrimaryTorsionCore.instHopfAlgebra_H ModularCurve.JZeroNeronPrimaryTorsionFFModels.instCommRing_HffBarQ ModularCurve.JZeroNeronPrimaryTorsionFFModels.instHopfAlgebra_Hff ModularCurve.JZeroNeronPrimaryTorsionCore.instFlat_H ModularCurve.JZeroNeronPrimaryTorsionFFModels.instCocomm_HffBarQ ModularCurve.JZeroNeronPrimaryTorsionCore.instFiniteType_H ModularCurve.JZeroNeronPrimaryTorsionFFModels.instCommRing_Hff ModularCurve.JZeroNeronPrimaryTorsionFFModels.instFlat_Hff ModularCurve.JZeroNeronDataPrime.instFiniteΦ ModularCurve.JZeroNeronDataPrime.instAddCommGroupΦ ModularCurve.JZeroNeronDataPrime.instModuleΦ ModularCurve.JZeroNeronData.instAddCommGroupΦ ModularCurve.JZeroNeronData.instModuleΦ ModularCurve.JZeroNeronData.instFiniteΦ AlgebraicGeometry.Scheme.Fppf.instLocallyOfFinitePresentationHomDiscretePUnit AlgebraicGeometry.Scheme.Fppf.instFlatHomDiscretePUnit AlgebraicGeometry.Scheme.instAdditiveAbFunctorOppositeFppfConst AlgebraicGeometry.Scheme.instHasIsosFppfPrecoverage_definitions AlgebraicGeometry.Scheme.Fppf.instFullOverForget AlgebraicGeometry.Scheme.instAdditiveAbSheafFppfSmallFppfTopologyConstantSheaf AlgebraicGeometry.Scheme.hasSheafify_smallFppfTopology AlgebraicGeometry.Scheme.instCategoryFppf AlgebraicGeometry.Scheme.instIsCocontinuousFppfOverForgetSmallFppfTopologyOverFppfTopology AlgebraicGeometry.Scheme.instHasTerminalFppf AlgebraicGeometry.Scheme.instIsMultiplicativeLocallyOfFinitePresentation_definitions AlgebraicGeometry.Scheme.abelian_sheaf_smallFppfTopology AlgebraicGeometry.Scheme.isGrothendieckAbelian_sheaf_smallFppfTopology AlgebraicGeometry.Scheme.hasExt_sheaf_smallFppfTopology AlgebraicGeometry.Scheme.instLocallyCoverDenseFppfOverForgetOverFppfTopology AlgebraicGeometry.Scheme.Fppf.instFaithfulOverForget AlgebraicGeometry.Scheme.instAddCommGroupFppfCohomology AlgebraicGeometry.Scheme.instHasPullbacksFppfPrecoverage_definitions FppfCohomologyLES.fppfSheavesIsGrothendieckAbelian ModularCurve.AdmissibleInvariants.instAdd"
p2m_attr_erase "instance" "ModularCurve.AdmissibleInvariants.instZero FppfRepresentableGroupSchemeSheaf.instIsCommMonObjSchemeTensorUnit_definitions FppfRepresentableGroupSchemeSheaf.gateTrivialSheafSectionsSubsingleton ValuationSubring.instIsAlgClosedResidueField WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "ModularCurve.JZeroNeronObjectAtP.LevelData.mk.sizeOf_spec ModularCurve.JZeroNeronObjectAtP.mk.injEq ModularCurve.JZeroNeronObjectAtP.mk.sizeOf_spec ModularCurve.JZeroNeronObjectAtP.LevelData.mk.injEq ModularCurve.JZeroNeronIdentityComponent.mk.injEq ModularCurve.JZeroNeronIdentityComponent.mk.sizeOf_spec ModularCurve.JZeroNeronPrimaryTorsionFFModels.mk.sizeOf_spec ModularCurve.JZeroNeronPrimaryTorsionSheaf.mk.injEq ModularCurve.JZeroNeronPrimaryTorsionFFModels.mk.injEq ModularCurve.JZeroNeronPrimaryTorsionInvPins.mk.sizeOf_spec ModularCurve.JZeroNeronPrimaryTorsionCore.mk.sizeOf_spec ModularCurve.JZeroNeronPrimaryTorsionCore.mk.injEq ModularCurve.JZeroNeronPrimaryTorsionSheaf.mk.sizeOf_spec ModularCurve.JZeroNeronPrimaryTorsionInvPins.mk.injEq ModularCurve.JZeroNeronDataPrime.mk.sizeOf_spec ModularCurve.JZeroNeronDataPrime.mk.injEq ModularCurve.JZeroNeronData.mk.injEq ModularCurve.JZeroNeronData.mk.sizeOf_spec ModularCurve.eisensteinEval_heckeGen ModularCurve.modSystem_apply ModularCurve.FppfKummerData.mk.injEq ModularCurve.JKummerRow.mk.injEq ModularCurve.JKummerRow.mk.sizeOf_spec ModularCurve.FppfKummerData.mk.sizeOf_spec FppfCohomologyLES.cohomologyMapAddEquiv_apply FppfCohomologyLES.biprodSESHom_τ₃ FppfCohomologyLES.cohomologyMap_apply FppfCohomologyLES.cohomologyδ_apply FppfCohomologyLES.cohomologyMapAddEquiv_symm_apply FppfCohomologyLES.biprodSESHom_τ₁ ModularCurve.AdmissibleInvariants.zero_h1 ModularCurve.AdmissibleInvariants.add_h0 ModularCurve.AdmissibleInvariants.zero_δ ModularCurve.AdmissibleInvariants.zero_α ModularCurve.AdmissibleInvariants.zero_h0 ModularCurve.AdmissibleInvariants.add_α ModularCurve.AdmissibleInvariants.mk.sizeOf_spec FppfKummerSES.kummerSES_g FppfKummerSES.kummerSES_X₃ ModularCurve.AdmissibleInvariants.genericDefect_zero"
p2m_attr_erase "simp" "ModularCurve.AdmissibleInvariants.add_δ ModularCurve.AdmissibleInvariants.add_h1 FppfKummerSES.kummerSES_X₁ ModularCurve.AdmissibleInvariants.mk.injEq ModularCurve.AdmissibleInvariants.eulerDefect_zero FppfKummerSES.kummerSES_X₂ GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord RegularLocalRingQuotientAscent.dualNumberFst_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

open IsLocalRing ModularCurve.PlaceSpecialization MvPolynomial MvPolynomial.CrossingQuotient
open scoped ModularCurve.IgusaScheme

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

namespace ValIdLevel

section ValSub

variable (D K : Type*) [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] [Field K] [Algebra D K] [IsFractionRing D K]

noncomputable def valSub : ValuationSubring K :=
  { (algebraMap D K).range with
    mem_or_inv_mem' := fun x => by
      rcases ValuationRing.isInteger_or_isInteger D x with h | h
      · exact Or.inl h
      · exact Or.inr h }

theorem mem_valSub_iff (x : K) : x ∈ valSub D K ↔ x ∈ Set.range (algebraMap D K) := by
  show x ∈ (algebraMap D K).range ↔ _
  rw [RingHom.mem_range, Set.mem_range]

theorem coe_valSub : ((valSub D K : ValuationSubring K) : Set K) = Set.range (algebraMap D K) :=
  Set.ext (mem_valSub_iff D K)

theorem algebraMap_mem_valSub (d : D) : algebraMap D K d ∈ valSub D K := (mem_valSub_iff D K _).mpr ⟨d, rfl⟩

variable {D} in

theorem algebraMap_mem_nonunits_of_mem_maximalIdeal {ϖ : D} (hϖ : ϖ ∈ IsLocalRing.maximalIdeal D) :
    algebraMap D K ϖ ∈ (valSub D K).nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or]
  by_cases h0 : ϖ = 0
  · left; rw [h0, map_zero]
  right
  intro hinv
  obtain ⟨d, hd⟩ := (mem_valSub_iff D K _).mp hinv
  have hne : algebraMap D K ϖ ≠ 0 := fun h => h0 ((IsFractionRing.injective D K) (by rw [h, map_zero]))
  apply (IsLocalRing.mem_maximalIdeal _).mp hϖ
  refine isUnit_iff_exists_inv.mpr ⟨d, IsFractionRing.injective D K ?_⟩
  rw [map_mul, hd, map_one, mul_inv_cancel₀ hne]

variable {D} in

theorem exists_eq_pow_mul_of_maximalIdeal_eq {ϖ : D} (hϖ : IsLocalRing.maximalIdeal D = Ideal.span {ϖ})
    (g : K) (hg : g ∈ valSub D K) (hg0 : g ≠ 0) :
    ∃ n : ℕ, ∃ u ∈ valSub D K, u⁻¹ ∈ valSub D K ∧ g = (algebraMap D K ϖ) ^ n * u := by
  obtain ⟨d, rfl⟩ := (mem_valSub_iff D K _).mp hg
  have hd0 : d ≠ 0 := fun h => hg0 (by rw [h, map_zero])
  have hirr : Irreducible ϖ := IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal ϖ
    (fun h => IsDiscreteValuationRing.not_a_field D (by rw [hϖ, h, Ideal.span_singleton_eq_bot.mpr rfl])) hϖ
  obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd0 hirr
  refine ⟨n, algebraMap D K (v : D), algebraMap_mem_valSub D K _, ?_, ?_⟩
  · have : (algebraMap D K (v : D))⁻¹ = algebraMap D K ((v⁻¹ : Dˣ) : D) := by
      rw [inv_eq_of_mul_eq_one_right]
      rw [← map_mul, Units.mul_inv, map_one]
    rw [this]; exact algebraMap_mem_valSub D K _
  · rw [map_mul, map_pow, mul_comm]

end ValSub

end ValIdLevel

namespace ValIdLevel

variable {N₀ : ℕ} (q : ℕ) [NeZero N₀] [Fact q.Prime] {hqN : ¬ q ∣ N₀} (𝔛 : DRModelPackageLevel N₀ q hqN)
  (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : DRLevel.R q →+* O)

theorem eq_closedPoint_of_not_mem_basicOpen (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)}) (𝔭 : PrimeSpectrum O)
    (h𝔭 : 𝔭 ∉ (PrimeSpectrum.basicOpen ((q : ℕ) : O) : Set (PrimeSpectrum O))) : 𝔭 = IsLocalRing.closedPoint O := by
  apply PrimeSpectrum.ext
  have hp : ((q : ℕ) : O) ∈ 𝔭.asIdeal := by simpa [PrimeSpectrum.mem_basicOpen] using h𝔭
  show 𝔭.asIdeal = IsLocalRing.maximalIdeal O
  apply le_antisymm (IsLocalRing.le_maximalIdeal 𝔭.2.ne_top)
  rw [hϖ, Ideal.span_singleton_le_iff_mem]
  exact hp

theorem not_mem_basicOpen_closedPoint (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)}) :
    IsLocalRing.closedPoint O ∉ (PrimeSpectrum.basicOpen ((q : ℕ) : O) : Set (PrimeSpectrum O)) := by
  intro h
  rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at h
  apply h
  show ((q : ℕ) : O) ∈ IsLocalRing.maximalIdeal O
  rw [hϖ]; exact Ideal.mem_span_singleton_self _

theorem isDiscreteValuationRing_and_maximalIdeal_eq
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
    [hint : IsIntegral (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)))]
    (ξ : ↥(pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))))
    (hξU : ξ ∈ (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹ᵁ 𝔛.smoothLocus)
    (hξs : ξ ∉ (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens))
    (hmax : ∀ y : ↥(pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))), y ∉ (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) → y ⤳ ξ → y = ξ) :
    IsDiscreteValuationRing ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk ξ) ∧
      IsLocalRing.maximalIdeal ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk ξ) = Ideal.span {((q : ℕ) : (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk ξ)} := by

  haveI := 𝔛.smoothLocus_relDim
  haveI : Smooth (𝔛.smoothLocus.ι ≫ DRLevel.toBase N₀ q) :=
    SmoothOfRelativeDimension.smooth (n := 1) (f := 𝔛.smoothLocus.ι ≫ DRLevel.toBase N₀ q)
  let g := Spec.map (CommRingCat.ofHom ρO)
  let T := pullback (𝔛.smoothLocus.ι ≫ DRLevel.toBase N₀ q) g
  let t : T ⟶ Spec (CommRingCat.of O) := pullback.snd _ _
  let i : T ⟶ (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) :=
    pullback.map (𝔛.smoothLocus.ι ≫ DRLevel.toBase N₀ q) g (DRLevel.toBase N₀ q) g 𝔛.smoothLocus.ι (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])
  haveI : IsOpenImmersion i := inferInstance
  have hi_snd : i ≫ pullback.snd (DRLevel.toBase N₀ q) g = t := by
    show pullback.lift _ _ _ ≫ pullback.snd _ _ = _
    rw [pullback.lift_snd, Category.comp_id]

  have hξ : ξ ∈ Set.range i.base := by
    rw [Scheme.Pullback.range_map]
    refine ⟨?_, by simp⟩
    show (pullback.fst (DRLevel.toBase N₀ q) g).base ξ ∈ Set.range 𝔛.smoothLocus.ι.base
    rw [Scheme.Opens.range_ι]
    exact hξU
  obtain ⟨η, hη⟩ := hξ

  have hts : ∀ y : ↥T, t.base y = (pullback.snd (DRLevel.toBase N₀ q) g).base (i.base y) := by
    intro y; rw [← hi_snd]; rfl
  have hηs : t.base η = IsLocalRing.closedPoint O := by
    rw [hts, hη]
    exact eq_closedPoint_of_not_mem_basicOpen q O hϖ _ hξs
  have hgen : ∀ y : ↥T, y ⤳ η → t.base y = IsLocalRing.closedPoint O → y = η := by
    intro y hy hyc
    apply i.isOpenEmbedding.injective
    rw [hη]
    apply hmax
    · intro hc
      have hc' : (pullback.snd (DRLevel.toBase N₀ q) g).base (i.base y) ∈
          (PrimeSpectrum.basicOpen ((q : ℕ) : O) : Set (PrimeSpectrum O)) := hc
      rw [← hts, hyc] at hc'
      exact not_mem_basicOpen_closedPoint q O hϖ hc'
    · rw [← hη]; exact hy.map i.base.hom.continuous
  obtain ⟨_, hDVR⟩ := AlgebraicGeometry.Smooth.isDiscreteValuationRing_stalk_of_forall_specializes O t η hηs hgen
  have hmT := AlgebraicGeometry.Smooth.maximalIdeal_stalk_eq_span_of_forall_specializes O ((q : ℕ) : O) hϖ t η hηs hgen

  let E : (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk ξ ≃+* T.presheaf.stalk η :=
    (((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalkCongr (.of_eq hη.symm)).trans (asIso (i.stalkMap η))).commRingCatIsoToRingEquiv
  haveI : IsDiscreteValuationRing ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk ξ) := IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing E.symm
  refine ⟨inferInstance, ?_⟩

  have hgenT : (T.presheaf.germ ⊤ η trivial).hom ((t.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ((q : ℕ) : O)))
      = ((q : ℕ) : T.presheaf.stalk η) := by
    simp only [map_natCast]
  rw [hgenT] at hmT
  have hm : IsLocalRing.maximalIdeal ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk ξ) = (IsLocalRing.maximalIdeal (T.presheaf.stalk η)).comap E.toRingHom := by
    haveI : ((IsLocalRing.maximalIdeal (T.presheaf.stalk η)).comap E.toRingHom).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective (K := IsLocalRing.maximalIdeal (T.presheaf.stalk η)) E.toRingHom E.surjective
    exact (IsLocalRing.eq_maximalIdeal this).symm
  have hpE : ((q : ℕ) : T.presheaf.stalk η) = E.toRingHom ((q : ℕ) : ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk ξ)) := (map_natCast E.toRingHom q).symm
  rw [hm, hmT, hpE, ← Set.image_singleton, ← Ideal.map_span]
  exact Ideal.comap_map_of_bijective E.toRingHom E.bijective

end ValIdLevel

namespace ValIdLevel

section Readings

variable (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime]
  (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : DRLevel.R q →+* O)
  [hint : IsIntegral (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)))]
  (x : ↥(pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))))
  (φ : ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField) →+* ↥(modularFunctionFieldBar (N₀ * q)))
  [hne : Nonempty (Scheme.Opens.toScheme ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹ᵁ
            ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)))]

noncomputable def psi : ↥(IgusaScheme.chartAlgFin (N₀ * q) q) →+* ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField) :=
  ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).inv ≫
    ((IgusaScheme.ιFin (N₀ * q) q).appIso ⊤).inv ≫
      (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).app
        ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤) ≫
        (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).germToFunctionField ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹ᵁ
            ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤))).hom

theorem psi_apply (a : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : psi N₀ q O ρO a =
    ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).germToFunctionField ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹ᵁ
            ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤))
      (((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).app
          ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)).hom
        (((IgusaScheme.ιFin (N₀ * q) q).appIso ⊤).inv
          ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).inv a)))) := rfl

noncomputable def thetaO : O →+* ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField) :=
  (algebraMap ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk x) ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField)).comp
    (((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.germ ⊤ x trivial).hom.comp
      (((pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).appTop).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom))

theorem thetaO_apply (a : O) : thetaO N₀ q O ρO x a =
    algebraMap ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk x) _
      (((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.germ ⊤ x trivial).hom
        (((pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).appTop).hom
          ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a))) := rfl

variable
  (hφj : ∀ a : ↥(IgusaScheme.chartAlgFin (N₀ * q) q), ((φ (psi N₀ q O ρO a) : ↥(modularFunctionFieldBar (N₀ * q))) : LaurentSeries (AlgebraicClosure ℚ)) =
    coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ))

include hφj in
theorem psi_injective : Function.Injective (psi N₀ q O ρO) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have h := hφj a
  rw [ha, map_zero, ZeroMemClass.coe_zero] at h
  have : ((a : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) = 0 := by
    apply HahnSeries.ext; funext k
    have := congrArg (fun s : LaurentSeries (AlgebraicClosure ℚ) => s.coeff k) h
    simp only [HahnSeries.coeff_zero, coeffEmb_coeff] at this
    simp only [HahnSeries.coeff_zero]
    exact (map_eq_zero_iff _ (algebraMap ℚ (AlgebraicClosure ℚ)).injective).mp this.symm
  exact Subtype.ext (Subtype.ext this)

theorem isFractionRing_chartAlgFin :
    IsFractionRing ↥(IgusaScheme.chartAlgFin (N₀ * q) q) ↥(modularFunctionFieldFull (N₀ * q)) := by
  haveI : FaithfulSMul ↥(IgusaScheme.chartAlgFin (N₀ * q) q) ↥(modularFunctionFieldFull (N₀ * q)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Subtype.val_injective
  apply IsFractionRing.of_field
  intro z
  obtain ⟨g, hg, hg0, hgz⟩ := ModularCurve.IgusaScheme.exists_mul_mem_adjoin_jFull_jqN (N₀ * q) q z
  have hjqN := (ModularCurve.IgusaScheme.jqN_mem_chartAlgFin_and_jFull_mem_chartAlg_jqN (N₀ * q) q).1
  have hgA : g ∈ IgusaScheme.chartAlgFin (N₀ * q) q := IgusaScheme.adjoin_le_chartAlg (N₀ * q) q _ hg
  have hle : Algebra.adjoin ↥(GaloisRep.ratLocalizedAt q)
      ({IgusaScheme.jFull (N₀ * q), ⟨jqN (N₀ * q), modularFunctionField_le_full (N₀ * q) (jqN_mem (N₀ * q))⟩} :
        Set ↥(modularFunctionFieldFull (N₀ * q))) ≤ IgusaScheme.chartAlgFin (N₀ * q) q := by
    refine Algebra.adjoin_le ?_
    rintro y hy
    rcases hy with rfl | hy
    · exact IgusaScheme.subset_chartAlg (N₀ * q) q _ rfl
    · rw [Set.mem_singleton_iff] at hy; rw [hy]; exact hjqN
  have hgzA : g * z ∈ IgusaScheme.chartAlgFin (N₀ * q) q := hle hgz
  have hg0' : ((⟨g, hgA⟩ : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) ≠ 0 := hg0
  refine ⟨⟨g * z, hgzA⟩, ⟨g, hgA⟩, ?_⟩
  show z = ((⟨g * z, hgzA⟩ : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) /
    ((⟨g, hgA⟩ : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q)))
  rw [eq_div_iff hg0']
  show z * g = g * z
  ring

noncomputable def thetaF : ↥(modularFunctionFieldFull (N₀ * q)) →+* ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField) :=
  haveI := isFractionRing_chartAlgFin N₀ q
  IsFractionRing.lift (psi_injective N₀ q O ρO φ hφj)

theorem thetaF_algebraMap (a : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) :
    thetaF N₀ q O ρO φ hφj (algebraMap _ ↥(modularFunctionFieldFull (N₀ * q)) a) = psi N₀ q O ρO a := by
  haveI := isFractionRing_chartAlgFin N₀ q
  exact IsFractionRing.lift_algebraMap (psi_injective N₀ q O ρO φ hφj) a

theorem thetaF_coe (a : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : thetaF N₀ q O ρO φ hφj (a : ↥(modularFunctionFieldFull (N₀ * q))) = psi N₀ q O ρO a :=
  thetaF_algebraMap N₀ q O ρO φ hφj a

include hφj in
theorem coe_phi_thetaF (f : ↥(modularFunctionFieldFull (N₀ * q))) :
    ((φ (thetaF N₀ q O ρO φ hφj f) : ↥(modularFunctionFieldBar (N₀ * q))) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ) := by
  haveI := isFractionRing_chartAlgFin N₀ q
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) f
  rw [map_div₀, map_div₀, thetaF_algebraMap, thetaF_algebraMap]
  show (((φ (psi N₀ q O ρO a) / φ (psi N₀ q O ρO b) : ↥(modularFunctionFieldBar (N₀ * q))) : LaurentSeries (AlgebraicClosure ℚ))) = _
  rw [IntermediateField.coe_div, hφj, hφj, ← map_div₀]
  congr 1

end Readings

end ValIdLevel

namespace ValIdLevel

section Feed

variable (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime]
  (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : DRLevel.R q →+* O)
  [hint : IsIntegral (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)))]
  (x : ↥(pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))))
  (φ : ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField) →+* ↥(modularFunctionFieldBar (N₀ * q)))
  [hne : Nonempty (Scheme.Opens.toScheme ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹ᵁ
            ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)))]
  (hφj : ∀ a : ↥(IgusaScheme.chartAlgFin (N₀ * q) q), ((φ (psi N₀ q O ρO a) : ↥(modularFunctionFieldBar (N₀ * q))) : LaurentSeries (AlgebraicClosure ℚ)) =
    coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ))

include hint hne in

theorem closure_range_thetaF_union_range_thetaO_eq_top :
    Subfield.closure (Set.range (thetaF N₀ q O ρO φ hφj) ∪ Set.range (thetaO N₀ q O ρO x)) = ⊤ := by
  have h := ModularCurve.IgusaScheme.subfieldClosure_range_germToFunctionField_union_range_eq_top (N₀ * q) q O ρO x
  rw [eq_top_iff, ← h]
  apply Subfield.closure_mono
  rintro y (⟨a, rfl⟩ | ⟨s, rfl⟩)
  · exact Or.inl ⟨(a : ↥(modularFunctionFieldFull (N₀ * q))), thetaF_coe N₀ q O ρO φ hφj a⟩
  · exact Or.inr ⟨s, rfl⟩

theorem thetaO_mem_range (ξ : ↥(pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)))) (a : O) :
    thetaO N₀ q O ρO x a ∈ Set.range (algebraMap ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk ξ) ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField)) := by
  refine ⟨((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.germ ⊤ ξ trivial).hom
      (((pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)), ?_⟩
  rw [thetaO_apply]

  show ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.germ ⊤ ξ trivial ≫ (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalkSpecializes _).hom _ =
    ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.germ ⊤ x trivial ≫ (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalkSpecializes _).hom _
  rw [TopCat.Presheaf.germ_stalkSpecializes, TopCat.Presheaf.germ_stalkSpecializes]

theorem range_algebraMap_stalk_subset_of_specializes {ξ y : ↥(pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)))} (h : ξ ⤳ y) :
    Set.range (algebraMap ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk y) ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField)) ⊆
      Set.range (algebraMap ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk ξ) ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField)) := by
  rintro _ ⟨s, rfl⟩
  refine ⟨((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalkSpecializes h).hom s, ?_⟩
  show ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalkSpecializes h ≫ (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalkSpecializes _).hom s = ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalkSpecializes _).hom s
  rw [TopCat.Presheaf.stalkSpecializes_comp]

end Feed

end ValIdLevel

namespace ValIdLevel

p2m_open "ModularCurve.CharPReduction Polynomial AlgebraicGeometry.Polynomial"

variable {N₀ : ℕ} {p : ℕ} [NeZero N₀] [Fact p.Prime]

section IntSeries

variable (A : ValuationSubring (AlgebraicClosure ℚ)) {k : Type*} [Field k] (red : A →+* k)

noncomputable def intSeries (y : LaurentSeries ℤ) : LaurentSeries (AlgebraicClosure ℚ) :=
  coeffMap (Int.castRingHom (AlgebraicClosure ℚ)) y

theorem intSeries_mem (y : LaurentSeries ℤ) : intSeries y ∈ integralCoeffs A.toSubring := by
  intro n
  change (Int.castRingHom (AlgebraicClosure ℚ)) (y.coeff n) ∈ A.toSubring
  rw [eq_intCast]
  exact intCast_mem _ _

theorem coeffRed_intSeries (y : LaurentSeries ℤ) :
    coeffRed A.toSubring red ⟨intSeries y, intSeries_mem A y⟩ = coeffMap (Int.castRingHom k) y := by
  ext n
  rw [coeffRed_coeff, coeffMap_coeff]
  have : (⟨(intSeries y).coeff n, intSeries_mem A y n⟩ : A.toSubring) = ((y.coeff n : ℤ) : A.toSubring) := by
    apply Subtype.ext
    change (Int.castRingHom (AlgebraicClosure ℚ)) (y.coeff n) = _
    rw [eq_intCast]
    rfl
  rw [this, map_intCast, eq_intCast]

theorem coeffEmb_coeffMap_int (y : LaurentSeries ℤ) :
    coeffEmb (AlgebraicClosure ℚ) (coeffMap (Int.castRingHom ℚ) y) = intSeries y := by
  rw [intSeries, coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (RingHom.ext_int _ _) y

variable [CharP k p]

theorem coeffMap_int_ne_zero_iff (y : LaurentSeries ℤ) :
    coeffMap (Int.castRingHom k) y ≠ 0 ↔ coeffMap (Int.castRingHom (ZMod p)) y ≠ 0 := by
  have hfac : Int.castRingHom k = (ZMod.castHom (dvd_refl p) k).comp (Int.castRingHom (ZMod p)) :=
    RingHom.ext_int _ _
  rw [not_iff_not, coeffMap_congr hfac, ← coeffMap_coeffMap]
  change coeffMap _ (coeffMap (Int.castRingHom (ZMod p)) y) = 0 ↔ coeffMap (Int.castRingHom (ZMod p)) y = 0
  constructor
  · intro h
    ext n
    rw [coeffMap_coeff, HahnSeries.coeff_zero]
    have := congrArg (fun z : LaurentSeries k => z.coeff n) h
    simp only [coeffMap_coeff, HahnSeries.coeff_zero] at this
    exact (ZMod.castHom (dvd_refl p) k).injective (this.trans (map_zero _).symm)
  · intro h; rw [h, map_zero]

omit [Fact p.Prime] in

theorem coeffMap_int_eq (y : LaurentSeries ℤ) :
    coeffMap (Int.castRingHom k) y = coeffMap (ZMod.castHom (dvd_refl p) k) (coeffMap (Int.castRingHom (ZMod p)) y) := by
  have hfac : Int.castRingHom k = (ZMod.castHom (dvd_refl p) k).comp (Int.castRingHom (ZMod p)) :=
    RingHom.ext_int _ _
  rw [coeffMap_congr hfac, ← coeffMap_coeffMap]

end IntSeries

section Package

variable {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k p] {red : A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N₀ p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N₀ p}
    {P : PlaceSpecialization A p N₀ data hKr k red hα hβ}

set_option maxHeartbeats 16000000 in

theorem tuplePackage (R : ProlongationTuple P) :
    ∃ (V₁ V₂ : ValuationSubring ↥(modularFunctionFieldBar (N₀ * p)))
      (ρ₁ : ↥V₁ →+* LaurentSeries k) (ρ₂ : ↥V₂ →+* LaurentSeries k),
      R.R₁.integers = V₁ ∧ R.R₂.integers = V₂ ∧

      (∀ x : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p)) x ∈ V₁ ↔ x ∈ A) ∧
      (∀ x : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p)) x ∈ V₂ ↔ x ∈ A) ∧

      (∀ g : ↥V₁, ρ₁ g = 0 ↔ (g : ↥(modularFunctionFieldBar (N₀ * p))) ∈ V₁.nonunits) ∧
      (∀ g : ↥V₂, ρ₂ g = 0 ↔ (g : ↥(modularFunctionFieldBar (N₀ * p))) ∈ V₂.nonunits) ∧

      (∀ (a : A) (h : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p)) (a : AlgebraicClosure ℚ) ∈ V₁),
        ρ₁ ⟨_, h⟩ = HahnSeries.C (red a)) ∧
      (∀ (a : A) (h : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p)) (a : AlgebraicClosure ℚ) ∈ V₂),
        ρ₂ ⟨_, h⟩ = HahnSeries.C (red a)) ∧

      (∀ g : ↥(modularFunctionFieldBar (N₀ * p)), g ∈ V₁ →
        ∃ r s : ↥(modularRing (N₀ * p) A.toSubring),
          s ∉ redKer A.toSubring red (modularRing (N₀ * p) A.toSubring) (modularRing_le_integralCoeffs (N₀ * p) A.toSubring) ∧
          (g : LaurentSeries (AlgebraicClosure ℚ)) * s = r ∧
          ∀ h : g ∈ V₁, ρ₁ ⟨g, h⟩ *
              redRes A.toSubring red (modularRing (N₀ * p) A.toSubring) (modularRing_le_integralCoeffs (N₀ * p) A.toSubring) s =
            redRes A.toSubring red (modularRing (N₀ * p) A.toSubring) (modularRing_le_integralCoeffs (N₀ * p) A.toSubring) r) ∧

      (∀ g : ↥(modularFunctionFieldBar (N₀ * p)), g ∈ V₂ ↔ ProlongationTuple.atkinLehnerBar N₀ p g ∈ V₁) ∧
      (∀ (g : ↥(modularFunctionFieldBar (N₀ * p))) (h : g ∈ V₂) (h' : ProlongationTuple.atkinLehnerBar N₀ p g ∈ V₁),
        ρ₂ ⟨g, h⟩ = ρ₁ ⟨_, h'⟩) := by

  let coeK : ↥(modularFunctionFieldC k N₀) →+* LaurentSeries k := (modularFunctionFieldC k N₀).val.toRingHom
  have hcoeK : ∀ x, coeK x = (x : LaurentSeries k) := fun x => rfl
  let ρ₁ : ↥R.R₁.integers →+* LaurentSeries k := coeK.comp (R.ι.comp R.R₁.residue)
  let ρ₂ : ↥R.R₂.integers →+* LaurentSeries k := coeK.comp (R.ι.comp R.R₂.residue)
  have hρ₁ : ∀ g, ρ₁ g = ((R.ι (R.R₁.residue g) : ↥(modularFunctionFieldC k N₀)) : LaurentSeries k) := fun g => rfl
  have hρ₂ : ∀ g, ρ₂ g = ((R.ι (R.R₂.residue g) : ↥(modularFunctionFieldC k N₀)) : LaurentSeries k) := fun g => rfl

  have hconst : ∀ c : ResidueField A,
      (((algebraMap (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) N₀)) c : ↥(modularFunctionFieldFullC (ResidueField ↥A) N₀)) :
        LaurentSeries (ResidueField A)) = algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) c := fun c => by
    rw [Algebra.algebraMap_eq_smul_one, IntermediateField.coe_smul, IntermediateField.coe_one, Algebra.algebraMap_eq_smul_one]
  refine ⟨R.R₁.integers, R.R₂.integers, ρ₁, ρ₂, rfl, rfl, R.R₁.algebraMap_mem_iff, R.R₂.algebraMap_mem_iff,
    ?_, ?_, ?_, ?_, ?_, R.mem_integers₂_iff, ?_⟩
  · intro g
    rw [hρ₁, ZeroMemClass.coe_eq_zero, map_eq_zero, ValuationSubring.coe_mem_nonunits_iff, ← R.R₁.ker_residue,
      RingHom.mem_ker]
  · intro g
    rw [hρ₂, ZeroMemClass.coe_eq_zero, map_eq_zero, ValuationSubring.coe_mem_nonunits_iff, ← R.R₂.ker_residue,
      RingHom.mem_ker]
  · intro a h
    rw [hρ₁, R.R₁.residue_algebraMap a, R.ι_coe, hconst (residue A a), algebraMap_laurentSeries_eq_single,
      coeffMap_single, R.redBar_residue, HahnSeries.C_apply]
  · intro a h
    rw [hρ₂, R.R₂.residue_algebraMap a, R.ι_coe, hconst (residue A a), algebraMap_laurentSeries_eq_single,
      coeffMap_single, R.redBar_residue, HahnSeries.C_apply]
  · intro g hg
    have hML := (R.mem_integersFst_iff g).mp hg
    obtain ⟨r, s, hs, hgs⟩ := (mem_localizedAtKer A.toSubring red _ (modularRing_le_integralCoeffs (N₀ * p) A.toSubring)).mp hML
    refine ⟨r, s, hs, hgs, fun h => ?_⟩
    obtain ⟨h', hres⟩ := R.residue₁_eq_modularRedLocHom g hML
    have hspec := redLoc_spec (A := A.toSubring) (red := red) (R := modularRing (N₀ * p) A.toSubring)
      (hR := modularRing_le_integralCoeffs (N₀ * p) A.toSubring) ⟨(g : LaurentSeries (AlgebraicClosure ℚ)), hML⟩ hgs
    have hproof : R.R₁.residue ⟨g, h⟩ = R.R₁.residue ⟨g, h'⟩ := rfl
    rw [hρ₁, hproof, hres]
    simp only [modularRedLocHom]
    exact hspec
  · intro g h h'
    rw [hρ₂, hρ₁, R.residue₂_eq g h]

end Package

end ValIdLevel

namespace ValIdLevel

section Val

variable {L : Type*} [Field L]

theorem eq_of_le_of_forall_nonunit_div {W W' : ValuationSubring L} (hle : W ≤ W') {ϖ : L} (hϖ0 : ϖ ≠ 0)
    (hϖ : ϖ ∈ W'.nonunits) (hdiv : ∀ f ∈ W.nonunits, (f : L) * ϖ⁻¹ ∈ W) : W = W' := by
  refine le_antisymm hle fun f hf => ?_
  by_contra hfW
  have hfi : f⁻¹ ∈ W := (W.mem_or_inv_mem f).resolve_left hfW
  have hf0 : f ≠ 0 := by rintro rfl; exact hfW W.zero_mem
  have hnu : f⁻¹ ∈ W.nonunits := W.inv_mem_nonunits_iff.mpr (Or.inr hfW)
  have h1 : f⁻¹ * ϖ⁻¹ ∈ W' := hle (hdiv _ hnu)
  have h2 : ϖ⁻¹ ∈ W' := by
    have := W'.mul_mem _ _ hf h1
    rwa [← mul_assoc, mul_inv_cancel₀ hf0, one_mul] at this
  rcases W'.mem_nonunits_iff_or.mp hϖ with h | h
  · exact hϖ0 h
  · exact h h2

end Val

end ValIdLevel

namespace ValIdLevel

theorem comp_base_apply' {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (x : ↥X) : (f ≫ g).base x = g.base (f.base x) := rfl

section Germs

variable (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime]
  (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : DRLevel.R q →+* O)
  [hint : IsIntegral (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)))]
  [hne : Nonempty (Scheme.Opens.toScheme ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹ᵁ
            ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)))]

noncomputable abbrev sec (a : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) :
    Γ(pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)),
      (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)) :=
  ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).app ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)).hom
    (((IgusaScheme.ιFin (N₀ * q) q).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).inv a))

include hint hne in

theorem psi_eq_algebraMap_germ (ξ : ↥(pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))))
    (hy : (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).base ξ ∈ (IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)
    (a : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) :
    psi N₀ q O ρO a = algebraMap ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk ξ) _
      (((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.germ
        ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)) ξ hy).hom
          (sec N₀ q O ρO a)) := by
  rw [psi_apply]
  show ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).germToFunctionField _) (sec N₀ q O ρO a) = _
  unfold Scheme.germToFunctionField
  show _ = ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.germ _ ξ hy ≫
    (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalkSpecializes _).hom (sec N₀ q O ρO a)
  rw [TopCat.Presheaf.germ_stalkSpecializes]

end Germs

section ValSubFacts

variable {D K : Type*} [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] [Field K] [Algebra D K] [IsFractionRing D K]

theorem algebraMap_mem_nonunits_iff (d : D) : algebraMap D K d ∈ (valSub D K).nonunits ↔ d ∈ IsLocalRing.maximalIdeal D := by
  refine ⟨fun h => ?_, algebraMap_mem_nonunits_of_mem_maximalIdeal K⟩
  by_contra hd
  have hu : IsUnit d := by simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hd
  obtain ⟨u, rfl⟩ := hu
  rw [ValuationSubring.mem_nonunits_iff_or] at h
  rcases h with h | h
  · exact u.ne_zero ((IsFractionRing.injective D K) (by rw [h, map_zero]))
  · apply h
    have : (algebraMap D K (u : D))⁻¹ = algebraMap D K ((u⁻¹ : Dˣ) : D) := by
      rw [inv_eq_of_mul_eq_one_right]
      rw [← map_mul, Units.mul_inv, map_one]
    rw [this]
    exact algebraMap_mem_valSub D K _

theorem forall_mem_and_of_valSub_eq {L : Type*} [Field L] (φ : K →+* L) (V : ValuationSubring L)
    (h : valSub D K = V.comap φ) :
    ∀ u : D, φ (algebraMap D K u) ∈ V ∧ (u ∈ IsLocalRing.maximalIdeal D → φ (algebraMap D K u) ∈ V.nonunits) := by
  intro u
  have hmem : algebraMap D K u ∈ V.comap φ := h ▸ algebraMap_mem_valSub D K u
  refine ⟨hmem, fun hu => ?_⟩
  have hnu : algebraMap D K u ∈ (V.comap φ).nonunits := h ▸ algebraMap_mem_nonunits_of_mem_maximalIdeal K hu
  rw [(V.comap φ).mem_nonunits_iff_or] at hnu
  rw [V.mem_nonunits_iff_or]
  rcases hnu with h0 | h0
  · left; rw [h0, map_zero]
  · right; intro hinv; apply h0
    rw [ValuationSubring.mem_comap, map_inv₀]; exact hinv

end ValSubFacts

end ValIdLevel

namespace ValIdLevel

p2m_open "ModularCurve.CharPReduction Polynomial AlgebraicGeometry.Polynomial"

set_option maxHeartbeats 12800000 in
theorem core
    {N₀ : ℕ} [NeZero N₀] (p : ℕ) [Fact p.Prime]
    (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (ιO : O →+* AlgebraicClosure ℚ)
    {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k p] {red : A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N₀ p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N₀ p}
    (P : PlaceSpecialization A p N₀ data hKr k red hα hβ) (R : ProlongationTuple P)
    (hιA : ∀ a : O, ιO a ∈ A)
    (L : Type*) [Field L] (φ : L →+* ↥(modularFunctionFieldBar (N₀ * p)))
    (θO : O →+* L)
    (hθO : ∀ a : O, φ (θO a) = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p)) (ιO a))
    (θF : ↥(modularFunctionFieldFull (N₀ * p)) →+* L)
    (hθF : ∀ f : ↥(modularFunctionFieldFull (N₀ * p)),
      ((φ (θF f) : ↥(modularFunctionFieldBar (N₀ * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ))
    (hgen : Subfield.closure (Set.range θF ∪ Set.range θO) = ⊤)
    (𝒱 : ValuationSubring L)
    (hp𝒱 : ((p : ℕ) : L) ∈ 𝒱.nonunits)
    (hdisc : ∀ g ∈ 𝒱, g ≠ 0 → ∃ n : ℕ, ∃ u ∈ 𝒱, u⁻¹ ∈ 𝒱 ∧ g = ((p : ℕ) : L) ^ n * u)
    (hO𝒱 : ∀ a : O, θO a ∈ 𝒱)

    (W : Fin 2 → ValuationSubring ↥(modularFunctionFieldFull (N₀ * p)))
    (hW1 : ∀ f : ↥(modularFunctionFieldFull (N₀ * p)), f ∈ W 0 ↔
        ∃ x y : LaurentSeries ℤ, coeffMap (Int.castRingHom (ZMod p)) y ≠ 0 ∧
          (f : LaurentSeries ℚ) * coeffMap (Int.castRingHom ℚ) y = coeffMap (Int.castRingHom ℚ) x)
    (hW2 : ∀ f : ↥(modularFunctionFieldFull (N₀ * p)), f ∈ W 1 ↔ atkinLehnerInvolutionFull N₀ p f ∈ W 0)
    (hW4 : ∀ i, ((p : ℕ) : ↥(modularFunctionFieldFull (N₀ * p))) ∈ (W i).nonunits ∧
        (∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
          Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull (N₀ * p)))
              ⟨jq, modularFunctionField_le_full (N₀ * p) (jq_mem (N₀ * p))⟩ P ∈ W i ∧
            (Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull (N₀ * p)))
              ⟨jq, modularFunctionField_le_full (N₀ * p) (jq_mem (N₀ * p))⟩ P)⁻¹ ∈ W i) ∧
        (∀ f ∈ (W i).nonunits, f * ((p : ℕ) : ↥(modularFunctionFieldFull (N₀ * p)))⁻¹ ∈ W i))

    (i : Fin 2) (h𝒱i : 𝒱.comap θF = W i) :
    𝒱 = (if i = 0 then R.R₁.integers else R.R₂.integers).comap φ := by
  classical

  obtain ⟨V₁, V₂, ρ₁, ρ₂, hRV₁, hRV₂, hcV₁, hcV₂, hker₁, hker₂, hρc₁, hρc₂, hdict, hV₂iff, hρ₂₁⟩ := tuplePackage R
  rw [hRV₁, hRV₂]

  have hpFb : ((p : ℕ) : ↥(modularFunctionFieldBar (N₀ * p))) ≠ 0 := NeZero.ne _
  have hpL : ((p : ℕ) : L) ≠ 0 := by
    intro h
    have := congrArg φ h
    rw [map_natCast, map_zero] at this
    exact hpFb this
  have hredp : red ⟨(p : AlgebraicClosure ℚ), by exact_mod_cast (natCast_mem A p)⟩ = 0 := by
    have : (⟨(p : AlgebraicClosure ℚ), by exact_mod_cast (natCast_mem A p)⟩ : A) = (p : A) :=
      Subtype.ext (by push_cast; rfl)
    rw [this, map_natCast, CharP.cast_eq_zero]
  have hpinvA : ((p : ℕ) : AlgebraicClosure ℚ)⁻¹ ∉ A := by
    intro h
    have h1 : red (⟨(p : AlgebraicClosure ℚ), by exact_mod_cast (natCast_mem A p)⟩ * ⟨_, h⟩) = 1 := by
      have : (⟨(p : AlgebraicClosure ℚ), by exact_mod_cast (natCast_mem A p)⟩ * ⟨_, h⟩ : A) = 1 :=
        Subtype.ext (by push_cast; exact mul_inv_cancel₀ (NeZero.ne _))
      rw [this, map_one]
    rw [map_mul, hredp, zero_mul] at h1
    exact zero_ne_one h1

  have hpV : ∀ V : ValuationSubring ↥(modularFunctionFieldBar (N₀ * p)),
      (∀ x : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p)) x ∈ V ↔ x ∈ A) →
      ((p : ℕ) : ↥(modularFunctionFieldBar (N₀ * p))) ∈ V.nonunits := by
    intro V hcV
    rw [ValuationSubring.mem_nonunits_iff_or]
    refine Or.inr fun h => hpinvA ?_
    rw [← hcV]
    rwa [map_inv₀, map_natCast]
  have hp𝒲 : ∀ V : ValuationSubring ↥(modularFunctionFieldBar (N₀ * p)),
      ((p : ℕ) : ↥(modularFunctionFieldBar (N₀ * p))) ∈ V.nonunits → ((p : ℕ) : L) ∈ (V.comap φ).nonunits := by
    intro V hV
    rw [ValuationSubring.mem_nonunits_iff_or]
    refine Or.inr fun h => ?_
    rw [ValuationSubring.mem_comap, map_inv₀, map_natCast] at h
    rcases (V.mem_nonunits_iff_or).mp hV with h' | h'
    · exact hpFb h'
    · exact h' h

  have h𝒲O : ∀ V : ValuationSubring ↥(modularFunctionFieldBar (N₀ * p)),
      (∀ x : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p)) x ∈ V ↔ x ∈ A) →
      ∀ a : O, θO a ∈ V.comap φ := by
    intro V hcV a
    rw [ValuationSubring.mem_comap, hθO, hcV]
    exact hιA a

  have hnucomap : ∀ (V : ValuationSubring ↥(modularFunctionFieldBar (N₀ * p))) (g : L),
      g ∈ (V.comap φ).nonunits ↔ φ g ∈ V.nonunits := fun V g => by
    rw [(V.comap φ).mem_nonunits_iff_or, V.mem_nonunits_iff_or, map_eq_zero_iff φ φ.injective, ← map_inv₀,
      ValuationSubring.mem_comap]

  have hres : ∀ V : ValuationSubring ↥(modularFunctionFieldBar (N₀ * p)),
      ∃ r : ↥(V.comap φ) →+* ↥V, ∀ g, (r g : ↥(modularFunctionFieldBar (N₀ * p))) = φ g := fun V =>
    ⟨φ.restrict (V.comap φ) V fun g hg => hg, fun g => RingHom.coe_restrict_apply _ _ _ _ g⟩

  obtain ⟨θb, hθbdef⟩ : ∃ θb : ↥(modularFunctionFieldFull (N₀ * p)) → ↥(modularFunctionFieldBar (N₀ * p)), ∀ f,
      θb f = ⟨coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) f.2⟩ :=
    ⟨_, fun f => rfl⟩
  have hθb : ∀ f, ((θb f : ↥(modularFunctionFieldBar (N₀ * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ) := fun f => by rw [hθbdef]
  have hφθ : ∀ f, φ (θF f) = θb f := by
    intro f
    apply Subtype.ext
    rw [hθb, hθF]

  have hθbw : ∀ f, ProlongationTuple.atkinLehnerBar N₀ p (θb f) = θb (atkinLehnerInvolutionFull N₀ p f) := by
    intro f
    rw [hθbdef, hθbdef]
    exact geomAut_coeffEmb (AlgebraicClosure ℚ) (modularFunctionFieldFull (N₀ * p)) (atkinLehnerInvolutionFull N₀ p) f

  have hmemW : ∀ (V : ValuationSubring ↥(modularFunctionFieldBar (N₀ * p))) f, f ∈ (V.comap φ).comap θF ↔ θb f ∈ V :=
    fun V f => by rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap, hφθ]

  have hpF : ∀ 𝒲 : ValuationSubring L, ((p : ℕ) : L) ∈ 𝒲.nonunits →
      ((p : ℕ) : ↥(modularFunctionFieldFull (N₀ * p))) ∈ (𝒲.comap θF).nonunits := by
    intro 𝒲 h
    rw [ValuationSubring.mem_nonunits_iff_or]
    refine Or.inr fun h' => ?_
    rw [ValuationSubring.mem_comap, map_inv₀, map_natCast] at h'
    rcases (𝒲.mem_nonunits_iff_or).mp h with h'' | h''
    · exact hpL h''
    · exact h'' h'

  have hMR : modularRing (N₀ * p) A.toSubring ≤ integralCoeffs A.toSubring := modularRing_le_integralCoeffs (N₀ * p) A.toSubring
  have hW0 : ∀ f, f ∈ W 0 → θb f ∈ V₁ ∧ ∀ h : θb f ∈ V₁, ∃ y : LaurentSeries (ZMod p), coeffMap (ZMod.castHom (dvd_refl p) k) y = ρ₁ ⟨θb f, h⟩ := by
    intro f hf
    obtain ⟨x, y, hy, hxy⟩ := (hW1 f).mp hf

    have hFy : ((θb f : ↥(modularFunctionFieldBar (N₀ * p))) : LaurentSeries (AlgebraicClosure ℚ)) * intSeries y =
        intSeries x := by
      rw [hθb, ← coeffEmb_coeffMap_int, ← coeffEmb_coeffMap_int, ← map_mul, hxy]
    have hyk : coeffMap (Int.castRingHom k) y ≠ 0 := (coeffMap_int_ne_zero_iff (p := p) y).mpr hy

    have hint : θb f ∈ V₁ := by
      by_contra hfV
      have hgV : (θb f)⁻¹ ∈ V₁ := (V₁.mem_or_inv_mem _).resolve_left hfV
      have hgnu : ((θb f)⁻¹ : ↥(modularFunctionFieldBar (N₀ * p))) ∈ V₁.nonunits := V₁.inv_mem_nonunits_iff.mpr (Or.inr hfV)
      have hf0 : ((θb f : ↥(modularFunctionFieldBar (N₀ * p))) : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := by
        intro h; apply hfV
        have : θb f = 0 := by exact_mod_cast h
        rw [this]; exact V₁.zero_mem
      obtain ⟨r, s, hs, hgs, hres⟩ := hdict _ hgV
      have hredr : redRes A.toSubring red (modularRing (N₀ * p) A.toSubring) hMR r = 0 := by
        rw [← hres hgV, (hker₁ _).mpr hgnu, zero_mul]
      have hginv : (((θb f)⁻¹ : ↥(modularFunctionFieldBar (N₀ * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
          ((θb f : ↥(modularFunctionFieldBar (N₀ * p))) : LaurentSeries (AlgebraicClosure ℚ))⁻¹ :=
        IntermediateField.coe_inv _ _
      have hid : (r : LaurentSeries (AlgebraicClosure ℚ)) * intSeries x = (s : LaurentSeries (AlgebraicClosure ℚ)) * intSeries y := by
        rw [← hgs, ← hFy, hginv]
        field_simp
      have hid' : (⟨(r : LaurentSeries (AlgebraicClosure ℚ)), hMR r.2⟩ : ↥(integralCoeffs A.toSubring)) *
          ⟨intSeries x, intSeries_mem A x⟩ = ⟨(s : LaurentSeries (AlgebraicClosure ℚ)), hMR s.2⟩ * ⟨intSeries y, intSeries_mem A y⟩ :=
        Subtype.ext hid
      have hred := congrArg (coeffRed A.toSubring red) hid'
      rw [map_mul, map_mul, coeffRed_intSeries, coeffRed_intSeries, ← redRes_apply, ← redRes_apply, hredr,
        zero_mul] at hred
      exact mul_ne_zero (redRes_ne_zero_of_notMem hs) hyk hred.symm

    refine ⟨hint, fun h => ?_⟩
    obtain ⟨r, s, hs, hgs, hres⟩ := hdict _ h
    have hid : (r : LaurentSeries (AlgebraicClosure ℚ)) * intSeries y = (s : LaurentSeries (AlgebraicClosure ℚ)) * intSeries x := by
      rw [← hgs, ← hFy]; ring
    have hid' : (⟨(r : LaurentSeries (AlgebraicClosure ℚ)), hMR r.2⟩ : ↥(integralCoeffs A.toSubring)) *
        ⟨intSeries y, intSeries_mem A y⟩ = ⟨(s : LaurentSeries (AlgebraicClosure ℚ)), hMR s.2⟩ * ⟨intSeries x, intSeries_mem A x⟩ :=
      Subtype.ext hid
    have hred := congrArg (coeffRed A.toSubring red) hid'
    rw [map_mul, map_mul, coeffRed_intSeries, coeffRed_intSeries, ← redRes_apply, ← redRes_apply, ← hres h] at hred
    have hred' : ρ₁ ⟨θb f, h⟩ * coeffMap (Int.castRingHom k) y = coeffMap (Int.castRingHom k) x := by
      apply mul_left_cancel₀ (redRes_ne_zero_of_notMem hs)
      linear_combination hred
    refine ⟨coeffMap (Int.castRingHom (ZMod p)) x / coeffMap (Int.castRingHom (ZMod p)) y, ?_⟩
    rw [map_div₀, ← coeffMap_int_eq, ← coeffMap_int_eq, div_eq_iff hyk]
    exact hred'.symm

  have hWR₁ : W 0 = (V₁.comap φ).comap θF :=
    eq_of_le_of_forall_nonunit_div (fun f hf => (hmemW V₁ f).mpr (hW0 f hf).1) (NeZero.ne _)
      (hpF _ (hp𝒲 V₁ (hpV V₁ hcV₁))) (hW4 0).2.2
  have hWR₂ : W 1 = (V₂.comap φ).comap θF := by
    ext f
    rw [hW2 f, hWR₁, hmemW, hmemW, hV₂iff, hθbw]

  have hW1' : ∀ f, f ∈ W 1 → ∀ h : θb f ∈ V₂, ∃ y : LaurentSeries (ZMod p),
      coeffMap (ZMod.castHom (dvd_refl p) k) y = ρ₂ ⟨θb f, h⟩ := by
    intro f hf h
    have hwf : atkinLehnerInvolutionFull N₀ p f ∈ W 0 := (hW2 f).mp hf
    have h' : ProlongationTuple.atkinLehnerBar N₀ p (θb f) ∈ V₁ := by rw [hθbw]; exact (hW0 _ hwf).1
    obtain ⟨y, hy⟩ := (hW0 _ hwf).2 (by rw [← hθbw]; exact h')
    refine ⟨y, ?_⟩
    rw [hy, hρ₂₁ (θb f) h h']
    congr 1
    exact Subtype.ext (hθbw f).symm

  have hside : ∀ (V : ValuationSubring ↥(modularFunctionFieldBar (N₀ * p))) (ρV : ↥V →+* LaurentSeries k) (i : Fin 2),
      (∀ x : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p)) x ∈ V ↔ x ∈ A) →
      (∀ g : ↥V, ρV g = 0 ↔ (g : ↥(modularFunctionFieldBar (N₀ * p))) ∈ V.nonunits) →
      (∀ (a : A) (h : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p)) (a : AlgebraicClosure ℚ) ∈ V),
        ρV ⟨_, h⟩ = HahnSeries.C (red a)) →
      (∀ f, f ∈ W i → ∀ h : θb f ∈ V, ∃ y : LaurentSeries (ZMod p), coeffMap (ZMod.castHom (dvd_refl p) k) y = ρV ⟨θb f, h⟩) →
      W i = (V.comap φ).comap θF → 𝒱.comap θF = W i → 𝒱 = V.comap φ := by
    intro V ρV i hcV hkerV hρcV hratV hWi h𝒱i
    obtain ⟨rV, hrV⟩ := hres V
    refine ModularCurve.valuationSubring_eq_of_comap_eq_of_forall_exists_coeffMap_eq p O hϖ ιO red hιA θO θF hgen 𝒱 (V.comap φ) hpL hp𝒱 (hp𝒲 V (hpV V hcV)) hdisc hO𝒱 (h𝒲O V hcV)
      (h𝒱i.trans hWi) (hpF 𝒱 hp𝒱) ?_ (ρV.comp rV) ?_ ?_ ?_
    ·
      rw [h𝒱i]; exact (hW4 i).2.2
    ·
      intro g
      rw [RingHom.comp_apply, hkerV, hrV, hnucomap]
    ·
      intro a
      have hmem : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p)) (ιO a) ∈ V := (hcV _).mpr (hιA a)
      have : rV ⟨θO a, h𝒲O V hcV a⟩ = ⟨_, hmem⟩ := Subtype.ext (by rw [hrV, hθO])
      rw [RingHom.comp_apply, this]
      exact hρcV ⟨ιO a, hιA a⟩ hmem
    ·
      intro f h
      have hfb : θb f ∈ V := by rw [← hφθ]; exact h
      have hfW : f ∈ W i := by rw [hWi, hmemW]; exact hfb
      obtain ⟨y, hy⟩ := hratV f hfW hfb
      refine ⟨y, ?_⟩
      have : rV ⟨θF f, h⟩ = ⟨θb f, hfb⟩ := Subtype.ext (by rw [hrV, hφθ])
      rw [hy, RingHom.comp_apply, this]

  revert h𝒱i
  refine Fin.cases ?_ (fun j => ?_) i
  · intro h0
    rw [if_pos rfl]
    exact hside V₁ ρ₁ 0 hcV₁ hker₁ hρc₁ (fun f hf h => (hW0 f hf).2 h) hWR₁ h0
  · intro h1
    have hj : j = 0 := Fin.eq_zero j
    subst hj
    rw [if_neg (by decide)]
    exact hside V₂ ρ₂ 1 hcV₂ hker₂ hρc₂ hW1' hWR₂ h1

end ValIdLevel

namespace ValIdLevel

p2m_open "ModularCurve.CharPReduction Polynomial AlgebraicGeometry.Polynomial"

set_option maxHeartbeats 12800000 in
theorem branch
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔛 : DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)}) (ρO : DRLevel.R q →+* O)
    (ιO : O →+* AlgebraicClosure ℚ)
    {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N₀ q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N₀ q}
    (P : PlaceSpecialization A q N₀ data hKr k red hα hβ) (R : ProlongationTuple P)
    (hιA : ∀ a : O, ιO a ∈ A)
    [hint : IsIntegral (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)))]
    (x₀ : ↥(pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))))
    (φ : ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField) →+* ↥(modularFunctionFieldBar (N₀ * q)))
    (hφO : ∀ a : O, φ (thetaO N₀ q O ρO x₀ a) = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q)) (ιO a))
    [hne : Nonempty (Scheme.Opens.toScheme ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹ᵁ
            ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)))]
    (hφj : ∀ a : ↥(IgusaScheme.chartAlgFin (N₀ * q) q), ((φ (psi N₀ q O ρO a) : ↥(modularFunctionFieldBar (N₀ * q))) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ))

    (W : Fin 2 → ValuationSubring ↥(modularFunctionFieldFull (N₀ * q)))
    (hW1 : ∀ f : ↥(modularFunctionFieldFull (N₀ * q)), f ∈ W 0 ↔
        ∃ x y : LaurentSeries ℤ, coeffMap (Int.castRingHom (ZMod q)) y ≠ 0 ∧
          (f : LaurentSeries ℚ) * coeffMap (Int.castRingHom ℚ) y = coeffMap (Int.castRingHom ℚ) x)
    (hW2 : ∀ f : ↥(modularFunctionFieldFull (N₀ * q)), f ∈ W 1 ↔ atkinLehnerInvolutionFull N₀ q f ∈ W 0)
    (hW4 : ∀ i, ((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ∈ (W i).nonunits ∧
        (∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod q)) ≠ 0 →
          Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull (N₀ * q)))
              ⟨jq, modularFunctionField_le_full (N₀ * q) (jq_mem (N₀ * q))⟩ P ∈ W i ∧
            (Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull (N₀ * q)))
              ⟨jq, modularFunctionField_le_full (N₀ * q) (jq_mem (N₀ * q))⟩ P)⁻¹ ∈ W i) ∧
        (∀ f ∈ (W i).nonunits, f * ((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q)))⁻¹ ∈ W i))
    (hW5 : ∀ V : ValuationSubring ↥(modularFunctionFieldFull (N₀ * q)),
        ((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ∈ V.nonunits →
        (∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod q)) ≠ 0 →
          Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull (N₀ * q)))
              ⟨jq, modularFunctionField_le_full (N₀ * q) (jq_mem (N₀ * q))⟩ P ∈ V ∧
            (Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull (N₀ * q)))
              ⟨jq, modularFunctionField_le_full (N₀ * q) (jq_mem (N₀ * q))⟩ P)⁻¹ ∈ V) →
        V = W 0 ∨ V = W 1)

    (hsep : ∃ a : ↥(IgusaScheme.chartAlgFin (N₀ * q) q),
      ¬ (((a : ↥(modularFunctionFieldFull (N₀ * q))) ∈ (W 0).nonunits) ↔ ((a : ↥(modularFunctionFieldFull (N₀ * q))) ∈ (W 1).nonunits)))

    (ξ : ↥(pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))))
    (hξU : ξ ∈ (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹ᵁ 𝔛.smoothLocus)
    (hξs : ξ ∉ (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens))
    (hmax : ∀ y : ↥(pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))), y ∉ (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) → y ⤳ ξ → y = ξ)

    (𝔮 : PrimeSpectrum ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
    (h𝔮 : (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).base ξ = (IgusaScheme.ιFin (N₀ * q) q).base 𝔮)
    (i : Fin 2)
    (hcentre : ∀ a : ↥(IgusaScheme.chartAlgFin (N₀ * q) q), a ∈ 𝔮.asIdeal ↔ ((a : ↥(modularFunctionFieldFull (N₀ * q))) ∈ (W i).nonunits))

    (Vside : ValuationSubring ↥(modularFunctionFieldBar (N₀ * q)))
    (hVside : Vside = if i = 0 then R.R₁.integers else R.R₂.integers) :
    ∀ u : (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk ξ,
      φ (algebraMap _ ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField) u) ∈ Vside ∧
        (u ∈ IsLocalRing.maximalIdeal _ → φ (algebraMap _ ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField) u) ∈
          Vside.nonunits) := by
  classical

  obtain ⟨hDVR, hm⟩ := isDiscreteValuationRing_and_maximalIdeal_eq q 𝔛 O ρO hϖ ξ hξU hξs hmax
  haveI := hDVR
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  subst hVside

  obtain ⟨𝒱, h𝒱def⟩ : ∃ 𝒱 : ValuationSubring ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField), 𝒱 = valSub ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk ξ) ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField) := ⟨_, rfl⟩

  suffices h𝒱eq : 𝒱 = (if i = 0 then R.R₁.integers else R.R₂.integers).comap φ from
    forall_mem_and_of_valSub_eq φ _ (h𝒱def ▸ h𝒱eq)

  have hqmem : ((q : ℕ) : (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk ξ) ∈ IsLocalRing.maximalIdeal _ := by
    rw [hm]; exact Ideal.mem_span_singleton_self _
  have hqcoe : ((q : ℕ) : ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField)) = algebraMap ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk ξ) _ ((q : ℕ) : (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk ξ) :=
    (map_natCast _ q).symm
  have hp𝒱 : ((q : ℕ) : ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField)) ∈ 𝒱.nonunits := by
    rw [hqcoe, h𝒱def]; exact algebraMap_mem_nonunits_of_mem_maximalIdeal _ hqmem
  have hdisc : ∀ g ∈ 𝒱, g ≠ 0 → ∃ n : ℕ, ∃ u ∈ 𝒱, u⁻¹ ∈ 𝒱 ∧ g = ((q : ℕ) : ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField)) ^ n * u := by
    rw [h𝒱def]
    intro g hg hg0
    obtain ⟨n, u, hu, hui, e⟩ := exists_eq_pow_mul_of_maximalIdeal_eq _ hm g hg hg0
    exact ⟨n, u, hu, hui, by rw [hqcoe]; exact e⟩
  have hO𝒱 : ∀ a : O, thetaO N₀ q O ρO x₀ a ∈ 𝒱 := fun a =>
    h𝒱def ▸ (mem_valSub_iff _ _ _).mpr (thetaO_mem_range N₀ q O ρO x₀ ξ a)

  have hy : (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).base ξ ∈ (IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤ := by
    rw [h𝔮]; exact ⟨𝔮, trivial, rfl⟩

  have hgerm : ∀ a : ↥(IgusaScheme.chartAlgFin (N₀ * q) q),
      psi N₀ q O ρO a = algebraMap ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk ξ) _ (((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.germ _ ξ hy).hom (sec N₀ q O ρO a)) :=
    fun a => psi_eq_algebraMap_germ N₀ q O ρO ξ hy a
  have hgerm𝔪 : ∀ a : ↥(IgusaScheme.chartAlgFin (N₀ * q) q),
      ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.germ _ ξ hy).hom (sec N₀ q O ρO a) ∈ IsLocalRing.maximalIdeal _ ↔ a ∈ 𝔮.asIdeal :=
    fun a => AlgebraicGeometry.Scheme.germ_app_appIso_inv_mem_maximalIdeal_iff
      (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) (CommRingCat.of ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
      (IgusaScheme.ιFin (N₀ * q) q) ξ 𝔮 hy h𝔮.symm a
  have hψ𝒱 : ∀ a : ↥(IgusaScheme.chartAlgFin (N₀ * q) q), psi N₀ q O ρO a ∈ 𝒱 := fun a => by
    rw [hgerm, h𝒱def]; exact algebraMap_mem_valSub _ _ _
  have hψnu : ∀ a : ↥(IgusaScheme.chartAlgFin (N₀ * q) q), psi N₀ q O ρO a ∈ 𝒱.nonunits ↔ a ∈ 𝔮.asIdeal := fun a => by
    rw [hgerm, h𝒱def, algebraMap_mem_nonunits_iff, hgerm𝔪]

  have hjcoe : (⟨jq, modularFunctionField_le_full (N₀ * q) (jq_mem (N₀ * q))⟩ : ↥(modularFunctionFieldFull (N₀ * q))) =
      ((IgusaScheme.jChartFin (N₀ * q) q : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) := rfl
  have hevalA : ∀ Q : Polynomial ℤ,
      Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull (N₀ * q))) ⟨jq, modularFunctionField_le_full (N₀ * q) (jq_mem (N₀ * q))⟩ Q =
        ((Polynomial.eval₂ (algebraMap ℤ ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) (IgusaScheme.jChartFin (N₀ * q) q) Q :
          ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) := by
    intro Q
    have h := Polynomial.hom_eval₂ Q (algebraMap ℤ ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
      ((IgusaScheme.chartAlgFin (N₀ * q) q).val.toRingHom) (IgusaScheme.jChartFin (N₀ * q) q)
    have hint : ((IgusaScheme.chartAlgFin (N₀ * q) q).val.toRingHom).comp (algebraMap ℤ ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) =
        algebraMap ℤ ↥(modularFunctionFieldFull (N₀ * q)) := RingHom.ext_int _ _
    rw [hint] at h
    rw [hjcoe]
    exact h.symm
  have hθint : (thetaF N₀ q O ρO φ hφj).comp (algebraMap ℤ ↥(modularFunctionFieldFull (N₀ * q))) = algebraMap ℤ _ := RingHom.ext_int _ _
  have hψint : (psi N₀ q O ρO).comp (algebraMap ℤ ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) = algebraMap ℤ _ := RingHom.ext_int _ _
  have hevalK : ∀ Q : Polynomial ℤ,
      Polynomial.eval₂ (algebraMap ℤ ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField)) (thetaF N₀ q O ρO φ hφj ⟨jq, modularFunctionField_le_full (N₀ * q) (jq_mem (N₀ * q))⟩) Q =
        psi N₀ q O ρO (Polynomial.eval₂ (algebraMap ℤ ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) (IgusaScheme.jChartFin (N₀ * q) q) Q) := by
    intro Q
    rw [hjcoe, thetaF_coe, Polynomial.hom_eval₂, hψint]
  have hevalθ : ∀ Q : Polynomial ℤ,
      thetaF N₀ q O ρO φ hφj (Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull (N₀ * q))) ⟨jq, modularFunctionField_le_full (N₀ * q) (jq_mem (N₀ * q))⟩ Q) =
        Polynomial.eval₂ (algebraMap ℤ ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField)) (thetaF N₀ q O ρO φ hφj ⟨jq, modularFunctionField_le_full (N₀ * q) (jq_mem (N₀ * q))⟩) Q := by
    intro Q
    rw [Polynomial.hom_eval₂, hθint]

  have hj𝒱 : ∀ Q : Polynomial ℤ, Q.map (Int.castRingHom (ZMod q)) ≠ 0 →
      Polynomial.eval₂ (algebraMap ℤ ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField)) (thetaF N₀ q O ρO φ hφj ⟨jq, modularFunctionField_le_full (N₀ * q) (jq_mem (N₀ * q))⟩) Q ∈ 𝒱 ∧
        (Polynomial.eval₂ (algebraMap ℤ ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField)) (thetaF N₀ q O ρO φ hφj ⟨jq, modularFunctionField_le_full (N₀ * q) (jq_mem (N₀ * q))⟩) Q)⁻¹ ∈ 𝒱 := by
    intro Q hQ
    rw [hevalK]
    set a := Polynomial.eval₂ (algebraMap ℤ ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) (IgusaScheme.jChartFin (N₀ * q) q) Q with ha
    refine ⟨hψ𝒱 a, ?_⟩
    by_cases ha𝔮 : a ∈ 𝔮.asIdeal
    ·
      have hnu : ((a : ↥(modularFunctionFieldFull (N₀ * q))) ∈ (W i).nonunits) := (hcentre a).mp ha𝔮
      have hu := (hW4 i).2.1 Q hQ
      rw [hevalA] at hu
      rcases (W i).mem_nonunits_iff_or.mp hnu with h0 | h0
      · have ha0 : a = 0 := by exact_mod_cast h0
        rw [ha0, map_zero, inv_zero]; exact 𝒱.zero_mem
      · exact absurd hu.2 h0
    ·
      have hunit : IsUnit (((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.germ _ ξ hy).hom (sec N₀ q O ρO a)) := by
        by_contra hnu
        exact ha𝔮 ((hgerm𝔪 a).mp ((IsLocalRing.mem_maximalIdeal _).mpr hnu))
      obtain ⟨v, hv⟩ := hunit
      rw [hgerm, ← hv]
      have : (algebraMap ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk ξ) ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField) (v : (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk ξ))⁻¹ =
          algebraMap ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk ξ) ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField) ((v⁻¹ : ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk ξ)ˣ) : (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk ξ) := by
        rw [inv_eq_of_mul_eq_one_right]
        rw [← map_mul, Units.mul_inv, map_one]
      rw [this, h𝒱def]
      exact algebraMap_mem_valSub _ _ _

  have hqFb : ((q : ℕ) : ↥(modularFunctionFieldBar (N₀ * q))) ≠ 0 := NeZero.ne _
  have hqK : ((q : ℕ) : ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField)) ≠ 0 := by
    intro h
    have := congrArg φ h
    rw [map_natCast, map_zero] at this
    exact hqFb this
  have hpF : ((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ∈ (𝒱.comap (thetaF N₀ q O ρO φ hφj)).nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_or]
    refine Or.inr fun h' => ?_
    rw [ValuationSubring.mem_comap, map_inv₀, map_natCast] at h'
    rcases (𝒱.mem_nonunits_iff_or).mp hp𝒱 with h'' | h''
    · exact hqK h''
    · exact h'' h'
  have hnucomapF : ∀ f : ↥(modularFunctionFieldFull (N₀ * q)),
      f ∈ (𝒱.comap (thetaF N₀ q O ρO φ hφj)).nonunits ↔ thetaF N₀ q O ρO φ hφj f ∈ 𝒱.nonunits := fun f => by
    rw [(𝒱.comap (thetaF N₀ q O ρO φ hφj)).mem_nonunits_iff_or, 𝒱.mem_nonunits_iff_or,
      map_eq_zero_iff _ (thetaF N₀ q O ρO φ hφj).injective, ← map_inv₀, ValuationSubring.mem_comap]

  have hW𝒱 : 𝒱.comap (thetaF N₀ q O ρO φ hφj) = W 0 ∨ 𝒱.comap (thetaF N₀ q O ρO φ hφj) = W 1 := by
    refine hW5 _ hpF fun Q hQ => ?_
    rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap, map_inv₀, hevalθ]
    exact hj𝒱 Q hQ

  have hcomapnu : ∀ a : ↥(IgusaScheme.chartAlgFin (N₀ * q) q),
      ((a : ↥(modularFunctionFieldFull (N₀ * q))) ∈ (𝒱.comap (thetaF N₀ q O ρO φ hφj)).nonunits) ↔ a ∈ 𝔮.asIdeal := by
    intro a
    rw [hnucomapF, thetaF_coe, hψnu]
  have hi01 : i = 0 ∨ i = 1 := by
    rcases i with ⟨_ | _ | n, hn⟩
    · left; rfl
    · right; rfl
    · omega
  have htr : 𝒱.comap (thetaF N₀ q O ρO φ hφj) = W i := by
    obtain ⟨a, ha⟩ := hsep
    have e : ∀ j : Fin 2, 𝒱.comap (thetaF N₀ q O ρO φ hφj) = W j →
        ((((a : ↥(modularFunctionFieldFull (N₀ * q))) ∈ (W i).nonunits)) ↔ (((a : ↥(modularFunctionFieldFull (N₀ * q))) ∈ (W j).nonunits))) := by
      intro j hj
      rw [← hcentre, ← hcomapnu, hj]
    rcases hi01 with rfl | rfl
    · rcases hW𝒱 with h | h
      · exact h
      · exact absurd (e 1 h) ha
    · rcases hW𝒱 with h | h
      · exact absurd (e 0 h).symm ha
      · exact h

  exact core q O hϖ ιO P R hιA _ φ (thetaO N₀ q O ρO x₀) hφO (thetaF N₀ q O ρO φ hφj) (coe_phi_thetaF N₀ q O ρO φ hφj)
    (closure_range_thetaF_union_range_thetaO_eq_top N₀ q O ρO x₀ φ hφj) 𝒱 hp𝒱 hdisc hO𝒱 W hW1 hW2 hW4 i htr

end ValIdLevel

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
open Classical in

theorem solution

    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)
    {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime q)
    (ρ : DRLevel.R q →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (DRLevel.R q) (AlgebraicClosure ℚ))

    (𝔓 : DRModelPackageLevel N₀ q hqN)

    [CharP (ResidueField ↥A) q] [IsAlgClosed (ResidueField ↥A)] [DecidableEq (ResidueField ↥A)]

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (eO : O ≃+* ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))))
    (hϖO : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
    (ρO : DRLevel.R q →+* O)
    (hρO : ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
        (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom))).comp ρO =
      algebraMap (DRLevel.R q) (AlgebraicClosure ℚ))
    (toκ : O →+* (ResidueField ↥A))
    (htoκ : ∀ o : O, toκ o = (residue ↥A) ⟨algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ) ((eO o : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) : ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))), (eO o).2⟩)
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N₀ q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N₀ q}
    (P : PlaceSpecialization A q N₀ data hKr (ResidueField ↥A) (residue ↥A) hα hβ)
    (R : ProlongationTuple P)
    [hfib0 : AlgebraicGeometry.IsIntegral (DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO))]
    [hint : IsIntegral (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)))]
    (φ : ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField) →+* ↥(modularFunctionFieldBar (N₀ * q)))

    (hφO : ∀ a : O,
      φ (algebraMap ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk (((𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO))))) _
        (((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.germ ⊤ (((𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))) trivial).hom
          (((pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)))) =
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q)) (((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom))) a))

    [hne : Nonempty (Scheme.Opens.toScheme ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)))]
    (hφj : ∀ a : ↥(IgusaScheme.chartAlgFin (N₀ * q) q),
      ((φ ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).germToFunctionField ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤))
          (((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).app ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)).hom
            (((IgusaScheme.ιFin (N₀ * q) q).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).inv a)))) : ↥(modularFunctionFieldBar (N₀ * q))) :
          LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ))
    :
    (∀ u : (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk (((𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))),
      φ (algebraMap _ ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField) u) ∈ R.R₁.integers ∧
      (u ∈ IsLocalRing.maximalIdeal _ → φ (algebraMap _ ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField) u) ∈ R.R₁.integers.nonunits)) ∧
    (∀ u : (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk (((𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1) ≫ DRLevel.bcMap ρO toκ).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))),
      φ (algebraMap _ ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField) u) ∈ R.R₂.integers ∧
      (u ∈ IsLocalRing.maximalIdeal _ → φ (algebraMap _ ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField) u) ∈ R.R₂.integers.nonunits)) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

  obtain ⟨ιO, hιOdef⟩ : ∃ ιO : O →+* AlgebraicClosure ℚ, ιO =
      ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
        (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom))) := ⟨_, rfl⟩
  have hιA : ∀ a : O, ιO a ∈ A := fun a => by
    rw [hιOdef]
    exact (eO a).2

  have hφO' : ∀ a : O, φ (ValIdLevel.thetaO N₀ q O ρO (((𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))) a) =
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q)) (ιO a) := fun a => by
    rw [ValIdLevel.thetaO_apply, hιOdef]
    exact hφO a
  have hφj' : ∀ a : ↥(IgusaScheme.chartAlgFin (N₀ * q) q),
      ((φ (ValIdLevel.psi N₀ q O ρO a) : ↥(modularFunctionFieldBar (N₀ * q))) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) := hφj

  obtain ⟨W, hW1, hW2, hW3, hW4, hW5⟩ := ModularCurve.exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd N₀ q hqN
  obtain ⟨Pc, hPmem, hPprime, hPne, hPmin⟩ :=
    ModularCurve.DRModelPackageLevel.exists_minimalPrimes_chartAlgFin_span_eq_pair_of_valuationSubring_pair N₀ q hqN W hW1 hW2 hW3 hW4 hW5
  have hsep : ∃ a : ↥(IgusaScheme.chartAlgFin (N₀ * q) q),
      ¬ (((a : ↥(modularFunctionFieldFull (N₀ * q))) ∈ (W 0).nonunits) ↔ ((a : ↥(modularFunctionFieldFull (N₀ * q))) ∈ (W 1).nonunits)) := by
    by_contra h
    push_neg at h
    apply hPne
    ext a
    rw [hPmem 0 a, hPmem 1 a]
    exact h a

  obtain ⟨𝔮₀, h𝔮₀, hcentre₀⟩ := ModularCurve.DRModelPackageLevel.exists_fst_comp_zero_genericPoint_eq_iotaFin_and_mem_asIdeal_iff
    N₀ q hqN 𝔓 (W 0) hW1 (ResidueField ↥A) (toκ.comp ρO)
  obtain ⟨⟨𝔮₁, h𝔮₁⟩, -⟩ := ModularCurve.DRModelPackageLevel.exists_fst_comp_genericPoint_eq_iotaFin_and_eq_iotaInf
    N₀ q hqN 𝔓 (ResidueField ↥A) (toκ.comp ρO) 1
  obtain ⟨hminFin, -, hne01⟩ := ModularCurve.DRModelPackageLevel.mem_minimalPrimes_of_fst_comp_genericPoint_eq_and_fst_comp_ne
    N₀ q hqN 𝔓 (ResidueField ↥A) (toκ.comp ρO)
  have h𝔮₀' : (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0 ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (toκ.comp ρO)))).base
      (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO))) = (IgusaScheme.ιFin (N₀ * q) q).base 𝔮₀ := by
    rw [ValIdLevel.comp_base_apply']; exact h𝔮₀
  have h𝔮₀P : 𝔮₀.asIdeal = Pc 0 := by
    ext a; rw [hcentre₀ a, hPmem 0 a]
  have h𝔮ne : 𝔮₀ ≠ 𝔮₁ := by
    intro h
    apply hne01
    rw [h𝔮₀', h𝔮₁, h]
  have hcentre₁ : ∀ a : ↥(IgusaScheme.chartAlgFin (N₀ * q) q),
      a ∈ 𝔮₁.asIdeal ↔ ((a : ↥(modularFunctionFieldFull (N₀ * q))) ∈ (W 1).nonunits) := by
    have hmem : 𝔮₁.asIdeal ∈ ({Pc 0, Pc 1} : Set (Ideal ↥(IgusaScheme.chartAlgFin (N₀ * q) q))) := hPmin ▸ hminFin 1 𝔮₁ h𝔮₁
    rcases hmem with h | h
    · exact absurd (PrimeSpectrum.ext (h𝔮₀P.trans h.symm)) h𝔮ne
    · rw [Set.mem_singleton_iff] at h
      intro a
      rw [← hPmem 1 a, h]

  have hbcfst : DRLevel.bcMap ρO toκ ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)) =
      pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (toκ.comp ρO))) := by
    rw [DRLevel.bcMap]
    exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have hfstξ : ∀ i : Fin 2, (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).base
      ((((𝔓.comp (ResidueField ↥A) (toκ.comp ρO) i) ≫ DRLevel.bcMap ρO toκ).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO))))) =
      (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) i ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (toκ.comp ρO)))).base
        (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO))) := by
    intro i
    rw [← ValIdLevel.comp_base_apply', Category.assoc, hbcfst]
  obtain ⟨hU₀, hU₁⟩ := ModularCurve.DRModelPackageLevel.xi_mem_preimage_smoothLocus N₀ q hqN 𝔓 O ρO (ResidueField ↥A) toκ
  obtain ⟨hmax₀, hmax₁⟩ := ModularCurve.DRModelPackageLevel.eq_xi_of_specializes N₀ q hqN 𝔓 O ρO hϖO (ResidueField ↥A) toκ
  have hs : ∀ i : Fin 2, (((𝔓.comp (ResidueField ↥A) (toκ.comp ρO) i) ≫ DRLevel.bcMap ρO toκ).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))) ∉
      (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹ᵁ (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) := by
    intro i
    rw [ValIdLevel.comp_base_apply']
    exact ModularCurve.DRLevel.bcMap_apply_notMem_preimage_basicOpen N₀ q O ρO (ResidueField ↥A) toκ _
  refine ⟨?_, ?_⟩
  · exact ValIdLevel.branch N₀ q hqN 𝔓 O hϖO ρO ιO P R hιA (((𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))) φ hφO' hφj' W hW1 hW2 hW4 hW5 hsep
      (((𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))) hU₀ (hs 0) hmax₀ 𝔮₀ ((hfstξ 0).trans h𝔮₀') 0 hcentre₀ R.R₁.integers (if_pos rfl).symm
  · exact ValIdLevel.branch N₀ q hqN 𝔓 O hϖO ρO ιO P R hιA (((𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))) φ hφO' hφj' W hW1 hW2 hW4 hW5 hsep
      (((𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1) ≫ DRLevel.bcMap ρO toκ).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))) hU₁ (hs 1) hmax₁ 𝔮₁ ((hfstξ 1).trans h𝔮₁) 1 hcentre₁ R.R₂.integers (if_neg (by decide)).symm

end S_ModularCurve_DRModelPackageLevel_phi_algebraMap_stalk_mem_integers_comp_genericPoint
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_phi_algebraMap_stalk_mem_integers_comp_genericPoint (solution)
