-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/6f0636ee-857f-53b4-a4bc-0e009e413dd6

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_FrobeniusEndo
import Definitions.Def_AlgebraicCurve_FrobeniusEndoPic0
import Definitions.Def_ModularCurve_KroneckerTransport
import Definitions.Def_ModularCurve_FibrePoly
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_ModularCurve_QAdicPlaceMod
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_RatPointMap_probe
import Definitions.Def_WeierstrassCurve_RatPointHom
import Definitions.Def_ModularCurve_ModuliPoint
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_ModularCurve_AtkinLehner
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_LevelOneAnnulusSpecialization
import Definitions.Def_FreyPackage_GaloisRep
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_FinitePlaceLift
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_LevelOneChartFst
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_UVCrossingGaussOrder
import Definitions.Def_ModularCurve_UVCrossingDominantIndices
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_RiemannRochRows
import Definitions.Def_ModularCurve_ProlongationTupleSmoothPoint
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Theorems.Thm_AlgebraicCurve_Annulus_abv_evalAt_lt_one_of_isAttached_of_ord_residue_pos
import Theorems.Thm_AlgebraicCurve_Annulus_abv_modulus_zpow_ord_residue_le_abv_of_isAttached_both_ends
import Theorems.Thm_AlgebraicCurve_Annulus_abv_mul_abv_modulus_zpow_ord_residue_le_one_of_isAttached_both_ends
import Theorems.Thm_AlgebraicCurve_Annulus_ord_residue_add_nonneg_and_abv_le_one_of_isAttached_both_ends
import Theorems.Thm_AlgebraicCurve_Annulus_sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_AlgebraicCurve_exists_weilCanonical_riemannRoch
import Theorems.Thm_Finsupp_exists_eq_sum_single_of_mapDomain_eq_sum_single
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_chartFstSupply_of_isModel
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_tubeEquation_smul_sub_self_of_annulus
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatum_exists_nodePackage_over
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_hasValue_of_mem_smoothLocalRingFst_levelOne
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_hasValue_of_mem_smoothLocalRingSnd
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_hasValue_of_mem_smoothLocalRingSnd_levelOne
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_crossingExponent_eq_placeWidth_mul_of_orderLawFixed_levelOne
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_oneSided_levelOne
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawZero_oneSided_levelOne
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_divisorLawFst_oneSided_levelOne
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_divisorLawSnd_oneSided_levelOne
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_ringEquiv_adicCompletion_nodeIntegersOver_uvCrossingModel_of_isMaximal
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_slopeDrop_eq_sum_div_depth_of_sum_div_reduceFst_eq
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_gaussOrder_fst_end_ringEquiv_adicCompletion_eq_add_of_eq_nodeConst_pow_mul
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_gaussOrder_snd_end_ringEquiv_adicCompletion_eq_add_of_eq_nodeConst_pow_mul
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_iota_bijective
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_redBar_bijective
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_regularityLawFst_oneSided_levelOne
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_regularityLawSnd_oneSided_levelOne
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_div_reduceFst_le_ord_residueFst_add_ord_residueSnd
import Theorems.Thm_ModularCurve_PlaceSpecialization_centred_of_reduceFst_eq_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_isStrictFst_isStrictSnd_general_position_disjoint_forall_inertia_smul_eq
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_levelOneProlongationPair_of_prolongationTuple
import Theorems.Thm_ModularCurve_PlaceSpecialization_not_fixed_reduceFst_of_isStrictSnd
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_eq_charLGeomPlaceOfPoint_iff
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_eq_charLGeomPlaceOfPoint_of_ord_pos
import Theorems.Thm_ModularCurve_PlaceSpecialization_redSnd_eq_charLGeomPlaceOfPoint_of_ord_pos
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceFst_eq_iff_centred_levelOne
import Theorems.Thm_ModularCurve_UVCrossingModel_sInf_dominantIndices_eq_of_sub_mul_U_pow_mem
import Theorems.Thm_ModularCurve_UVCrossingModel_sSup_dominantIndices_eq_neg_of_sub_mul_V_pow_mem
import Theorems.Thm_ModularCurve_arithFrobC_smul_arithFrobC_smul_eq_self_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_eq_zero_of_mem_ssJSet_three
import Theorems.Thm_ModularCurve_eq_zero_of_mem_ssJSet_two
import Theorems.Thm_ModularCurve_essFiniteType_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_exists_effective_pic0Mk_sub_eq_of_genusFF_le_degree
import Theorems.Thm_ModularCurve_exists_eq_algebraMap_of_hasValue_smul_of_generalPosition
import Theorems.Thm_ModularCurve_exists_ssAnnulus_centred_ofNat1728_of_crossingPresentation_of_branchPrimes
import Theorems.Thm_ModularCurve_exists_ssAnnulus_centred_of_widthOne
import Theorems.Thm_ModularCurve_exists_ssAnnulus_centred_of_widthOne_level
import Theorems.Thm_ModularCurve_exists_ssAnnulus_centred_zero_of_crossingPresentation_of_branchPrimes
import Theorems.Thm_ModularCurve_exists_ssAnnulus_oppAnnulus_isAttached_of_chartSpec_of_eq_zero_or_eq_ofNat1728
import Theorems.Thm_ModularCurve_exists_ssAnnulus_oppAnnulus_isAttached_of_chartSpec_of_eq_zero_or_eq_ofNat1728_levelOne
import Theorems.Thm_ModularCurve_finite_setOf_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self
import Theorems.Thm_ModularCurve_finite_setOf_ord_jGeomGen_sub_pos
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_charLGeomPlaceOfPoint
import Theorems.Thm_ModularCurve_genusFF_modularFunctionFieldBar_mul_add_one_eq_of_ssPlaces
import Theorems.Thm_ModularCurve_genusFF_modularFunctionFieldC_one_eq_zero
import Theorems.Thm_ModularCurve_isAffineGeomPlace_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_levelOne
import Theorems.Thm_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne
import Theorems.Thm_ModularCurve_isAttached_ssAnnulus_zeroChart_of_chartSpec_levelOne
import Theorems.Thm_ModularCurve_isAttached_ssAnnulus_zeroChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_mem_ssJSet_map_of_isAlgClosed
import Theorems.Thm_ModularCurve_mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceOfPoint_aeval_jqModC_eq_rootMultiplicity
import Theorems.Thm_ModularCurve_pow_mem_ssJSet_iff_of_perfectField
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Theorems.Thm_ModularCurve_slopeLaw_oppAnnulus_inftyChart_of_chartSpec_levelOne
import Theorems.Thm_ModularCurve_slopeLaw_ssAnnulus_zeroChart_of_chartSpec_levelOne
import Theorems.Thm_ModularCurve_ssPlaces_nonempty
import Theorems.Thm_ValuationSubring_exists_absoluteValue_isNonarchimedean_mem_iff_le_one_of_liesOverPrime
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ModularCurve_isAttached_ssAnnulus_zeroChart_of_chartSpec_levelOne_univ
import Theorems.Thm_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_levelOne_univ
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_modularLocalizedAtPoint_iff_exists_mem_nodeIntegersOver
import Theorems.Thm_ModularCurve_isAttached_ssAnnulus_zeroChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne_univ
import Theorems.Thm_ModularCurve_isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne_univ
import Theorems.Thm_ModularCurve_exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residue_jFun_jqFun
import Theorems.Thm_ModularCurve_geomAut_atkinLehnerInvolutionFull_one_eq_frickeInvolutionBar
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeDepths_lt_one_and_partition_of_nodeEquation_of_orderLawFixed
import Theorems.Thm_ModularCurve_arithFrobC_smul_mem_ssPlaces_univ
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_valuation_coe_lt_one_of_maximalIdeal_eq_span
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ValuationSubring.instIsAlgClosedResidueField ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne"
p2m_attr_erase "instance" "ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar AlgebraicCurve.GaussReduction.isLocalHom_constToGauss ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.numberField_of_finiteDimensional AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.tateLaurent_a₆"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one"
p2m_attr_erase "simp" "TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.NodeLocalized.coe_modularEvalAt"
p2m_attr_erase "simp" "ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.ProjectiveLine.map_mk AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk"
p2m_attr_erase "simp" "WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂ AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers ModularCurve.frobeniusPullbackGeomLevelUnconditional_single ModularCurve.frobeniusPushforwardGeomLevelUnconditional_single ModularCurve.frobeniusGeomLevelUnconditional_apply_coe ModularCurve.symPoly_zero AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

set_option synthInstance.maxHeartbeats 1600000

noncomputable section
namespace ChartOkChartFst

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~coeffMap_injective P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve.PlaceSpecialization.ProlongationTuple"
open Classical

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

local notation "Qb" => AlgebraicClosure ℚ

def restrictConstants {κ : Type*} [Field κ] {F : Type*} [Field F] [Algebra k F] [Algebra κ F]
    (σ : κ →+* k) (hσ : ∀ c, algebraMap κ F c = algebraMap k F (σ c)) (v : Place k F) : Place κ F where
  toValuationSubring := v.toValuationSubring
  algebraMap_mem' c := by rw [hσ]; exact v.algebraMap_mem' (σ c)
  ne_top' := v.ne_top'
  isPrincipalIdealRing' := v.isPrincipalIdealRing'

@[scoped simp] theorem restrictConstants_toValuationSubring {κ : Type*} [Field κ] {F : Type*} [Field F] [Algebra k F]
    [Algebra κ F] (σ : κ →+* k) (hσ : ∀ c, algebraMap κ F c = algebraMap k F (σ c)) (v : Place k F) :
    (restrictConstants σ hσ v).toValuationSubring = v.toValuationSubring := rfl

theorem restrictConstants_injective {κ : Type*} [Field κ] {F : Type*} [Field F] [Algebra k F]
    [Algebra κ F] (σ : κ →+* k) (hσ : ∀ c, algebraMap κ F c = algebraMap k F (σ c)) :
    Function.Injective (restrictConstants σ hσ) := by
  intro v w h
  have : (restrictConstants σ hσ v).toValuationSubring = (restrictConstants σ hσ w).toValuationSubring := by rw [h]
  exact Place.ext this

theorem restrictConstants_surjective {κ : Type*} [Field κ] {F : Type*} [Field F] [Algebra k F]
    [Algebra κ F] (σ : κ →+* k) (hσ : ∀ c, algebraMap κ F c = algebraMap k F (σ c)) (hsurj : Function.Surjective σ) :
    Function.Surjective (restrictConstants σ hσ) := by
  intro w
  refine ⟨{ toValuationSubring := w.toValuationSubring
            algebraMap_mem' := fun c => by obtain ⟨c', rfl⟩ := hsurj c; rw [← hσ]; exact w.algebraMap_mem' c'
            ne_top' := w.ne_top'
            isPrincipalIdealRing' := w.isPrincipalIdealRing' }, ?_⟩
  exact Place.ext rfl

variable {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : ProlongationTuple P)

def algebraResidueField : Algebra (ResidueField A) (modularFunctionFieldC k 1) := ((algebraMap k (modularFunctionFieldC k 1)).comp R.redBar).toAlgebra

theorem algebraMap_residueField_eq (c : ResidueField A) :
    letI := algebraResidueField R
    algebraMap (ResidueField A) (modularFunctionFieldC k 1) c = algebraMap k (modularFunctionFieldC k 1) (R.redBar c) := rfl

def rc (v : Place k (modularFunctionFieldC k 1)) :
    letI := algebraResidueField R; Place (ResidueField A) (modularFunctionFieldC k 1) :=
  letI := algebraResidueField R; restrictConstants R.redBar (fun _ => rfl) v

theorem rc_injective : Function.Injective (rc R) := by
  letI := algebraResidueField R
  exact restrictConstants_injective R.redBar (fun _ => rfl)

theorem rc_surjective : Function.Surjective (rc R) := by
  letI := algebraResidueField R
  exact restrictConstants_surjective R.redBar (fun _ => rfl) (ProlongationTuple.redBar_bijective R).2

theorem rc_toValuationSubring (v : Place k (modularFunctionFieldC k 1)) :
    letI := algebraResidueField R; (rc R v).toValuationSubring = v.toValuationSubring := rfl

theorem ord_rc (v : Place k (modularFunctionFieldC k 1)) (g : (modularFunctionFieldC k 1)) :
    letI := algebraResidueField R; (rc R v).ord g = v.ord g := rfl

theorem iota_algebraMap (x : ResidueField A) :
    letI := algebraResidueField R
    R.ι (algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1) x)
      = algebraMap (ResidueField A) ↥(modularFunctionFieldC k 1) x := by
  apply Subtype.ext
  rw [R.ι_coe]
  change coeffMap R.redBar (algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) x)
    = algebraMap k (LaurentSeries k) (R.redBar x)
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

theorem algebraMap_rc_residueField (v : Place k (modularFunctionFieldC k 1)) (x : ResidueField A) :
    letI := algebraResidueField R
    algebraMap (ResidueField A) (rc R v).ResidueField x = algebraMap k v.ResidueField (R.redBar x) := by
  letI := algebraResidueField R
  rw [← (rc R v).residue_algebraMap x, ← v.residue_algebraMap (R.redBar x)]
  rfl

noncomputable def fixedPlaces (P : PlaceSpecialization A q 1 data hKr k red hα hβ) : Finset (Place k (modularFunctionFieldC k 1)) :=
  (ModularCurve.finite_setOf_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self k 1 data hKr).toFinset

theorem mem_fixedPlaces_iff (v : Place k (modularFunctionFieldC k 1)) :
    v ∈ fixedPlaces P ↔ frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) = v := by
  rw [fixedPlaces, Set.Finite.mem_toFinset]; rfl

set_option maxHeartbeats 6400000 in

noncomputable def chartFst (hR : R.IsModel) [HasPrincipalDivisors Qb (modularFunctionFieldBar (1 * q))] :
    letI := algebraResidueField R; ComponentChart A (modularFunctionFieldBar (1 * q)) (modularFunctionFieldC k 1) := by
  letI := algebraResidueField R
  exact
  { integers := R.R₁.integers
    residue := R.residue₁
    dom := {V | P.IsStrictFst V}
    nodes := (fixedPlaces P).image (rc R)
    placeMap := fun V => rc R (P.reduceFst V)
    algebraMap_mem_iff := R.R₁.algebraMap_mem_iff
    residue_surjective := (ProlongationTuple.iota_bijective R).2.comp R.R₁.residue_surjective
    ker_residue := by
      rw [← R.R₁.ker_residue]
      ext x
      simp only [RingHom.mem_ker, residue₁_apply, map_eq_zero_iff _ (ProlongationTuple.iota_bijective R).1]
    residue_algebraMap := fun a => by
      rw [residue₁_apply, R.R₁.residue_algebraMap]
      exact iota_algebraMap R _
    exists_smul_mem := fun f hf => by
      obtain ⟨c, h, hres⟩ := R.R₁.exists_smul_mem f hf
      exact ⟨c, h, fun h0 => hres ((map_eq_zero_iff _ (ProlongationTuple.iota_bijective R).1).mp h0)⟩
    placeMap_not_mem_nodes := fun V hV hn => by
      obtain ⟨v, hv, hvV⟩ := Finset.mem_image.mp hn
      have hvv : v = P.reduceFst V := rc_injective R hvV
      rw [mem_fixedPlaces_iff] at hv
      exact hV.2 (hvv ▸ hv)
    pointwise := fun V hV _ f hf hfib => by
      have hr : f ∈ R.smoothLocalRingFst (P.reduceFst V) := by
        rw [R.mem_smoothLocalRingFst_iff]
        exact ⟨hf, fun W hW hWV => hfib W hW (by show rc R (P.reduceFst W) = rc R (P.reduceFst V); rw [hWV])⟩
      obtain ⟨c, hc, hv⟩ := hR.exists_hasValue_of_mem_smoothLocalRingFst_levelOne hV f hf hr
      have hev : V.evalAt f = (c : AlgebraicClosure ℚ) := by
        rw [V.evalAt_of_mem hc.mem, hc.residue_eq, Place.residueInv_algebraMap]
      have hcA : V.evalAt f ∈ A := hev ▸ c.2
      refine ⟨hv.mem, hcA, ?_⟩
      have hcc : (⟨V.evalAt f, hcA⟩ : ↥A) = c := Subtype.ext hev
      rw [hcc, algebraMap_rc_residueField, R.redBar_residue]
      exact hv.residue_eq.symm
    mapDomain_placeMap := fun f hres D hD hD0 Q hQ => by
      obtain ⟨v, rfl⟩ := rc_surjective R Q
      have hfix : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) ≠ v := by
        intro h
        exact hQ (Finset.mem_image.mpr ⟨v, (mem_fixedPlaces_iff v).mpr h, rfl⟩)
      have hres₁ : R.R₁.residue f ≠ 0 := fun h0 => hres (by rw [residue₁_apply, h0, map_zero])
      have hf0 : (f : ↥(modularFunctionFieldBar (1 * q))) ≠ 0 := by
        intro h; apply hres₁
        have : f = 0 := Subtype.ext h
        rw [this, map_zero]
      obtain ⟨D', hD', -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) (f : ↥(modularFunctionFieldBar (1 * q))) hf0
      have hlaw := ProlongationTuple.divisorLawFst_oneSided_levelOne P R hR f.1 f.2 hres₁ D' hD' v hfix

      have hDD : D = D'.filter P.IsStrictFst := by
        ext W
        rw [Finsupp.filter_apply]
        by_cases hW : P.IsStrictFst W
        · rw [if_pos hW, hD W hW, hD' W]
        · rw [if_neg hW, hD0 W hW]
      have hcomp : (fun V => rc R (P.reduceFst V)) = rc R ∘ P.reduceFst := rfl
      rw [hcomp, Finsupp.mapDomain_comp, Finsupp.mapDomain_apply (rc_injective R), hDD, hlaw]
      rfl }

section Unfold
variable (hR : R.IsModel) [HasPrincipalDivisors Qb (modularFunctionFieldBar (1 * q))]

theorem chartFst_integers : letI := algebraResidueField R; (chartFst R hR).integers = R.R₁.integers := rfl
theorem chartFst_residue : letI := algebraResidueField R; (chartFst R hR).residue = R.residue₁ := rfl
theorem chartFst_dom : letI := algebraResidueField R; (chartFst R hR).dom = {V | P.IsStrictFst V} := rfl
theorem chartFst_nodes : letI := algebraResidueField R; (chartFst R hR).nodes = (fixedPlaces P).image (rc R) := rfl
theorem chartFst_placeMap (V : Place Qb ↥(modularFunctionFieldBar (1 * q))) :
    letI := algebraResidueField R; (chartFst R hR).placeMap V = rc R (P.reduceFst V) := rfl

theorem rc_mem_nodes_of_fixed (v : Place k (modularFunctionFieldC k 1))
    (hv : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) = v) :
    letI := algebraResidueField R; rc R v ∈ (chartFst R hR).nodes :=
  Finset.mem_image.mpr ⟨v, (mem_fixedPlaces_iff v).mpr hv, rfl⟩

theorem rc_mem_nodes_of_mem_ssPlaces (v : Place k (modularFunctionFieldC k 1)) (hv : v ∈ ssPlaces q 1 k) :
    letI := algebraResidueField R; rc R v ∈ (chartFst R hR).nodes := by
  apply rc_mem_nodes_of_fixed
  obtain ⟨a, ha, rfl⟩ := (ModularCurve.mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq q k v).mp hv
  rw [ModularCurve.frobOnPlacesGeomLevel_charLGeomPlaceOfPoint, ModularCurve.frobOnPlacesGeomLevel_charLGeomPlaceOfPoint,
    ← pow_mul, ← sq, ModularCurve.pow_q_sq_eq_self_of_mem_ssJSet q ha]

end Unfold

end ChartOkChartFst
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"
end
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"

noncomputable section
namespace ChartOkChartFst

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~coeffMap_injective P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve.PlaceSpecialization.ProlongationTuple"
open Classical

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : ProlongationTuple P)

local notation "Qb" => AlgebraicClosure ℚ

set_option maxHeartbeats 6400000 in

noncomputable def chartSnd (hR : R.IsModel) [HasPrincipalDivisors Qb (modularFunctionFieldBar (1 * q))] :
    letI := algebraResidueField R; ComponentChart A (modularFunctionFieldBar (1 * q)) (modularFunctionFieldC k 1) := by
  letI := algebraResidueField R
  exact
  { integers := R.R₂.integers
    residue := R.residue₂
    dom := {V | P.IsStrictSnd V}
    nodes := (fixedPlaces P).image (rc R)
    placeMap := fun V => rc R (P.reduceSnd V)
    algebraMap_mem_iff := R.R₂.algebraMap_mem_iff
    residue_surjective := (ProlongationTuple.iota_bijective R).2.comp R.R₂.residue_surjective
    ker_residue := by
      rw [← R.R₂.ker_residue]
      ext x
      simp only [RingHom.mem_ker, residue₂_apply, map_eq_zero_iff _ (ProlongationTuple.iota_bijective R).1]
    residue_algebraMap := fun a => by
      rw [residue₂_apply, R.R₂.residue_algebraMap]
      exact iota_algebraMap R _
    exists_smul_mem := fun f hf => by
      obtain ⟨c, h, hres⟩ := R.R₂.exists_smul_mem f hf
      exact ⟨c, h, fun h0 => hres ((map_eq_zero_iff _ (ProlongationTuple.iota_bijective R).1).mp h0)⟩
    placeMap_not_mem_nodes := fun V hV hn => by
      obtain ⟨v, hv, hvV⟩ := Finset.mem_image.mp hn
      have hvv : v = P.reduceSnd V := rc_injective R hvV
      rw [mem_fixedPlaces_iff] at hv
      exact hV.2 (hvv ▸ hv)
    pointwise := fun V hV _ f hf hfib => by
      have hr : f ∈ R.smoothLocalRingSnd (P.reduceSnd V) := by
        rw [R.mem_smoothLocalRingSnd_iff]
        exact ⟨hf, fun W hW hWV => hfib W hW (by show rc R (P.reduceSnd W) = rc R (P.reduceSnd V); rw [hWV])⟩
      obtain ⟨c, hc, hv⟩ := hR.exists_hasValue_of_mem_smoothLocalRingSnd_levelOne hV f hf hr
      have hev : V.evalAt f = (c : AlgebraicClosure ℚ) := by
        rw [V.evalAt_of_mem hc.mem, hc.residue_eq, Place.residueInv_algebraMap]
      have hcA : V.evalAt f ∈ A := hev ▸ c.2
      refine ⟨hv.mem, hcA, ?_⟩
      have hcc : (⟨V.evalAt f, hcA⟩ : ↥A) = c := Subtype.ext hev
      rw [hcc, algebraMap_rc_residueField, R.redBar_residue]
      exact hv.residue_eq.symm
    mapDomain_placeMap := fun f hres D hD hD0 Q hQ => by
      obtain ⟨v, rfl⟩ := rc_surjective R Q
      have hfix : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) ≠ v := by
        intro h
        exact hQ (Finset.mem_image.mpr ⟨v, (mem_fixedPlaces_iff v).mpr h, rfl⟩)
      have hres₂ : R.R₂.residue f ≠ 0 := fun h0 => hres (by rw [residue₂_apply, h0, map_zero])
      have hf0 : (f : ↥(modularFunctionFieldBar (1 * q))) ≠ 0 := by
        intro h; apply hres₂
        have : f = 0 := Subtype.ext h
        rw [this, map_zero]
      obtain ⟨D', hD', -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) (f : ↥(modularFunctionFieldBar (1 * q))) hf0
      have hlaw := ProlongationTuple.divisorLawSnd_oneSided_levelOne P R hR f.1 f.2 hres₂ D' hD' v hfix
      have hDD : D = D'.filter P.IsStrictSnd := by
        ext W
        rw [Finsupp.filter_apply]
        by_cases hW : P.IsStrictSnd W
        · rw [if_pos hW, hD W hW, hD' W]
        · rw [if_neg hW, hD0 W hW]
      have hcomp : (fun V => rc R (P.reduceSnd V)) = rc R ∘ P.reduceSnd := rfl
      rw [hcomp, Finsupp.mapDomain_comp, Finsupp.mapDomain_apply (rc_injective R), hDD, hlaw]
      rfl }

section UnfoldSnd
variable (hR : R.IsModel) [HasPrincipalDivisors Qb (modularFunctionFieldBar (1 * q))]

theorem chartSnd_integers : letI := algebraResidueField R; (chartSnd R hR).integers = R.R₂.integers := rfl
theorem chartSnd_residue : letI := algebraResidueField R; (chartSnd R hR).residue = R.residue₂ := rfl
theorem chartSnd_dom : letI := algebraResidueField R; (chartSnd R hR).dom = {V | P.IsStrictSnd V} := rfl
theorem chartSnd_nodes : letI := algebraResidueField R; (chartSnd R hR).nodes = (fixedPlaces P).image (rc R) := rfl
theorem chartSnd_placeMap (V : Place Qb ↥(modularFunctionFieldBar (1 * q))) :
    letI := algebraResidueField R; (chartSnd R hR).placeMap V = rc R (P.reduceSnd V) := rfl

theorem rc_mem_nodes_chartSnd_of_mem_ssPlaces (v : Place k (modularFunctionFieldC k 1)) (hv : v ∈ ssPlaces q 1 k) :
    letI := algebraResidueField R; rc R v ∈ (chartSnd R hR).nodes :=
  rc_mem_nodes_of_mem_ssPlaces R hR v hv

end UnfoldSnd
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"

end ChartOkChartFst
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"
end
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"

section Dictionaries
p2m_open "ModularCurve~coeffMap_injective P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve ModularCurve.CharPReduction"
namespace FltWs21
namespace RedIndep

theorem coeffMap_comp {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    coeffMap (g.comp f) = (coeffMap g).comp (coeffMap f) :=
  RingHom.ext (congrFun rfl)

theorem coeffMap_injective {S T : Type*} [CommRing S] [CommRing T] (g : S →+* T) (hg : Function.Injective g) :
    Function.Injective (coeffMap g) := by
  intro x y h
  ext n
  apply hg
  have := congrArg (fun z : LaurentSeries T => z.coeff n) h
  exact this

variable {L : Type*} [CommRing L] {k₀ k : Type*} [Field k₀] [Field k] {A : Subring L}
  (red₀ : A →+* k₀) (σ : k₀ →+* k)
  (R : Subring (LaurentSeries L)) (hR : R ≤ integralCoeffs A)

theorem coeffRed_comp : coeffRed A (σ.comp red₀) = (coeffMap σ).comp (coeffRed A red₀) := by
  unfold coeffRed
  rw [coeffMap_comp]
  rfl

theorem redRes_comp (r : R) : redRes A (σ.comp red₀) R hR r = coeffMap σ (redRes A red₀ R hR r) := by
  rw [redRes_apply, redRes_apply, coeffRed_comp]
  rfl

theorem redKer_comp : redKer A (σ.comp red₀) R hR = redKer A red₀ R hR := by
  ext s
  simp only [redKer, RingHom.mem_ker]
  rw [redRes_comp]
  constructor
  · intro h
    apply coeffMap_injective σ σ.injective
    rw [h, map_zero]
  · intro h
    rw [h, map_zero]

theorem localizedAtKer_comp : localizedAtKer A (σ.comp red₀) R hR = localizedAtKer A red₀ R hR := by
  ext f
  rw [mem_localizedAtKer, mem_localizedAtKer, redKer_comp]

theorem redLocHom_comp (f : LaurentSeries L) (hf₀ : f ∈ localizedAtKer A red₀ R hR)
    (hf : f ∈ localizedAtKer A (σ.comp red₀) R hR) :
    redLocHom (A := A) (red := σ.comp red₀) (R := R) (hR := hR) ⟨f, hf⟩ =
      coeffMap σ (redLocHom (A := A) (red := red₀) (R := R) (hR := hR) ⟨f, hf₀⟩) := by
  have hf₀' := hf₀
  obtain ⟨r, s, hs, hfs⟩ := hf₀'
  have h1 := redLoc_spec (A := A) (red := σ.comp red₀) (R := R) (hR := hR) ⟨f, hf⟩ (r := r) (s := s) hfs
  have h0 := redLoc_spec (A := A) (red := red₀) (R := R) (hR := hR) ⟨f, hf₀⟩ (r := r) (s := s) hfs
  rw [redLocHom_apply, redLocHom_apply]
  have hsne : redRes A (σ.comp red₀) R hR s ≠ 0 := by
    rw [← notMem_redKer_iff, redKer_comp]; exact hs
  apply mul_right_cancel₀ hsne
  rw [h1, redRes_comp, redRes_comp, ← map_mul, h0]

end FltWs21.RedIndep
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"

namespace FltWs21
namespace RedIndep

variable (N : ℕ) [NeZero N] {L : Type*} [CommRing L] (A : Subring L) {k₀ k : Type*} [Field k₀] [Field k]
  (red₀ : A →+* k₀) (σ : k₀ →+* k)

theorem modularLocalized_comp : modularLocalized N A (σ.comp red₀) = modularLocalized N A red₀ :=
  localizedAtKer_comp red₀ σ _ _

theorem modularRedLocHom_comp (f : LaurentSeries L) (hf₀ : f ∈ modularLocalized N A red₀)
    (hf : f ∈ modularLocalized N A (σ.comp red₀)) :
    modularRedLocHom N A (σ.comp red₀) ⟨f, hf⟩ = coeffMap σ (modularRedLocHom N A red₀ ⟨f, hf₀⟩) :=
  redLocHom_comp red₀ σ _ _ f hf₀ hf

end FltWs21.RedIndep
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"

p2m_open "AlgebraicCurve ModularCurve~coeffMap_injective P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve Polynomial"
namespace FltWs21
namespace OrdExt

theorem coeffMap_jqModC {κ k : Type*} [Field κ] [Field k] (σ : κ →+* k) : coeffMap σ (jqModC κ) = jqModC k := by
  rw [jqModC_eq_map_intCast κ, jqModC_eq_map_intCast k]
  change HahnSeries.map (HahnSeries.map (jqModC ℤ) (Int.castRingHom κ)) σ = _
  ext n
  simp only [HahnSeries.map_coeff]
  exact map_intCast σ _

theorem coeffMap_comp_algebraMap {κ k : Type*} [Field κ] [Field k] (σ : κ →+* k) :
    (coeffMap σ).comp (algebraMap κ (LaurentSeries κ)) = (algebraMap k (LaurentSeries k)).comp σ := by
  ext c : 1
  rw [RingHom.comp_apply, RingHom.comp_apply, algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single,
    coeffMap_single]

theorem coeffMap_aeval_jqModC {κ k : Type*} [Field κ] [Field k] (σ : κ →+* k) (p : Polynomial κ) :
    coeffMap σ (aeval (jqModC κ) p) = aeval (jqModC k) (p.map σ) := by
  rw [aeval_def, aeval_def, eval₂_map, ← coeffMap_jqModC σ, hom_eval₂, coeffMap_comp_algebraMap]

section OneField
variable (K : Type*) [Field K]

noncomputable abbrev J : ↥(modularFunctionFieldC K 1) := ⟨jqModC K, jqModC_mem K 1⟩

theorem coe_aeval_J (p : Polynomial K) :
    ((aeval (J K) p : ↥(modularFunctionFieldC K 1)) : LaurentSeries K) = aeval (jqModC K) p :=
  (aeval_algHom_apply (modularFunctionFieldC K 1).val (J K) p).symm

theorem ratFuncEquivCharLOneC_algebraMap (p : Polynomial K) :
    (ratFuncEquivCharLOneC K (algebraMap (Polynomial K) (RatFunc K) p) : LaurentSeries K) = aeval (jqModC K) p := by
  unfold ratFuncEquivCharLOneC
  change ((RatFunc.algEquivOfTranscendental (jqModC K) (transcendental_jqModC K))
          (algebraMap K[X] (RatFunc K) p) : LaurentSeries K) = _
  rw [RatFunc.algEquivOfTranscendental_apply, RatFunc.num_algebraMap, RatFunc.denom_algebraMap, map_one, div_one]

theorem exists_eq_aeval_div (y : ↥(modularFunctionFieldC K 1)) :
    ∃ P Q : Polynomial K, aeval (jqModC K) Q ≠ 0 ∧
      (y : LaurentSeries K) = aeval (jqModC K) P / aeval (jqModC K) Q := by
  set u := (ratFuncEquivCharLOneC K).symm y with hu
  have hy : y = ratFuncEquivCharLOneC K u := by rw [hu, AlgEquiv.apply_symm_apply]
  refine ⟨u.num, u.denom, ?_, ?_⟩
  · rw [← ratFuncEquivCharLOneC_algebraMap]
    intro h0
    have : ratFuncEquivCharLOneC K (algebraMap K[X] (RatFunc K) u.denom) = 0 := Subtype.ext h0
    rw [map_eq_zero_iff _ (ratFuncEquivCharLOneC K).injective,
      map_eq_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))] at this
    exact u.denom_ne_zero this
  · conv_lhs => rw [hy, ← RatFunc.num_div_denom u]
    rw [map_div₀, IntermediateField.coe_div, ratFuncEquivCharLOneC_algebraMap, ratFuncEquivCharLOneC_algebraMap]

theorem ord_of_coe_eq_aeval_div [IsAlgClosed K] [DecidableEq K] (a : K)
    (y : ↥(modularFunctionFieldC K 1)) (hy0 : y ≠ 0) (P Q : Polynomial K) (hQ : aeval (jqModC K) Q ≠ 0)
    (hy : (y : LaurentSeries K) = aeval (jqModC K) P / aeval (jqModC K) Q) :
    (charLGeomPlaceOfPoint K a).ord y = (P.rootMultiplicity a : ℤ) - (Q.rootMultiplicity a : ℤ) := by
  have hQ0 : (aeval (J K) Q : ↥(modularFunctionFieldC K 1)) ≠ 0 := by
    intro h0; apply hQ; rw [← coe_aeval_J, h0]; rfl
  have hyq : y * aeval (J K) Q = aeval (J K) P := by
    apply Subtype.ext
    rw [MulMemClass.coe_mul, coe_aeval_J, coe_aeval_J, hy, div_mul_cancel₀ _ hQ]
  have h := congrArg (charLGeomPlaceOfPoint K a).ord hyq
  rw [(charLGeomPlaceOfPoint K a).ord_mul hy0 hQ0,
    ModularCurve.ord_charLGeomPlaceOfPoint_aeval_jqModC_eq_rootMultiplicity,
    ModularCurve.ord_charLGeomPlaceOfPoint_aeval_jqModC_eq_rootMultiplicity] at h
  linarith

end OneField
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"

theorem ord_charLGeomPlaceOfPoint_eq_of_coe_eq_coeffMap (κ k : Type*) [Field κ] [Field k]
    [IsAlgClosed κ] [IsAlgClosed k] [DecidableEq κ] [DecidableEq k] (σ : κ →+* k) (c : κ)
    (y : ↥(modularFunctionFieldC κ 1)) (x : ↥(modularFunctionFieldC k 1))
    (hxy : (x : LaurentSeries k) = coeffMap σ (y : LaurentSeries κ)) :
    (charLGeomPlaceOfPoint k (σ c)).ord x = (charLGeomPlaceOfPoint κ c).ord y := by
  by_cases hy0 : y = 0
  · have hx0 : x = 0 := by
      apply Subtype.ext; rw [hxy, hy0]; simp
    rw [hx0, hy0, Place.ord_zero, Place.ord_zero]
  obtain ⟨P, Q, hQ, hy⟩ := exists_eq_aeval_div κ y
  have hQk : aeval (jqModC k) (Q.map σ) ≠ 0 := by
    rw [← coeffMap_aeval_jqModC]; intro h0
    apply hQ
    have hinj : Function.Injective (coeffMap σ) := by
      intro a b h; ext n; apply σ.injective
      exact congrArg (fun z : LaurentSeries k => z.coeff n) h
    exact hinj (h0.trans (map_zero _).symm)
  have hx : (x : LaurentSeries k) = aeval (jqModC k) (P.map σ) / aeval (jqModC k) (Q.map σ) := by
    rw [hxy, hy, map_div₀, coeffMap_aeval_jqModC, coeffMap_aeval_jqModC]
  have hx0 : x ≠ 0 := by
    intro h0; apply hy0
    apply Subtype.ext
    have : coeffMap σ (y : LaurentSeries κ) = 0 := by rw [← hxy, h0]; rfl
    have hinj : Function.Injective (coeffMap σ) := by
      intro a b h; ext n; apply σ.injective
      exact congrArg (fun z : LaurentSeries k => z.coeff n) h
    exact hinj (this.trans (map_zero _).symm)
  rw [ord_of_coe_eq_aeval_div κ c y hy0 P Q hQ hy, ord_of_coe_eq_aeval_div k (σ c) x hx0 _ _ hQk hx,
    ← eq_rootMultiplicity_map σ.injective, ← eq_rootMultiplicity_map σ.injective]

end FltWs21.OrdExt
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"

end Dictionaries
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"

noncomputable section
namespace ChartOkChartFst

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~coeffMap_injective P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve.PlaceSpecialization.ProlongationTuple"
open Classical

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : ProlongationTuple P)

local notation "Qb" => AlgebraicClosure ℚ

theorem jFun_jqFun_snd (hA : A.LiesOverPrime q) :
    ∃ (h₃ : PlaceSpecialization.jqFun (q := q) ∈ R.R₂.integers) (h₄ : PlaceSpecialization.jFun (q := q) ∈ R.R₂.integers),
      ((R.R₂.residue ⟨_, h₃⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
          = jqModC (ResidueField A) ∧
      ((R.R₂.residue ⟨_, h₄⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
          = jqModC (ResidueField A) ^ q := by
  obtain ⟨V, -, hV₂⟩ := ModularCurve.PlaceSpecialization.exists_levelOneProlongationPair_of_prolongationTuple R
  obtain ⟨-, -, h₃, h₄, -, -, e₃, e₄⟩ := ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue_jFun_jqFun hA V
  have key : ∀ (S : RegularProlongation A (modularFunctionFieldBar (1 * q)) (modularFunctionFieldFullC (ResidueField A) 1))
      (hS : S = R.R₂) (h₃ : PlaceSpecialization.jqFun (q := q) ∈ S.integers) (h₄ : PlaceSpecialization.jFun (q := q) ∈ S.integers),
      ((S.residue ⟨_, h₃⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A)) = jqModC (ResidueField A) →
      ((S.residue ⟨_, h₄⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A)) = jqModC (ResidueField A) ^ q →
      ∃ (h₃' : PlaceSpecialization.jqFun (q := q) ∈ R.R₂.integers) (h₄' : PlaceSpecialization.jFun (q := q) ∈ R.R₂.integers),
        ((R.R₂.residue ⟨_, h₃'⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A)) = jqModC (ResidueField A) ∧
        ((R.R₂.residue ⟨_, h₄'⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A)) = jqModC (ResidueField A) ^ q := by
    rintro S rfl h₃ h₄ e₃ e₄
    exact ⟨h₃, h₄, e₃, e₄⟩
  exact key V.R₂ hV₂ h₃ h₄ e₃ e₄

theorem jqFun_mem_integersSnd (hA : A.LiesOverPrime q) : PlaceSpecialization.jqFun (q := q) ∈ R.R₂.integers :=
  (jFun_jqFun_snd R hA).1
theorem jFun_mem_integersSnd (hA : A.LiesOverPrime q) : PlaceSpecialization.jFun (q := q) ∈ R.R₂.integers :=
  (jFun_jqFun_snd R hA).2.1

theorem residue₂_jqFun (hA : A.LiesOverPrime q) :
    R.residue₂ ⟨_, jqFun_mem_integersSnd R hA⟩ = (⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) := by
  obtain ⟨h₃, h₄, e₃, e₄⟩ := jFun_jqFun_snd R hA
  apply Subtype.ext
  rw [residue₂_apply, R.ι_coe, e₃]
  exact FltWs21.OrdExt.coeffMap_jqModC R.redBar

theorem residue₂_jFun (hA : A.LiesOverPrime q) :
    R.residue₂ ⟨_, jFun_mem_integersSnd R hA⟩ = (⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) ^ q := by
  obtain ⟨h₃, h₄, e₃, e₄⟩ := jFun_jqFun_snd R hA
  apply Subtype.ext
  rw [residue₂_apply, R.ι_coe, e₄, map_pow, FltWs21.OrdExt.coeffMap_jqModC R.redBar]
  rfl

theorem atkinLehnerBar_one_eq : ProlongationTuple.atkinLehnerBar 1 q = frickeInvolutionBar (1 * q) := by
  unfold ProlongationTuple.atkinLehnerBar
  exact ModularCurve.geomAut_atkinLehnerInvolutionFull_one_eq_frickeInvolutionBar q

theorem red_eq_comp : red = R.redBar.comp (IsLocalRing.residue A) :=
  RingHom.ext fun a => (R.redBar_residue a).symm

include R in
theorem modularLocalized_red_eq :
    CharPReduction.modularLocalized (1 * q) A.toSubring red =
      CharPReduction.modularLocalized (1 * q) A.toSubring (IsLocalRing.residue A) := by
  rw [red_eq_comp R]
  exact FltWs21.RedIndep.modularLocalized_comp (1 * q) A.toSubring (IsLocalRing.residue A) R.redBar

theorem modularRedLocHom_congr {red₁ red₂ : A →+* k} (h : red₁ = red₂) (f : LaurentSeries Qb)
    (h₁ : f ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red₁) (h₂ : f ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red₂) :
    CharPReduction.modularRedLocHom (1 * q) A.toSubring red₁ ⟨f, h₁⟩ = CharPReduction.modularRedLocHom (1 * q) A.toSubring red₂ ⟨f, h₂⟩ := by
  subst h; rfl

theorem modularRedLocHom_red_eq (f : LaurentSeries Qb)
    (h₁ : f ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₀ : f ∈ CharPReduction.modularLocalized (1 * q) A.toSubring (IsLocalRing.residue A)) :
    CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨f, h₁⟩ =
      coeffMap R.redBar (CharPReduction.modularRedLocHom (1 * q) A.toSubring (IsLocalRing.residue A) ⟨f, h₀⟩) := by
  have h₂ : f ∈ CharPReduction.modularLocalized (1 * q) A.toSubring (R.redBar.comp (IsLocalRing.residue A)) := by
    rw [FltWs21.RedIndep.modularLocalized_comp]; exact h₀
  rw [modularRedLocHom_congr (red_eq_comp R) f h₁ h₂]
  exact FltWs21.RedIndep.modularRedLocHom_comp (1 * q) A.toSubring (IsLocalRing.residue A) R.redBar f h₀ h₂

theorem mem_integersSnd_and_coe_residue₂_eq (g : ↥(modularFunctionFieldBar (1 * q)))
    (h₂ : ((frickeInvolutionBar (1 * q) g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries Qb) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring (IsLocalRing.residue A)) :
    ∃ hg : g ∈ R.R₂.integers,
      ((R.residue₂ ⟨g, hg⟩ : ↥(modularFunctionFieldC k 1)) : LaurentSeries k) =
        coeffMap R.redBar (CharPReduction.modularRedLocHom (1 * q) A.toSubring (IsLocalRing.residue A) ⟨_, h₂⟩) := by
  have hAL : ((ProlongationTuple.atkinLehnerBar 1 q g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries Qb) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red := by
    rw [modularLocalized_red_eq R, atkinLehnerBar_one_eq]; exact h₂
  have hg : g ∈ R.R₂.integers := (R.mem_integersSnd_iff g).mpr hAL
  refine ⟨hg, ?_⟩
  obtain ⟨h₁, e₁⟩ := R.residue₁_eq_modularRedLocHom (ProlongationTuple.atkinLehnerBar 1 q g) hAL
  rw [residue₂_apply, R.residue₂_eq g hg]
  have : R.R₁.residue ⟨ProlongationTuple.atkinLehnerBar 1 q g, (R.mem_integersFst_iff _).mpr ((R.mem_integersSnd_iff g).mp hg)⟩ =
      R.R₁.residue ⟨ProlongationTuple.atkinLehnerBar 1 q g, h₁⟩ := rfl
  rw [this, e₁]
  have h₂' : ((ProlongationTuple.atkinLehnerBar 1 q g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries Qb) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring (IsLocalRing.residue A) := by
    rw [atkinLehnerBar_one_eq]; exact h₂
  rw [modularRedLocHom_red_eq R _ hAL h₂']
  congr 2
  apply Subtype.ext
  simp [atkinLehnerBar_one_eq]

theorem hunit0_chartSnd (hR : R.IsModel) [HasPrincipalDivisors Qb (modularFunctionFieldBar (1 * q))]
    (g : ↥(modularFunctionFieldBar (1 * q)))
    (h₂ : ((frickeInvolutionBar (1 * q) g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries Qb) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring (IsLocalRing.residue A))
    (hne : CharPReduction.modularRedLocHom (1 * q) A.toSubring (IsLocalRing.residue A) ⟨_, h₂⟩ ≠ 0) :
    letI := algebraResidueField R
    ∃ hg : g ∈ (chartSnd R hR).integers, (chartSnd R hR).residue ⟨g, hg⟩ ≠ 0 := by
  letI := algebraResidueField R
  obtain ⟨hg, e⟩ := mem_integersSnd_and_coe_residue₂_eq R g h₂
  refine ⟨hg, fun h0 => hne ?_⟩
  have h0' : ((R.residue₂ ⟨g, hg⟩ : ↥(modularFunctionFieldC k 1)) : LaurentSeries k) = 0 := by
    change ((chartSnd R hR).residue ⟨g, hg⟩ : LaurentSeries k) = 0
    rw [h0]; rfl
  rw [e] at h0'
  exact FltWs21.RedIndep.coeffMap_injective R.redBar R.redBar.injective (h0'.trans (map_zero _).symm)

theorem hordres0_chartSnd [IsAlgClosed (ResidueField A)] [DecidableEq (ResidueField A)]
    (hR : R.IsModel) [HasPrincipalDivisors Qb (modularFunctionFieldBar (1 * q))]
    (c : ResidueField A) (g : ↥(modularFunctionFieldBar (1 * q)))
    (hg : letI := algebraResidueField R; g ∈ (chartSnd R hR).integers)
    (h₂ : ((frickeInvolutionBar (1 * q) g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries Qb) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring (IsLocalRing.residue A))
    (h₂F : CharPReduction.modularRedLocHom (1 * q) A.toSubring (IsLocalRing.residue A) ⟨_, h₂⟩ ∈
      modularFunctionFieldC (ResidueField A) 1) :
    letI := algebraResidueField R
    (rc R (charLGeomPlaceOfPoint k (R.redBar c))).ord ((chartSnd R hR).residue ⟨g, hg⟩) =
      (charLGeomPlaceOfPoint (ResidueField A) c).ord (⟨_, h₂F⟩ : ↥(modularFunctionFieldC (ResidueField A) 1)) := by
  letI := algebraResidueField R
  obtain ⟨hg', e⟩ := mem_integersSnd_and_coe_residue₂_eq R g h₂
  rw [ord_rc]
  change (charLGeomPlaceOfPoint k (R.redBar c)).ord (R.residue₂ ⟨g, hg'⟩) = _
  exact FltWs21.OrdExt.ord_charLGeomPlaceOfPoint_eq_of_coe_eq_coeffMap (ResidueField A) k R.redBar c
    ⟨_, h₂F⟩ (R.residue₂ ⟨g, hg'⟩) e

theorem hres_chartSnd (hR : R.IsModel) [HasPrincipalDivisors Qb (modularFunctionFieldBar (1 * q))] (hA : A.LiesOverPrime q) :
    letI := algebraResidueField R
    (chartSnd R hR).residue ⟨_, jqFun_mem_integersSnd R hA⟩ = (⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) ∧
    (chartSnd R hR).residue ⟨_, jFun_mem_integersSnd R hA⟩ = (⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) ^ q :=
  ⟨residue₂_jqFun R hA, residue₂_jFun R hA⟩

end ChartOkChartFst
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"
end
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"

noncomputable section
namespace ChartOkChartFst

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~coeffMap_injective P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve.PlaceSpecialization.ProlongationTuple"
open Classical

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : ProlongationTuple P)

local notation "Qb" => AlgebraicClosure ℚ

theorem jFun_jqFun_fst (hA : A.LiesOverPrime q) :
    ∃ (h₁ : PlaceSpecialization.jFun (q := q) ∈ R.R₁.integers) (h₂ : PlaceSpecialization.jqFun (q := q) ∈ R.R₁.integers),
      ((R.R₁.residue ⟨_, h₁⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
          = jqModC (ResidueField A) ∧
      ((R.R₁.residue ⟨_, h₂⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
          = jqModC (ResidueField A) ^ q := by
  obtain ⟨V, hV₁, -⟩ := ModularCurve.PlaceSpecialization.exists_levelOneProlongationPair_of_prolongationTuple R
  obtain ⟨h₁, h₂, -, -, e₁, e₂, -, -⟩ := ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue_jFun_jqFun hA V
  have key : ∀ (S : RegularProlongation A (modularFunctionFieldBar (1 * q)) (modularFunctionFieldFullC (ResidueField A) 1))
      (hS : S = R.R₁) (h₁ : PlaceSpecialization.jFun (q := q) ∈ S.integers) (h₂ : PlaceSpecialization.jqFun (q := q) ∈ S.integers),
      ((S.residue ⟨_, h₁⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A)) = jqModC (ResidueField A) →
      ((S.residue ⟨_, h₂⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A)) = jqModC (ResidueField A) ^ q →
      ∃ (h₁' : PlaceSpecialization.jFun (q := q) ∈ R.R₁.integers) (h₂' : PlaceSpecialization.jqFun (q := q) ∈ R.R₁.integers),
        ((R.R₁.residue ⟨_, h₁'⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A)) = jqModC (ResidueField A) ∧
        ((R.R₁.residue ⟨_, h₂'⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A)) = jqModC (ResidueField A) ^ q := by
    rintro S rfl h₁ h₂ e₁ e₂
    exact ⟨h₁, h₂, e₁, e₂⟩
  exact key V.R₁ hV₁ h₁ h₂ e₁ e₂

theorem jFun_mem_integersFst (hA : A.LiesOverPrime q) : PlaceSpecialization.jFun (q := q) ∈ R.R₁.integers :=
  (jFun_jqFun_fst R hA).1
theorem jqFun_mem_integersFst (hA : A.LiesOverPrime q) : PlaceSpecialization.jqFun (q := q) ∈ R.R₁.integers :=
  (jFun_jqFun_fst R hA).2.1

theorem residue₁_jFun (hA : A.LiesOverPrime q) :
    R.residue₁ ⟨_, jFun_mem_integersFst R hA⟩ = (⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) := by
  obtain ⟨h₁, h₂, e₁, e₂⟩ := jFun_jqFun_fst R hA
  apply Subtype.ext
  rw [residue₁_apply, R.ι_coe, e₁]
  exact FltWs21.OrdExt.coeffMap_jqModC R.redBar

theorem residue₁_jqFun (hA : A.LiesOverPrime q) :
    R.residue₁ ⟨_, jqFun_mem_integersFst R hA⟩ = (⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) ^ q := by
  obtain ⟨h₁, h₂, e₁, e₂⟩ := jFun_jqFun_fst R hA
  apply Subtype.ext
  rw [residue₁_apply, R.ι_coe, e₂, map_pow, FltWs21.OrdExt.coeffMap_jqModC R.redBar]
  rfl

theorem mem_integersFst_and_coe_residue₁_eq (g : ↥(modularFunctionFieldBar (1 * q)))
    (h₁ : ((g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries Qb) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring (IsLocalRing.residue A)) :
    ∃ hg : g ∈ R.R₁.integers,
      ((R.residue₁ ⟨g, hg⟩ : ↥(modularFunctionFieldC k 1)) : LaurentSeries k) =
        coeffMap R.redBar (CharPReduction.modularRedLocHom (1 * q) A.toSubring (IsLocalRing.residue A) ⟨_, h₁⟩) := by
  have h₁' : ((g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries Qb) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red := by
    rw [modularLocalized_red_eq R]; exact h₁
  obtain ⟨hg, e⟩ := R.residue₁_eq_modularRedLocHom g h₁'
  refine ⟨hg, ?_⟩
  rw [residue₁_apply, e, modularRedLocHom_red_eq R _ h₁' h₁]

theorem hunit_chartFst (hR : R.IsModel) [HasPrincipalDivisors Qb (modularFunctionFieldBar (1 * q))]
    (g : ↥(modularFunctionFieldBar (1 * q)))
    (h₁ : ((g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries Qb) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring (IsLocalRing.residue A))
    (hne : CharPReduction.modularRedLocHom (1 * q) A.toSubring (IsLocalRing.residue A) ⟨_, h₁⟩ ≠ 0) :
    letI := algebraResidueField R
    ∃ hg : g ∈ (chartFst R hR).integers, (chartFst R hR).residue ⟨g, hg⟩ ≠ 0 := by
  letI := algebraResidueField R
  obtain ⟨hg, e⟩ := mem_integersFst_and_coe_residue₁_eq R g h₁
  refine ⟨hg, fun h0 => hne ?_⟩
  have h0' : ((R.residue₁ ⟨g, hg⟩ : ↥(modularFunctionFieldC k 1)) : LaurentSeries k) = 0 := by
    change ((chartFst R hR).residue ⟨g, hg⟩ : LaurentSeries k) = 0
    rw [h0]; rfl
  rw [e] at h0'
  exact FltWs21.RedIndep.coeffMap_injective R.redBar R.redBar.injective (h0'.trans (map_zero _).symm)

theorem hordres_chartFst [IsAlgClosed (ResidueField A)] [DecidableEq (ResidueField A)]
    (hR : R.IsModel) [HasPrincipalDivisors Qb (modularFunctionFieldBar (1 * q))]
    (c : ResidueField A) (g : ↥(modularFunctionFieldBar (1 * q)))
    (hg : letI := algebraResidueField R; g ∈ (chartFst R hR).integers)
    (h₁ : ((g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries Qb) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring (IsLocalRing.residue A))
    (h₁F : CharPReduction.modularRedLocHom (1 * q) A.toSubring (IsLocalRing.residue A) ⟨_, h₁⟩ ∈
      modularFunctionFieldC (ResidueField A) 1) :
    letI := algebraResidueField R
    (rc R (charLGeomPlaceOfPoint k (R.redBar c))).ord ((chartFst R hR).residue ⟨g, hg⟩) =
      (charLGeomPlaceOfPoint (ResidueField A) c).ord (⟨_, h₁F⟩ : ↥(modularFunctionFieldC (ResidueField A) 1)) := by
  letI := algebraResidueField R
  obtain ⟨hg', e⟩ := mem_integersFst_and_coe_residue₁_eq R g h₁
  rw [ord_rc]
  change (charLGeomPlaceOfPoint k (R.redBar c)).ord (R.residue₁ ⟨g, hg'⟩) = _
  exact FltWs21.OrdExt.ord_charLGeomPlaceOfPoint_eq_of_coe_eq_coeffMap (ResidueField A) k R.redBar c
    ⟨_, h₁F⟩ (R.residue₁ ⟨g, hg'⟩) e

theorem hres_chartFst (hR : R.IsModel) [HasPrincipalDivisors Qb (modularFunctionFieldBar (1 * q))] (hA : A.LiesOverPrime q) :
    letI := algebraResidueField R
    (chartFst R hR).residue ⟨_, jFun_mem_integersFst R hA⟩ = (⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) ∧
    (chartFst R hR).residue ⟨_, jqFun_mem_integersFst R hA⟩ = (⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) ^ q :=
  ⟨residue₁_jFun R hA, residue₁_jqFun R hA⟩

end ChartOkChartFst
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"
end
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"

namespace ChartOkAbv

set_option autoImplicit false

variable {L : Type*} [Field L] (A : ValuationSubring L) (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1)
include hμA

theorem abv_lt_one_iff_inv_not_mem {a : L} (ha : a ≠ 0) : μ a < 1 ↔ a⁻¹ ∉ A := by
  rw [hμA, not_le, map_inv₀, one_lt_inv₀ (μ.pos ha)]

theorem abv_lt_one_iff_mem_maximalIdeal {a : L} (haA : a ∈ A) (ha : a ≠ 0) :
    μ a < 1 ↔ (⟨a, haA⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
  rw [abv_lt_one_iff_inv_not_mem A μ hμA ha, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro h hu
    apply h
    have hmul : ((hu.unit⁻¹ : Aˣ) : A).1 * a = 1 := by
      have h' := congrArg Subtype.val hu.unit.inv_mul
      rw [IsUnit.unit_spec] at h'
      exact h'
    have : ((hu.unit⁻¹ : Aˣ) : A).1 = a⁻¹ := eq_inv_of_mul_eq_one_left hmul
    rw [← this]; exact Subtype.mem _
  · intro h hinv
    exact h ⟨⟨⟨a, haA⟩, ⟨a⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ ha), Subtype.ext (inv_mul_cancel₀ ha)⟩, rfl⟩

theorem abv_le_abv_iff_div_mem {b c : L} (hc : c ≠ 0) : μ b ≤ μ c ↔ b / c ∈ A := by
  rw [hμA, map_div₀, div_le_one (μ.pos hc)]

theorem abv_zpow_le_iff {x c : L} (hc : c ≠ 0) (n : ℤ) : μ x ^ n ≤ μ c ↔ x ^ n / c ∈ A := by
  rw [← map_zpow₀, abv_le_abv_iff_div_mem A μ hμA hc]

theorem abv_le_zpow_iff {x c : L} (hx : x ≠ 0) (n : ℤ) : μ c ≤ μ x ^ n ↔ c / x ^ n ∈ A := by
  rw [← map_zpow₀, abv_le_abv_iff_div_mem A μ hμA (zpow_ne_zero n hx)]

end ChartOkAbv
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"

namespace ChartOkTwist

open AlgebraicCurve IsLocalRing

set_option autoImplicit false

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem isUnit_of_residue_ne_zero (C : ComponentChart A F Fbar) {f : ↥C.integers} (hf : C.residue f ≠ 0) : IsUnit f := by
  by_contra h
  apply hf
  have hmem : f ∈ maximalIdeal ↥C.integers := (IsLocalRing.mem_maximalIdeal f).mpr h
  rw [← C.ker_residue] at hmem
  exact hmem

theorem residue_algebraMap_eq_zero (C : ComponentChart A F Fbar) (a : A) (ha : a ∈ maximalIdeal A) :
    C.residue ⟨algebraMap L F a, (C.algebraMap_mem_iff a).mpr a.2⟩ = 0 := by
  rw [C.residue_algebraMap, (IsLocalRing.residue_eq_zero_iff a).mpr ha, map_zero]

theorem sub_const_mem_and_residue (C : ComponentChart A F Fbar) (z : F) (hz : z ∈ C.integers) (a : A) (ha : a ∈ maximalIdeal A) :
    ∃ h : z - algebraMap L F a ∈ C.integers, C.residue ⟨z - algebraMap L F a, h⟩ = C.residue ⟨z, hz⟩ := by
  have haI : algebraMap L F a ∈ C.integers := (C.algebraMap_mem_iff a).mpr a.2
  refine ⟨sub_mem hz haI, ?_⟩
  have : (⟨z - algebraMap L F a, sub_mem hz haI⟩ : ↥C.integers) = ⟨z, hz⟩ - ⟨algebraMap L F a, haI⟩ := rfl
  rw [this, map_sub, residue_algebraMap_eq_zero C a ha, sub_zero]

theorem zpow_mem_and_residue (C : ComponentChart A F Fbar) (u : F) (hu : u ∈ C.integers) (hres : C.residue ⟨u, hu⟩ ≠ 0) (m : ℤ) :
    ∃ h : u ^ m ∈ C.integers, C.residue ⟨u ^ m, h⟩ = C.residue ⟨u, hu⟩ ^ m := by
  have hunit : IsUnit (⟨u, hu⟩ : ↥C.integers) := isUnit_of_residue_ne_zero C hres
  obtain ⟨U, hU⟩ := hunit
  have hval : ((↑(U ^ m) : ↥C.integers) : F) = u ^ m := by
    have : ((↑(U ^ m) : ↥C.integers) : F) = ((Units.map (C.integers.subtype : ↥C.integers →* F) (U ^ m) : Fˣ) : F) := by
      rw [Units.coe_map]; rfl
    rw [this, map_zpow, Units.val_zpow_eq_zpow_val, Units.coe_map, MonoidHom.coe_coe]
    change ((U : ↥C.integers) : F) ^ m = u ^ m
    rw [hU]
  refine ⟨hval ▸ (↑(U ^ m) : ↥C.integers).2, ?_⟩
  have heq : (⟨u ^ m, hval ▸ (↑(U ^ m) : ↥C.integers).2⟩ : ↥C.integers) = ↑(U ^ m) := Subtype.ext hval.symm
  rw [heq]
  have : C.residue (↑(U ^ m) : ↥C.integers) = ((Units.map (C.residue : ↥C.integers →* Fbar) (U ^ m) : Fbarˣ) : Fbar) := by
    rw [Units.coe_map]; rfl
  rw [this, map_zpow, Units.val_zpow_eq_zpow_val, Units.coe_map, MonoidHom.coe_coe, hU]

end ChartOkTwist
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"

namespace ChartOkTwist

open AlgebraicCurve IsLocalRing

set_option autoImplicit false

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem inv_mem_of_residue_ne_zero (C : ComponentChart A F Fbar) {u : F} (hu : u ∈ C.integers) (hres : C.residue ⟨u, hu⟩ ≠ 0) :
    u⁻¹ ∈ C.integers := by
  obtain ⟨U, hU⟩ := isUnit_of_residue_ne_zero C hres
  have hprod : ((↑(U⁻¹) : ↥C.integers) : F) * u = 1 := by
    have h := congrArg (fun x : ↥C.integers => (x : F)) U.inv_mul
    beta_reduce at h
    rw [hU] at h
    exact h
  have hinvval : ((↑(U⁻¹) : ↥C.integers) : F) = u⁻¹ := eq_inv_of_mul_eq_one_left hprod
  rw [← hinvval]; exact Subtype.mem _

theorem far_factor_mem_and_residue (C' : ComponentChart A F Fbar) (z z' : F) (hz' : z' ∈ C'.integers)
    (hres' : C'.residue ⟨z', hz'⟩ ≠ 0) (π : A) (htwo : z' * z = algebraMap L F (π : L))
    (a : A) (ha0 : (a : L) ≠ 0) (b : A) (hb : b ∈ maximalIdeal A) (hπab : (π : L) = a * b) :
    ∃ h : (z - algebraMap L F a) * (algebraMap L F (-(a : L)))⁻¹ ∈ C'.integers,
      C'.residue ⟨_, h⟩ = 1 := by
  have hz'0 : z' ≠ 0 := by
    intro h0; apply hres'
    have : (⟨z', hz'⟩ : ↥C'.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hinv : z'⁻¹ ∈ C'.integers := inv_mem_of_residue_ne_zero C' hz' hres'
  have hbI : algebraMap L F (b : L) ∈ C'.integers := (C'.algebraMap_mem_iff b).mpr b.2
  have ha0' : algebraMap L F (a : L) ≠ 0 := (map_ne_zero _).mpr ha0
  have hr : (z - algebraMap L F a) * (algebraMap L F (-(a : L)))⁻¹ = 1 - algebraMap L F (b : L) * z'⁻¹ := by
    have hz : z = algebraMap L F (π : L) * z'⁻¹ := by rw [← htwo]; field_simp
    rw [hz, hπab, map_neg, map_mul]
    field_simp
    ring
  have hmem : (z - algebraMap L F a) * (algebraMap L F (-(a : L)))⁻¹ ∈ C'.integers := by
    rw [hr]; exact sub_mem (one_mem _) (mul_mem hbI hinv)
  refine ⟨hmem, ?_⟩
  have heq : (⟨_, hmem⟩ : ↥C'.integers) = 1 - ⟨algebraMap L F (b : L), hbI⟩ * ⟨z'⁻¹, hinv⟩ := Subtype.ext hr
  rw [heq, map_sub, map_one, map_mul, residue_algebraMap_eq_zero C' b hb, zero_mul, sub_zero]

end ChartOkTwist
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"

namespace ChartOkTwist

open AlgebraicCurve IsLocalRing
open Classical

set_option autoImplicit false

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem twistMonomial_mem_and_residue (C : ComponentChart A F Fbar) (z : F) (hz : z ∈ C.integers) (hzres : C.residue ⟨z, hz⟩ ≠ 0)
    {ι : Type*} (s : Finset ι) (a : ι → A) (ha : ∀ i ∈ s, a i ∈ maximalIdeal A) (m : ι → ℤ) :
    ∃ h : ∏ i ∈ s, (z - algebraMap L F (a i)) ^ m i ∈ C.integers,
      C.residue ⟨∏ i ∈ s, (z - algebraMap L F (a i)) ^ m i, h⟩ = C.residue ⟨z, hz⟩ ^ (∑ i ∈ s, m i) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by rw [Finset.prod_empty]; exact one_mem _, ?_⟩
    have : (⟨∏ i ∈ (∅ : Finset ι), (z - algebraMap L F (a i)) ^ m i, by rw [Finset.prod_empty]; exact one_mem _⟩ : ↥C.integers) = 1 :=
      Subtype.ext (by simp)
    rw [this, map_one, Finset.sum_empty, zpow_zero]
  | insert j s hj ih =>
    obtain ⟨hmem, hres⟩ := ih (fun i hi => ha i (Finset.mem_insert_of_mem hi))
    obtain ⟨hj1, hjres⟩ := sub_const_mem_and_residue C z hz (a j) (ha j (Finset.mem_insert_self j s))
    obtain ⟨hjm, hjmres⟩ := zpow_mem_and_residue C _ hj1 (by rw [hjres]; exact hzres) (m j)
    have hmem' : ∏ i ∈ insert j s, (z - algebraMap L F (a i)) ^ m i ∈ C.integers := by
      rw [Finset.prod_insert hj]; exact mul_mem hjm hmem
    refine ⟨hmem', ?_⟩
    have heq : (⟨∏ i ∈ insert j s, (z - algebraMap L F (a i)) ^ m i, hmem'⟩ : ↥C.integers)
        = ⟨(z - algebraMap L F (a j)) ^ m j, hjm⟩ * ⟨∏ i ∈ s, (z - algebraMap L F (a i)) ^ m i, hmem⟩ :=
      Subtype.ext (by change ∏ i ∈ insert j s, (z - algebraMap L F (a i)) ^ m i = _ * _; rw [Finset.prod_insert hj])
    rw [heq, map_mul, hjmres, hjres, hres, Finset.sum_insert hj, zpow_add₀ hzres]

theorem twistMonomial_far_mem_and_residue (C' : ComponentChart A F Fbar) (z z' : F) (hz' : z' ∈ C'.integers)
    (hres' : C'.residue ⟨z', hz'⟩ ≠ 0) (π : A) (htwo : z' * z = algebraMap L F (π : L))
    {ι : Type*} (s : Finset ι) (a b : ι → A) (ha0 : ∀ i ∈ s, (a i : L) ≠ 0) (hb : ∀ i ∈ s, b i ∈ maximalIdeal A)
    (hπab : ∀ i ∈ s, (π : L) = a i * b i) (m : ι → ℤ) :
    ∃ h : ∏ i ∈ s, ((z - algebraMap L F (a i)) * (algebraMap L F (-(a i : L)))⁻¹) ^ m i ∈ C'.integers,
      C'.residue ⟨_, h⟩ = 1 := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by rw [Finset.prod_empty]; exact one_mem _, ?_⟩
    have : (⟨∏ i ∈ (∅ : Finset ι), ((z - algebraMap L F (a i)) * (algebraMap L F (-(a i : L)))⁻¹) ^ m i,
        by rw [Finset.prod_empty]; exact one_mem _⟩ : ↥C'.integers) = 1 := Subtype.ext (by simp)
    rw [this, map_one]
  | insert j s hj ih =>
    obtain ⟨hmem, hres⟩ := ih (fun i hi => ha0 i (Finset.mem_insert_of_mem hi)) (fun i hi => hb i (Finset.mem_insert_of_mem hi))
      (fun i hi => hπab i (Finset.mem_insert_of_mem hi))
    obtain ⟨hj1, hjres⟩ := far_factor_mem_and_residue C' z z' hz' hres' π htwo (a j) (ha0 j (Finset.mem_insert_self j s))
      (b j) (hb j (Finset.mem_insert_self j s)) (hπab j (Finset.mem_insert_self j s))
    obtain ⟨hjm, hjmres⟩ := zpow_mem_and_residue C' _ hj1 (by rw [hjres]; exact one_ne_zero) (m j)
    have hmem' : ∏ i ∈ insert j s, ((z - algebraMap L F (a i)) * (algebraMap L F (-(a i : L)))⁻¹) ^ m i ∈ C'.integers := by
      rw [Finset.prod_insert hj]; exact mul_mem hjm hmem
    refine ⟨hmem', ?_⟩
    have heq : (⟨∏ i ∈ insert j s, ((z - algebraMap L F (a i)) * (algebraMap L F (-(a i : L)))⁻¹) ^ m i, hmem'⟩ : ↥C'.integers)
        = ⟨_, hjm⟩ * ⟨_, hmem⟩ := Subtype.ext (by
          change ∏ i ∈ insert j s, ((z - algebraMap L F (a i)) * (algebraMap L F (-(a i : L)))⁻¹) ^ m i = _ * _
          rw [Finset.prod_insert hj])
    rw [heq, map_mul, hjmres, hjres, hres, one_zpow, one_mul]

end ChartOkTwist
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"

noncomputable section
namespace ChartOkChartFst

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~coeffMap_injective P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve.PlaceSpecialization.ProlongationTuple"
open Classical Polynomial

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : ProlongationTuple P)

theorem hord_poly_rc (c : ResidueField A) (Pp : Polynomial (ResidueField A)) :
    letI := algebraResidueField R
    (rc R (charLGeomPlaceOfPoint k (R.redBar c))).ord
        (Polynomial.aeval ((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1))) Pp) =
      (Pp.rootMultiplicity c : ℤ) := by
  letI := algebraResidueField R
  rw [ord_rc]

  have hcomp : (algebraMap k ↥(modularFunctionFieldC k 1)).comp R.redBar = algebraMap (ResidueField A) ↥(modularFunctionFieldC k 1) :=
    RingHom.ext fun x => (algebraMap_residueField_eq R x).symm
  have haeval : Polynomial.aeval ((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1))) Pp =
      Polynomial.aeval ((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1))) (Pp.map R.redBar) := by
    rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map, hcomp]
  rw [haeval, ModularCurve.ord_charLGeomPlaceOfPoint_aeval_jqModC_eq_rootMultiplicity,
    ← Polynomial.eq_rootMultiplicity_map R.redBar.injective]

end ChartOkChartFst
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"
end
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"

namespace ChartOkChartFst

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~coeffMap_injective P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve.PlaceSpecialization.ProlongationTuple"
open Classical

set_option autoImplicit false

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}

theorem liesOverPrime_of_ker (R : ProlongationTuple P) (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A) :
    A.LiesOverPrime q := by
  change ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits
  have hq0 : red ((q : ℕ) : A) = 0 := by rw [map_natCast]; exact CharP.cast_eq_zero k q
  have hmem : ((q : ℕ) : A) ∈ IsLocalRing.maximalIdeal A := (hker _).mp hq0
  have hcoe : ((q : ℕ) : AlgebraicClosure ℚ) = ((((q : ℕ) : A) : A) : AlgebraicClosure ℚ) := by simp
  rw [hcoe]
  exact ValuationSubring.coe_mem_nonunits_iff.mpr hmem

theorem exists_ssAnnulus_isAttached_both_ends_of_ne (R : ProlongationTuple P) (hR : R.IsModel)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))]
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A) (hq : 5 ≤ q)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728) :
    letI := algebraResidueField R
    ∃ (An An' : Annulus A ↥(modularFunctionFieldBar (1 * q))),
      (An'.dom = An.dom ∧ An'.modulus = An.modulus ∧ ((An.modulus : AlgebraicClosure ℚ) ≠ 0) ∧
        An'.param * An.param = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((An.modulus : AlgebraicClosure ℚ))) ∧
      (∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
        W ∈ An.dom ↔
          ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ))))) ∧
      An.param = (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q ∧
      An.modulus = ((q : ℕ) : A)  ∧
      An.IsAttached (chartSnd R hR) (rc R (charLGeomPlaceOfPoint k (a ^ q))) ∧
      An'.IsAttached (chartFst R hR) (rc R (charLGeomPlaceOfPoint k a)) := by
  letI := algebraResidueField R
  haveI hA : A.LiesOverPrime q := liesOverPrime_of_ker R hker
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
  letI : DecidableEq (ResidueField A) := Classical.decEq _

  let e : ResidueField A ≃+* k := RingEquiv.ofBijective R.redBar (ProlongationTuple.redBar_bijective R)
  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  set aκ : ResidueField A := e.symm a with haκ
  have hred : R.redBar aκ = a := e.apply_symm_apply a
  have hredq : R.redBar (aκ ^ q) = a ^ q := by rw [map_pow, hred]
  have hssκ : aκ ∈ ssJSet q (ResidueField A) := ModularCurve.mem_ssJSet_map_of_isAlgClosed (e.symm : k →+* ResidueField A) a ha
  have haκ2 : aκ ^ (q ^ 2) = aκ := e.injective (by
    change R.redBar (aκ ^ (q ^ 2)) = R.redBar aκ
    rw [map_pow, hred, ha2])
  have h0κ : aκ ≠ 0 := fun h => h0 (by rw [← hred, h, map_zero])
  have h1728κ : aκ ≠ 1728 := fun h => h1728 (by rw [← hred, h, map_ofNat])

  obtain ⟨An, An', h4, hdom, hparam, hmod⟩ := ModularCurve.exists_ssAnnulus_centred_of_widthOne red hker hq a ha ha2 h0 h1728

  have hredres : ∀ x : A, red x = R.redBar (IsLocalRing.residue A x) := fun x => (R.redBar_residue x).symm
  have hinj := (ProlongationTuple.redBar_bijective R).1
  have hiffx : ∀ x : A, red x = a ↔ IsLocalRing.residue A x = aκ := fun x => by
    rw [hredres, ← hred]; exact ⟨fun h => hinj h, fun h => by rw [h]⟩
  have hiffy : ∀ y : A, red y = a ^ q ↔ IsLocalRing.residue A y = aκ ^ q := fun y => by
    rw [hredres, ← hredq]; exact ⟨fun h => hinj h, fun h => by rw [h]⟩
  have hdom' : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), W ∈ An.dom ↔
      ((∃ x : A, IsLocalRing.residue ↥A x = aκ ∧
        0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
       (∃ y : A, IsLocalRing.residue ↥A y = aκ ^ q ∧
        0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) := by
    intro W
    rw [hdom W]
    simp only [hiffx, hiffy]
  refine ⟨An, An', h4, hdom, hparam, hmod, ?_, ?_⟩
  ·
    have hnodes0 : rc R (charLGeomPlaceOfPoint k (R.redBar (aκ ^ q))) ∈ (chartSnd R hR).nodes := by
      rw [hredq]
      exact rc_mem_nodes_chartSnd_of_mem_ssPlaces R hR _
        ((ModularCurve.mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq q k _).mpr
          ⟨a ^ q, (ModularCurve.pow_mem_ssJSet_iff_of_perfectField ..).mpr ha, rfl⟩)
    have hatt := ModularCurve.isAttached_ssAnnulus_zeroChart_of_chartSpec_levelOne_univ q A hq (chartSnd R hR)
      (⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) (fun c => rc R (charLGeomPlaceOfPoint k (R.redBar c)))
      (hord_poly_rc R) (jFun_mem_integersSnd R hA) (jqFun_mem_integersSnd R hA) (hres_chartSnd R hR hA).1 (hres_chartSnd R hR hA).2
      aκ hssκ haκ2 h0κ h1728κ hnodes0 An hparam hdom' (hunit0_chartSnd R hR)
      (fun g hg h₂ h₂F => hordres0_chartSnd R hR (aκ ^ q) g hg h₂ h₂F)
    simpa only [hredq] using hatt
  ·
    have hparam' : An'.param * An.param = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ) := by
      rw [h4.2.2.2, hmod]; rfl
    rw [hparam] at hparam'
    have hatt := ModularCurve.isAttached_oppAnnulus_inftyChart_of_chartSpec_levelOne_univ q A hq (chartFst R hR)
      (⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) (fun c => rc R (charLGeomPlaceOfPoint k (R.redBar c)))
      (hord_poly_rc R) (jFun_mem_integersFst R hA) (jqFun_mem_integersFst R hA) (hres_chartFst R hR hA).1 (hres_chartFst R hR hA).2
      (fun b hb => rc_mem_nodes_of_mem_ssPlaces R hR _
          ((ModularCurve.mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq q k _).mpr
            ⟨R.redBar b, ModularCurve.mem_ssJSet_map_of_isAlgClosed R.redBar b hb, rfl⟩))
      aκ hssκ haκ2 h0κ h1728κ An' hparam' (fun W => (h4.1 ▸ hdom' W : _)) (hunit_chartFst R hR)
      (fun g hg h₁ h₁F => hordres_chartFst R hR aκ g hg h₁ h₁F)
    simpa only [hred] using hatt

end ChartOkChartFst
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"

namespace ChartOkChartFst

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~coeffMap_injective P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve.PlaceSpecialization.ProlongationTuple"
open Classical

set_option autoImplicit false

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}

theorem jQFun_one_eq : ProlongationTuple.jQFun 1 q = (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) := by
  apply Subtype.ext
  change coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq)
  simp only [one_mul]

theorem jFun_one_eq : ProlongationTuple.jFun 1 q = (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) := rfl

theorem mem_dom_iff_reduceFst_eq (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ ssPlaces q 1 k)
    (a : k) (ha : w.evalAt (jGeomGen k 1) = a)
    (An : Annulus A ↥(modularFunctionFieldBar (1 * q)))
    (hdom : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), W ∈ An.dom ↔
          ((∃ x : A, red x = a ∧ 0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
           (∃ y : A, red y = a ^ q ∧ 0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))))
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) :
    V ∈ An.dom ↔ P.reduceFst V = w := by
  rw [hdom V, ModularCurve.PlaceSpecialization.reduceFst_eq_iff_centred_levelOne P w hw a ha V, jQFun_one_eq (q := q),
    jFun_one_eq (q := q)]

end ChartOkChartFst
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"

namespace ChartOkTwist

open AlgebraicCurve IsLocalRing
open Classical

set_option autoImplicit false

variable {L : Type*} [Field L] [IsAlgClosed L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]

theorem wide_of_modulus_ne_zero (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1) (An : Annulus A F)
    (hmod0 : (An.modulus : L) ≠ 0) :
    ∃ Q₁ ∈ An.dom, ∃ Q₂ ∈ An.dom, μ (Q₁.evalAt An.param) ≠ μ (Q₂.evalAt An.param) := by
  set π : L := (An.modulus : L) with hπ
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq π (by norm_num : 0 < 3)
  have hr0 : r ≠ 0 := by rintro rfl; apply hmod0; rw [← hr]; norm_num
  have hπm : An.modulus ∈ maximalIdeal A := An.modulus_mem
  have hμπ : μ π < 1 := (ChartOkAbv.abv_lt_one_iff_mem_maximalIdeal A μ hμA An.modulus.2 hmod0).mpr hπm
  have hμr : μ r < 1 := by
    have h3 : μ r ^ 3 = μ π := by rw [← map_pow, hr]
    by_contra hle; push_neg at hle
    have : 1 ≤ μ r ^ 3 := one_le_pow₀ hle
    linarith
  have hμr0 : 0 < μ r := μ.pos hr0
  have hrA : r ∈ A := (hμA r).mpr hμr.le
  have hr2A : r ^ 2 ∈ A := pow_mem hrA 2
  have hrm : (⟨r, hrA⟩ : A) ∈ maximalIdeal A := (ChartOkAbv.abv_lt_one_iff_mem_maximalIdeal A μ hμA hrA hr0).mp hμr
  have hr2m : (⟨r ^ 2, hr2A⟩ : A) ∈ maximalIdeal A := by
    have : (⟨r ^ 2, hr2A⟩ : A) = ⟨r, hrA⟩ ^ 2 := Subtype.ext (by simp)
    rw [this]; exact Ideal.pow_mem_of_mem _ hrm 2 (by norm_num)
  have hπr : π = r * r ^ 2 := by rw [← hr]; ring
  have hπr2 : π = r ^ 2 * r := by rw [← hr]; ring
  obtain ⟨Q₁, ⟨hQ₁, hz₁⟩, -⟩ := An.existsUnique_evalAt_eq ⟨r, hrA⟩ hrm hr0 ⟨⟨r ^ 2, hr2A⟩, hr2m, hπr⟩
  obtain ⟨Q₂, ⟨hQ₂, hz₂⟩, -⟩ := An.existsUnique_evalAt_eq ⟨r ^ 2, hr2A⟩ hr2m (pow_ne_zero 2 hr0) ⟨⟨r, hrA⟩, hrm, hπr2⟩
  refine ⟨Q₁, hQ₁, Q₂, hQ₂, ?_⟩
  change Q₁.evalAt An.param = r at hz₁
  change Q₂.evalAt An.param = r ^ 2 at hz₂
  rw [hz₁, hz₂, map_pow]
  intro h
  have : μ r * (1 - μ r) = 0 := by nlinarith [h]
  rcases mul_eq_zero.mp this with h1 | h1
  · exact (ne_of_gt hμr0) h1
  · exact absurd h1 (ne_of_gt (sub_pos.mpr hμr))

end ChartOkTwist
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"

namespace ChartOkChartFst

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~coeffMap_injective P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve.PlaceSpecialization.ProlongationTuple"
open Classical

set_option autoImplicit false

theorem exists_annulus_charts_isAttached_of_mem_ssPlaces
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (R : ProlongationTuple P) (hR : R.IsModel)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))]
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A) (hq : 5 ≤ q)
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1)
    (w : Place k ↥(modularFunctionFieldC k 1)) (hw : w ∈ ssPlaces q 1 k)
    (h0 : w.evalAt (jGeomGen k 1) ≠ 0) (h1728 : w.evalAt (jGeomGen k 1) ≠ 1728) :
    letI : Algebra (ResidueField A) ↥(modularFunctionFieldC k 1) := ((algebraMap k ↥(modularFunctionFieldC k 1)).comp R.redBar).toAlgebra
    ∃ (An An' : Annulus A ↥(modularFunctionFieldBar (1 * q)))
      (C₁ C₂ : ComponentChart A ↥(modularFunctionFieldBar (1 * q)) ↥(modularFunctionFieldC k 1))
      (x₁ x₂ : Place (ResidueField A) ↥(modularFunctionFieldC k 1)),
      (An'.dom = An.dom ∧ An'.modulus = An.modulus ∧ ((An.modulus : AlgebraicClosure ℚ) ≠ 0) ∧
        An'.param * An.param = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((An.modulus : AlgebraicClosure ℚ))) ∧
      An.modulus = ((q : ℕ) : A) ∧
      (∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), V ∈ An.dom ↔ P.reduceFst V = w) ∧
      An'.IsAttached C₁ x₁ ∧ An.IsAttached C₂ x₂ ∧
      C₁.integers = R.R₁.integers ∧ C₂.integers = R.R₂.integers ∧
      (∀ (g : ↥(modularFunctionFieldBar (1 * q))) (hg : g ∈ R.R₁.integers), ∃ hg' : g ∈ C₁.integers,
          C₁.residue ⟨g, hg'⟩ = R.residue₁ ⟨g, hg⟩) ∧
      (∀ (g : ↥(modularFunctionFieldBar (1 * q))) (hg : g ∈ R.R₂.integers), ∃ hg' : g ∈ C₂.integers,
          C₂.residue ⟨g, hg'⟩ = R.residue₂ ⟨g, hg⟩) ∧
      (∀ gbar : ↥(modularFunctionFieldC k 1), x₁.ord gbar = w.ord gbar) ∧
      (∀ gbar : ↥(modularFunctionFieldC k 1), x₂.ord gbar = (arithFrobC q k 1 • w).ord gbar) ∧
      (∃ Q₁ ∈ An.dom, ∃ Q₂ ∈ An.dom, μ (Q₁.evalAt An.param) ≠ μ (Q₂.evalAt An.param)) ∧
      (∃ Q₁ ∈ An'.dom, ∃ Q₂ ∈ An'.dom, μ (Q₁.evalAt An'.param) ≠ μ (Q₂.evalAt An'.param)) := by
  letI := algebraResidueField R

  obtain ⟨a, ha, hwa⟩ := (ModularCurve.mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq q k w).mp hw
  have hj0 : (jGeomGen k 1 : ↥(modularFunctionFieldC k 1)) - algebraMap k _ a ≠ 0 := jGeomGen_sub_algebraMap_ne_zero k 1 a
  have hord1 : 0 < (charLGeomPlaceOfPoint k a).ord ((jGeomGen k 1 : ↥(modularFunctionFieldC k 1)) - algebraMap k _ a) := by
    have h := ModularCurve.ord_charLGeomPlaceOfPoint_aeval_jqModC_eq_rootMultiplicity k a (Polynomial.X - Polynomial.C a)
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Polynomial.rootMultiplicity_X_sub_C_self] at h
    change (charLGeomPlaceOfPoint k a).ord (jGeomGen k 1 - algebraMap k _ a) = 1 at h
    rw [h]; exact zero_lt_one
  have hwa' : w.evalAt (jGeomGen k 1) = a := by
    rw [← hwa]
    have hmemc : algebraMap k ↥(modularFunctionFieldC k 1) a ∈ (charLGeomPlaceOfPoint k a).toValuationSubring :=
      (charLGeomPlaceOfPoint k a).algebraMap_mem' a
    have hmem : (jGeomGen k 1 : ↥(modularFunctionFieldC k 1)) ∈ (charLGeomPlaceOfPoint k a).toValuationSubring := by
      have := (charLGeomPlaceOfPoint k a).mem_of_ord_nonneg hj0 hord1.le
      simpa using add_mem this hmemc
    rw [AlgebraicCurve.Place.evalAt_congr _ hmem hmemc (Or.inr hord1), AlgebraicCurve.Place.evalAt_algebraMap]
  have h0a : a ≠ 0 := by rw [← hwa']; exact h0
  have h1728a : a ≠ 1728 := by rw [← hwa']; exact h1728
  have ha2 : a ^ (q ^ 2) = a := ModularCurve.pow_q_sq_eq_self_of_mem_ssJSet q ha
  obtain ⟨An, An', h4, hdom, hparam, hmod, hattS, hattF⟩ := exists_ssAnnulus_isAttached_both_ends_of_ne R hR hker hq a ha ha2 h0a h1728a
  have hφ : arithFrobC q k 1 • w = charLGeomPlaceOfPoint k (a ^ q) := by
    rw [ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel q k 1 data hKr w, ← hwa,
      ModularCurve.frobOnPlacesGeomLevel_charLGeomPlaceOfPoint k data hKr a]
  have hmod0 : (An.modulus : AlgebraicClosure ℚ) ≠ 0 := h4.2.2.1
  have hmod0' : (An'.modulus : AlgebraicClosure ℚ) ≠ 0 := by rw [h4.2.1]; exact hmod0
  refine ⟨An, An', chartFst R hR, chartSnd R hR, rc R w, rc R (arithFrobC q k 1 • w), h4, hmod,
    mem_dom_iff_reduceFst_eq w hw a hwa' An hdom, ?_, ?_, rfl, rfl, fun g hg => ⟨hg, rfl⟩, fun g hg => ⟨hg, rfl⟩,
    fun gbar => rfl, fun gbar => rfl,
    ChartOkTwist.wide_of_modulus_ne_zero μ hμA An hmod0, ChartOkTwist.wide_of_modulus_ne_zero μ hμA An' hmod0'⟩
  · rw [← hwa]; exact hattF
  · rw [hφ]; exact hattS

end ChartOkChartFst
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"

namespace ChartOkCPT

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~coeffMap_injective P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve.PlaceSpecialization.ProlongationTuple"
open Classical

set_option autoImplicit false

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}

theorem y_mem_and_ord (R : ProlongationTuple P) {K : IntermediateField ℚ (AlgebraicClosure ℚ)}
    {w : Place k ↥(modularFunctionFieldC k 1)} (c : R.NodeCoordinates K w) :
    ∃ hy : (c.y : ↥(modularFunctionFieldBar (1 * q))) ∈ R.R₁.integers,
      w.ord (R.residue₁ ⟨(c.y : ↥(modularFunctionFieldBar (1 * q))), hy⟩) = 1 ∧
      R.residue₁ ⟨(c.y : ↥(modularFunctionFieldBar (1 * q))), hy⟩ ≠ 0 := by
  refine ⟨c.y.2.1.1, ?_, ?_⟩
  · have := c.y_fst
    rwa [nodeResidue₁_apply] at this
  · intro h0
    have := c.y_fst
    rw [nodeResidue₁_apply] at this
    change w.ord (R.residue₁ ⟨(c.y : ↥(modularFunctionFieldBar (1 * q))), c.y.2.1.1⟩) = 1 at this
    rw [h0, Place.ord_zero] at this
    exact zero_ne_one this

theorem y_mem_place_and_evalAt_ne_zero (R : ProlongationTuple P) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place k ↥(modularFunctionFieldC k 1))) (hW : ∀ w ∈ W, w ∈ ssPlaces q 1 k)
    (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k ↥(modularFunctionFieldC k 1)) (hw : w ∈ W) (hVI : R.ValueIntegralityLaw w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K)) (hϖ0 : (ϖ : AlgebraicClosure ℚ) ≠ 0)
    (c : R.NodeCoordinates K w) (E : ℕ) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E * u)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hV : P.reduceFst V = w) :
    (c.y : ↥(modularFunctionFieldBar (1 * q))) ∈ V.toValuationSubring ∧ V.evalAt (c.y : ↥(modularFunctionFieldBar (1 * q))) ≠ 0 := by
  have hq1 : ¬ q ∣ 1 := fun h => (Fact.out : q.Prime).one_lt.ne' (Nat.dvd_one.mp h)
  obtain ⟨-, -, hprod⟩ := nodeDepths_lt_one_and_partition_of_nodeEquation_of_orderLawFixed R hq1 hR hO W hW hRL hNV K w hw hVI
    ϖ c E u hu hxy V hV
  refine ⟨c.y.2.1.2.2 V hV, ?_⟩
  intro h0
  have hy0 : c.yDepth V = 0 := by
    change A.valuation (V.evalAt (c.y : ↥(modularFunctionFieldBar (1 * q)))) = 0
    rw [h0, map_zero]
  rw [hy0, mul_zero] at hprod
  have hvϖ : A.valuation (ϖ : AlgebraicClosure ℚ) ≠ 0 := fun h => hϖ0 ((Valuation.zero_iff _).mp h)
  exact pow_ne_zero E hvϖ hprod.symm

end ChartOkCPT
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"

namespace ChartOkNT
p2m_open "AlgebraicCurve IsLocalRing ModularCurve~coeffMap_injective P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve ModularCurve.NodeLocalized ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve.PlaceSpecialization.ProlongationTuple"
open Classical

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

local notation "Qb" => AlgebraicClosure ℚ

theorem not_strict_of_reduceFst_mem (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    {W : Finset (Place k ↥(modularFunctionFieldC k 1))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (V : Place Qb ↥(modularFunctionFieldBar (1 * q))) {w : Place k ↥(modularFunctionFieldC k 1)} (hw : w ∈ W) (hV : P.reduceFst V = w) :
    ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V := by
  have hq1 : ¬ q ∣ 1 := fun h => (Fact.out : q.Prime).one_lt.ne' (Nat.dvd_one.mp h)
  have hφ : ∀ v : Place k ↥(modularFunctionFieldC k 1), frobOnPlacesGeomLevel k 1 data hKr v = arithFrobC q k 1 • v :=
    fun v => (ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel q k 1 data hKr v).symm
  have hfix2 : ∀ v ∈ W, arithFrobC q k 1 • (arithFrobC q k 1 • v) = v := fun v hv =>
    ModularCurve.arithFrobC_smul_arithFrobC_smul_eq_self_of_mem_ssPlaces q 1 hq1 k v ((hW v).mp hv)
  constructor
  · rintro ⟨-, h2⟩
    apply h2
    rw [hφ, hφ, hV]
    exact hfix2 w hw
  · rintro ⟨h1, h2⟩
    apply h2
    rw [hφ] at h1
    rw [hφ, hφ]
    have h3 : arithFrobC q k 1 • P.reduceSnd V = w := h1.symm.trans hV
    have hinj : Function.Injective fun v : Place k ↥(modularFunctionFieldC k 1) => arithFrobC q k 1 • v := MulAction.injective _
    have h4 : P.reduceSnd V = arithFrobC q k 1 • w := hinj (by simp only; rw [h3, hfix2 w hw])
    rw [h3, h4]

theorem divf_eq_neg_over (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    {W : Finset (Place k ↥(modularFunctionFieldC k 1))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    {d₁ d₂ : ℕ} (Q₁ : Fin d₁ → Place Qb ↥(modularFunctionFieldBar (1 * q))) (Q₂ : Fin d₂ → Place Qb ↥(modularFunctionFieldBar (1 * q)))
    (hQ₁ : ∀ i, P.IsStrictFst (Q₁ i)) (hQ₂ : ∀ j, P.IsStrictSnd (Q₂ j))
    (E D : Divisor Qb ↥(modularFunctionFieldBar (1 * q))) {w : Place k ↥(modularFunctionFieldC k 1)} (hw : w ∈ W)
    (hEw : ∀ V : Place Qb ↥(modularFunctionFieldBar (1 * q)), P.reduceFst V = w → E V = 0)
    (V : Place Qb ↥(modularFunctionFieldBar (1 * q))) (hV : P.reduceFst V = w) :
    (E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) - D) V = -(D V) := by
  have hns := not_strict_of_reduceFst_mem P hW V hw hV
  have h1 : (∑ i, Finsupp.single (Q₁ i) (1 : ℤ)) V = 0 := by
    rw [Finsupp.finset_sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finsupp.single_apply, if_neg]
    rintro rfl; exact hns.1 (hQ₁ i)
  have h2 : (∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) V = 0 := by
    rw [Finsupp.finset_sum_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finsupp.single_apply, if_neg]
    rintro rfl; exact hns.2 (hQ₂ j)
  rw [Finsupp.sub_apply, Finsupp.sub_apply, Finsupp.add_apply, h1, h2, hEw V hV]
  ring

theorem sum_second_diff (a : ℕ → ℤ) (n : ℕ) :
    ∑ d ∈ Finset.Ico 1 (n + 1), (a (d - 1) - 2 * a d + a (d + 1)) = a 0 - a 1 - a n + a (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Ico_succ_top (by omega), ih]
      simp only [Nat.add_sub_cancel]
      ring

end ChartOkNT
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"

namespace ChartOkTwist

open AlgebraicCurve IsLocalRing
open Classical

set_option autoImplicit false

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]

theorem ord_eq_zero_of_residue_ne_zero (v : Place L F) {f : F} (hf : f ∈ v.toValuationSubring)
    (hres : IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ ≠ 0) : v.ord f = 0 := by
  have hunit : IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
    by_contra h
    exact hres ((IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr h))
  obtain ⟨u, hu⟩ := hunit
  have := v.ord_coe_unit u
  rwa [hu] at this

theorem ord_prod_of_ne_zero (v : Place L F) {ι : Type*} (s : Finset ι) (f : ι → F) (hf : ∀ i ∈ s, f i ≠ 0) :
    v.ord (∏ i ∈ s, f i) = ∑ i ∈ s, v.ord (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj,
      v.ord_mul (hf j (Finset.mem_insert_self j s)) (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

theorem evalAt_param_ne (An : Annulus A F) {V R : Place L F} (hV : V ∈ An.dom) (hR : R ∈ An.dom) (hRV : R ≠ V) :
    V.evalAt An.param ≠ R.evalAt An.param := by
  obtain ⟨-, -, ⟨haR, hmaR⟩, hneR, mR, hmR, hmodR⟩ := An.mem_dom R hR
  intro heq
  obtain ⟨P, -, huniq⟩ := An.existsUnique_evalAt_eq ⟨_, haR⟩ hmaR hneR ⟨mR, hmR, hmodR⟩
  exact hRV ((huniq R ⟨hR, rfl⟩).trans (huniq V ⟨hV, heq⟩).symm)

theorem ord_param_sub_evalAt (An : Annulus A F) {V R : Place L F} (hV : V ∈ An.dom) (hR : R ∈ An.dom) :
    V.ord (An.param - algebraMap L F (R.evalAt An.param)) = if R = V then 1 else 0 := by
  split_ifs with hRV
  · rw [hRV]; exact An.ord_param_sub V hV
  · obtain ⟨hrat, hzV, -⟩ := An.mem_dom V hV
    have hne := evalAt_param_ne An hV hR hRV
    have hcmem : algebraMap L F (R.evalAt An.param) ∈ V.toValuationSubring := V.algebraMap_mem' _
    have hmem : An.param - algebraMap L F (R.evalAt An.param) ∈ V.toValuationSubring := sub_mem hzV hcmem
    apply ord_eq_zero_of_residue_ne_zero V hmem
    intro h0
    apply hne
    have hsplit : (⟨An.param - algebraMap L F (R.evalAt An.param), hmem⟩ : V.toValuationSubring)
        = ⟨An.param, hzV⟩ - ⟨algebraMap L F (R.evalAt An.param), hcmem⟩ := rfl
    have hres_c : IsLocalRing.residue V.toValuationSubring ⟨algebraMap L F (R.evalAt An.param), hcmem⟩
        = algebraMap L V.ResidueField (R.evalAt An.param) := V.residue_algebraMap _
    rw [hsplit, map_sub, ← V.algebraMap_evalAt hrat hzV, hres_c, ← map_sub] at h0
    exact sub_eq_zero.mp ((algebraMap L V.ResidueField).injective (h0.trans (map_zero _).symm))

theorem ord_twistMonomial (An : Annulus A F) (D : Place L F →₀ ℤ) (hD : ∀ P, D P ≠ 0 → P ∈ An.dom)
    {V : Place L F} (hV : V ∈ An.dom) :
    V.ord (∏ R ∈ D.support, (An.param - algebraMap L F (R.evalAt An.param)) ^ D R) = D V := by
  have hfac0 : ∀ R ∈ D.support, (An.param - algebraMap L F (R.evalAt An.param)) ^ D R ≠ 0 := by
    intro R hR
    apply zpow_ne_zero
    intro h0
    have := An.ord_param_sub R (hD R (Finsupp.mem_support_iff.mp hR))
    rw [h0, Place.ord_zero] at this
    exact zero_ne_one this
  rw [ord_prod_of_ne_zero V _ _ hfac0]
  have : ∀ R ∈ D.support, V.ord ((An.param - algebraMap L F (R.evalAt An.param)) ^ D R) = if R = V then D V else 0 := by
    intro R hR
    rw [V.ord_zpow, ord_param_sub_evalAt An hV (hD R (Finsupp.mem_support_iff.mp hR))]
    split_ifs with h <;> simp [h]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (Finsupp.notMem_support_iff.mp h).symm

end ChartOkTwist
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"

namespace ChartOkTwist

open AlgebraicCurve IsLocalRing
open Classical

set_option autoImplicit false

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]

theorem evalAt_mul_of_mem (v : Place L F) (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f * g) = v.evalAt f * v.evalAt g := by
  apply (algebraMap L v.ResidueField).injective
  rw [map_mul, v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg, v.algebraMap_evalAt hv (mul_mem hf hg)]
  rw [← map_mul]; rfl

theorem evalAt_algebraMap' (v : Place L F) (hv : v.IsRational) (a : L) (ha : algebraMap L F a ∈ v.toValuationSubring) :
    v.evalAt (algebraMap L F a) = a := by
  apply (algebraMap L v.ResidueField).injective
  rw [v.algebraMap_evalAt hv ha]
  rfl

theorem evalAt_param'_mul (An An' : Annulus A F) (hdom : An'.dom = An.dom)
    (htwo : An'.param * An.param = algebraMap L F (An.modulus : L)) {P : Place L F} (hP : P ∈ An.dom) :
    P.evalAt An'.param * P.evalAt An.param = (An.modulus : L) := by
  obtain ⟨hrat, hz, -⟩ := An.mem_dom P hP
  obtain ⟨-, hz', -⟩ := An'.mem_dom P (hdom ▸ hP)
  rw [← evalAt_mul_of_mem P hrat hz' hz, htwo]
  exact evalAt_algebraMap' P hrat _ (htwo ▸ mul_mem hz' hz)

end ChartOkTwist
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"

namespace ChartOkCPT

open AlgebraicCurve IsLocalRing
open Classical

set_option autoImplicit false

variable {L : Type*} [Field L] {A : ValuationSubring L}

theorem abv_le_abv_iff_valuation_le (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1) {a b : L} (hb : b ≠ 0) :
    μ a ≤ μ b ↔ A.valuation a ≤ A.valuation b := by
  rw [ChartOkAbv.abv_le_abv_iff_div_mem A μ hμA hb, ← A.valuation_le_one_iff, map_div₀,
    div_le_one₀ ((Valuation.pos_iff _).mpr hb)]

theorem abv_eq_abv_iff_valuation_eq (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1) {a b : L} (ha : a ≠ 0) (hb : b ≠ 0) :
    μ a = μ b ↔ A.valuation a = A.valuation b := by
  constructor
  · intro h; exact le_antisymm ((abv_le_abv_iff_valuation_le μ hμA hb).mp h.le) ((abv_le_abv_iff_valuation_le μ hμA ha).mp h.ge)
  · intro h; exact le_antisymm ((abv_le_abv_iff_valuation_le μ hμA hb).mpr h.le) ((abv_le_abv_iff_valuation_le μ hμA ha).mpr h.ge)

variable {F : Type*} [Field F] [Algebra L F]

theorem ord_eq_zero_of_evalAt_ne_zero (v : Place L F) (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring)
    (hne : v.evalAt f ≠ 0) : v.ord f = 0 := by
  apply ChartOkTwist.ord_eq_zero_of_residue_ne_zero v hf
  intro h0
  apply hne
  apply (algebraMap L v.ResidueField).injective
  rw [v.algebraMap_evalAt hv hf, h0, map_zero]

end ChartOkCPT
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"

namespace ChartOkCPT

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~coeffMap_injective P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve.PlaceSpecialization.ProlongationTuple"
open Classical

set_option autoImplicit false

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}

theorem x_mem_and_ord (R : ProlongationTuple P) {K : IntermediateField ℚ (AlgebraicClosure ℚ)}
    {w : Place k ↥(modularFunctionFieldC k 1)} (c : R.NodeCoordinates K w) :
    ∃ hx : (c.x : ↥(modularFunctionFieldBar (1 * q))) ∈ R.R₂.integers,
      (arithFrobC q k 1 • w).ord (R.residue₂ ⟨(c.x : ↥(modularFunctionFieldBar (1 * q))), hx⟩) = 1 ∧
      R.residue₂ ⟨(c.x : ↥(modularFunctionFieldBar (1 * q))), hx⟩ ≠ 0 := by
  refine ⟨c.x.2.1.2.1, ?_, ?_⟩
  · have := c.x_snd
    rwa [nodeResidue₂_apply] at this
  · intro h0
    have := c.x_snd
    rw [nodeResidue₂_apply] at this
    change (arithFrobC q k 1 • w).ord (R.residue₂ ⟨(c.x : ↥(modularFunctionFieldBar (1 * q))), c.x.2.1.2.1⟩) = 1 at this
    rw [h0, Place.ord_zero] at this
    exact zero_ne_one this

theorem x_mem_place_and_evalAt_ne_zero (R : ProlongationTuple P) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place k ↥(modularFunctionFieldC k 1))) (hW : ∀ w ∈ W, w ∈ ssPlaces q 1 k)
    (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k ↥(modularFunctionFieldC k 1)) (hw : w ∈ W) (hVI : R.ValueIntegralityLaw w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K)) (hϖ0 : (ϖ : AlgebraicClosure ℚ) ≠ 0)
    (c : R.NodeCoordinates K w) (E : ℕ) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E * u)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hV : P.reduceFst V = w) :
    (c.x : ↥(modularFunctionFieldBar (1 * q))) ∈ V.toValuationSubring ∧ V.evalAt (c.x : ↥(modularFunctionFieldBar (1 * q))) ≠ 0 ∧
      A.valuation (V.evalAt (c.x : ↥(modularFunctionFieldBar (1 * q)))) * A.valuation (V.evalAt (c.y : ↥(modularFunctionFieldBar (1 * q)))) = A.valuation (ϖ : AlgebraicClosure ℚ) ^ E := by
  have hq1 : ¬ q ∣ 1 := fun h => (Fact.out : q.Prime).one_lt.ne' (Nat.dvd_one.mp h)
  obtain ⟨-, -, hprod⟩ := nodeDepths_lt_one_and_partition_of_nodeEquation_of_orderLawFixed R hq1 hR hO W hW hRL hNV K w hw hVI
    ϖ c E u hu hxy V hV
  refine ⟨c.x.2.1.2.2 V hV, ?_, hprod⟩
  intro h0
  have hx0 : c.xDepth V = 0 := by
    change A.valuation (V.evalAt (c.x : ↥(modularFunctionFieldBar (1 * q)))) = 0
    rw [h0, map_zero]
  rw [hx0, zero_mul] at hprod
  have hvϖ : A.valuation (ϖ : AlgebraicClosure ℚ) ≠ 0 := fun h => hϖ0 ((Valuation.zero_iff _).mp h)
  exact pow_ne_zero E hvϖ hprod.symm

end ChartOkCPT
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~coeffMap_injective P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve.PlaceSpecialization"

section

end
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"

section
set_option synthInstance.maxHeartbeats 1600000
p2m_open "AlgebraicCurve IsLocalRing ModularCurve~coeffMap_injective P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"

section
set_option synthInstance.maxHeartbeats 1600000
p2m_open "AlgebraicCurve IsLocalRing ModularCurve~coeffMap_injective P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"

namespace ModularCurve p2m_export "ModularCurve" "qExpand jq ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange modularFunctionFieldBar jqModC jqNModC map_jqModC jqModC_eq_map_intCast modularFunctionFieldC jqModC_mem HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence frobOnPlacesGeomLevel PlaceSpecialization ratFuncEquivCharLOneC charLGeomPlaceOfPoint transcendental_jqModC jGeomGen jNGeomGen_one jGeomGen_sub_algebraMap_ne_zero IsAffineGeomPlace ssJSet IsSupersingularPlace ssPlaces arithFrobC frickeInvolutionBar coeffMap_jqModC modularFunctionFieldFullC coeffMap_qExpand CharPReduction.modularLocalized CharPReduction.modularRedLocHom PlaceSpecialization.ProlongationTuple PlaceSpecialization.LevelOneProlongationPair PlaceSpecialization.jFun PlaceSpecialization.jqFun NodeLocalized.modularEval NodeLocalized.modularLocalizedAtPoint NodeLocalized.modularEval_mem_modularLocalizedAtPoint NodeLocalized.coeffSubring NodeLocalized.redRestrict NodeLocalized.fieldOver jWidth jWidth_of_eq_zero jWidth_of_eq_1728 jWidth_pos jWidth_map placeRamificationJ placeWidth PlaceSpecialization.exists_levelOneProlongationPair_of_prolongationTuple PlaceSpecialization.reduceFst_eq_iff_centred_levelOne arithFrobC_smul_arithFrobC_smul_eq_self_of_mem_ssPlaces arithFrobC_smul_eq_frobOnPlacesGeomLevel exists_ssAnnulus_centred_ofNat1728_of_crossingPresentation_of_branchPrimes exists_ssAnnulus_centred_of_widthOne exists_ssAnnulus_centred_zero_of_crossingPresentation_of_branchPrimes finite_setOf_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self frobOnPlacesGeomLevel_charLGeomPlaceOfPoint mem_ssJSet_map_of_isAlgClosed mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq modularFunctionFieldC_eq_modularFunctionFieldFullC ord_charLGeomPlaceOfPoint_aeval_jqModC_eq_rootMultiplicity pow_mem_ssJSet_iff_of_perfectField pow_q_sq_eq_self_of_mem_ssJSet isAttached_ssAnnulus_zeroChart_of_chartSpec_levelOne_univ isAttached_oppAnnulus_inftyChart_of_chartSpec_levelOne_univ hasPrincipalDivisors_modularFunctionFieldBar_unconditional isAttached_ssAnnulus_zeroChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne_univ isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne_univ exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring PlaceSpecialization.LevelOneProlongationPair.residue_jFun_jqFun geomAut_atkinLehnerInvolutionFull_one_eq_frickeInvolutionBar" namespace PlaceSpecialization p2m_export "ModularCurve.PlaceSpecialization" "mk d2 d1 reduceFst reduceSnd IsStrictFst IsStrictSnd ProlongationTuple.atkinLehnerBar ProlongationTuple.jFun ProlongationTuple.jQFun ProlongationTuple LevelOneProlongationPair jFun jqFun ProlongationTuple.coe_nodeConst ProlongationTuple.divisorLawFst_oneSided_levelOne ProlongationTuple.divisorLawSnd_oneSided_levelOne ProlongationTuple.iota_bijective ProlongationTuple.redBar_bijective exists_levelOneProlongationPair_of_prolongationTuple reduceFst_eq_iff_centred_levelOne LevelOneProlongationPair.residue_jFun_jqFun" namespace ProlongationTuple p2m_export "ModularCurve.PlaceSpecialization.ProlongationTuple" "atkinLehnerBar jFun jQFun residue₁ residue₂ residue₁_apply residue₂_apply OrderLawFixed IsModel NodeValueLaw RegularityLaw ι_coe R₁ mk ι redBar_residue mem_integersFst_iff R₂ residue₁_eq_modularRedLocHom redBar mem_integersSnd_iff residue₂_eq nodeIntegers ord_nonneg_of_mem_nodeIntegers nodeResidue₁ nodeResidue₂ nodeResidue₁_apply nodeResidue₂_apply nodeIntegersOver nodeIntegersOver_le nodeConst coe_nodeConst NodeCoordinates ValueIntegralityLaw smoothLocalRingFst smoothLocalRingSnd mem_smoothLocalRingFst_iff mem_smoothLocalRingSnd_iff crossingExponent_eq_placeWidth_mul_of_orderLawFixed_levelOne divisorLawFst_oneSided_levelOne divisorLawSnd_oneSided_levelOne iota_bijective redBar_bijective mem_modularLocalizedAtPoint_iff_exists_mem_nodeIntegersOver nodeDepths_lt_one_and_partition_of_nodeEquation_of_orderLawFixed" end ModularCurve.PlaceSpecialization.ProlongationTuple
namespace ModularCurve.PlaceSpecialization.ProlongationTuple
p2m_open_scoped "ModularCurve ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple" in

private theorem _root_.ModularCurve.PlaceSpecialization.ProlongationTuple.exists_crossingPresentation_modularLocalizedAtPoint_coe_eq_of_nodeCoordinates
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hmodel : R.IsModel)
    (W : Finset (Place k (modularFunctionFieldC k 1))) (hW : ∀ w ∈ W, w ∈ ssPlaces q 1 k)
    (hreg : R.RegularityLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W)
    (a : k) (ha : w.evalAt (jGeomGen k 1) = a)
    (xa : ↥(NodeLocalized.coeffSubring A K)) (hxa : NodeLocalized.redRestrict red K xa = a)
    (ϖ : ↥(NodeLocalized.coeffSubring A K)) (eK : ℕ)
    (c : R.NodeCoordinates K w) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ (jWidth a * eK) * u)
    (hmax : (Ideal.span {R.nodeConst K w ϖ, c.x, c.y}).IsMaximal ∧
        ∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hbr : (Ideal.span {R.nodeConst K w ϖ, c.x}).IsPrime ∧ (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime ∧
        c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x} ∧ c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y})
    (hJS : PlaceSpecialization.jFun (q := q) ∈ R.nodeIntegersOver K w)
    (hJQS : PlaceSpecialization.jqFun (q := q) ∈ R.nodeIntegersOver K w)
    (hspx : Ideal.span {R.nodeConst K w ϖ, c.x} =
        Ideal.span {R.nodeConst K w ϖ, ⟨PlaceSpecialization.jqFun (q := q), hJQS⟩ - ⟨PlaceSpecialization.jFun (q := q), hJS⟩ ^ q})
    (hspy : Ideal.span {R.nodeConst K w ϖ, c.y} =
        Ideal.span {R.nodeConst K w ϖ, ⟨PlaceSpecialization.jFun (q := q), hJS⟩ - ⟨PlaceSpecialization.jqFun (q := q), hJQS⟩ ^ q}) :
    ∃ (G' H' w' : ↥(NodeLocalized.modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q))),
      (G' : LaurentSeries (AlgebraicClosure ℚ)) = (((c.x : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∧
      (H' : LaurentSeries (AlgebraicClosure ℚ)) = (((c.y : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∧
      (w' : LaurentSeries (AlgebraicClosure ℚ)) = ((u : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∧
      IsUnit w' ∧
      G' * H' = (⟨NodeLocalized.modularEval (1 * q) (NodeLocalized.coeffSubring A K) (MvPolynomial.C ϖ),
          NodeLocalized.modularEval_mem_modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q) _⟩ :
          ↥(NodeLocalized.modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q))) ^ (jWidth a * eK) * w' ∧
      (∀ [IsLocalRing ↥(NodeLocalized.modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q))],
        IsLocalRing.maximalIdeal ↥(NodeLocalized.modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q)) =
          Ideal.span {(⟨NodeLocalized.modularEval (1 * q) (NodeLocalized.coeffSubring A K) (MvPolynomial.C ϖ),
          NodeLocalized.modularEval_mem_modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q) _⟩ :
          ↥(NodeLocalized.modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q))), G', H'}) ∧
      (Ideal.span {(⟨NodeLocalized.modularEval (1 * q) (NodeLocalized.coeffSubring A K) (MvPolynomial.C ϖ),
          NodeLocalized.modularEval_mem_modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q) _⟩ :
          ↥(NodeLocalized.modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q))), G'}).IsPrime ∧
      (Ideal.span {(⟨NodeLocalized.modularEval (1 * q) (NodeLocalized.coeffSubring A K) (MvPolynomial.C ϖ),
          NodeLocalized.modularEval_mem_modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q) _⟩ :
          ↥(NodeLocalized.modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q))), H'}).IsPrime ∧
      H' ∉ Ideal.span {(⟨NodeLocalized.modularEval (1 * q) (NodeLocalized.coeffSubring A K) (MvPolynomial.C ϖ),
          NodeLocalized.modularEval_mem_modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q) _⟩ :
          ↥(NodeLocalized.modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q))), G'} ∧
      G' ∉ Ideal.span {(⟨NodeLocalized.modularEval (1 * q) (NodeLocalized.coeffSubring A K) (MvPolynomial.C ϖ),
          NodeLocalized.modularEval_mem_modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q) _⟩ :
          ↥(NodeLocalized.modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q))), H'} ∧
      Ideal.span {(⟨NodeLocalized.modularEval (1 * q) (NodeLocalized.coeffSubring A K) (MvPolynomial.C ϖ),
          NodeLocalized.modularEval_mem_modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q) _⟩ :
          ↥(NodeLocalized.modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q))), G'} = Ideal.span {(⟨NodeLocalized.modularEval (1 * q) (NodeLocalized.coeffSubring A K) (MvPolynomial.C ϖ),
          NodeLocalized.modularEval_mem_modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q) _⟩ :
          ↥(NodeLocalized.modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q))), (⟨NodeLocalized.modularEval (1 * q) (NodeLocalized.coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          NodeLocalized.modularEval_mem_modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q) _⟩ :
          ↥(NodeLocalized.modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q)))} ∧
      Ideal.span {(⟨NodeLocalized.modularEval (1 * q) (NodeLocalized.coeffSubring A K) (MvPolynomial.C ϖ),
          NodeLocalized.modularEval_mem_modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q) _⟩ :
          ↥(NodeLocalized.modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q))), H'} = Ideal.span {(⟨NodeLocalized.modularEval (1 * q) (NodeLocalized.coeffSubring A K) (MvPolynomial.C ϖ),
          NodeLocalized.modularEval_mem_modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q) _⟩ :
          ↥(NodeLocalized.modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q))), (⟨NodeLocalized.modularEval (1 * q) (NodeLocalized.coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          NodeLocalized.modularEval_mem_modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q) _⟩ :
          ↥(NodeLocalized.modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q)))} := by
  classical

  let ι : ↥(R.nodeIntegersOver K w) →+* LaurentSeries (AlgebraicClosure ℚ) :=
    (algebraMap ↥(modularFunctionFieldBar (1 * q)) (LaurentSeries (AlgebraicClosure ℚ))).comp (R.nodeIntegersOver K w).subtype
  have hι : ∀ g : ↥(R.nodeIntegersOver K w), ι g = ((g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) :=
    fun g => rfl
  have hιinj : Function.Injective ι := by
    intro g g' h
    rw [hι, hι] at h
    exact Subtype.ext (Subtype.ext h)

  have hιmem : ∀ g : ↥(R.nodeIntegersOver K w), ι g ∈ NodeLocalized.modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q) := fun g =>
    (R.mem_modularLocalizedAtPoint_iff_exists_mem_nodeIntegersOver hmodel W hW hreg K w hw a ha xa hxa (ι g)).mpr
      ⟨g, g.2, rfl⟩
  let ιR : ↥(R.nodeIntegersOver K w) →+* ↥(NodeLocalized.modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q)) := ι.codRestrict (NodeLocalized.modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q)) hιmem
  have hιR : ∀ g : ↥(R.nodeIntegersOver K w), ((ιR g : ↥(NodeLocalized.modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q))) : LaurentSeries (AlgebraicClosure ℚ)) = ι g := fun g => rfl
  have hbij : Function.Bijective ιR := by
    refine ⟨fun g g' h => hιinj (congrArg (fun z : ↥(NodeLocalized.modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q)) => (z : LaurentSeries (AlgebraicClosure ℚ))) h), fun f => ?_⟩
    obtain ⟨g, hg, hgf⟩ :=
      (R.mem_modularLocalizedAtPoint_iff_exists_mem_nodeIntegersOver hmodel W hW hreg K w hw a ha xa hxa f).mp f.2
    exact ⟨⟨g, hg⟩, Subtype.ext hgf⟩
  let e : ↥(R.nodeIntegersOver K w) ≃+* ↥(NodeLocalized.modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q)) := RingEquiv.ofBijective ιR hbij
  have he : ∀ g : ↥(R.nodeIntegersOver K w), ((e g : ↥(NodeLocalized.modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q))) : LaurentSeries (AlgebraicClosure ℚ)) = ι g := fun g => rfl

  have heϖ : e (R.nodeConst K w ϖ) = ⟨NodeLocalized.modularEval (1 * q) (NodeLocalized.coeffSubring A K) (MvPolynomial.C ϖ),
      NodeLocalized.modularEval_mem_modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K)
        (NodeLocalized.redRestrict red K) a (a ^ q) _⟩ := by
    apply Subtype.ext
    rw [he, hι]
    change (((R.nodeConst K w ϖ) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) =
      NodeLocalized.modularEval (1 * q) (NodeLocalized.coeffSubring A K) (MvPolynomial.C ϖ)
    rw [NodeLocalized.modularEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, ProlongationTuple.coe_nodeConst]
    rfl
  refine ⟨e c.x, e c.y, e u, rfl, rfl, rfl, hu.map e, ?_, ?_⟩
  ·
    have := congrArg e hxy
    rw [map_mul, map_mul, map_pow, heϖ] at this
    exact this

  have heJ : e ⟨PlaceSpecialization.jFun (q := q), hJS⟩ =
      ⟨NodeLocalized.modularEval (1 * q) (NodeLocalized.coeffSubring A K) (MvPolynomial.X 0),
        NodeLocalized.modularEval_mem_modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K)
          (NodeLocalized.redRestrict red K) a (a ^ q) _⟩ := by
    apply Subtype.ext
    rw [he, hι]
    change ModularCurve.coeffEmb (AlgebraicClosure ℚ) jq = NodeLocalized.modularEval (1 * q) (NodeLocalized.coeffSubring A K) (MvPolynomial.X 0)
    rw [NodeLocalized.modularEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
    change ModularCurve.coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (ModularCurve.jqModC ℚ) = ModularCurve.jqModC (AlgebraicClosure ℚ)
    exact ModularCurve.map_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))
  have heJQ : e ⟨PlaceSpecialization.jqFun (q := q), hJQS⟩ =
      ⟨NodeLocalized.modularEval (1 * q) (NodeLocalized.coeffSubring A K) (MvPolynomial.X 1),
        NodeLocalized.modularEval_mem_modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K)
          (NodeLocalized.redRestrict red K) a (a ^ q) _⟩ := by
    apply Subtype.ext
    rw [he, hι]
    change ModularCurve.coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq) =
      NodeLocalized.modularEval (1 * q) (NodeLocalized.coeffSubring A K) (MvPolynomial.X 1)
    rw [NodeLocalized.modularEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
    change ModularCurve.coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (qExpand ℚ (1 * q) (ModularCurve.jqModC ℚ)) =
      qExpand (AlgebraicClosure ℚ) (1 * q) (ModularCurve.jqModC (AlgebraicClosure ℚ))
    rw [ModularCurve.coeffMap_qExpand]
    congr 1
    exact ModularCurve.map_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))

  have hspan2 : ∀ s₁ s₂ : ↥(R.nodeIntegersOver K w), Ideal.map e (Ideal.span {s₁, s₂}) = Ideal.span {e s₁, e s₂} := by
    intro s₁ s₂
    rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
  have hspan3 : ∀ s₁ s₂ s₃ : ↥(R.nodeIntegersOver K w),
      Ideal.map e (Ideal.span {s₁, s₂, s₃}) = Ideal.span {e s₁, e s₂, e s₃} := by
    intro s₁ s₂ s₃
    rw [Ideal.map_span, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
  have hmem : ∀ (I : Ideal ↥(R.nodeIntegersOver K w)) (s : ↥(R.nodeIntegersOver K w)), e s ∈ Ideal.map e I ↔ s ∈ I := by
    intro I s
    rw [← Ideal.comap_symm, Ideal.mem_comap]
    simp
  have hprime : ∀ (I : Ideal ↥(R.nodeIntegersOver K w)), I.IsPrime → (Ideal.map e I).IsPrime := by
    intro I hI
    exact Ideal.map_isPrime_of_equiv e
  obtain ⟨hp1, hp2, hn1, hn2⟩ := hbr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro _inst
    have hM : (Ideal.map e (Ideal.span {R.nodeConst K w ϖ, c.x, c.y})).IsMaximal := by
      haveI := hmax.1
      exact Ideal.map_isMaximal_of_equiv e
    rw [hspan3, heϖ] at hM
    exact (IsLocalRing.eq_maximalIdeal hM).symm
  · have := hprime _ hp1; rwa [hspan2, heϖ] at this
  · have := hprime _ hp2; rwa [hspan2, heϖ] at this
  · rw [← heϖ, ← hspan2, hmem]; exact hn1
  · rw [← heϖ, ← hspan2, hmem]; exact hn2
  · have := congrArg (Ideal.map e) hspx
    rw [hspan2, hspan2, heϖ, map_sub, map_pow, heJ, heJQ] at this
    convert this using 4
    apply Subtype.ext
    simp [map_sub, map_pow]
  · have := congrArg (Ideal.map e) hspy
    rw [hspan2, hspan2, heϖ, map_sub, map_pow, heJ, heJQ] at this
    convert this using 4
    apply Subtype.ext
    simp [map_sub, map_pow]

end ModularCurve.PlaceSpecialization.ProlongationTuple
p2m_export "" "ModularCurve.PlaceSpecialization.ProlongationTuple.exists_crossingPresentation_modularLocalizedAtPoint_coe_eq_of_nodeCoordinates"
namespace ChartOkChartFst

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~coeffMap_injective P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve.PlaceSpecialization.ProlongationTuple"
open Classical

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}

theorem mem_ssJSet_of_evalAt_eq (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ ssPlaces q 1 k)
    (a : k) (ha : w.evalAt (jGeomGen k 1) = a) : a ∈ ssJSet q k ∧ charLGeomPlaceOfPoint k a = w := by
  obtain ⟨b, hb, hwb⟩ := (ModularCurve.mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq q k w).mp hw
  have hj0 : (jGeomGen k 1 : ↥(modularFunctionFieldC k 1)) - algebraMap k _ b ≠ 0 := jGeomGen_sub_algebraMap_ne_zero k 1 b
  have hord1 : 0 < (charLGeomPlaceOfPoint k b).ord ((jGeomGen k 1 : ↥(modularFunctionFieldC k 1)) - algebraMap k _ b) := by
    have h := ModularCurve.ord_charLGeomPlaceOfPoint_aeval_jqModC_eq_rootMultiplicity k b (Polynomial.X - Polynomial.C b)
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Polynomial.rootMultiplicity_X_sub_C_self] at h
    change (charLGeomPlaceOfPoint k b).ord (jGeomGen k 1 - algebraMap k _ b) = 1 at h
    rw [h]; exact zero_lt_one
  have hwb' : w.evalAt (jGeomGen k 1) = b := by
    rw [← hwb]
    have hmemc : algebraMap k ↥(modularFunctionFieldC k 1) b ∈ (charLGeomPlaceOfPoint k b).toValuationSubring :=
      (charLGeomPlaceOfPoint k b).algebraMap_mem' b
    have hmem : (jGeomGen k 1 : ↥(modularFunctionFieldC k 1)) ∈ (charLGeomPlaceOfPoint k b).toValuationSubring := by
      have := (charLGeomPlaceOfPoint k b).mem_of_ord_nonneg hj0 hord1.le
      simpa using add_mem this hmemc
    rw [AlgebraicCurve.Place.evalAt_congr _ hmem hmemc (Or.inr hord1), AlgebraicCurve.Place.evalAt_algebraMap]
  have hab : a = b := ha.symm.trans hwb'
  subst hab
  exact ⟨hb, hwb⟩

theorem gauss_snd_of_mem (R : ProlongationTuple P) (hA : A.LiesOverPrime q) [CharP (ResidueField A) q]
    (g : ↥(modularFunctionFieldBar (1 * q))) (hg : g ∈ R.R₂.integers) :
    ∃ (h : ((frickeInvolutionBar (1 * q) g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized (1 * q) A.toSubring (IsLocalRing.residue A))
      (hF : CharPReduction.modularRedLocHom (1 * q) A.toSubring (IsLocalRing.residue A) ⟨_, h⟩ ∈
            modularFunctionFieldC (ResidueField A) 1),
      ((R.residue₂ ⟨g, hg⟩ : ↥(modularFunctionFieldC k 1)) : LaurentSeries k) =
        coeffMap R.redBar (CharPReduction.modularRedLocHom (1 * q) A.toSubring (IsLocalRing.residue A) ⟨_, h⟩) := by
  have hAL := (R.mem_integersSnd_iff g).mp hg
  rw [atkinLehnerBar_one_eq, modularLocalized_red_eq R] at hAL
  obtain ⟨hg', e⟩ := mem_integersSnd_and_coe_residue₂_eq R g hAL
  have e2 : ((R.residue₂ ⟨g, hg'⟩ : ↥(modularFunctionFieldC k 1)) : LaurentSeries k) =
      coeffMap R.redBar ((R.R₂.residue ⟨g, hg'⟩ : ↥(modularFunctionFieldFullC (ResidueField A) 1)) : LaurentSeries (ResidueField A)) := by
    rw [residue₂_apply, R.ι_coe]
  have e3 : ((R.R₂.residue ⟨g, hg'⟩ : ↥(modularFunctionFieldFullC (ResidueField A) 1)) : LaurentSeries (ResidueField A)) =
      CharPReduction.modularRedLocHom (1 * q) A.toSubring (IsLocalRing.residue A) ⟨_, hAL⟩ :=
    FltWs21.RedIndep.coeffMap_injective R.redBar R.redBar.injective (e2.symm.trans e)
  have hF : CharPReduction.modularRedLocHom (1 * q) A.toSubring (IsLocalRing.residue A) ⟨_, hAL⟩ ∈
      modularFunctionFieldC (ResidueField A) 1 := by
    rw [← e3, ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC (ResidueField A) q 1
      (fun h => (Fact.out : q.Prime).one_lt.ne' (Nat.dvd_one.mp h))]
    exact (R.R₂.residue ⟨g, hg'⟩).2
  exact ⟨hAL, hF, e⟩

theorem gauss_fst_of_mem (R : ProlongationTuple P) (hA : A.LiesOverPrime q) [CharP (ResidueField A) q]
    (g : ↥(modularFunctionFieldBar (1 * q))) (hg : g ∈ R.R₁.integers) :
    ∃ (h : ((g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized (1 * q) A.toSubring (IsLocalRing.residue A))
      (hF : CharPReduction.modularRedLocHom (1 * q) A.toSubring (IsLocalRing.residue A) ⟨_, h⟩ ∈
            modularFunctionFieldC (ResidueField A) 1),
      ((R.residue₁ ⟨g, hg⟩ : ↥(modularFunctionFieldC k 1)) : LaurentSeries k) =
        coeffMap R.redBar (CharPReduction.modularRedLocHom (1 * q) A.toSubring (IsLocalRing.residue A) ⟨_, h⟩) := by
  have h₁ := (R.mem_integersFst_iff g).mp hg
  rw [modularLocalized_red_eq R] at h₁
  obtain ⟨hg', e⟩ := mem_integersFst_and_coe_residue₁_eq R g h₁
  have e2 : ((R.residue₁ ⟨g, hg'⟩ : ↥(modularFunctionFieldC k 1)) : LaurentSeries k) =
      coeffMap R.redBar ((R.R₁.residue ⟨g, hg'⟩ : ↥(modularFunctionFieldFullC (ResidueField A) 1)) : LaurentSeries (ResidueField A)) := by
    rw [residue₁_apply, R.ι_coe]
  have e3 : ((R.R₁.residue ⟨g, hg'⟩ : ↥(modularFunctionFieldFullC (ResidueField A) 1)) : LaurentSeries (ResidueField A)) =
      CharPReduction.modularRedLocHom (1 * q) A.toSubring (IsLocalRing.residue A) ⟨_, h₁⟩ :=
    FltWs21.RedIndep.coeffMap_injective R.redBar R.redBar.injective (e2.symm.trans e)
  have hF : CharPReduction.modularRedLocHom (1 * q) A.toSubring (IsLocalRing.residue A) ⟨_, h₁⟩ ∈
      modularFunctionFieldC (ResidueField A) 1 := by
    rw [← e3, ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC (ResidueField A) q 1
      (fun h => (Fact.out : q.Prime).one_lt.ne' (Nat.dvd_one.mp h))]
    exact (R.R₁.residue ⟨g, hg'⟩).2
  exact ⟨h₁, hF, e⟩

theorem ord_residue_eq_zero_of_mul_eq_one (R : ProlongationTuple P)
    (W : Finset (Place k (modularFunctionFieldC k 1))) (hW : ∀ w ∈ W, w ∈ ssPlaces q 1 k) (hreg : R.RegularityLaw W)
    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W)
    (f fi : ↥(modularFunctionFieldBar (1 * q))) (hf : f ∈ R.nodeIntegers w) (hfi : fi ∈ R.nodeIntegers w) (h1 : f * fi = 1) :
    w.ord (R.residue₁ ⟨f, hf.1⟩) = 0 ∧ (arithFrobC q k 1 • w).ord (R.residue₂ ⟨f, hf.2.1⟩) = 0 := by
  have hss := hW w hw
  have hfix : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr w) = w := by
    have h := ModularCurve.arithFrobC_smul_arithFrobC_smul_eq_self_of_mem_ssPlaces q 1
      (fun h => (Fact.out : q.Prime).one_lt.ne' (Nat.dvd_one.mp h)) k w hss
    rwa [ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel q k 1 data hKr,
      ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel q k 1 data hKr] at h
  have haff : IsAffineGeomPlace k 1 w := (show IsSupersingularPlace q 1 k w from hss).2.1
  have hφ : arithFrobC q k 1 • w = frobOnPlacesGeomLevel k 1 data hKr w :=
    ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel q k 1 data hKr w

  have hprod1 : R.residue₁ ⟨f, hf.1⟩ * R.residue₁ ⟨fi, hfi.1⟩ = 1 := by
    rw [← map_mul, ← map_one R.residue₁]; congr 1; exact Subtype.ext h1
  have hprod2 : R.residue₂ ⟨f, hf.2.1⟩ * R.residue₂ ⟨fi, hfi.2.1⟩ = 1 := by
    rw [← map_mul, ← map_one R.residue₂]; congr 1; exact Subtype.ext h1
  have hne1 : R.residue₁ ⟨f, hf.1⟩ ≠ 0 := left_ne_zero_of_mul_eq_one hprod1
  have hne1' : R.residue₁ ⟨fi, hfi.1⟩ ≠ 0 := right_ne_zero_of_mul_eq_one hprod1
  have hne2 : R.residue₂ ⟨f, hf.2.1⟩ ≠ 0 := left_ne_zero_of_mul_eq_one hprod2
  have hne2' : R.residue₂ ⟨fi, hfi.2.1⟩ ≠ 0 := right_ne_zero_of_mul_eq_one hprod2
  have hreg_f := hreg.1 f hf.1 hf.2.1 w hfix haff (fun V hV => V.ord_nonneg_of_mem (hf.2.2 V hV))
  have hreg_fi := hreg.1 fi hfi.1 hfi.2.1 w hfix haff (fun V hV => V.ord_nonneg_of_mem (hfi.2.2 V hV))
  have hs1 : w.ord (R.residue₁ ⟨f, hf.1⟩) + w.ord (R.residue₁ ⟨fi, hfi.1⟩) = 0 := by
    rw [← Place.ord_mul _ hne1 hne1', hprod1, Place.ord_one]
  have hs2 : (arithFrobC q k 1 • w).ord (R.residue₂ ⟨f, hf.2.1⟩) + (arithFrobC q k 1 • w).ord (R.residue₂ ⟨fi, hfi.2.1⟩) = 0 := by
    rw [← Place.ord_mul _ hne2 hne2', hprod2, Place.ord_one]
  have h1a := hreg_f.1 hne1
  have h1b := hreg_fi.1 hne1'
  have h2a := hreg_f.2 hne2
  have h2b := hreg_fi.2 hne2'
  rw [← hφ] at h2a h2b
  exact ⟨by omega, by omega⟩

theorem attach_both_wide (R : ProlongationTuple P) (hR : R.IsModel)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))]
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A) (hq : 5 ≤ q)
    (W : Finset (Place k (modularFunctionFieldC k 1))) (hW : ∀ w ∈ W, w ∈ ssPlaces q 1 k) (hreg : R.RegularityLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W)
    (a : k) (ha : w.evalAt (jGeomGen k 1) = a) (hj : a = 0 ∨ a = 1728)
    (xa : ↥(NodeLocalized.coeffSubring A K)) (hxa : NodeLocalized.redRestrict red K xa = a)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (eK : ℕ) (heK : 1 ≤ eK) (ε : ↥(NodeLocalized.coeffSubring A K)) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε)
    (c : R.NodeCoordinates K w) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ (jWidth a * eK) * u)
    (hmax : (Ideal.span {R.nodeConst K w ϖ, c.x, c.y}).IsMaximal ∧
        ∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hbr : (Ideal.span {R.nodeConst K w ϖ, c.x}).IsPrime ∧ (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime ∧
        c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x} ∧ c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y})
    (hJS : PlaceSpecialization.jFun (q := q) ∈ R.nodeIntegersOver K w)
    (hJQS : PlaceSpecialization.jqFun (q := q) ∈ R.nodeIntegersOver K w)
    (hspx : Ideal.span {R.nodeConst K w ϖ, c.x} =
        Ideal.span {R.nodeConst K w ϖ, ⟨PlaceSpecialization.jqFun (q := q), hJQS⟩ - ⟨PlaceSpecialization.jFun (q := q), hJS⟩ ^ q})
    (hspy : Ideal.span {R.nodeConst K w ϖ, c.y} =
        Ideal.span {R.nodeConst K w ϖ, ⟨PlaceSpecialization.jFun (q := q), hJS⟩ - ⟨PlaceSpecialization.jqFun (q := q), hJQS⟩ ^ q})
    (hVI : R.ValueIntegralityLaw w)
    (An An' : Annulus A ↥(modularFunctionFieldBar (1 * q)))
    (h4 : An'.dom = An.dom ∧ An'.modulus = An.modulus ∧ ((An.modulus : AlgebraicClosure ℚ) ≠ 0) ∧
        An'.param * An.param = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((An.modulus : AlgebraicClosure ℚ)))
    (hdom : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
        W ∈ An.dom ↔
          ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))))
    (hparamx : An.param = ((c.x : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))))
    (hmodw : An.modulus = ((q : ℕ) : A) ^ jWidth a)
    (hss : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) :
    letI := algebraResidueField R
    An.IsAttached (chartSnd R hR) (rc R (charLGeomPlaceOfPoint k (a ^ q))) ∧
    An'.IsAttached (chartFst R hR) (rc R (charLGeomPlaceOfPoint k a)) := by
  letI := algebraResidueField R
  haveI hA : A.LiesOverPrime q := liesOverPrime_of_ker R hker
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
  letI : DecidableEq (ResidueField A) := Classical.decEq _
  let e : ResidueField A ≃+* k := RingEquiv.ofBijective R.redBar (ProlongationTuple.redBar_bijective R)
  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  set aκ : ResidueField A := e.symm a with haκ
  have hred : R.redBar aκ = a := e.apply_symm_apply a
  have hredq : R.redBar (aκ ^ q) = a ^ q := by rw [map_pow, hred]
  have hssκ : aκ ∈ ssJSet q (ResidueField A) :=
    ModularCurve.mem_ssJSet_map_of_isAlgClosed (e.symm : k →+* ResidueField A) a hss
  have haκ2 : aκ ^ (q ^ 2) = aκ := e.injective (by
    change R.redBar (aκ ^ (q ^ 2)) = R.redBar aκ
    rw [map_pow, hred, ha2])
  have hwκ : aκ = 0 ∨ aκ = 1728 := by
    rcases hj with h | h
    · left; rw [haκ, h, map_zero]
    · right; rw [haκ, h, map_ofNat]
  have hjW : jWidth aκ = jWidth a := jWidth_map (e.symm : k →+* ResidueField A) a
  have hwpl : charLGeomPlaceOfPoint k a = w := (mem_ssJSet_of_evalAt_eq w (hW w hw) a ha).2
  have hφ : arithFrobC q k 1 • w = charLGeomPlaceOfPoint k (a ^ q) := by
    rw [ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel q k 1 data hKr w, ← hwpl,
      ModularCurve.frobOnPlacesGeomLevel_charLGeomPlaceOfPoint k data hKr a]

  have hredres : ∀ x : A, red x = R.redBar (IsLocalRing.residue A x) := fun x => (R.redBar_residue x).symm
  have hinj := (ProlongationTuple.redBar_bijective R).1
  have hiffx : ∀ x : A, red x = a ↔ IsLocalRing.residue A x = aκ := fun x => by
    rw [hredres, ← hred]; exact ⟨fun h => hinj h, fun h => by rw [h]⟩
  have hiffy : ∀ y : A, red y = a ^ q ↔ IsLocalRing.residue A y = aκ ^ q := fun y => by
    rw [hredres, ← hredq]; exact ⟨fun h => hinj h, fun h => by rw [h]⟩
  have hdom' : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), W ∈ An.dom ↔
      ((∃ x : A, IsLocalRing.residue ↥A x = aκ ∧
        0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
       (∃ y : A, IsLocalRing.residue ↥A y = aκ ^ q ∧
        0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) := by
    intro W
    rw [hdom W]
    simp only [hiffx, hiffy]

  have hxN : ((c.x : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))) ∈ R.nodeIntegers w := c.x.2.1
  obtain ⟨hx, hxF, ex⟩ := gauss_snd_of_mem R hA _ hxN.2.1
  have hx_ne : R.residue₂ ⟨_, hxN.2.1⟩ ≠ 0 := by
    have := c.nodeResidue₂_x_ne_zero; rwa [nodeResidue₂_apply] at this
  have hx_ord : (arithFrobC q k 1 • w).ord (R.residue₂ ⟨_, hxN.2.1⟩) = 1 := by
    have := c.x_snd; rwa [nodeResidue₂_apply] at this
  have hzg : ∃ (h : ((frickeInvolutionBar (1 * q) ((c.x : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized (1 * q) A.toSubring (IsLocalRing.residue ↥A))
         (hF : CharPReduction.modularRedLocHom (1 * q) A.toSubring (IsLocalRing.residue ↥A) ⟨_, h⟩ ∈ modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1),
         CharPReduction.modularRedLocHom (1 * q) A.toSubring (IsLocalRing.residue ↥A) ⟨_, h⟩ ≠ 0 ∧
         (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (aκ ^ q)).ord (⟨_, hF⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) = 1 := by
    refine ⟨hx, hxF, ?_, ?_⟩
    · intro h0
      apply hx_ne
      apply Subtype.ext
      rw [ex, h0, map_zero]
      rfl
    · have hoe := FltWs21.OrdExt.ord_charLGeomPlaceOfPoint_eq_of_coe_eq_coeffMap (ResidueField A) k R.redBar (aκ ^ q)
        ⟨_, hxF⟩ (R.residue₂ ⟨_, hxN.2.1⟩) ex
      rw [hredq, ← hφ] at hoe
      rw [← hoe]
      exact hx_ord

  have hx0 : ((c.x : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))) ≠ 0 := by
    intro h0
    apply hx_ne
    have : (⟨_, hxN.2.1⟩ : ↥R.R₂.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  let vU : ↥(R.nodeIntegersOver K w) := ↑(hu.unit⁻¹) * R.nodeConst K w (ε ^ jWidth a)
  have hvU_unit : IsUnit vU := (hu.unit⁻¹).isUnit.mul ((hε.pow _).map _)
  obtain ⟨vUi, hvUi⟩ := hvU_unit.exists_right_inv
  have huinv : ((u : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))) * ((↑(hu.unit⁻¹) : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))) = 1 := by
    have := congrArg (fun t : ↥(R.nodeIntegersOver K w) => (t : ↥(modularFunctionFieldBar (1 * q)))) hu.mul_val_inv
    simp only [Subring.coe_mul, OneMemClass.coe_one] at this
    exact this
  have hxyF : ((c.x : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))) * ((c.y : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))) =
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ^ (jWidth a * eK)) * ((u : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))) := by
    have := congrArg (fun t : ↥(R.nodeIntegersOver K w) => (t : ↥(modularFunctionFieldBar (1 * q)))) hxy
    simpa [map_pow] using this
  have hqQ : ((q : ℕ) : AlgebraicClosure ℚ) =
      ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ^ eK * ((ε : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) := by
    have := congrArg (fun t : ↥(NodeLocalized.coeffSubring A K) => (t : AlgebraicClosure ℚ)) hqϖ
    simpa using this
  have hvU_coe : ((vU : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))) = ((↑(hu.unit⁻¹) : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))) *
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (((ε : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ^ jWidth a) := by
    show ((↑(hu.unit⁻¹) * R.nodeConst K w (ε ^ jWidth a) : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))) = _
    rw [Subring.coe_mul, coe_nodeConst, SubmonoidClass.coe_pow]
  have hcoe : ((((q : ℕ) : ↥A) ^ jWidth a : ↥A) : AlgebraicClosure ℚ) = ((q : ℕ) : AlgebraicClosure ℚ) ^ jWidth a := by
    norm_cast
  have hPx : An'.param * ((c.x : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))) =
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (((q : ℕ) : AlgebraicClosure ℚ) ^ jWidth a) := by
    rw [← hparamx, h4.2.2.2, hmodw, hcoe]
  have hz' : An'.param = ((c.y * vU : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))) := by
    apply mul_right_cancel₀ hx0
    rw [hPx, Subring.coe_mul, hvU_coe, hqQ, mul_pow, ← pow_mul, map_mul, map_pow, map_pow]
    rw [mul_comm (jWidth a) eK, map_pow] at hxyF
    linear_combination (-(algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) ((ε : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ)) ^ jWidth a *
        ((↑(hu.unit⁻¹) : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q)))) * hxyF +
      (-(algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) ((ε : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ)) ^ jWidth a *
        (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ)) ^ (eK * jWidth a)) * huinv
  have hz'N : An'.param ∈ R.nodeIntegers w := by rw [hz']; exact (c.y * vU).2.1
  obtain ⟨hz1, hz1F, ez⟩ := gauss_fst_of_mem R hA An'.param hz'N.1
  have hvU_N : ((vU : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))) ∈ R.nodeIntegers w := vU.2.1
  have hvUi_N : ((vUi : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))) ∈ R.nodeIntegers w := vUi.2.1
  have hvv : ((vU : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))) * ((vUi : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))) = 1 := by
    have := congrArg (fun t : ↥(R.nodeIntegersOver K w) => (t : ↥(modularFunctionFieldBar (1 * q)))) hvUi
    simpa using this
  have hordv := (ord_residue_eq_zero_of_mul_eq_one R W hW hreg w hw _ _ hvU_N hvUi_N hvv).1
  have hprodv : R.residue₁ ⟨_, hvU_N.1⟩ * R.residue₁ ⟨_, hvUi_N.1⟩ = 1 := by
    rw [← map_mul, ← map_one R.residue₁]; congr 1; exact Subtype.ext hvv
  have hv_ne : R.residue₁ ⟨_, hvU_N.1⟩ ≠ 0 := left_ne_zero_of_mul_eq_one hprodv
  have hy_ord : w.ord (R.residue₁ ⟨_, c.y.2.1.1⟩) = 1 := by
    have := c.y_fst; rwa [nodeResidue₁_apply] at this
  have hy_ne : R.residue₁ ⟨_, c.y.2.1.1⟩ ≠ 0 := by
    have := c.nodeResidue₁_y_ne_zero; rwa [nodeResidue₁_apply] at this
  have hz_res : R.residue₁ ⟨An'.param, hz'N.1⟩ = R.residue₁ ⟨_, c.y.2.1.1⟩ * R.residue₁ ⟨_, hvU_N.1⟩ := by
    rw [← map_mul]; congr 1; apply Subtype.ext
    show An'.param = ((c.y : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))) * ((vU : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q)))
    rw [hz', Subring.coe_mul]
  have hz_ord : w.ord (R.residue₁ ⟨An'.param, hz'N.1⟩) = 1 := by
    rw [hz_res, Place.ord_mul _ hy_ne hv_ne, hy_ord, hordv, add_zero]
  have hz_ne : R.residue₁ ⟨An'.param, hz'N.1⟩ ≠ 0 := by rw [hz_res]; exact mul_ne_zero hy_ne hv_ne
  have hzg' : ∃ (h : ((An'.param : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized (1 * q) A.toSubring (IsLocalRing.residue ↥A))
         (hF : CharPReduction.modularRedLocHom (1 * q) A.toSubring (IsLocalRing.residue ↥A) ⟨_, h⟩ ∈ modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1),
         CharPReduction.modularRedLocHom (1 * q) A.toSubring (IsLocalRing.residue ↥A) ⟨_, h⟩ ≠ 0 ∧
         (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) aκ).ord (⟨_, hF⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) = 1 := by
    refine ⟨hz1, hz1F, ?_, ?_⟩
    · intro h0
      apply hz_ne
      apply Subtype.ext
      rw [ez, h0, map_zero]
      rfl
    · have hoe := FltWs21.OrdExt.ord_charLGeomPlaceOfPoint_eq_of_coe_eq_coeffMap (ResidueField A) k R.redBar aκ
        ⟨_, hz1F⟩ (R.residue₁ ⟨An'.param, hz'N.1⟩) ez
      rw [hred, hwpl] at hoe
      rw [← hoe]
      exact hz_ord

  have hmodQ : ((An.modulus : ↥A) : AlgebraicClosure ℚ) = ((q : ℕ) : AlgebraicClosure ℚ) ^ jWidth aκ := by
    rw [hmodw, hjW]; exact hcoe
  have hmod34 : An'.param * ((c.x : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))) =
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (((q : ℕ) : AlgebraicClosure ℚ) ^ jWidth aκ) := by
    rw [← hparamx, h4.2.2.2, hmodQ]
  have hmodF : An'.param * ((c.x : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))) =
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) ((An'.modulus : ↥A) : AlgebraicClosure ℚ) := by
    rw [h4.2.1, ← hparamx]; exact h4.2.2.2
  have hmodwF : An'.modulus = ((q : ℕ) : ↥A) ^ jWidth aκ := by rw [h4.2.1, hmodw, hjW]
  refine ⟨?_, ?_⟩
  ·
    have hnodes0 : rc R (charLGeomPlaceOfPoint k (R.redBar (aκ ^ q))) ∈ (chartSnd R hR).nodes := by
      rw [hredq]
      exact rc_mem_nodes_chartSnd_of_mem_ssPlaces R hR _
        ((ModularCurve.mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq q k _).mpr
          ⟨a ^ q, (ModularCurve.pow_mem_ssJSet_iff_of_perfectField ..).mpr hss, rfl⟩)
    have hatt := ModularCurve.isAttached_ssAnnulus_zeroChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne_univ
      q A hq (chartSnd R hR) (rc R (charLGeomPlaceOfPoint k (R.redBar (aκ ^ q)))) aκ hssκ haκ2 hwκ hnodes0
      An ((c.x : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))) hparamx hdom' hzg An'.param hmod34 hzg'
      (hunit0_chartSnd R hR) (fun g hg h₂ h₂F => hordres0_chartSnd R hR (aκ ^ q) g hg h₂ h₂F)
    simpa only [hredq] using hatt
  ·
    have hnodesi : rc R (charLGeomPlaceOfPoint k (R.redBar aκ)) ∈ (chartFst R hR).nodes :=
      rc_mem_nodes_of_mem_ssPlaces R hR _
        ((ModularCurve.mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq q k _).mpr
          ⟨R.redBar aκ, ModularCurve.mem_ssJSet_map_of_isAlgClosed R.redBar aκ hssκ, rfl⟩)
    have hatt := ModularCurve.isAttached_oppAnnulus_inftyChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne_univ
      q A hq (chartFst R hR) (rc R (charLGeomPlaceOfPoint k (R.redBar aκ))) aκ hssκ haκ2 hwκ hnodesi
      An' An'.param ((c.x : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))) rfl hmodF hmodwF (fun W => (h4.1 ▸ hdom' W : _)) hzg' hzg
      (hunit_chartFst R hR) (fun g hg h₁ h₁F => hordres_chartFst R hR aκ g hg h₁ h₁F)
    simpa only [hred] using hatt

theorem attachSnd_wide (R : ProlongationTuple P) (hR : R.IsModel)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))]
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A) (hq : 5 ≤ q)
    (W : Finset (Place k (modularFunctionFieldC k 1))) (hW : ∀ w ∈ W, w ∈ ssPlaces q 1 k) (hreg : R.RegularityLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W)
    (a : k) (ha : w.evalAt (jGeomGen k 1) = a) (hj : a = 0 ∨ a = 1728)
    (xa : ↥(NodeLocalized.coeffSubring A K)) (hxa : NodeLocalized.redRestrict red K xa = a)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (eK : ℕ) (heK : 1 ≤ eK) (ε : ↥(NodeLocalized.coeffSubring A K)) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε)
    (c : R.NodeCoordinates K w) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ (jWidth a * eK) * u)
    (hmax : (Ideal.span {R.nodeConst K w ϖ, c.x, c.y}).IsMaximal ∧
        ∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hbr : (Ideal.span {R.nodeConst K w ϖ, c.x}).IsPrime ∧ (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime ∧
        c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x} ∧ c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y})
    (hJS : PlaceSpecialization.jFun (q := q) ∈ R.nodeIntegersOver K w)
    (hJQS : PlaceSpecialization.jqFun (q := q) ∈ R.nodeIntegersOver K w)
    (hspx : Ideal.span {R.nodeConst K w ϖ, c.x} =
        Ideal.span {R.nodeConst K w ϖ, ⟨PlaceSpecialization.jqFun (q := q), hJQS⟩ - ⟨PlaceSpecialization.jFun (q := q), hJS⟩ ^ q})
    (hspy : Ideal.span {R.nodeConst K w ϖ, c.y} =
        Ideal.span {R.nodeConst K w ϖ, ⟨PlaceSpecialization.jFun (q := q), hJS⟩ - ⟨PlaceSpecialization.jqFun (q := q), hJQS⟩ ^ q})
    (hVI : R.ValueIntegralityLaw w)
    (An An' : Annulus A ↥(modularFunctionFieldBar (1 * q)))
    (h4 : An'.dom = An.dom ∧ An'.modulus = An.modulus ∧ ((An.modulus : AlgebraicClosure ℚ) ≠ 0) ∧
        An'.param * An.param = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((An.modulus : AlgebraicClosure ℚ)))
    (hdom : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
        W ∈ An.dom ↔
          ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))))
    (hparamx : An.param = ((c.x : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))))
    (hmodw : An.modulus = ((q : ℕ) : A) ^ jWidth a)
    (hss : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) :
    letI := algebraResidueField R
    An.IsAttached (chartSnd R hR) (rc R (charLGeomPlaceOfPoint k (a ^ q))) := by
  exact (attach_both_wide R hR hker hq W hW hreg K w hw a ha hj xa hxa ϖ hϖ eK heK ε hε hqϖ c u hu hxy hmax hbr hJS hJQS hspx hspy hVI An An' h4 hdom hparamx hmodw hss ha2).1

theorem attachFst_wide (R : ProlongationTuple P) (hR : R.IsModel)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))]
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A) (hq : 5 ≤ q)
    (W : Finset (Place k (modularFunctionFieldC k 1))) (hW : ∀ w ∈ W, w ∈ ssPlaces q 1 k) (hreg : R.RegularityLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W)
    (a : k) (ha : w.evalAt (jGeomGen k 1) = a) (hj : a = 0 ∨ a = 1728)
    (xa : ↥(NodeLocalized.coeffSubring A K)) (hxa : NodeLocalized.redRestrict red K xa = a)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (eK : ℕ) (heK : 1 ≤ eK) (ε : ↥(NodeLocalized.coeffSubring A K)) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε)
    (c : R.NodeCoordinates K w) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ (jWidth a * eK) * u)
    (hmax : (Ideal.span {R.nodeConst K w ϖ, c.x, c.y}).IsMaximal ∧
        ∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hbr : (Ideal.span {R.nodeConst K w ϖ, c.x}).IsPrime ∧ (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime ∧
        c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x} ∧ c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y})
    (hJS : PlaceSpecialization.jFun (q := q) ∈ R.nodeIntegersOver K w)
    (hJQS : PlaceSpecialization.jqFun (q := q) ∈ R.nodeIntegersOver K w)
    (hspx : Ideal.span {R.nodeConst K w ϖ, c.x} =
        Ideal.span {R.nodeConst K w ϖ, ⟨PlaceSpecialization.jqFun (q := q), hJQS⟩ - ⟨PlaceSpecialization.jFun (q := q), hJS⟩ ^ q})
    (hspy : Ideal.span {R.nodeConst K w ϖ, c.y} =
        Ideal.span {R.nodeConst K w ϖ, ⟨PlaceSpecialization.jFun (q := q), hJS⟩ - ⟨PlaceSpecialization.jqFun (q := q), hJQS⟩ ^ q})
    (hVI : R.ValueIntegralityLaw w)
    (An An' : Annulus A ↥(modularFunctionFieldBar (1 * q)))
    (h4 : An'.dom = An.dom ∧ An'.modulus = An.modulus ∧ ((An.modulus : AlgebraicClosure ℚ) ≠ 0) ∧
        An'.param * An.param = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((An.modulus : AlgebraicClosure ℚ)))
    (hdom : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
        W ∈ An.dom ↔
          ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))))
    (hparamx : An.param = ((c.x : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))))
    (hmodw : An.modulus = ((q : ℕ) : A) ^ jWidth a)
    (hss : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) :
    letI := algebraResidueField R
    An'.IsAttached (chartFst R hR) (rc R (charLGeomPlaceOfPoint k a)) := by
  exact (attach_both_wide R hR hker hq W hW hreg K w hw a ha hj xa hxa ϖ hϖ eK heK ε hε hqϖ c u hu hxy hmax hbr hJS hJQS hspx hspy hVI An An' h4 hdom hparamx hmodw hss ha2).2

theorem exists_ssAnnulus_isAttached_both_ends_of_eq_zero_or_eq_1728 (R : ProlongationTuple P) (hR : R.IsModel)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))]
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A) (hq : 5 ≤ q)
    (W : Finset (Place k (modularFunctionFieldC k 1))) (hW : ∀ w ∈ W, w ∈ ssPlaces q 1 k) (hreg : R.RegularityLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W)
    (a : k) (ha : w.evalAt (jGeomGen k 1) = a) (hj : a = 0 ∨ a = 1728)
    (xa : ↥(NodeLocalized.coeffSubring A K)) (hxa : NodeLocalized.redRestrict red K xa = a)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (eK : ℕ) (heK : 1 ≤ eK) (ε : ↥(NodeLocalized.coeffSubring A K)) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε)
    (c : R.NodeCoordinates K w) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ (jWidth a * eK) * u)
    (hmax : (Ideal.span {R.nodeConst K w ϖ, c.x, c.y}).IsMaximal ∧
        ∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hbr : (Ideal.span {R.nodeConst K w ϖ, c.x}).IsPrime ∧ (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime ∧
        c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x} ∧ c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y})
    (hJS : PlaceSpecialization.jFun (q := q) ∈ R.nodeIntegersOver K w)
    (hJQS : PlaceSpecialization.jqFun (q := q) ∈ R.nodeIntegersOver K w)
    (hspx : Ideal.span {R.nodeConst K w ϖ, c.x} =
        Ideal.span {R.nodeConst K w ϖ, ⟨PlaceSpecialization.jqFun (q := q), hJQS⟩ - ⟨PlaceSpecialization.jFun (q := q), hJS⟩ ^ q})
    (hspy : Ideal.span {R.nodeConst K w ϖ, c.y} =
        Ideal.span {R.nodeConst K w ϖ, ⟨PlaceSpecialization.jFun (q := q), hJS⟩ - ⟨PlaceSpecialization.jqFun (q := q), hJQS⟩ ^ q})
    (hVI : R.ValueIntegralityLaw w) :
    letI := algebraResidueField R
    ∃ (An An' : Annulus A ↥(modularFunctionFieldBar (1 * q))),
      (An'.dom = An.dom ∧ An'.modulus = An.modulus ∧ ((An.modulus : AlgebraicClosure ℚ) ≠ 0) ∧
        An'.param * An.param = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((An.modulus : AlgebraicClosure ℚ))) ∧
      (∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
        W ∈ An.dom ↔
          ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ))))) ∧
      An.param = ((c.x : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))) ∧
      An.modulus = ((q : ℕ) : A) ^ jWidth a ∧
      An.IsAttached (chartSnd R hR) (rc R (charLGeomPlaceOfPoint k (a ^ q))) ∧
      An'.IsAttached (chartFst R hR) (rc R (charLGeomPlaceOfPoint k a)) := by
  letI := algebraResidueField R
  obtain ⟨hss, hwa⟩ := mem_ssJSet_of_evalAt_eq w (hW w hw) a ha
  have ha2 : a ^ (q ^ 2) = a := ModularCurve.pow_q_sq_eq_self_of_mem_ssJSet q hss

  obtain ⟨G', H', w', hG, hH, hw', hwU, hGH, hmax', hpr1, hpr2, hnm1, hnm2, hsp1, hsp2⟩ :=
    R.exists_crossingPresentation_modularLocalizedAtPoint_coe_eq_of_nodeCoordinates hR W hW hreg K w hw a ha xa hxa ϖ eK
      c u hu hxy hmax hbr hJS hJQS hspx hspy
  rcases hj with rfl | rfl
  ·
    obtain ⟨An, An', h4, hdom, hparamLS, hmod⟩ :=
      ModularCurve.exists_ssAnnulus_centred_zero_of_crossingPresentation_of_branchPrimes red hker hq hss K ϖ hϖ eK ε hε hqϖ
        G' H' w' hwU hGH hmax' heK hpr1 hpr2 hnm1 hnm2 hsp1 hsp2
    have hparamx : An.param = ((c.x : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))) :=
      Subtype.ext (hparamLS.trans hG)
    have hmodw : An.modulus = ((q : ℕ) : A) ^ jWidth (0 : k) := by rw [hmod, jWidth_of_eq_zero rfl]
    exact ⟨An, An', h4, hdom, hparamx, hmodw,
      attachSnd_wide R hR hker hq W hW hreg K w hw 0 ha (Or.inl rfl) xa hxa ϖ hϖ eK heK ε hε hqϖ c u hu hxy hmax hbr hJS hJQS hspx hspy
        hVI An An' h4 hdom hparamx hmodw hss ha2,
      attachFst_wide R hR hker hq W hW hreg K w hw 0 ha (Or.inl rfl) xa hxa ϖ hϖ eK heK ε hε hqϖ c u hu hxy hmax hbr hJS hJQS hspx hspy
        hVI An An' h4 hdom hparamx hmodw hss ha2⟩
  ·
    obtain ⟨An, An', h4, hdom, hparamLS, hmod⟩ :=
      ModularCurve.exists_ssAnnulus_centred_ofNat1728_of_crossingPresentation_of_branchPrimes red hker hq hss K ϖ hϖ eK ε hε hqϖ
        G' H' w' hwU hGH hmax' heK hpr1 hpr2 hnm1 hnm2 hsp1 hsp2
    have hparamx : An.param = ((c.x : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))) :=
      Subtype.ext (hparamLS.trans hG)
    have h0 : (1728 : k) ≠ 0 := by
      intro h
      have h' : ((1728 : ℕ) : k) = 0 := by exact_mod_cast h
      rw [CharP.cast_eq_zero_iff k q] at h'
      have hp : q.Prime := Fact.out
      have h23 : q ∣ 2 ^ 6 * 3 ^ 3 := by norm_num at h' ⊢; exact h'
      rcases (Nat.Prime.dvd_mul hp).mp h23 with h2 | h3
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2); omega
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3); omega
    have hmodw : An.modulus = ((q : ℕ) : A) ^ jWidth (1728 : k) := by rw [hmod, jWidth_of_eq_1728 rfl h0]
    exact ⟨An, An', h4, hdom, hparamx, hmodw,
      attachSnd_wide R hR hker hq W hW hreg K w hw 1728 ha (Or.inr rfl) xa hxa ϖ hϖ eK heK ε hε hqϖ c u hu hxy hmax hbr hJS hJQS hspx hspy
        hVI An An' h4 hdom hparamx hmodw hss ha2,
      attachFst_wide R hR hker hq W hW hreg K w hw 1728 ha (Or.inr rfl) xa hxa ϖ hϖ eK heK ε hε hqϖ c u hu hxy hmax hbr hJS hJQS hspx hspy
        hVI An An' h4 hdom hparamx hmodw hss ha2⟩

end ChartOkChartFst
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~coeffMap_injective P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve.PlaceSpecialization"

section

end
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"

section
open ModularCurve.NodeLocalized

end
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"

namespace Ideal p2m_export "Ideal" "Quotient.eq_zero_iff_mem mem_span_singleton mul_mem_right mem_span_insert Quotient.eq IsPrime.ne_top span_mono map_isPrime_of_equiv map_span map_symm map_isMaximal_of_equiv mem_bot span isDomain comap_isPrime mul_mem_mul Quotient.isDomain IsMaximal mem_span_pair Quotient.mk mul_mem_left iInf_pow_eq_bot_of_isDomain map span_singleton_eq_top ext le_of_dvd mem_iInf pow_mem_of_mem IsPrime comap_symm span_le ResidueField mem_comap IsPrime.mem_or_mem under comap eq_top_iff_one subset_span Quotient.mk_surjective" end Ideal
p2m_open_scoped "Ideal" in
theorem Ideal.eq_span_pair_of_isPrime_of_mem_of_crossing
    {S : Type*} [CommRing S] [IsNoetherianRing S] [IsLocalRing S]
    (ϖ x y : S) (hmax : IsLocalRing.maximalIdeal S = Ideal.span {ϖ, x, y})
    (hxy : x * y ∈ Ideal.span {ϖ})
    (hP₁ : (Ideal.span {ϖ, x}).IsPrime) (hy : y ∉ Ideal.span {ϖ, x})
    (P : Ideal S) [P.IsPrime] (hϖ : ϖ ∈ P) (hx : x ∈ P) (hP : P ≠ IsLocalRing.maximalIdeal S) :
    P = Ideal.span {ϖ, x} := by
  classical
  set P₁ : Ideal S := Ideal.span {ϖ, x} with hP₁def

  have hle : P₁ ≤ P := by
    rw [hP₁def, Ideal.span_le]
    rintro z (rfl | rfl)
    · exact hϖ
    · exact hx
  have hPM : P ≤ IsLocalRing.maximalIdeal S := IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)
  have hyP : y ∉ P := by
    intro hyP'
    apply hP
    refine le_antisymm hPM ?_
    rw [hmax, Ideal.span_le]
    rintro z (rfl | rfl | rfl)
    · exact hϖ
    · exact hx
    · exact hyP'
  have hyM : y ∈ IsLocalRing.maximalIdeal S := by
    rw [hmax]; exact Ideal.subset_span (by simp)

  haveI : P₁.IsPrime := hP₁
  let mk := Ideal.Quotient.mk P₁
  haveI : IsDomain (S ⧸ P₁) := Ideal.Quotient.isDomain P₁
  haveI : IsNoetherianRing (S ⧸ P₁) := inferInstance
  have hJ : (Ideal.span {mk y} : Ideal (S ⧸ P₁)) ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    obtain ⟨z, hz⟩ := hu.exists_right_inv
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [← map_mul, ← map_one mk, Ideal.Quotient.eq] at hz

    have h1 : (1 : S) ∈ IsLocalRing.maximalIdeal S := by
      have := sub_mem (Ideal.mul_mem_right z _ hyM) ((hle.trans hPM) hz)
      simp at this
    exact (IsLocalRing.maximalIdeal.isMaximal S).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

  have hpow : ∀ n : ℕ, ∀ t ∈ P, mk t ∈ (Ideal.span {mk y} : Ideal (S ⧸ P₁)) ^ n := by
    intro n
    induction n with
    | zero => intro t _; simp
    | succ n ih =>
      intro t ht

      have htM : t ∈ Ideal.span {ϖ, x, y} := hmax ▸ hPM ht
      obtain ⟨a, z, hz, rfl⟩ := Ideal.mem_span_insert.mp htM
      obtain ⟨b, c, rfl⟩ := Ideal.mem_span_pair.mp hz

      have hcy : c * y ∈ P := by
        have := sub_mem (sub_mem ht (Ideal.mul_mem_left P a hϖ)) (Ideal.mul_mem_left P b hx)
        simpa [add_sub_cancel_left] using this
      have hc : c ∈ P := ((Ideal.IsPrime.mem_or_mem inferInstance hcy).resolve_right hyP)
      have hmk : mk (a * ϖ + (b * x + c * y)) = mk c * mk y := by
        have hϖ0 : mk ϖ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
        have hx0 : mk x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
        simp only [map_add, map_mul, hϖ0, hx0, mul_zero, zero_add]
      rw [hmk, pow_succ]
      exact Ideal.mul_mem_mul (ih c hc) (Ideal.subset_span (Set.mem_singleton _))

  have hK : (⨅ n : ℕ, (Ideal.span {mk y} : Ideal (S ⧸ P₁)) ^ n) = ⊥ := Ideal.iInf_pow_eq_bot_of_isDomain _ hJ
  refine le_antisymm ?_ hle
  intro t ht
  have : mk t ∈ (⨅ n : ℕ, (Ideal.span {mk y} : Ideal (S ⧸ P₁)) ^ n) := Ideal.mem_iInf.mpr fun n => hpow n t ht
  rw [hK, Ideal.mem_bot] at this
  exact Ideal.Quotient.eq_zero_iff_mem.mp this

namespace ChartOkDictW

p2m_open "ModularCurve.PlaceSpecialization.ProlongationTuple P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve.PlaceSpecialization.ProlongationTuple"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}

theorem nodeResidue₁_eq_zero_iff_mem_span (R : ProlongationTuple P)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (w : Place k (modularFunctionFieldC k 1))
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (c : R.NodeCoordinates K w) (n : ℕ) (hn : 1 ≤ n) (u : ↥(R.nodeIntegersOver K w))
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ n * u)
    (hmax : (Ideal.span {R.nodeConst K w ϖ, c.x, c.y}).IsMaximal ∧
        ∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hbr : (Ideal.span {R.nodeConst K w ϖ, c.x}).IsPrime ∧ (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime ∧
        c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x} ∧ c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y})
    (hnoeth : IsNoetherianRing ↥(R.nodeIntegersOver K w))
    (g : ↥(R.nodeIntegersOver K w)) :
    R.nodeResidue₁ w ⟨g, g.2.1⟩ = 0 ↔ g ∈ Ideal.span {R.nodeConst K w ϖ, c.x} := by
  classical
  haveI := hnoeth

  haveI : IsLocalRing ↥(R.nodeIntegersOver K w) :=
    IsLocalRing.of_unique_max_ideal ⟨_, hmax.1, fun M hM => hmax.2 M hM⟩
  have hM : IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, c.x, c.y} :=
    (IsLocalRing.eq_maximalIdeal hmax.1).symm

  let φ : ↥(R.nodeIntegersOver K w) →+* ↥(modularFunctionFieldC k 1) :=
    (R.nodeResidue₁ w).comp (Subring.inclusion (R.nodeIntegersOver_le K w))
  have hφ : ∀ g : ↥(R.nodeIntegersOver K w), φ g = R.nodeResidue₁ w ⟨g, g.2.1⟩ := fun g => rfl
  haveI hPker : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ

  have hϖm : (⟨(ϖ : AlgebraicClosure ℚ), ϖ.2.1⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← hker]
    have h := (hϖ ϖ).mpr ⟨1, (mul_one ϖ).symm⟩
    exact h
  have hkϖ : R.nodeConst K w ϖ ∈ RingHom.ker φ := by
    rw [RingHom.mem_ker, hφ, nodeResidue₁_apply]
    change R.residue₁ ⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))
      (((⟨(ϖ : AlgebraicClosure ℚ), ϖ.2.1⟩ : A) : AlgebraicClosure ℚ)), _⟩ = 0
    rw [residue₁_apply, R.R₁.residue_algebraMap, (IsLocalRing.residue_eq_zero_iff _).mpr hϖm, map_zero, map_zero]

  have hkx : c.x ∈ RingHom.ker φ := by rw [RingHom.mem_ker, hφ]; exact c.x_fst
  have hky : c.y ∉ RingHom.ker φ := by rw [RingHom.mem_ker, hφ]; exact c.nodeResidue₁_y_ne_zero
  have hne : RingHom.ker φ ≠ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) := by
    intro h; apply hky; rw [h, hM]; exact Ideal.subset_span (by simp)
  have hxy' : c.x * c.y ∈ Ideal.span {R.nodeConst K w ϖ} := by
    rw [hxy, Ideal.mem_span_singleton]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact ⟨R.nodeConst K w ϖ ^ m * u, by ring⟩
  have key := Ideal.eq_span_pair_of_isPrime_of_mem_of_crossing (R.nodeConst K w ϖ) c.x c.y hM hxy' hbr.1 hbr.2.2.1
    (RingHom.ker φ) hkϖ hkx hne
  rw [← hφ g, ← RingHom.mem_ker, key]

theorem nodeResidue₂_eq_zero_iff_mem_span (R : ProlongationTuple P)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (w : Place k (modularFunctionFieldC k 1))
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (c : R.NodeCoordinates K w) (n : ℕ) (hn : 1 ≤ n) (u : ↥(R.nodeIntegersOver K w))
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ n * u)
    (hmax : (Ideal.span {R.nodeConst K w ϖ, c.x, c.y}).IsMaximal ∧
        ∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hbr : (Ideal.span {R.nodeConst K w ϖ, c.x}).IsPrime ∧ (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime ∧
        c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x} ∧ c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y})
    (hnoeth : IsNoetherianRing ↥(R.nodeIntegersOver K w))
    (g : ↥(R.nodeIntegersOver K w)) :
    R.nodeResidue₂ w ⟨g, g.2.1⟩ = 0 ↔ g ∈ Ideal.span {R.nodeConst K w ϖ, c.y} := by
  classical
  haveI := hnoeth

  haveI : IsLocalRing ↥(R.nodeIntegersOver K w) :=
    IsLocalRing.of_unique_max_ideal ⟨_, hmax.1, fun M hM => hmax.2 M hM⟩
  have hM : IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, c.x, c.y} :=
    (IsLocalRing.eq_maximalIdeal hmax.1).symm

  let φ : ↥(R.nodeIntegersOver K w) →+* ↥(modularFunctionFieldC k 1) :=
    (R.nodeResidue₂ w).comp (Subring.inclusion (R.nodeIntegersOver_le K w))
  have hφ : ∀ g : ↥(R.nodeIntegersOver K w), φ g = R.nodeResidue₂ w ⟨g, g.2.1⟩ := fun g => rfl
  haveI hPker : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ

  have hϖm : (⟨(ϖ : AlgebraicClosure ℚ), ϖ.2.1⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← hker]
    have h := (hϖ ϖ).mpr ⟨1, (mul_one ϖ).symm⟩
    exact h
  have hkϖ : R.nodeConst K w ϖ ∈ RingHom.ker φ := by
    rw [RingHom.mem_ker, hφ, nodeResidue₂_apply]
    change R.residue₂ ⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))
      (((⟨(ϖ : AlgebraicClosure ℚ), ϖ.2.1⟩ : A) : AlgebraicClosure ℚ)), _⟩ = 0
    rw [residue₂_apply, R.R₂.residue_algebraMap, (IsLocalRing.residue_eq_zero_iff _).mpr hϖm, map_zero, map_zero]

  have hky : c.y ∈ RingHom.ker φ := by rw [RingHom.mem_ker, hφ]; exact c.y_snd
  have hkx : c.x ∉ RingHom.ker φ := by rw [RingHom.mem_ker, hφ]; exact c.nodeResidue₂_x_ne_zero
  have hne : RingHom.ker φ ≠ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) := by
    intro h; apply hkx; rw [h, hM]; exact Ideal.subset_span (by simp)
  have hM' : IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, c.y, c.x} := by
    rw [hM]
    congr 1
    rw [Set.pair_comm]
  have hyx' : c.y * c.x ∈ Ideal.span {R.nodeConst K w ϖ} := by
    rw [mul_comm c.y c.x, hxy, Ideal.mem_span_singleton]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact ⟨R.nodeConst K w ϖ ^ m * u, by ring⟩
  have key := Ideal.eq_span_pair_of_isPrime_of_mem_of_crossing (R.nodeConst K w ϖ) c.y c.x hM' hyx' hbr.2.1 hbr.2.2.2
    (RingHom.ker φ) hkϖ hky hne
  rw [← hφ g, ← RingHom.mem_ker, key]

#print axioms nodeResidue₁_eq_zero_iff_mem_span
#print axioms nodeResidue₂_eq_zero_iff_mem_span

theorem span_nodeConst_eq_span_kronecker (R : ProlongationTuple P) (hmodel : R.IsModel)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A) (hq : 5 ≤ q)
    (W : Finset (Place k (modularFunctionFieldC k 1))) (hW : ∀ w ∈ W, w ∈ ssPlaces q 1 k)
    (hreg : R.RegularityLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W)
    (a : k) (ha : w.evalAt (jGeomGen k 1) = a) (hss : a ∈ ssJSet q k)
    (xa : ↥(NodeLocalized.coeffSubring A K)) (hxa : NodeLocalized.redRestrict red K xa = a)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (c : R.NodeCoordinates K w) (n : ℕ) (hn : 1 ≤ n) (u : ↥(R.nodeIntegersOver K w))
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ n * u)
    (hmax : (Ideal.span {R.nodeConst K w ϖ, c.x, c.y}).IsMaximal ∧
        ∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hbr : (Ideal.span {R.nodeConst K w ϖ, c.x}).IsPrime ∧ (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime ∧
        c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x} ∧ c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y})
    (hnoeth : IsNoetherianRing ↥(R.nodeIntegersOver K w))
    (hJS : PlaceSpecialization.jFun (q := q) ∈ R.nodeIntegersOver K w)
    (hJQS : PlaceSpecialization.jqFun (q := q) ∈ R.nodeIntegersOver K w) :
    Ideal.span {R.nodeConst K w ϖ, c.x} =
        Ideal.span {R.nodeConst K w ϖ, ⟨PlaceSpecialization.jqFun (q := q), hJQS⟩ - ⟨PlaceSpecialization.jFun (q := q), hJS⟩ ^ q} ∧
    Ideal.span {R.nodeConst K w ϖ, c.y} =
        Ideal.span {R.nodeConst K w ϖ, ⟨PlaceSpecialization.jFun (q := q), hJS⟩ - ⟨PlaceSpecialization.jqFun (q := q), hJQS⟩ ^ q} := by
  classical
  haveI := hnoeth
  haveI : IsLocalRing ↥(R.nodeIntegersOver K w) :=
    IsLocalRing.of_unique_max_ideal ⟨_, hmax.1, fun M hM => hmax.2 M hM⟩
  have hM : IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, c.x, c.y} :=
    (IsLocalRing.eq_maximalIdeal hmax.1).symm
  haveI hA : A.LiesOverPrime q := ChartOkChartFst.liesOverPrime_of_ker R hker
  have ha2 : a ^ (q ^ 2) = a := ModularCurve.pow_q_sq_eq_self_of_mem_ssJSet q hss

  let ι : ↥(R.nodeIntegersOver K w) →+* LaurentSeries (AlgebraicClosure ℚ) :=
    (algebraMap ↥(modularFunctionFieldBar (1 * q)) (LaurentSeries (AlgebraicClosure ℚ))).comp (R.nodeIntegersOver K w).subtype
  have hι : ∀ g : ↥(R.nodeIntegersOver K w), ι g = ((g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) :=
    fun g => rfl
  have hιinj : Function.Injective ι := by
    intro g g' h
    rw [hι, hι] at h
    exact Subtype.ext (Subtype.ext h)
  have hιmem : ∀ g : ↥(R.nodeIntegersOver K w), ι g ∈ NodeLocalized.modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q) := fun g =>
    (R.mem_modularLocalizedAtPoint_iff_exists_mem_nodeIntegersOver hmodel W hW hreg K w hw a ha xa hxa (ι g)).mpr
      ⟨g, g.2, rfl⟩
  let ιR : ↥(R.nodeIntegersOver K w) →+* ↥(NodeLocalized.modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q)) := ι.codRestrict (NodeLocalized.modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q)) hιmem
  have hbij : Function.Bijective ιR := by
    refine ⟨fun g g' h => hιinj (congrArg (fun z : ↥(NodeLocalized.modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q)) => (z : LaurentSeries (AlgebraicClosure ℚ))) h), fun f => ?_⟩
    obtain ⟨g, hg, hgf⟩ :=
      (R.mem_modularLocalizedAtPoint_iff_exists_mem_nodeIntegersOver hmodel W hW hreg K w hw a ha xa hxa f).mp f.2
    exact ⟨⟨g, hg⟩, Subtype.ext hgf⟩
  let e : ↥(R.nodeIntegersOver K w) ≃+* ↥(NodeLocalized.modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q)) := RingEquiv.ofBijective ιR hbij
  have he : ∀ g : ↥(R.nodeIntegersOver K w), ((e g : ↥(NodeLocalized.modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q))) : LaurentSeries (AlgebraicClosure ℚ)) = ι g := fun g => rfl
  have heϖ : e (R.nodeConst K w ϖ) = ⟨NodeLocalized.modularEval (1 * q) (NodeLocalized.coeffSubring A K) (MvPolynomial.C ϖ),
      NodeLocalized.modularEval_mem_modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K)
        (NodeLocalized.redRestrict red K) a (a ^ q) _⟩ := by
    apply Subtype.ext
    rw [he, hι]
    change (((R.nodeConst K w ϖ) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) =
      NodeLocalized.modularEval (1 * q) (NodeLocalized.coeffSubring A K) (MvPolynomial.C ϖ)
    rw [NodeLocalized.modularEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, ProlongationTuple.coe_nodeConst]
    rfl
  have heJ : e ⟨PlaceSpecialization.jFun (q := q), hJS⟩ = (⟨NodeLocalized.modularEval (1 * q) (NodeLocalized.coeffSubring A K) (MvPolynomial.X 0),
        NodeLocalized.modularEval_mem_modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K)
          (NodeLocalized.redRestrict red K) a (a ^ q) _⟩ : ↥(NodeLocalized.modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q))) := by
    apply Subtype.ext
    rw [he, hι]
    change ModularCurve.coeffEmb (AlgebraicClosure ℚ) jq = NodeLocalized.modularEval (1 * q) (NodeLocalized.coeffSubring A K) (MvPolynomial.X 0)
    rw [NodeLocalized.modularEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
    change ModularCurve.coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (ModularCurve.jqModC ℚ) = ModularCurve.jqModC (AlgebraicClosure ℚ)
    exact ModularCurve.map_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))
  have heJQ : e ⟨PlaceSpecialization.jqFun (q := q), hJQS⟩ = (⟨NodeLocalized.modularEval (1 * q) (NodeLocalized.coeffSubring A K) (MvPolynomial.X 1),
        NodeLocalized.modularEval_mem_modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K)
          (NodeLocalized.redRestrict red K) a (a ^ q) _⟩ : ↥(NodeLocalized.modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q))) := by
    apply Subtype.ext
    rw [he, hι]
    change ModularCurve.coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq) =
      NodeLocalized.modularEval (1 * q) (NodeLocalized.coeffSubring A K) (MvPolynomial.X 1)
    rw [NodeLocalized.modularEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
    change ModularCurve.coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (qExpand ℚ (1 * q) (ModularCurve.jqModC ℚ)) =
      qExpand (AlgebraicClosure ℚ) (1 * q) (ModularCurve.jqModC (AlgebraicClosure ℚ))
    rw [ModularCurve.coeffMap_qExpand]
    congr 1
    exact ModularCurve.map_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))
  have heKx : e (⟨PlaceSpecialization.jqFun (q := q), hJQS⟩ - ⟨PlaceSpecialization.jFun (q := q), hJS⟩ ^ q) =
      (⟨NodeLocalized.modularEval (1 * q) (NodeLocalized.coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
        NodeLocalized.modularEval_mem_modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K)
          (NodeLocalized.redRestrict red K) a (a ^ q) _⟩ : ↥(NodeLocalized.modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q))) := by
    rw [map_sub, map_pow, heJ, heJQ]; apply Subtype.ext; simp [map_sub, map_pow]
  have heKy : e (⟨PlaceSpecialization.jFun (q := q), hJS⟩ - ⟨PlaceSpecialization.jqFun (q := q), hJQS⟩ ^ q) =
      (⟨NodeLocalized.modularEval (1 * q) (NodeLocalized.coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
        NodeLocalized.modularEval_mem_modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K)
          (NodeLocalized.redRestrict red K) a (a ^ q) _⟩ : ↥(NodeLocalized.modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q))) := by
    rw [map_sub, map_pow, heJ, heJQ]; apply Subtype.ext; simp [map_sub, map_pow]

  have hcomap2 : ∀ s₁ s₂ : ↥(R.nodeIntegersOver K w), Ideal.comap e (Ideal.span {e s₁, e s₂}) = Ideal.span {s₁, s₂} := by
    intro s₁ s₂
    rw [← Ideal.map_symm, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
    simp

  obtain ⟨eK', ε', -, -, -, G'ₑ, H'ₑ, wₑ, -, -, -, hpr1ₑ, hpr2ₑ, hnm1ₑ, hnm2ₑ, hsp1ₑ, hsp2ₑ⟩ :=
    ModularCurve.exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring red a hss ha2 hq K xa hxa ϖ hϖ

  have hkronx : R.nodeResidue₁ w ⟨((⟨PlaceSpecialization.jqFun (q := q), hJQS⟩ - ⟨PlaceSpecialization.jFun (q := q), hJS⟩ ^ q :
      ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))), (⟨PlaceSpecialization.jqFun (q := q), hJQS⟩ -
        ⟨PlaceSpecialization.jFun (q := q), hJS⟩ ^ q : ↥(R.nodeIntegersOver K w)).2.1⟩ = 0 := by
    have h1 := ChartOkChartFst.residue₁_jqFun R hA
    have h2 := ChartOkChartFst.residue₁_jFun R hA
    rw [nodeResidue₁_apply]
    have : (⟨((⟨PlaceSpecialization.jqFun (q := q), hJQS⟩ - ⟨PlaceSpecialization.jFun (q := q), hJS⟩ ^ q :
        ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))), _⟩ : ↥(R.R₁.integers)) =
        ⟨_, ChartOkChartFst.jqFun_mem_integersFst R hA⟩ - ⟨_, ChartOkChartFst.jFun_mem_integersFst R hA⟩ ^ q := rfl
    rw [this, map_sub, map_pow, h1, h2, sub_self]
  have hkrony : R.nodeResidue₂ w ⟨((⟨PlaceSpecialization.jFun (q := q), hJS⟩ - ⟨PlaceSpecialization.jqFun (q := q), hJQS⟩ ^ q :
      ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))), (⟨PlaceSpecialization.jFun (q := q), hJS⟩ -
        ⟨PlaceSpecialization.jqFun (q := q), hJQS⟩ ^ q : ↥(R.nodeIntegersOver K w)).2.1⟩ = 0 := by
    have h1 := ChartOkChartFst.residue₂_jqFun R hA
    have h2 := ChartOkChartFst.residue₂_jFun R hA
    rw [nodeResidue₂_apply]
    have : (⟨((⟨PlaceSpecialization.jFun (q := q), hJS⟩ - ⟨PlaceSpecialization.jqFun (q := q), hJQS⟩ ^ q :
        ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (1 * q))), _⟩ : ↥(R.R₂.integers)) =
        ⟨_, ChartOkChartFst.jFun_mem_integersSnd R hA⟩ - ⟨_, ChartOkChartFst.jqFun_mem_integersSnd R hA⟩ ^ q := rfl
    rw [this, map_sub, map_pow, h1, h2, sub_self]

  have hsubx : (⟨PlaceSpecialization.jqFun (q := q), hJQS⟩ - ⟨PlaceSpecialization.jFun (q := q), hJS⟩ ^ q : ↥(R.nodeIntegersOver K w)) ∈
      Ideal.span {R.nodeConst K w ϖ, c.x} :=
    (nodeResidue₁_eq_zero_iff_mem_span R hker K w ϖ hϖ c n hn u hxy hmax hbr hnoeth _).mp hkronx
  have hsuby : (⟨PlaceSpecialization.jFun (q := q), hJS⟩ - ⟨PlaceSpecialization.jqFun (q := q), hJQS⟩ ^ q : ↥(R.nodeIntegersOver K w)) ∈
      Ideal.span {R.nodeConst K w ϖ, c.y} :=
    (nodeResidue₂_eq_zero_iff_mem_span R hker K w ϖ hϖ c n hn u hxy hmax hbr hnoeth _).mp hkrony
  have hxy' : c.x * c.y ∈ Ideal.span {R.nodeConst K w ϖ} := by
    rw [hxy, Ideal.mem_span_singleton]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact ⟨R.nodeConst K w ϖ ^ m * u, by ring⟩

  have step : ∀ (b b' : ↥(R.nodeIntegersOver K w)) (t : ↥(R.nodeIntegersOver K w)) (Hₑ : ↥(NodeLocalized.modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q))),
      IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, b, b'} →
      b * b' ∈ Ideal.span {R.nodeConst K w ϖ} →
      (Ideal.span {R.nodeConst K w ϖ, b}).IsPrime → b' ∉ Ideal.span {R.nodeConst K w ϖ, b} →
      t ∈ Ideal.span {R.nodeConst K w ϖ, b} →
      (Ideal.span {e (R.nodeConst K w ϖ), e t}).IsPrime → Hₑ ∉ Ideal.span {e (R.nodeConst K w ϖ), e t} →
      ¬ IsUnit Hₑ →
      Ideal.span {R.nodeConst K w ϖ, b} = Ideal.span {R.nodeConst K w ϖ, t} := by
    intro b b' t Hₑ hMb hbb' hPb hb' ht hQ hH hHu

    have hP : Ideal.span {R.nodeConst K w ϖ, t} = Ideal.comap e (Ideal.span {e (R.nodeConst K w ϖ), e t}) :=
      (hcomap2 _ _).symm
    haveI : (Ideal.span {R.nodeConst K w ϖ, t}).IsPrime := by rw [hP]; exact Ideal.comap_isPrime e _
    have hne : Ideal.span {R.nodeConst K w ϖ, t} ≠ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) := by
      intro hmx
      apply hH
      have h1 : e.symm Hₑ ∈ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) :=
        (IsLocalRing.mem_maximalIdeal _).mpr (fun hu' => hHu (by simpa using hu'.map e))
      rw [← hmx, hP, Ideal.mem_comap] at h1
      simpa using h1

    have hle : Ideal.span {R.nodeConst K w ϖ, t} ≤ Ideal.span {R.nodeConst K w ϖ, b} := by
      rw [Ideal.span_le]
      rintro s (rfl | rfl)
      · exact Ideal.subset_span (by simp)
      · simpa using ht
    have hϖP : R.nodeConst K w ϖ ∈ Ideal.span {R.nodeConst K w ϖ, t} := Ideal.subset_span (by simp)
    have hbP : b ∈ Ideal.span {R.nodeConst K w ϖ, t} := by
      have hprod : b * b' ∈ Ideal.span {R.nodeConst K w ϖ, t} :=
        Ideal.span_mono (by simp) hbb'
      rcases (Ideal.IsPrime.mem_or_mem inferInstance hprod) with h | h
      · exact h
      · exact absurd (hle h) hb'
    exact (Ideal.eq_span_pair_of_isPrime_of_mem_of_crossing (R.nodeConst K w ϖ) b b' hMb hbb' hPb hb'
      (Ideal.span {R.nodeConst K w ϖ, t}) hϖP hbP hne).symm

  have hHu : ¬ IsUnit H'ₑ := fun hu' => hpr2ₑ.ne_top ((Ideal.eq_top_iff_one _).mpr
    (by obtain ⟨v, hv⟩ := hu'.exists_left_inv; rw [← hv]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))))
  have hGu : ¬ IsUnit G'ₑ := fun hu' => hpr1ₑ.ne_top ((Ideal.eq_top_iff_one _).mpr
    (by obtain ⟨v, hv⟩ := hu'.exists_left_inv; rw [← hv]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))))
  refine ⟨?_, ?_⟩
  · refine step c.x c.y _ H'ₑ hM hxy' hbr.1 hbr.2.2.1 hsubx ?_ ?_ hHu
    · rw [heϖ, heKx, ← hsp1ₑ]; exact hpr1ₑ
    · rw [heϖ, heKx, ← hsp1ₑ]; exact hnm1ₑ
  · have hM' : IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, c.y, c.x} := by
      rw [hM]; congr 1; rw [Set.pair_comm]
    have hyx' : c.y * c.x ∈ Ideal.span {R.nodeConst K w ϖ} := by rw [mul_comm c.y c.x]; exact hxy'
    refine step c.y c.x _ G'ₑ hM' hyx' hbr.2.1 hbr.2.2.2 hsuby ?_ ?_ hGu
    · rw [heϖ, heKy, ← hsp2ₑ]; exact hpr2ₑ
    · rw [heϖ, heKy, ← hsp2ₑ]; exact hnm2ₑ

#print axioms span_nodeConst_eq_span_kronecker

end ChartOkDictW
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~coeffMap_injective P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve.PlaceSpecialization"

namespace ChartOkDictW

theorem jFun_jqFun_mem_nodeIntegersOver
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k]
    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ ssPlaces q 1 k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (h₁ : PlaceSpecialization.jFun (q := q) ∈ R.R₁.integers) (h₂ : PlaceSpecialization.jFun (q := q) ∈ R.R₂.integers)
    (h₁' : PlaceSpecialization.jqFun (q := q) ∈ R.R₁.integers) (h₂' : PlaceSpecialization.jqFun (q := q) ∈ R.R₂.integers) :
    PlaceSpecialization.jFun (q := q) ∈ R.nodeIntegersOver K w ∧ PlaceSpecialization.jqFun (q := q) ∈ R.nodeIntegersOver K w := by
  classical

  have hj1 : ProlongationTuple.jFun 1 q = PlaceSpecialization.jFun (q := q) := rfl
  have hjq1 : ProlongationTuple.jQFun 1 q = PlaceSpecialization.jqFun (q := q) := by
    apply Subtype.ext
    change coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq)
    simp only [one_mul]

  have hint : ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (f : ↥(modularFunctionFieldBar (1 * q)))
      (x : A), 0 < V.ord (f - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ)) →
      f ∈ V.toValuationSubring := by
    intro V f x hpos
    have hc : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ) ∈ V.toValuationSubring :=
      V.algebraMap_mem' x
    by_cases h0 : f - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ) = 0
    · rw [sub_eq_zero] at h0; rw [h0]; exact hc
    · have hm := V.mem_of_ord_nonneg h0 hpos.le
      have : f = (f - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ)) +
          algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ) := by ring
      rw [this]
      exact add_mem hm hc
  have hplaces : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), P.reduceFst V = w →
      PlaceSpecialization.jFun (q := q) ∈ V.toValuationSubring ∧ PlaceSpecialization.jqFun (q := q) ∈ V.toValuationSubring := by
    intro V hV
    obtain ⟨⟨x, -, hx⟩, ⟨y, -, hy⟩⟩ :=
      (ModularCurve.PlaceSpecialization.reduceFst_eq_iff_centred_levelOne P w hw _ rfl V).mp hV
    rw [hj1] at hx
    rw [hjq1] at hy
    exact ⟨hint V _ x hx, hint V _ y hy⟩

  have hcoeJ : ((PlaceSpecialization.jFun (q := q) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) =
      ModularCurve.jqModC (AlgebraicClosure ℚ) := by
    change ModularCurve.coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (ModularCurve.jqModC ℚ) = _
    exact ModularCurve.map_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))
  have hcoeJQ : ((PlaceSpecialization.jqFun (q := q) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) =
      ModularCurve.jqNModC (AlgebraicClosure ℚ) (1 * q) := by
    change ModularCurve.coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (qExpand ℚ (1 * q) (ModularCurve.jqModC ℚ)) =
      qExpand (AlgebraicClosure ℚ) (1 * q) (ModularCurve.jqModC (AlgebraicClosure ℚ))
    rw [ModularCurve.coeffMap_qExpand, ← hcoeJ]
    rfl
  have hKJ : ((PlaceSpecialization.jFun (q := q) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      NodeLocalized.fieldOver (1 * q) K := by
    rw [hcoeJ]
    exact Subfield.subset_closure (Or.inr (Set.mem_insert _ _))
  have hKJQ : ((PlaceSpecialization.jqFun (q := q) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      NodeLocalized.fieldOver (1 * q) K := by
    rw [hcoeJQ]
    exact Subfield.subset_closure (Or.inr (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  exact ⟨⟨⟨h₁, h₂, fun V hV => (hplaces V hV).1⟩, hKJ⟩, ⟨⟨h₁', h₂', fun V hV => (hplaces V hV).2⟩, hKJQ⟩⟩

#print axioms jFun_jqFun_mem_nodeIntegersOver

end ChartOkDictW
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

namespace ChartOkECA

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~coeffMap_injective P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve.PlaceSpecialization.ProlongationTuple"
open Classical

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}

theorem exists_coeff_lift (R : ProlongationTuple P)
    {W : Finset (Place k ↥(modularFunctionFieldC k 1))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k) (hRL : R.RegularityLaw W)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (w : Place k ↥(modularFunctionFieldC k 1)) (hw : w ∈ W)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (c : R.NodeCoordinates K w)
    (hmax : (Ideal.span {R.nodeConst K w ϖ, c.x, c.y}).IsMaximal ∧
        ∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hres : ∀ g : ↥(R.nodeIntegersOver K w), ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o))
    (hJS : PlaceSpecialization.jFun (q := q) ∈ R.nodeIntegersOver K w) (hA : A.LiesOverPrime q) :
    ∃ xa : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K xa = w.evalAt (jGeomGen k 1) := by
  haveI : IsLocalRing ↥(R.nodeIntegersOver K w) :=
    IsLocalRing.of_unique_max_ideal ⟨_, hmax.1, fun M hM => hmax.2 M hM⟩
  have hM : IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, c.x, c.y} :=
    (IsLocalRing.eq_maximalIdeal hmax.1).symm
  obtain ⟨o, ho⟩ := hres ⟨PlaceSpecialization.jFun (q := q), hJS⟩
  refine ⟨o, ?_⟩

  have hmem : (⟨PlaceSpecialization.jFun (q := q), hJS⟩ - R.nodeConst K w o : ↥(R.nodeIntegersOver K w)) ∈
      Ideal.span {R.nodeConst K w ϖ, c.x, c.y} := by
    rw [← hM]; exact (IsLocalRing.mem_maximalIdeal _).mpr ho
  obtain ⟨r, s, t, hrst⟩ : ∃ r s t : ↥(R.nodeIntegersOver K w),
      (⟨PlaceSpecialization.jFun (q := q), hJS⟩ - R.nodeConst K w o : ↥(R.nodeIntegersOver K w)) =
        r * R.nodeConst K w ϖ + s * c.x + t * c.y := by
    rw [Ideal.mem_span_insert] at hmem
    obtain ⟨r, z, hz, h⟩ := hmem
    rw [Ideal.mem_span_pair] at hz
    obtain ⟨s, t, rfl⟩ := hz
    exact ⟨r, s, t, by rw [h]; ring⟩

  let φ : ↥(R.nodeIntegersOver K w) →+* ↥(modularFunctionFieldC k 1) :=
    (R.nodeResidue₁ w).comp (Subring.inclusion (R.nodeIntegersOver_le K w))
  have hφ : ∀ g : ↥(R.nodeIntegersOver K w), φ g = R.nodeResidue₁ w ⟨g, g.2.1⟩ := fun g => rfl
  have hϖm : (⟨(ϖ : AlgebraicClosure ℚ), ϖ.2.1⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← hker]; exact (hϖ ϖ).mpr ⟨1, (mul_one ϖ).symm⟩
  have hφϖ : φ (R.nodeConst K w ϖ) = 0 := by
    rw [hφ, nodeResidue₁_apply]
    change R.residue₁ ⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))
      (((⟨(ϖ : AlgebraicClosure ℚ), ϖ.2.1⟩ : A) : AlgebraicClosure ℚ)), _⟩ = 0
    rw [residue₁_apply, R.R₁.residue_algebraMap, (IsLocalRing.residue_eq_zero_iff _).mpr hϖm, map_zero, map_zero]
  have hφo : φ (R.nodeConst K w o) = algebraMap k ↥(modularFunctionFieldC k 1) (NodeLocalized.redRestrict red K o) := by
    rw [hφ, nodeResidue₁_apply]
    change R.residue₁ ⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))
      (((⟨(o : AlgebraicClosure ℚ), o.2.1⟩ : A) : AlgebraicClosure ℚ)), _⟩ = _
    rw [residue₁_apply, R.R₁.residue_algebraMap, ChartOkChartFst.iota_algebraMap R]
    change algebraMap k ↥(modularFunctionFieldC k 1) (R.redBar (IsLocalRing.residue A _)) = _
    rw [R.redBar_residue]
    rfl
  have hφx : φ c.x = 0 := by rw [hφ]; exact c.x_fst
  have hφj : φ ⟨PlaceSpecialization.jFun (q := q), hJS⟩ = jGeomGen k 1 := by
    rw [hφ, nodeResidue₁_apply]
    exact ChartOkChartFst.residue₁_jFun R hA
  have key : jGeomGen k 1 - algebraMap k ↥(modularFunctionFieldC k 1) (NodeLocalized.redRestrict red K o) = φ t * φ c.y := by
    have := congrArg φ hrst
    rw [map_sub, hφj, hφo, map_add, map_add, map_mul, map_mul, map_mul, hφϖ, hφx, mul_zero, mul_zero, zero_add, zero_add] at this
    exact this

  have hy1 : w.ord (φ c.y) = 1 := by rw [hφ]; exact c.y_fst
  have hss : w ∈ ssPlaces q 1 k := (hW w).mp hw
  obtain ⟨a, ha, hwa⟩ := (ModularCurve.mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq q k w).mp hss
  have hfix : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr w) = w := by
    rw [← hwa, ModularCurve.frobOnPlacesGeomLevel_charLGeomPlaceOfPoint, ModularCurve.frobOnPlacesGeomLevel_charLGeomPlaceOfPoint,
      ← pow_mul, ← sq, ModularCurve.pow_q_sq_eq_self_of_mem_ssJSet q ha]
  have hj0 : (jGeomGen k 1 : ↥(modularFunctionFieldC k 1)) - algebraMap k _ a ≠ 0 := jGeomGen_sub_algebraMap_ne_zero k 1 a
  have hord1 : 0 < (charLGeomPlaceOfPoint k a).ord ((jGeomGen k 1 : ↥(modularFunctionFieldC k 1)) - algebraMap k _ a) := by
    have h := ModularCurve.ord_charLGeomPlaceOfPoint_aeval_jqModC_eq_rootMultiplicity k a (Polynomial.X - Polynomial.C a)
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Polynomial.rootMultiplicity_X_sub_C_self] at h
    change (charLGeomPlaceOfPoint k a).ord (jGeomGen k 1 - algebraMap k _ a) = 1 at h
    rw [h]; exact zero_lt_one
  have hjmem : (jGeomGen k 1 : ↥(modularFunctionFieldC k 1)) ∈ w.toValuationSubring := by
    rw [← hwa]
    have := (charLGeomPlaceOfPoint k a).mem_of_ord_nonneg hj0 hord1.le
    simpa using add_mem this ((charLGeomPlaceOfPoint k a).algebraMap_mem' a)
  have haff : IsAffineGeomPlace k 1 w := by
    refine ⟨hjmem, ?_⟩
    rw [ModularCurve.jNGeomGen_one]; exact hjmem

  have ht0 : 0 ≤ w.ord (φ t * φ c.y) := by
    by_cases hzero : φ t = 0
    · rw [hzero, zero_mul, Place.ord_zero]
    · have hreg := (hRL.1 (t : ↥(modularFunctionFieldBar (1 * q))) t.2.1.1 t.2.1.2.1 w hfix haff
        (fun V hV => R.ord_nonneg_of_mem_nodeIntegers t.2.1 hV)).1
      have hne : R.residue₁ ⟨(t : ↥(modularFunctionFieldBar (1 * q))), t.2.1.1⟩ ≠ 0 := by
        rw [hφ, nodeResidue₁_apply] at hzero; exact hzero
      have h0 : 0 ≤ w.ord (φ t) := by rw [hφ, nodeResidue₁_apply]; exact hreg hne
      have hy0 : φ c.y ≠ 0 := by rw [hφ]; exact c.nodeResidue₁_y_ne_zero
      rw [Place.ord_mul _ hzero hy0, hy1]; omega

  have hmemc : algebraMap k ↥(modularFunctionFieldC k 1) (NodeLocalized.redRestrict red K o) ∈ w.toValuationSubring :=
    w.algebraMap_mem' _
  by_cases hz : jGeomGen k 1 - algebraMap k ↥(modularFunctionFieldC k 1) (NodeLocalized.redRestrict red K o) = 0
  · rw [sub_eq_zero] at hz
    rw [hz, Place.evalAt_algebraMap]
  · have hpos : 0 < w.ord (jGeomGen k 1 - algebraMap k ↥(modularFunctionFieldC k 1) (NodeLocalized.redRestrict red K o)) := by
      rw [key] at hz ⊢
      have hy0 : φ c.y ≠ 0 := by rw [hφ]; exact c.nodeResidue₁_y_ne_zero
      have ht' : φ t ≠ 0 := fun h => hz (by rw [h, zero_mul])
      have hreg := (hRL.1 (t : ↥(modularFunctionFieldBar (1 * q))) t.2.1.1 t.2.1.2.1 w hfix haff
        (fun V hV => R.ord_nonneg_of_mem_nodeIntegers t.2.1 hV)).1
      have hne : R.residue₁ ⟨(t : ↥(modularFunctionFieldBar (1 * q))), t.2.1.1⟩ ≠ 0 := by
        rw [hφ, nodeResidue₁_apply] at ht'; exact ht'
      have h0 : 0 ≤ w.ord (φ t) := by rw [hφ, nodeResidue₁_apply]; exact hreg hne
      rw [Place.ord_mul _ ht' hy0, hy1]; omega
    rw [AlgebraicCurve.Place.evalAt_congr _ hjmem hmemc (Or.inr hpos), AlgebraicCurve.Place.evalAt_algebraMap]

#print axioms exists_coeff_lift

end ChartOkECA
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

namespace ChartOkECA

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~coeffMap_injective P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve.PlaceSpecialization.ProlongationTuple"
open Classical

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}

theorem ew_eq_jWidth (R : ProlongationTuple P) (hq : 5 ≤ q) (hR : R.IsModel)
    (W : Finset (Place k ↥(modularFunctionFieldC k 1))) (hW : ∀ w ∈ W, w ∈ ssPlaces q 1 k)
    (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W) (hO : R.OrderLawFixed)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k ↥(modularFunctionFieldC k 1)) (hw : w ∈ W) (a : k) (ha : w.evalAt (jGeomGen k 1) = a)
    (xa : ↥(NodeLocalized.coeffSubring A K)) (hxa : NodeLocalized.redRestrict red K xa = w.evalAt (jGeomGen k 1))
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (eK : ℕ) (heK : 1 ≤ eK) (ε : ↥(NodeLocalized.coeffSubring A K)) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε)
    (c : R.NodeCoordinates K w) (ew : ℕ) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ (ew * eK) * u) :
    ew = jWidth a := by

  have hE := R.crossingExponent_eq_placeWidth_mul_of_orderLawFixed_levelOne hq hR W hW hRL hNV hO hker K w hw xa hxa ϖ hϖ eK ε hε hqϖ
    c (ew * eK) u hu hxy
  have heK0 : 0 < eK := heK
  have hew : ew = placeWidth 1 w := Nat.eq_of_mul_eq_mul_right heK0 hE
  rw [hew, ModularCurve.placeWidth, ha]

  obtain ⟨b, hb, hwb⟩ := (ModularCurve.mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq q k w).mp (hW w hw)
  have hj0 : (jGeomGen k 1 : ↥(modularFunctionFieldC k 1)) - algebraMap k _ b ≠ 0 := jGeomGen_sub_algebraMap_ne_zero k 1 b
  have hordb : (charLGeomPlaceOfPoint k b).ord ((jGeomGen k 1 : ↥(modularFunctionFieldC k 1)) - algebraMap k _ b) = 1 := by
    have h := ModularCurve.ord_charLGeomPlaceOfPoint_aeval_jqModC_eq_rootMultiplicity k b (Polynomial.X - Polynomial.C b)
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Polynomial.rootMultiplicity_X_sub_C_self] at h
    exact h
  have hwb' : w.evalAt (jGeomGen k 1) = b := by
    rw [← hwb]
    have hmemc : algebraMap k ↥(modularFunctionFieldC k 1) b ∈ (charLGeomPlaceOfPoint k b).toValuationSubring :=
      (charLGeomPlaceOfPoint k b).algebraMap_mem' b
    have hmem : (jGeomGen k 1 : ↥(modularFunctionFieldC k 1)) ∈ (charLGeomPlaceOfPoint k b).toValuationSubring := by
      have := (charLGeomPlaceOfPoint k b).mem_of_ord_nonneg hj0 (by rw [hordb]; exact zero_le_one)
      simpa using add_mem this hmemc
    rw [AlgebraicCurve.Place.evalAt_congr _ hmem hmemc (Or.inr (by rw [hordb]; exact zero_lt_one)), AlgebraicCurve.Place.evalAt_algebraMap]
  have hab : a = b := ha.symm.trans hwb'
  subst hab
  have hram : placeRamificationJ 1 w = 1 := by
    rw [ModularCurve.placeRamificationJ, hwb', ← hwb, hordb]; rfl
  rw [hram, Nat.div_one]

#print axioms ew_eq_jWidth

end ChartOkECA
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"

namespace ChartOkECA
p2m_open "AlgebraicCurve IsLocalRing ModularCurve~coeffMap_injective P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve.PlaceSpecialization.ProlongationTuple"
open Classical
set_option autoImplicit false

set_option maxHeartbeats 12800000 in
theorem eca_wide
    {q : ℕ} [Fact q.Prime] (hq5 : 5 ≤ q) {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    {W : Finset (Place k (modularFunctionFieldC k 1))}
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)

    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K]
    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W) (hVI : R.ValueIntegralityLaw w)
    (hj : w.evalAt (jGeomGen k 1) = 0 ∨ w.evalAt (jGeomGen k 1) = 1728)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (eK : ℕ) (heK : 1 ≤ eK) (ε : ↥(NodeLocalized.coeffSubring A K)) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε)
    (c : R.NodeCoordinates K w) (ew : ℕ) (hew : 1 ≤ ew)
    (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ (ew * eK) * u)
    (hmax : (Ideal.span {R.nodeConst K w ϖ, c.x, c.y}).IsMaximal ∧
        ∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hbr : (Ideal.span {R.nodeConst K w ϖ, c.x}).IsPrime ∧ (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime ∧
        c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x} ∧ c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y})
    (hnoeth : IsNoetherianRing ↥(R.nodeIntegersOver K w))
    (hres : ∀ g : ↥(R.nodeIntegersOver K w), ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o))

    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) :
    letI : Algebra (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC k 1) := ((algebraMap k ↥(modularFunctionFieldC k 1)).comp R.redBar).toAlgebra
    ∃ (C₁ : ComponentChart A ↥(modularFunctionFieldBar (1 * q)) ↥(modularFunctionFieldC k 1)) (x₁ : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC k 1))
      (C₂ : ComponentChart A ↥(modularFunctionFieldBar (1 * q)) ↥(modularFunctionFieldC k 1)) (x₂ : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC k 1))
      (An₁ An₂ : Annulus A ↥(modularFunctionFieldBar (1 * q))),

      An₂.dom = An₁.dom ∧ An₂.modulus = An₁.modulus ∧ ((An₁.modulus : AlgebraicClosure ℚ) ≠ 0) ∧
      An₂.param * An₁.param = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (An₁.modulus : AlgebraicClosure ℚ) ∧
      An₁.IsAttached C₁ x₁ ∧ An₂.IsAttached C₂ x₂ ∧
      (∃ Q₁ ∈ An₁.dom, ∃ Q₂ ∈ An₁.dom, μ (Q₁.evalAt An₁.param) ≠ μ (Q₂.evalAt An₁.param)) ∧

      (∀ f : ↥(modularFunctionFieldBar (1 * q)), f ∈ C₁.integers ↔ f ∈ R.R₁.integers) ∧ (∀ f : ↥(modularFunctionFieldBar (1 * q)), f ∈ C₂.integers ↔ f ∈ R.R₂.integers) ∧

      (∀ (f : ↥(modularFunctionFieldBar (1 * q))) (hC : f ∈ C₁.integers) (h₁ : f ∈ R.R₁.integers),
        (C₁.residue ⟨f, hC⟩ ≠ 0 ↔ R.R₁.residue ⟨f, h₁⟩ ≠ 0) ∧
        x₁.ord (C₁.residue ⟨f, hC⟩) = w.ord (R.residue₁ ⟨f, h₁⟩)) ∧
      (∀ (f : ↥(modularFunctionFieldBar (1 * q))) (hC : f ∈ C₂.integers) (h₂ : f ∈ R.R₂.integers),
        (C₂.residue ⟨f, hC⟩ ≠ 0 ↔ R.R₂.residue ⟨f, h₂⟩ ≠ 0) ∧
        x₂.ord (C₂.residue ⟨f, hC⟩) = (arithFrobC q k 1 • w).ord (R.residue₂ ⟨f, h₂⟩)) ∧

      (∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), V ∈ An₁.dom ↔ (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V)) ∧

      (∀ V ∈ An₁.dom, μ (V.evalAt An₁.param) = μ (V.evalAt (c.y : ↥(modularFunctionFieldBar (1 * q))))) ∧

      μ (An₁.modulus : AlgebraicClosure ℚ) = μ ((q : ℕ) : AlgebraicClosure ℚ) ^ ew := by
  classical
  letI : Algebra (ResidueField A) ↥(modularFunctionFieldC k 1) := ((algebraMap k ↥(modularFunctionFieldC k 1)).comp R.redBar).toAlgebra
  haveI := ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * q)
  have hA : A.LiesOverPrime q := ChartOkChartFst.liesOverPrime_of_ker R hker
  have hW' : ∀ w ∈ W, w ∈ ssPlaces q 1 k := fun w hw => (hW w).mp hw
  have hwss : w ∈ ssPlaces q 1 k := hW' w hw

  obtain ⟨a, hass, hwa⟩ := (ModularCurve.mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq q k w).mp hwss
  have hj0 : (jGeomGen k 1 : ↥(modularFunctionFieldC k 1)) - algebraMap k _ a ≠ 0 := jGeomGen_sub_algebraMap_ne_zero k 1 a
  have hord1 : 0 < (charLGeomPlaceOfPoint k a).ord ((jGeomGen k 1 : ↥(modularFunctionFieldC k 1)) - algebraMap k _ a) := by
    have h := ModularCurve.ord_charLGeomPlaceOfPoint_aeval_jqModC_eq_rootMultiplicity k a (Polynomial.X - Polynomial.C a)
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Polynomial.rootMultiplicity_X_sub_C_self] at h
    change (charLGeomPlaceOfPoint k a).ord (jGeomGen k 1 - algebraMap k _ a) = 1 at h
    rw [h]; exact zero_lt_one
  have ha : w.evalAt (jGeomGen k 1) = a := by
    rw [← hwa]
    have hmemc : algebraMap k ↥(modularFunctionFieldC k 1) a ∈ (charLGeomPlaceOfPoint k a).toValuationSubring :=
      (charLGeomPlaceOfPoint k a).algebraMap_mem' a
    have hmem : (jGeomGen k 1 : ↥(modularFunctionFieldC k 1)) ∈ (charLGeomPlaceOfPoint k a).toValuationSubring := by
      have := (charLGeomPlaceOfPoint k a).mem_of_ord_nonneg hj0 hord1.le
      simpa using add_mem this hmemc
    rw [AlgebraicCurve.Place.evalAt_congr _ hmem hmemc (Or.inr hord1), AlgebraicCurve.Place.evalAt_algebraMap]
  have hja : a = 0 ∨ a = 1728 := by rw [← ha]; exact hj

  obtain ⟨hJS, hJQS⟩ := ChartOkDictW.jFun_jqFun_mem_nodeIntegersOver R w hwss K (ChartOkChartFst.jFun_mem_integersFst R hA)
    (ChartOkChartFst.jFun_mem_integersSnd R hA) (ChartOkChartFst.jqFun_mem_integersFst R hA) (ChartOkChartFst.jqFun_mem_integersSnd R hA)
  obtain ⟨xa, hxa⟩ := exists_coeff_lift R hW hRL hker K w hw ϖ hϖ c hmax hres hJS hA
  have hwid : ew = jWidth a := ew_eq_jWidth R hq5 hR W hW' hRL hNV hO hker K w hw a ha xa hxa ϖ hϖ eK heK ε hε hqϖ c ew u hu hxy
  have hxy' : c.x * c.y = R.nodeConst K w ϖ ^ (jWidth a * eK) * u := by rw [← hwid]; exact hxy
  have hxa' : NodeLocalized.redRestrict red K xa = a := hxa.trans ha
  obtain ⟨hspx, hspy⟩ := ChartOkDictW.span_nodeConst_eq_span_kronecker R hR hker hq5 W hW' hRL K w hw a ha hass xa hxa' ϖ hϖ c
    (jWidth a * eK) (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (jWidth_pos a).ne' (by omega))) u hxy' hmax hbr hnoeth hJS hJQS
  obtain ⟨An, An', h4, hdom, hparamx, hmodw, hattS, hattF⟩ :=
    ChartOkChartFst.exists_ssAnnulus_isAttached_both_ends_of_eq_zero_or_eq_1728 R hR hker hq5 W hW' hRL K w hw a ha hja xa hxa' ϖ hϖ
      eK heK ε hε hqϖ c u hu hxy' hmax hbr hJS hJQS hspx hspy hVI

  have hφ : arithFrobC q k 1 • w = charLGeomPlaceOfPoint k (a ^ q) := by
    rw [ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel q k 1 data hKr w, ← hwa,
      ModularCurve.frobOnPlacesGeomLevel_charLGeomPlaceOfPoint k data hKr a]
  have hdom' : An'.dom = An.dom := h4.1
  have hmod' : An'.modulus = An.modulus := h4.2.1
  have hmod0 : (An.modulus : AlgebraicClosure ℚ) ≠ 0 := h4.2.2.1
  have hmod0' : (An'.modulus : AlgebraicClosure ℚ) ≠ 0 := by rw [hmod']; exact hmod0
  have htwo' : An.param * An'.param = algebraMap (AlgebraicClosure ℚ) _ (An'.modulus : AlgebraicClosure ℚ) := by
    rw [mul_comm An.param, hmod']; exact h4.2.2.2
  have hdomw : ∀ V, V ∈ An.dom ↔ P.reduceFst V = w := ChartOkChartFst.mem_dom_iff_reduceFst_eq w hwss a ha An hdom
  have hover : ∀ V, V ∈ An'.dom ↔ P.reduceFst V = w := fun V => by rw [hdom']; exact hdomw V
  have hattF' : An'.IsAttached (ChartOkChartFst.chartFst R hR) (ChartOkChartFst.rc R w) := by rw [← hwa]; exact hattF
  have hattS' : An.IsAttached (ChartOkChartFst.chartSnd R hR) (ChartOkChartFst.rc R (arithFrobC q k 1 • w)) := by rw [hφ]; exact hattS

  obtain ⟨hyR, hyord, hyres⟩ := ChartOkCPT.y_mem_and_ord R c
  have hyC : (c.y : ↥(modularFunctionFieldBar (1 * q))) ∈ (ChartOkChartFst.chartFst R hR).integers := hyR
  have hx1y : (ChartOkChartFst.rc R w).ord ((ChartOkChartFst.chartFst R hR).residue ⟨(c.y : ↥(modularFunctionFieldBar (1 * q))), hyC⟩) = 1 := hyord
  have hyCne : (ChartOkChartFst.chartFst R hR).residue ⟨(c.y : ↥(modularFunctionFieldBar (1 * q))), hyC⟩ ≠ 0 := hyres
  have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  have hϖ0 : (ϖ : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0
    apply hq0
    have h1 := congrArg Subtype.val hqϖ
    simp only [Subring.coe_natCast, Subring.coe_mul, SubmonoidClass.coe_pow] at h1
    rw [h1, h0, zero_pow (by omega), zero_mul]
  have hzf : ∀ Q ∈ An'.dom, Q.ord (c.y : ↥(modularFunctionFieldBar (1 * q))) = 0 := fun Q hQ => by
    have hQw := (hover Q).mp hQ
    obtain ⟨hmem, hne⟩ := ChartOkCPT.y_mem_place_and_evalAt_ne_zero R hR hO W hW' hRL hNV K w hw hVI ϖ hϖ0 c
      (ew * eK) u hu hxy Q hQw
    exact ChartOkCPT.ord_eq_zero_of_evalAt_ne_zero Q (An'.mem_dom Q hQ).1 hmem hne
  have hμy : ∀ Q ∈ An'.dom, μ (Q.evalAt (c.y : ↥(modularFunctionFieldBar (1 * q)))) = μ (Q.evalAt An'.param) := fun Q hQ => by
    have h := (AlgebraicCurve.Annulus.abv_evalAt_lt_one_of_isAttached_of_ord_residue_pos μ hμA An' (ChartOkChartFst.chartFst R hR)
      (ChartOkChartFst.rc R w) hattF' _ hyC hyCne (by rw [hx1y]; exact zero_lt_one) hzf Q hQ).2
    rw [hx1y, zpow_one] at h
    exact h
  refine ⟨ChartOkChartFst.chartFst R hR, ChartOkChartFst.rc R w, ChartOkChartFst.chartSnd R hR, ChartOkChartFst.rc R (arithFrobC q k 1 • w),
    An', An, hdom'.symm, hmod'.symm, hmod0', htwo', hattF', hattS', ChartOkTwist.wide_of_modulus_ne_zero μ hμA An' hmod0',
    fun g => Iff.rfl, fun g => Iff.rfl, ?_, ?_, ?_, fun V hV => (hμy V hV).symm, ?_⟩
  · intro g hCg h₁
    refine ⟨?_, rfl⟩
    change R.residue₁ ⟨g, h₁⟩ ≠ 0 ↔ _
    rw [residue₁_apply]
    exact ⟨fun h h0 => h (by rw [h0, map_zero]), fun h h0 => h ((ProlongationTuple.iota_bijective R).1 (by rw [map_zero]; exact h0))⟩
  · intro g hCg h₂
    refine ⟨?_, rfl⟩
    change R.residue₂ ⟨g, h₂⟩ ≠ 0 ↔ _
    rw [residue₂_apply]
    exact ⟨fun h h0 => h (by rw [h0, map_zero]), fun h h0 => h ((ProlongationTuple.iota_bijective R).1 (by rw [map_zero]; exact h0))⟩
  · intro V
    rw [hover V]
    exact ⟨fun h => ⟨h, ChartOkNT.not_strict_of_reduceFst_mem P hW V hw h⟩, fun h => h.1⟩
  · rw [hmod', hmodw, hwid]
    simp [map_pow]

end ChartOkECA
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ChartOkChartFst"

p2m_open "ModularCurve~coeffMap_injective" in open AlgebraicCurve IsLocalRing _root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve _root_.ModularCurve.PlaceSpecialization _root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.ModularCurve.PlaceSpecialization in
set_option maxHeartbeats 12800000 in
theorem solution
    {q : ℕ} [Fact q.Prime] (hq5 : 5 ≤ q) {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    {W : Finset (Place k (modularFunctionFieldC k 1))}
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)

    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K]
    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W) (hVI : R.ValueIntegralityLaw w)
    (hj : w.evalAt (jGeomGen k 1) = 0 ∨ w.evalAt (jGeomGen k 1) = 1728)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (eK : ℕ) (heK : 1 ≤ eK) (ε : ↥(NodeLocalized.coeffSubring A K)) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε)
    (c : R.NodeCoordinates K w) (ew : ℕ) (hew : 1 ≤ ew)
    (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ (ew * eK) * u)
    (hmax : (Ideal.span {R.nodeConst K w ϖ, c.x, c.y}).IsMaximal ∧
        ∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hbr : (Ideal.span {R.nodeConst K w ϖ, c.x}).IsPrime ∧ (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime ∧
        c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x} ∧ c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y})
    (hnoeth : IsNoetherianRing ↥(R.nodeIntegersOver K w))
    (hres : ∀ g : ↥(R.nodeIntegersOver K w), ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o))

    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) :
    letI : Algebra (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC k 1) :=
      ((algebraMap k ↥(modularFunctionFieldC k 1)).comp R.redBar).toAlgebra
    ∃ (C₁ : ComponentChart A ↥(modularFunctionFieldBar (1 * q)) ↥(modularFunctionFieldC k 1)) (x₁ : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC k 1))
      (C₂ : ComponentChart A ↥(modularFunctionFieldBar (1 * q)) ↥(modularFunctionFieldC k 1)) (x₂ : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC k 1))
      (An₁ An₂ : Annulus A ↥(modularFunctionFieldBar (1 * q))),

      An₂.dom = An₁.dom ∧ An₂.modulus = An₁.modulus ∧ ((An₁.modulus : AlgebraicClosure ℚ) ≠ 0) ∧
      An₂.param * An₁.param = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (An₁.modulus : AlgebraicClosure ℚ) ∧
      An₁.IsAttached C₁ x₁ ∧ An₂.IsAttached C₂ x₂ ∧
      (∃ Q₁ ∈ An₁.dom, ∃ Q₂ ∈ An₁.dom, μ (Q₁.evalAt An₁.param) ≠ μ (Q₂.evalAt An₁.param)) ∧

      (∀ f : ↥(modularFunctionFieldBar (1 * q)), f ∈ C₁.integers ↔ f ∈ R.R₁.integers) ∧ (∀ f : ↥(modularFunctionFieldBar (1 * q)), f ∈ C₂.integers ↔ f ∈ R.R₂.integers) ∧

      (∀ (f : ↥(modularFunctionFieldBar (1 * q))) (hC : f ∈ C₁.integers) (h₁ : f ∈ R.R₁.integers),
        (C₁.residue ⟨f, hC⟩ ≠ 0 ↔ R.R₁.residue ⟨f, h₁⟩ ≠ 0) ∧
        x₁.ord (C₁.residue ⟨f, hC⟩) = w.ord (R.residue₁ ⟨f, h₁⟩)) ∧
      (∀ (f : ↥(modularFunctionFieldBar (1 * q))) (hC : f ∈ C₂.integers) (h₂ : f ∈ R.R₂.integers),
        (C₂.residue ⟨f, hC⟩ ≠ 0 ↔ R.R₂.residue ⟨f, h₂⟩ ≠ 0) ∧
        x₂.ord (C₂.residue ⟨f, hC⟩) = (arithFrobC q k 1 • w).ord (R.residue₂ ⟨f, h₂⟩)) ∧

      (∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), V ∈ An₁.dom ↔ (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V)) ∧

      (∀ V ∈ An₁.dom, μ (V.evalAt An₁.param) = μ (V.evalAt (c.y : ↥(modularFunctionFieldBar (1 * q))))) ∧

      μ (An₁.modulus : AlgebraicClosure ℚ) = μ ((q : ℕ) : AlgebraicClosure ℚ) ^ ew := by
  exact ChartOkECA.eca_wide hq5 P hW R hR hRL hNV hO hker K w hw hVI hj ϖ hϖ eK heK ε hε hqϖ c ew hew u hu hxy hmax hbr hnoeth hres μ hμA

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728 (solution)
