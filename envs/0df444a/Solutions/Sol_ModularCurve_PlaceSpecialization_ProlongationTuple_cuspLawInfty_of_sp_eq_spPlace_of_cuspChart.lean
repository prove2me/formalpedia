-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.cuspLawInfty_of_sp_eq_spPlace_of_cuspChart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/3d6ae0ce-7dd8-5cd8-8b9c-2ed3a7a7eda4

import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_mapDomain_spPlace_eq_ord_coeffMap_of_surjective
import Theorems.Thm_ModularCurve_modularFunctionFieldBar_eq_modularFunctionFieldC
import Definitions.Def_ModularCurve_ChartSemicontinuity
import Theorems.Thm_ModularCurve_finiteAlong_heckeAlphaBar_of_prime
import Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
import Theorems.Thm_AlgebraicCurve_normFormulaAlong_of_separableAlong
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_CharPReduction_modularRedLocHom_mem
import Theorems.Thm_ModularCurve_exists_mem_riemannRochSpace_notMem_sub_single_of_le_degree
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isCuspidal_of_not_isAffineGeomPlace_reduceFst
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_not_isAffineGeomPlace_reduceFst_of_isCuspidal
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isInftySide_or_isZeroSide_of_isCuspidal
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_not_isInftySide_of_isZeroSide
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_reduceFst_eq_frobOnPlacesGeomLevel_reduceSnd_of_isZeroSide
import Theorems.Thm_ModularCurve_isAffineGeomPlace_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace
import Theorems.Thm_ModularCurve_coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized_mul_of_not_dvd
import Theorems.Thm_ModularCurve_coeffEmb_jq
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_exists_regularProlongation_modularFunctionFieldBar_mul_of_not_dvd
import Theorems.Thm_ModularCurve_geomAut_atkinLehner_comp_legs
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ValuationSubring_ringHom_apply_eq_zero_of_mem_maximalIdeal
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isInftySide_atkinLehnerBar_smul_iff
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceFst_atkinLehnerBar_smul
import Theorems.Thm_ModularCurve_PlaceSpecialization_mem_chartLocalSetFst_of_split
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_ModularCurve_mem_integralCoeffs_of_integral_affineBaseFin
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_coe_piFin_eq_coeffRed
import Theorems.Thm_AlgebraicCurve_Place_mem_toValuationSubring_of_isIntegral_adjoin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Theorems.Thm_ModularCurve_coe_atkinLehnerInvolutionFull_modularUnitSeries
import Theorems.Thm_ModularCurve_finrankAlong_heckeBetaBar
import Theorems.Thm_AlgebraicCurve_finrankAlong_comp
import Theorems.Thm_AlgebraicCurve_finrankAlong_id
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ValuationSubring_ReduceAt
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_piFin_range_localizes_of_jqModC_mem
import Theorems.Thm_ModularCurve_CharPModel_exists_monic_eval2_affineBaseFin_eq_zero_of_mem_modularLocalized_of_forall_mem_of_jBar_mem
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_ord_coeffEmb_modularUnitSeries_eq_zero_of_not_isCusp
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_integersFst_residue_ne_zero_of_coe_eq_modularUnitSeries_level
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_eq_zero_of_coe_eq_modularUnitSeries_of_notMem_ssPlaces
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_residue_eq_zero_of_mem_integersSnd_of_coe_eq_modularUnitSeries
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceSnd_atkinLehnerBar_smul
import Theorems.Thm_ModularCurve_arithFrobC_smul_mem_ssPlaces_univ
import Definitions.Def_ModularCurve_FibreModel
import Theorems.Thm_ValuationSubring_exists_dvd_pow_of_mem_maximalIdeal
import Theorems.Thm_ModularCurve_adjoin_jBar_jNBar_eq_top
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_CharPReduction_mem_or_inv_mem_modularLocalized
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_FrobeniusModL
import Theorems.Thm_ModularCurve_qExpand_jqModC_eq_pow_unconditional
import Definitions.Def_ModularCurve_HeckeOperator
import Theorems.Thm_AlgebraicCurve_Place_exists_integralClosureAt_of_ord_fiber_nonneg
import Definitions.Def_ModularCurve_QAdicPlaceMod
import Theorems.Thm_ModularCurve_mem_integralCoeffs_of_integral_affineBaseInf
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_coe_piInf_eq_coeffRed_of_cuspChart
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_piInf_range_localizes_of_not_affine
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_normReduction_of_not_dvd_of_surjective
import Theorems.Thm_ModularCurve_PlaceSpecialization_hasCoordinates_of_sp_eq_spPlace
import Theorems.Thm_ModularCurve_CharPModel_exists_monic_eval2_affineBaseInf_eq_zero_of_mem_modularLocalized_of_forall_inv_jBar_mem
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_ramificationIndexAlong_heckeAlphaBar_filter_isInftySide_fiberAlong_eq_one_of_forall_ord_jq_sub_nonpos
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

section NR3_10_reducesDivisors

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~jBar P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve ModularCurve.CharPModel"

noncomputable section

section PenSLocalized

variable {N : ℕ} [NeZero N] {A : ValuationSubring (AlgebraicClosure ℚ)}

private def penS_pack (r : CharPReduction.modularRing N A.toSubring) : LaurentSeries A where
  coeff n := ⟨(r : LaurentSeries (AlgebraicClosure ℚ)).coeff n,
    CharPReduction.modularRing_le_integralCoeffs N A.toSubring r.2 n⟩
  isPWO_support' := (r : LaurentSeries (AlgebraicClosure ℚ)).isPWO_support.mono
    (fun _ hn h => hn (Subtype.ext h))

private theorem penS_coeffMap_subtype_pack (r : CharPReduction.modularRing N A.toSubring) :
    coeffMap A.subtype (penS_pack r) = (r : LaurentSeries (AlgebraicClosure ℚ)) := by
  ext n
  rfl

private theorem penS_coeffMap_red_pack {k : Type*} [Field k] (red : A →+* k)
    (r : CharPReduction.modularRing N A.toSubring) :
    coeffMap red (penS_pack r) =
      CharPReduction.redRes A.toSubring red (CharPReduction.modularRing N A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs N A.toSubring) r := by
  ext n
  rfl

private theorem penS_modularRedLocHom_eq_redLoc {k : Type*} [Field k] (red : A →+* k)
    (x : CharPReduction.modularLocalized N A.toSubring red) :
    CharPReduction.modularRedLocHom N A.toSubring red x
      = CharPReduction.redLoc (A := A.toSubring) (red := red)
          (R := CharPReduction.modularRing N A.toSubring)
          (hR := CharPReduction.modularRing_le_integralCoeffs N A.toSubring) x :=
  CharPReduction.redLocHom_apply x

private theorem penS_modularRedLocHom_coe {k : Type*} [Field k] (red : A →+* k)
    (t : CharPReduction.modularRing N A.toSubring) :
    CharPReduction.modularRedLocHom N A.toSubring red
        ⟨t, CharPReduction.subring_le_localizedAtKer A.toSubring red
          (CharPReduction.modularRing N A.toSubring)
          (CharPReduction.modularRing_le_integralCoeffs N A.toSubring) t.2⟩
      = coeffMap red (penS_pack t) := by
  rw [penS_coeffMap_red_pack, penS_modularRedLocHom_eq_redLoc]
  exact CharPReduction.redLoc_coe (hR := CharPReduction.modularRing_le_integralCoeffs N A.toSubring) t

private theorem penS_mem_bar_of_mem_modularRing (x : LaurentSeries (AlgebraicClosure ℚ))
    (hx : x ∈ CharPReduction.modularRing N A.toSubring) : x ∈ modularFunctionFieldBar N := by
  rw [modularFunctionFieldBar_eq_modularFunctionFieldC N]
  have hle : CharPReduction.modularRing N A.toSubring
      ≤ (modularFunctionFieldC (AlgebraicClosure ℚ) N).toSubalgebra.toSubring := by
    refine Subring.closure_le.mpr (Set.union_subset ?_ ?_)
    · rintro _ ⟨a, rfl⟩
      exact (modularFunctionFieldC (AlgebraicClosure ℚ) N).algebraMap_mem (a : AlgebraicClosure ℚ)
    · rintro _ hy
      rcases hy with rfl | rfl
      · exact jqModC_mem (AlgebraicClosure ℚ) N
      · exact jqNModC_mem (AlgebraicClosure ℚ) N
  exact hle hx

private theorem penS_mapDomain_spPlace_eq_ord_modularRedLocHom {q : ℕ} [Fact q.Prime]
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) (hred : Function.Surjective red) (hqN : ¬ q ∣ N)
    (fm : FibreModel N A q k red) (cc : fm.CuspChart)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (f : modularFunctionFieldBar N)
    (hf : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized N A.toSubring red)
    (h0 : CharPReduction.modularRedLocHom N A.toSubring red ⟨f, hf⟩ ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hD : ∀ V, D V = V.ord f)
    (v : Place k (modularFunctionFieldC k N)) :
    Finsupp.mapDomain (fm.spPlace hred dataAll hsep) D v =
      v.ord (⟨CharPReduction.modularRedLocHom N A.toSubring red ⟨f, hf⟩,
        CharPReduction.modularRedLocHom_mem A.toSubring red N ⟨f, hf⟩⟩ : modularFunctionFieldC k N) := by
  obtain ⟨r, s, hs, hfs⟩ := (CharPReduction.mem_localizedAtKer A.toSubring red
    (CharPReduction.modularRing N A.toSubring)
    (CharPReduction.modularRing_le_integralCoeffs N A.toSubring)).mp hf

  have hmem : ∀ t : CharPReduction.modularRing N A.toSubring,
      coeffMap red (penS_pack t) ∈ modularFunctionFieldC k N := by
    intro t
    rw [← penS_modularRedLocHom_coe red t]
    exact CharPReduction.modularRedLocHom_mem A.toSubring red N _
  have hsne : coeffMap red (penS_pack s) ≠ 0 := by
    rw [penS_coeffMap_red_pack]
    exact CharPReduction.redRes_ne_zero_of_notMem hs
  have hspec : CharPReduction.modularRedLocHom N A.toSubring red ⟨f, hf⟩ * coeffMap red (penS_pack s)
      = coeffMap red (penS_pack r) := by
    rw [penS_coeffMap_red_pack, penS_coeffMap_red_pack, penS_modularRedLocHom_eq_redLoc]
    exact CharPReduction.redLoc_spec (hR := CharPReduction.modularRing_le_integralCoeffs N A.toSubring)
      ⟨f, hf⟩ hfs
  have hrne : coeffMap red (penS_pack r) ≠ 0 := by
    rw [← hspec]
    exact mul_ne_zero h0 hsne

  have hyr : coeffMap A.subtype (penS_pack r) ∈ modularFunctionFieldBar N := by
    rw [penS_coeffMap_subtype_pack]
    exact penS_mem_bar_of_mem_modularRing _ r.2
  have hys : coeffMap A.subtype (penS_pack s) ∈ modularFunctionFieldBar N := by
    rw [penS_coeffMap_subtype_pack]
    exact penS_mem_bar_of_mem_modularRing _ s.2
  have hfs' : f * (⟨coeffMap A.subtype (penS_pack s), hys⟩ : modularFunctionFieldBar N)
      = ⟨coeffMap A.subtype (penS_pack r), hyr⟩ := by
    apply Subtype.ext
    rw [IntermediateField.coe_mul]
    show (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype (penS_pack s)
      = coeffMap A.subtype (penS_pack r)
    rw [penS_coeffMap_subtype_pack, penS_coeffMap_subtype_pack]
    exact hfs
  have hs'ne : (⟨coeffMap A.subtype (penS_pack s), hys⟩ : modularFunctionFieldBar N) ≠ 0 := by
    intro h
    have h1 : (s : LaurentSeries (AlgebraicClosure ℚ)) = 0 := by
      simpa [penS_coeffMap_subtype_pack] using congrArg Subtype.val h
    have h2 : s = 0 := by simpa using h1
    apply hsne
    rw [penS_coeffMap_red_pack, h2, map_zero]
  have hr'ne : (⟨coeffMap A.subtype (penS_pack r), hyr⟩ : modularFunctionFieldBar N) ≠ 0 := by
    intro h
    have h1 : (r : LaurentSeries (AlgebraicClosure ℚ)) = 0 := by
      simpa [penS_coeffMap_subtype_pack] using congrArg Subtype.val h
    have h2 : r = 0 := by simpa using h1
    apply hrne
    rw [penS_coeffMap_red_pack, h2, map_zero]
  have hfne : f ≠ 0 := by
    intro h
    apply hr'ne
    rw [← hfs', h, zero_mul]

  haveI := hasPrincipalDivisors_modularFunctionFieldBar_unconditional N
  obtain ⟨Dr, hDr, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ)
    (⟨coeffMap A.subtype (penS_pack r), hyr⟩ : modularFunctionFieldBar N) hr'ne
  obtain ⟨Ds, hDs, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ)
    (⟨coeffMap A.subtype (penS_pack s), hys⟩ : modularFunctionFieldBar N) hs'ne
  have hDeq : D = Dr - Ds := by
    ext V
    rw [Finsupp.sub_apply, hD V, hDr V, hDs V, ← hfs', V.ord_mul hfne hs'ne]
    omega

  have hr := FibreModel.mapDomain_spPlace_eq_ord_coeffMap_of_surjective N q A k red hred hqN fm cc
    dataAll hsep (penS_pack r) hyr (hmem r) hrne Dr hDr v
  have hs₂ := FibreModel.mapDomain_spPlace_eq_ord_coeffMap_of_surjective N q A k red hred hqN fm cc
    dataAll hsep (penS_pack s) hys (hmem s) hsne Ds hDs v
  rw [hDeq, Finsupp.mapDomain_sub, Finsupp.sub_apply, hr, hs₂]
  have himg : (⟨CharPReduction.modularRedLocHom N A.toSubring red ⟨f, hf⟩,
        CharPReduction.modularRedLocHom_mem A.toSubring red N ⟨f, hf⟩⟩ : modularFunctionFieldC k N)
        * ⟨coeffMap red (penS_pack s), hmem s⟩ = ⟨coeffMap red (penS_pack r), hmem r⟩ :=
    Subtype.ext (by rw [IntermediateField.coe_mul]; exact hspec)
  have himg_ne : (⟨CharPReduction.modularRedLocHom N A.toSubring red ⟨f, hf⟩,
      CharPReduction.modularRedLocHom_mem A.toSubring red N ⟨f, hf⟩⟩ : modularFunctionFieldC k N) ≠ 0 :=
    fun h => h0 (by simpa using congrArg Subtype.val h)
  have hsbar_ne : (⟨coeffMap red (penS_pack s), hmem s⟩ : modularFunctionFieldC k N) ≠ 0 :=
    fun h => hsne (by simpa using congrArg Subtype.val h)
  rw [← himg, v.ord_mul himg_ne hsbar_ne]
  omega

end PenSLocalized

end

end NR3_10_reducesDivisors

section NR3_20_normroad

p2m_open "AlgebraicCurve ModularCurve~jBar P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve ModularCurve.PlaceSpecialization~IsInftySide~jFun~tInfty~tZero~IsCuspidal~IsZeroSide P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve.PlaceSpecialization"

private theorem mapDomain_apply_eq_sum {α β : Type*} (r : α → β) [DecidableEq β] (D : α →₀ ℤ) (b : β) :
    Finsupp.mapDomain r D b = ∑ a ∈ D.support with r a = b, D a := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  simp only [Finsupp.sum, Finsupp.single_apply]
  rw [Finset.sum_filter]

private theorem mapDomain_filter_apply {α β : Type*} (r : α → β) (p : α → Prop) [DecidablePred p]
    [DecidableEq β] (D : α →₀ ℤ) (b : β) :
    Finsupp.mapDomain r (D.filter p) b = ∑ a ∈ D.support with (p a ∧ r a = b), D a := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  simp only [Finsupp.sum, Finsupp.support_filter, Finsupp.filter_apply, Finsupp.single_apply]
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  by_cases hp : p a <;> by_cases hr : r a = b <;> simp [hp, hr]

private scoped instance charZero_laurentSeries_algClosure : CharZero (LaurentSeries (AlgebraicClosure ℚ)) :=
  charZero_of_injective_ringHom (HahnSeries.C_injective (Γ := ℤ) (R := AlgebraicClosure ℚ))

private scoped instance charZero_modularFunctionFieldBar (M : ℕ) [NeZero M] :
    CharZero (modularFunctionFieldBar M) :=
  (algebraMap (↥(modularFunctionFieldBar M)) (LaurentSeries (AlgebraicClosure ℚ))).charZero

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_qExpand jNum jNumQ jq ofPowerSeries_coeff_of_neg coeff_jq_neg_one jqN evalAtJ evalAtJ_X ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffMap_algebraMap coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_eq_map_intCast modularFunctionFieldC jqModC_mem jqNModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff KroneckerCongruence ssPlaces jGeomGen jNGeomGen IsAffineGeomPlace cuspInftyGeom ord_cuspInftyGeom_jq order_jqModC_def jqModC_ne_zero_def jq_mem_full coeff_jqModC_neg_one coeffSemilinearAut.coeffMap_qExpand coeffSemilinearAut.coeffMap_jqModC coeffSemilinearAut.coeffMap_mem_modularFunctionFieldC coeffSemilinearAut arithFrobC isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_jqModC qExpandAlgHomC qExpandAlgHomC_apply divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full jqModC_mem_full coeffMap_qExpand CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.mem_localizedAtKer CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc CharPReduction.redRes_ne_zero_of_notMem CharPReduction.redLoc_spec CharPReduction.redLoc_coe CharPReduction.redLocHom_apply CharPReduction.constSeries CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.affineBaseFin CharPModel.affineBaseInf CharPModel.FibreModel modularFunctionFieldBar_eq_modularFunctionFieldC finiteAlong_heckeAlphaBar_of_prime isCurveOver_modularFunctionFieldBar arithFrobC_smul_eq_frobOnPlacesGeomLevel CharPReduction.modularRedLocHom_mem exists_mem_riemannRochSpace_notMem_sub_single_of_le_degree isAffineGeomPlace_frobOnPlacesGeomLevel coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized_mul_of_not_dvd coeffEmb_jq exists_isAtkinLehnerAutFull_of_prime_of_not_dvd exists_regularProlongation_modularFunctionFieldBar_mul_of_not_dvd geomAut_atkinLehner_comp_legs hasPrincipalDivisors_modularFunctionFieldBar_unconditional place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin finrankAlong_heckeBetaBar CharPModel.FibreModel.piFin_range_localizes_of_jqModC_mem CharPModel.exists_monic_eval2_affineBaseFin_eq_zero_of_mem_modularLocalized_of_forall_mem_of_jBar_mem arithFrobC_smul_mem_ssPlaces_univ adjoin_jBar_jNBar_eq_top nonempty_modularPolynomialData relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi CharPReduction.mem_or_inv_mem_modularLocalized pow_char_eq_coeffMap_frobenius_qExpand qExpand_jqModC_eq_pow_unconditional mem_integralCoeffs_of_integral_affineBaseInf CharPModel.exists_monic_eval2_affineBaseInf_eq_zero_of_mem_modularLocalized_of_forall_inv_jBar_mem"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.atkinLehnerBar ProlongationTuple.jFun ProlongationTuple.jQFun ProlongationTuple.tInfty ProlongationTuple.tZero ProlongationTuple.IsCuspidal ProlongationTuple.IsInftySide ProlongationTuple.IsZeroSide ProlongationTuple ProlongationTuple.residue₁_apply ProlongationTuple.residue₂_apply ProlongationTuple.OrderLawFixed ProlongationTuple.CuspLawInfty reduceFst reduceSnd IsStrictFst IsStrictSnd sp d0_j_pole d1 ReducesDivisors fibreReduction chartClosure chartLocalSetFst ChartEtaleAt IsChartAt HasCoordinates ProlongationTuple.isCuspidal_of_not_isAffineGeomPlace_reduceFst ProlongationTuple.not_isAffineGeomPlace_reduceFst_of_isCuspidal ProlongationTuple.isInftySide_or_isZeroSide_of_isCuspidal ProlongationTuple.not_isInftySide_of_isZeroSide ProlongationTuple.reduceFst_eq_frobOnPlacesGeomLevel_reduceSnd_of_isZeroSide exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace ProlongationTuple.isInftySide_atkinLehnerBar_smul_iff reduceFst_atkinLehnerBar_smul mem_chartLocalSetFst_of_split hasCoordinates_of_sp_eq_spPlace"
p2m_open "ModularCurve.PlaceSpecialization~IsInftySide~jFun~tInfty~tZero~IsCuspidal~IsZeroSide ModularCurve~jBar"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

private theorem inertiaDeg_heckeAlphaBar_eq_one
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    letI := algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q)
    haveI := isScalarTower_along (heckeAlphaBar (AlgebraicClosure ℚ) N q)
    haveI := isIntegral_along (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα
    W.inertiaDeg (modularFunctionFieldBar N) = 1 := by
  letI := algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q)
  haveI := isScalarTower_along (heckeAlphaBar (AlgebraicClosure ℚ) N q)
  haveI := isIntegral_along (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα
  show W.inertiaDeg (modularFunctionFieldBar N) = 1
  haveI := isCurveOver_modularFunctionFieldBar (N * q)
  haveI := isCurveOver_modularFunctionFieldBar N
  haveI := IsCurveOver.finite_residueField W
  haveI := IsCurveOver.finite_residueField (W.restrict (modularFunctionFieldBar N))
  have hW : W.deg = 1 := by
    refine W.deg_eq_one_of_isAlgClosed ?_
    exact Module.finrank_pos.ne'
  have hV : (W.restrict (modularFunctionFieldBar N)).deg = 1 := by
    refine (W.restrict (modularFunctionFieldBar N)).deg_eq_one_of_isAlgClosed ?_
    exact Module.finrank_pos.ne'
  have ht := W.deg_restrict_mul_inertiaDeg (F := modularFunctionFieldBar N)
  rw [hV, hW, one_mul] at ht
  exact ht

open Classical in

private theorem pushforwardAlong_heckeAlphaBar_apply
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (u : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    Divisor.pushforwardAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα D u =
      ∑ W ∈ D.support with W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα = u, D W := by
  letI := algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q)
  haveI := isScalarTower_along (heckeAlphaBar (AlgebraicClosure ℚ) N q)
  haveI := isIntegral_along (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα
  have hres : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα = W.restrict (modularFunctionFieldBar N) :=
    fun _ => rfl
  show Divisor.pushforward (modularFunctionFieldBar N) D u = _
  rw [Divisor.pushforward_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun W _ => ?_)
  have hW : W.inertiaDeg (modularFunctionFieldBar N) = 1 := inertiaDeg_heckeAlphaBar_eq_one (hα := hα) W
  rw [hres W, hW]
  simp

open Classical in

private theorem mapDomain_sp_pushforwardAlong (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (v : Place k (modularFunctionFieldC k N)) :
    Finsupp.mapDomain P.sp (Divisor.pushforwardAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα D) v =
      Finsupp.mapDomain P.reduceFst D v := by
  set E := Divisor.pushforwardAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα D with hEdef
  have hE : ∀ u, E u = ∑ W ∈ D.support with
      W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα = u, D W :=
    fun u => pushforwardAlong_heckeAlphaBar_apply D u
  rw [mapDomain_apply_eq_sum, mapDomain_apply_eq_sum]

  set T := D.support.image (fun W => W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα) with hT
  have hsub : E.support.filter (fun u => P.sp u = v) ⊆ T.filter (fun u => P.sp u = v) := by
    intro u hu
    rw [Finset.mem_filter] at hu ⊢
    refine ⟨?_, hu.2⟩
    by_contra hnot
    apply Finsupp.mem_support_iff.mp hu.1
    rw [hE u]
    refine Finset.sum_eq_zero (fun W hW => ?_)
    exact absurd (Finset.mem_image.mpr ⟨W, (Finset.mem_filter.mp hW).1, (Finset.mem_filter.mp hW).2⟩) hnot
  have hvan : ∀ u ∈ T.filter (fun u => P.sp u = v), u ∉ E.support.filter (fun u => P.sp u = v) → E u = 0 := by
    intro u hu hnot
    by_contra hne
    exact hnot (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hne, (Finset.mem_filter.mp hu).2⟩)
  rw [Finset.sum_subset hsub hvan]

  have hmaps : ∀ W ∈ D.support.filter (fun W => P.reduceFst W = v),
      W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα ∈ T.filter (fun u => P.sp u = v) := by
    intro W hW
    rw [Finset.mem_filter] at hW
    exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hW.1, hW.2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl (fun u hu => ?_)
  rw [hE u]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext W
  simp only [Finset.mem_filter, Finsupp.mem_support_iff]
  constructor
  · rintro ⟨hW, hWu⟩
    refine ⟨⟨hW, ?_⟩, hWu⟩
    have hu' := (Finset.mem_filter.mp hu).2
    show P.sp (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα) = v
    rw [hWu]
    exact hu'
  · rintro ⟨⟨hW, -⟩, hWu⟩
    exact ⟨hW, hWu⟩

variable {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P) (hqN : ¬ q ∣ N)

private def NormReduction : Prop :=
  ∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    letI := algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q)
    ∃ hn : ((Algebra.norm (modularFunctionFieldBar N) f : modularFunctionFieldBar N) :
        LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized N A.toSubring red,
      CharPReduction.modularRedLocHom N A.toSubring red ⟨Algebra.norm (modularFunctionFieldBar N) f, hn⟩ ≠ 0 ∧
      ∀ u : Place k (modularFunctionFieldC k N),
        (frobOnPlacesGeomLevel k N data hKr u).ord
            (⟨CharPReduction.modularRedLocHom N A.toSubring red ⟨Algebra.norm (modularFunctionFieldBar N) f, hn⟩,
              CharPReduction.modularRedLocHom_mem A.toSubring red N
                ⟨Algebra.norm (modularFunctionFieldBar N) f, hn⟩⟩ : modularFunctionFieldC k N) =
          (frobOnPlacesGeomLevel k N data hKr u).ord (R.residue₁ ⟨f, h₁⟩) + u.ord (R.residue₂ ⟨f, h₂⟩)

private theorem ne_zero_of_residue_ne_zero {f : modularFunctionFieldBar (N * q)} (h₁ : f ∈ R.R₁.integers)
    (hr₁ : R.R₁.residue ⟨f, h₁⟩ ≠ 0) : f ≠ 0 := by
  rintro rfl
  apply hr₁
  exact map_zero R.R₁.residue

include hqN in

private theorem mapDomain_reduceFst_eq_ord_add_ord (hsp : ReducesDivisors P) (hC : NormReduction R)
    (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (hr₁ : R.R₁.residue ⟨f, h₁⟩ ≠ 0) (hr₂ : R.R₂.residue ⟨f, h₂⟩ ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hD : ∀ W, D W = W.ord f)
    (u : Place k (modularFunctionFieldC k N)) :
    Finsupp.mapDomain P.reduceFst D (frobOnPlacesGeomLevel k N data hKr u) =
      (frobOnPlacesGeomLevel k N data hKr u).ord (R.residue₁ ⟨f, h₁⟩) + u.ord (R.residue₂ ⟨f, h₂⟩) := by
  have _ := hqN
  have hCf := hC f h₁ h₂ hr₁ hr₂
  obtain ⟨hn, hne, hord⟩ := hCf
  have hf0 : f ≠ 0 := ne_zero_of_residue_ne_zero R h₁ hr₁

  haveI := isCurveOver_modularFunctionFieldBar (N * q)
  have hfin := finiteAlong_heckeAlphaBar_of_prime (AlgebraicClosure ℚ) N q
  have hsep := separableAlong_of_charZero (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα
  have hN := normFormulaAlong_of_separableAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hfin hsep
  letI := algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q)
  haveI := isScalarTower_along (heckeAlphaBar (AlgebraicClosure ℚ) N q)
  haveI : Module.Finite (modularFunctionFieldBar N) (modularFunctionFieldBar (N * q)) := hfin
  have hN' : Divisor.PushforwardNormFormula (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
      (modularFunctionFieldBar (N * q)) := hN
  have hE : ∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      Divisor.pushforwardAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα D V =
        V.ord (Algebra.norm (modularFunctionFieldBar N) f) :=
    fun V => hN' f hf0 D hD V
  have h1 := hsp (Algebra.norm (modularFunctionFieldBar N) f) hn
    (CharPReduction.modularRedLocHom_mem A.toSubring red N ⟨_, hn⟩) hne
    (Divisor.pushforwardAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα D) hE
    (frobOnPlacesGeomLevel k N data hKr u)
  rw [mapDomain_sp_pushforwardAlong P D] at h1
  rw [h1]
  exact hord u

include hqN in

private theorem orderLawFixed_of_normReduction (hsp : ReducesDivisors P) (hC : NormReduction R) :
    R.OrderLawFixed := by
  unfold ProlongationTuple.OrderLawFixed
  intro f h₁ h₂ hr₁ hr₂ D hD v hv _hv'
  have h := mapDomain_reduceFst_eq_ord_add_ord R hqN hsp hC f h₁ h₂ hr₁ hr₂ D hD
    (frobOnPlacesGeomLevel k N data hKr v)
  rw [hv] at h
  exact h

open Classical in

private def CuspLocalSemicontinuity : Prop :=
  (∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      (∀ W, D W = W.ord f) →
      ∀ v : Place k (modularFunctionFieldC k N),
        (∃ c, ProlongationTuple.IsInftySide P c ∧ P.reduceFst c = v) →
        (∀ W, ProlongationTuple.IsInftySide P W → P.reduceFst W = v → 0 ≤ D W) →
        Finsupp.mapDomain P.reduceFst (D.filter (ProlongationTuple.IsInftySide P)) v ≤ v.ord (R.residue₁ ⟨f, h₁⟩)) ∧
  (∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      (∀ W, D W = W.ord f) →
      ∀ u : Place k (modularFunctionFieldC k N),
        (∃ c, ProlongationTuple.IsZeroSide P c ∧ P.reduceSnd c = u) →
        (∀ W, ProlongationTuple.IsZeroSide P W → P.reduceSnd W = u → 0 ≤ D W) →
        Finsupp.mapDomain P.reduceSnd (D.filter (ProlongationTuple.IsZeroSide P)) u ≤ u.ord (R.residue₂ ⟨f, h₂⟩))

private def CuspPoleCancellation : Prop :=
  ∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    ∀ u : Place k (modularFunctionFieldC k N),
      ∃ (h : modularFunctionFieldBar (N * q)) (hh₁ : h ∈ R.R₁.integers) (hh₂ : h ∈ R.R₂.integers),
        R.R₁.residue ⟨h, hh₁⟩ ≠ 0 ∧ R.R₂.residue ⟨h, hh₂⟩ ≠ 0 ∧
        (∀ W, ProlongationTuple.IsInftySide P W → P.reduceFst W = frobOnPlacesGeomLevel k N data hKr u →
          0 ≤ W.ord h) ∧
        (∀ W, ProlongationTuple.IsZeroSide P W → P.reduceSnd W = u → 0 ≤ W.ord h) ∧
        (∀ W, ProlongationTuple.IsInftySide P W → P.reduceFst W = frobOnPlacesGeomLevel k N data hKr u →
          0 ≤ W.ord (f * h)) ∧
        (∀ W, ProlongationTuple.IsZeroSide P W → P.reduceSnd W = u → 0 ≤ W.ord (f * h))

private def PullbackBalanced : Prop :=
  ∀ x : modularFunctionFieldBar N, x ≠ 0 →
    ∃ (c : AlgebraicClosure ℚ) (h₁ : c • heckeAlphaBar (AlgebraicClosure ℚ) N q x ∈ R.R₁.integers)
      (h₂ : c • heckeAlphaBar (AlgebraicClosure ℚ) N q x ∈ R.R₂.integers),
      R.R₁.residue ⟨_, h₁⟩ ≠ 0 ∧ R.R₂.residue ⟨_, h₂⟩ ≠ 0

private def SpAvoids (P : PlaceSpecialization A q N data hKr k red hα hβ) : Prop :=
  ∀ v : Place k (modularFunctionFieldC k N),
    ∃ t : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), P.sp t ≠ v

open Classical in

private theorem mapDomain_filter_inftySide_add
    (D E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (v : Place k (modularFunctionFieldC k N)) :
    Finsupp.mapDomain P.reduceFst ((D + E).filter (ProlongationTuple.IsInftySide P)) v =
      Finsupp.mapDomain P.reduceFst (D.filter (ProlongationTuple.IsInftySide P)) v +
        Finsupp.mapDomain P.reduceFst (E.filter (ProlongationTuple.IsInftySide P)) v := by
  rw [Finsupp.filter_add, Finsupp.mapDomain_add, Finsupp.add_apply]

variable [IsAlgClosed k]

include hqN in

private theorem reduceFst_eq_of_isZeroSide {W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))}
    {u : Place k (modularFunctionFieldC k N)} (hW : ProlongationTuple.IsZeroSide P W) (hWu : P.reduceSnd W = u) :
    P.reduceFst W = frobOnPlacesGeomLevel k N data hKr u := by
  classical
  rw [ProlongationTuple.reduceFst_eq_frobOnPlacesGeomLevel_reduceSnd_of_isZeroSide P hqN W hW, hWu]

include hqN in

private theorem not_isInftySide_iff (hinj : Function.Injective (frobOnPlacesGeomLevel k N data hKr))
    (u : Place k (modularFunctionFieldC k N))
    (hu : ¬ IsAffineGeomPlace k N (frobOnPlacesGeomLevel k N data hKr u))
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    (P.reduceFst W = frobOnPlacesGeomLevel k N data hKr u ∧ ¬ ProlongationTuple.IsInftySide P W) ↔
      (ProlongationTuple.IsZeroSide P W ∧ P.reduceSnd W = u) := by
  constructor
  · rintro ⟨hW, hns⟩
    have hcusp : ProlongationTuple.IsCuspidal P W :=
      ProlongationTuple.isCuspidal_of_not_isAffineGeomPlace_reduceFst P W (by rw [hW]; exact hu)
    rcases ProlongationTuple.isInftySide_or_isZeroSide_of_isCuspidal P hqN W hcusp with hinf | hzero
    · exact (hns hinf).elim
    · refine ⟨hzero, ?_⟩
      have hid := reduceFst_eq_of_isZeroSide (P := P) hqN hzero rfl
      rw [hW] at hid
      exact (hinj hid).symm
  · rintro ⟨hzero, hWu⟩
    exact ⟨reduceFst_eq_of_isZeroSide (P := P) hqN hzero hWu,
      ProlongationTuple.not_isInftySide_of_isZeroSide P W hzero⟩

include hqN in
open Classical in

private theorem sum_not_isInftySide_eq (hinj : Function.Injective (frobOnPlacesGeomLevel k N data hKr))
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (u : Place k (modularFunctionFieldC k N))
    (hu : ¬ IsAffineGeomPlace k N (frobOnPlacesGeomLevel k N data hKr u)) :
    (∑ W ∈ D.support with
        (P.reduceFst W = frobOnPlacesGeomLevel k N data hKr u ∧ ¬ ProlongationTuple.IsInftySide P W), D W) =
      Finsupp.mapDomain P.reduceSnd (D.filter (ProlongationTuple.IsZeroSide P)) u := by
  rw [mapDomain_filter_apply]
  exact Finset.sum_congr (Finset.filter_congr (fun W _ => not_isInftySide_iff (P := P) hqN hinj u hu W))
    (fun _ _ => rfl)

include hqN in
open Classical in

private theorem inftySide_add_zeroSide (hsp : ReducesDivisors P) (hC : NormReduction R)
    (hinj : Function.Injective (frobOnPlacesGeomLevel k N data hKr))
    (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (hr₁ : R.R₁.residue ⟨f, h₁⟩ ≠ 0) (hr₂ : R.R₂.residue ⟨f, h₂⟩ ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hD : ∀ W, D W = W.ord f)
    (u : Place k (modularFunctionFieldC k N))
    (hu : ¬ IsAffineGeomPlace k N (frobOnPlacesGeomLevel k N data hKr u)) :
    Finsupp.mapDomain P.reduceFst (D.filter (ProlongationTuple.IsInftySide P)) (frobOnPlacesGeomLevel k N data hKr u) +
        Finsupp.mapDomain P.reduceSnd (D.filter (ProlongationTuple.IsZeroSide P)) u =
      (frobOnPlacesGeomLevel k N data hKr u).ord (R.residue₁ ⟨f, h₁⟩) + u.ord (R.residue₂ ⟨f, h₂⟩) := by
  have hall := mapDomain_reduceFst_eq_ord_add_ord R hqN hsp hC f h₁ h₂ hr₁ hr₂ D hD u
  rw [mapDomain_apply_eq_sum] at hall
  rw [mapDomain_filter_apply, ← sum_not_isInftySide_eq (P := P) hqN hinj D u hu]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (D.support.filter (fun W => P.reduceFst W = frobOnPlacesGeomLevel k N data hKr u))
    (fun W => ProlongationTuple.IsInftySide P W) (fun W => D W)
  rw [Finset.filter_filter, Finset.filter_filter] at hsplit
  have hside : (∑ W ∈ D.support with (ProlongationTuple.IsInftySide P W ∧
      P.reduceFst W = frobOnPlacesGeomLevel k N data hKr u), D W) =
      ∑ W ∈ D.support with (P.reduceFst W = frobOnPlacesGeomLevel k N data hKr u ∧
        ProlongationTuple.IsInftySide P W), D W := by
    refine Finset.sum_congr (Finset.filter_congr (fun W _ => and_comm)) (fun _ _ => rfl)
  rw [hside, hsplit, hall]

include hqN in
open Classical in

private theorem inftySide_eq_of_nonneg (hsp : ReducesDivisors P) (hC : NormReduction R)
    (hinj : Function.Injective (frobOnPlacesGeomLevel k N data hKr)) (hL : CuspLocalSemicontinuity R)
    (g : modularFunctionFieldBar (N * q)) (h₁ : g ∈ R.R₁.integers) (h₂ : g ∈ R.R₂.integers)
    (hr₁ : R.R₁.residue ⟨g, h₁⟩ ≠ 0) (hr₂ : R.R₂.residue ⟨g, h₂⟩ ≠ 0)
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hE : ∀ W, E W = W.ord g)
    (u : Place k (modularFunctionFieldC k N))
    (hu : ¬ IsAffineGeomPlace k N (frobOnPlacesGeomLevel k N data hKr u))
    (hp₁ : ∀ W, ProlongationTuple.IsInftySide P W → P.reduceFst W = frobOnPlacesGeomLevel k N data hKr u → 0 ≤ E W)
    (hp₂ : ∀ W, ProlongationTuple.IsZeroSide P W → P.reduceSnd W = u → 0 ≤ E W) :
    Finsupp.mapDomain P.reduceFst (E.filter (ProlongationTuple.IsInftySide P)) (frobOnPlacesGeomLevel k N data hKr u) =
      (frobOnPlacesGeomLevel k N data hKr u).ord (R.residue₁ ⟨g, h₁⟩) := by
  have hkey := inftySide_add_zeroSide R hqN hsp hC hinj g h₁ h₂ hr₁ hr₂ E hE u hu

  have hu' : ¬ IsAffineGeomPlace k N u := fun h => hu (isAffineGeomPlace_frobOnPlacesGeomLevel k N data hKr u h)
  obtain ⟨hexists_inf, -⟩ :=
    exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace hqN P
      (frobOnPlacesGeomLevel k N data hKr u) hu
  obtain ⟨-, hexists_zero⟩ :=
    exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace hqN P u hu'
  have hl₁ := hL.1 g h₁ h₂ hr₁ hr₂ E hE (frobOnPlacesGeomLevel k N data hKr u) hexists_inf hp₁
  have hl₂ := hL.2 g h₁ h₂ hr₁ hr₂ E hE u hexists_zero hp₂
  omega

private theorem frobOnPlacesGeomLevel_bijective' :
    Function.Bijective (frobOnPlacesGeomLevel k N data hKr) := by
  have h : frobOnPlacesGeomLevel k N data hKr = fun w => arithFrobC q k N • w :=
    funext (fun w => (arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr w).symm)
  rw [h]
  exact MulAction.bijective _

include hqN in
set_option maxHeartbeats 3200000 in
open Classical in

private theorem cuspLawInfty_of_cuspLocalSemicontinuity (hsp : ReducesDivisors P) (hC : NormReduction R)
    (hL : CuspLocalSemicontinuity R) (hpc : CuspPoleCancellation R) : R.CuspLawInfty := by
  have hb : Function.Bijective (frobOnPlacesGeomLevel k N data hKr) :=
    frobOnPlacesGeomLevel_bijective' (q := q) (N := N) (k := k) (data := data) (hKr := hKr)
  unfold ProlongationTuple.CuspLawInfty
  intro f h₁ h₂ hr₁ hr₂ D hD c hc

  have hv : ¬ IsAffineGeomPlace k N (P.reduceFst c) :=
    ProlongationTuple.not_isAffineGeomPlace_reduceFst_of_isCuspidal P c hc.1
  obtain ⟨u, hu_eq⟩ := hb.2 (P.reduceFst c)
  rw [← hu_eq] at hv ⊢

  obtain ⟨h, hh₁, hh₂, hs₁, hs₂, hph₁, hph₂, hpfh₁, hpfh₂⟩ := hpc f h₁ h₂ hr₁ hr₂ u
  have hf0 : f ≠ 0 := ne_zero_of_residue_ne_zero R h₁ hr₁
  have hh0 : h ≠ 0 := ne_zero_of_residue_ne_zero R hh₁ hs₁
  haveI := isCurveOver_modularFunctionFieldBar (N * q)
  obtain ⟨E, hE, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) h hh0
  have hDE : ∀ W, (D + E) W = W.ord (f * h) := by
    intro W
    rw [Finsupp.add_apply, hD W, hE W, W.ord_mul hf0 hh0]
  have hfh₁ : f * h ∈ R.R₁.integers := mul_mem h₁ hh₁
  have hfh₂ : f * h ∈ R.R₂.integers := mul_mem h₂ hh₂
  have hmul₁ : (⟨f * h, hfh₁⟩ : R.R₁.integers) = ⟨f, h₁⟩ * ⟨h, hh₁⟩ := rfl
  have hmul₂ : (⟨f * h, hfh₂⟩ : R.R₂.integers) = ⟨f, h₂⟩ * ⟨h, hh₂⟩ := rfl
  have hrfh₁ : R.R₁.residue ⟨f * h, hfh₁⟩ ≠ 0 := by
    rw [hmul₁, map_mul]
    exact mul_ne_zero hr₁ hs₁
  have hrfh₂ : R.R₂.residue ⟨f * h, hfh₂⟩ ≠ 0 := by
    rw [hmul₂, map_mul]
    exact mul_ne_zero hr₂ hs₂

  have hres : R.residue₁ ⟨f * h, hfh₁⟩ = R.residue₁ ⟨f, h₁⟩ * R.residue₁ ⟨h, hh₁⟩ := by
    rw [hmul₁, map_mul]
  have hnf : R.residue₁ ⟨f, h₁⟩ ≠ 0 := by
    rw [ProlongationTuple.residue₁_apply]
    exact (map_ne_zero R.ι).mpr hr₁
  have hnh : R.residue₁ ⟨h, hh₁⟩ ≠ 0 := by
    rw [ProlongationTuple.residue₁_apply]
    exact (map_ne_zero R.ι).mpr hs₁

  have hA := inftySide_eq_of_nonneg R hqN hsp hC hb.1 hL (f * h) hfh₁ hfh₂ hrfh₁ hrfh₂ (D + E) hDE u hv
    (fun W hW hWu => by rw [hDE W]; exact hpfh₁ W hW hWu)
    (fun W hW hWu => by rw [hDE W]; exact hpfh₂ W hW hWu)
  have hB := inftySide_eq_of_nonneg R hqN hsp hC hb.1 hL h hh₁ hh₂ hs₁ hs₂ E hE u hv
    (fun W hW hWu => by rw [hE W]; exact hph₁ W hW hWu)
    (fun W hW hWu => by rw [hE W]; exact hph₂ W hW hWu)
  rw [mapDomain_filter_inftySide_add (P := P) D E, hB, hres,
    (frobOnPlacesGeomLevel k N data hKr u).ord_mul hnf hnh] at hA
  omega

private theorem deg_eq_one_levelN (t : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : t.deg = 1 := by
  haveI := isCurveOver_modularFunctionFieldBar N
  haveI := IsCurveOver.finite_residueField t
  refine t.deg_eq_one_of_isAlgClosed ?_
  exact Module.finrank_pos.ne'

open Classical in

private theorem exists_ord_bounds (t₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (T : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))) (M : ℕ) :
    ∃ x : modularFunctionFieldBar N, x ≠ 0 ∧ (∀ t, t ≠ t₀ → 0 ≤ t.ord x) ∧
      ∀ t ∈ T, t ≠ t₀ → (M : ℤ) ≤ t.ord x := by
  obtain ⟨g₀, hg₀⟩ := exists_mem_riemannRochSpace_notMem_sub_single_of_le_degree N
  obtain ⟨E, hE⟩ : ∃ E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      E = Finsupp.single t₀ ((g₀ + M * T.card : ℕ) : ℤ) - ∑ t ∈ T, Finsupp.single t (M : ℤ) := ⟨_, rfl⟩
  have hdeg : (g₀ : ℤ) ≤ Divisor.degree E := by
    rw [hE, map_sub, map_sum]
    simp only [Divisor.degree_single, deg_eq_one_levelN, Finset.sum_const, nsmul_eq_mul]
    push_cast
    linarith
  obtain ⟨x, hxE, hxnot⟩ := hg₀ E hdeg t₀
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hxnot (Submodule.zero_mem _)
  have hord := mem_riemannRochSpace_iff.mp hxE
  have hE_out : ∀ t, t ∉ T → t ≠ t₀ → E t = 0 := by
    intro t htT ht
    rw [hE]
    simp [Finsupp.single_apply, Ne.symm ht, htT]
  have hE_in : ∀ t, t ∈ T → t ≠ t₀ → E t = -(M : ℤ) := by
    intro t htT ht
    rw [hE]
    simp [Finsupp.single_apply, Ne.symm ht, htT]
  refine ⟨x, hx0, ?_, ?_⟩
  · intro t ht
    rcases hord t with h | h
    · exact absurd h hx0
    · by_cases htT : t ∈ T
      · have := hE_in t htT ht
        omega
      · have := hE_out t htT ht
        omega
  · intro t htT ht
    rcases hord t with h | h
    · exact absurd h hx0
    · have := hE_in t htT ht
      omega

omit [Fact q.Prime] [NeZero N] in

private theorem smul_eq_algebraMap_mul (c : AlgebraicClosure ℚ) (y : modularFunctionFieldBar (N * q)) :
    c • y = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) c * y :=
  Algebra.smul_def c y

omit [Fact q.Prime] [NeZero N] in

private theorem ne_zero_of_smul_ne_zero {c : AlgebraicClosure ℚ} {y : modularFunctionFieldBar (N * q)}
    (h : c • y ≠ 0) : c ≠ 0 ∧ y ≠ 0 := by
  rw [smul_eq_algebraMap_mul] at h
  refine ⟨fun hc => h ?_, fun hy => h ?_⟩
  · rw [hc, map_zero, zero_mul]
  · rw [hy, mul_zero]

omit [Fact q.Prime] [NeZero N] in

private theorem ord_smul_of_ne_zero (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    {c : AlgebraicClosure ℚ} (hc : c ≠ 0) {y : modularFunctionFieldBar (N * q)} (hy : y ≠ 0) :
    W.ord (c • y) = W.ord y := by
  have hmap : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) c ≠ 0 := by
    intro h
    apply hc
    exact (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).injective (by rw [h, map_zero])
  rw [smul_eq_algebraMap_mul, W.ord_mul hmap hy, ConstantReduction.ord_algebraMap W hc, zero_add]

include hqN in
set_option maxHeartbeats 3200000 in
open Classical in

private theorem cuspPoleCancellation_of_pullbackBalanced (hB : PullbackBalanced R) (hav : SpAvoids P) :
    CuspPoleCancellation R := by
  unfold CuspPoleCancellation
  intro f h₁ h₂ hr₁ hr₂ u
  have hf0 : f ≠ 0 := ne_zero_of_residue_ne_zero R h₁ hr₁
  haveI := isCurveOver_modularFunctionFieldBar (N * q)
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) f hf0
  obtain ⟨t₀, ht₀⟩ := hav (frobOnPlacesGeomLevel k N data hKr u)
  obtain ⟨S, hS⟩ : ∃ S : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))),
      S = D.support.filter (fun W => P.reduceFst W = frobOnPlacesGeomLevel k N data hKr u) := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
      T = S.image (fun W => W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα) := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = S.sup (fun W => (-D W).toNat) := ⟨_, rfl⟩
  obtain ⟨x, hx0, hx₁, hx₂⟩ := exists_ord_bounds t₀ T M
  obtain ⟨c, hc₁, hc₂, hres₁, hres₂⟩ := hB x hx0
  have h0 := ne_zero_of_residue_ne_zero R hc₁ hres₁
  obtain ⟨hc0, hy0⟩ := ne_zero_of_smul_ne_zero h0

  have key : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)), ∃ e : ℕ, 0 < e ∧
      W.ord (heckeAlphaBar (AlgebraicClosure ℚ) N q x) =
        (e : ℤ) * (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα).ord x := by
    intro W
    letI := algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q)
    haveI := isScalarTower_along (heckeAlphaBar (AlgebraicClosure ℚ) N q)
    haveI := isIntegral_along (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα
    refine ⟨W.ramificationIndex (modularFunctionFieldBar N),
      W.ramificationIndex_pos (F := modularFunctionFieldBar N), ?_⟩
    exact W.ord_restrict (F := modularFunctionFieldBar N) x

  have hnot : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      P.reduceFst W = frobOnPlacesGeomLevel k N data hKr u →
        W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα ≠ t₀ := by
    intro W hW h
    apply ht₀
    rw [← h]
    exact hW

  have hfree : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      P.reduceFst W = frobOnPlacesGeomLevel k N data hKr u →
        0 ≤ W.ord (heckeAlphaBar (AlgebraicClosure ℚ) N q x) := by
    intro W hW
    obtain ⟨e, he, heq⟩ := key W
    rw [heq]
    exact mul_nonneg (by omega) (hx₁ _ (hnot W hW))
  have hcancel : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      P.reduceFst W = frobOnPlacesGeomLevel k N data hKr u →
        0 ≤ W.ord f + W.ord (heckeAlphaBar (AlgebraicClosure ℚ) N q x) := by
    intro W hW
    have hWt₀ := hnot W hW
    obtain ⟨e, he, heq⟩ := key W
    have hordf : W.ord f = D W := (hD W).symm
    have hxnn : 0 ≤ (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα).ord x := hx₁ _ hWt₀
    have hex : (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα).ord x ≤
        (e : ℤ) * (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα).ord x :=
      le_mul_of_one_le_left hxnn (by omega)
    rw [heq]
    by_cases hpole : D W < 0
    · have hWS : W ∈ S := by
        rw [hS]
        exact Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr (by omega), hW⟩
      have hWT : W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα ∈ T := by
        rw [hT]
        exact Finset.mem_image_of_mem _ hWS
      have hMW : (-D W).toNat ≤ M := by
        rw [hM]
        exact Finset.le_sup (f := fun W => (-D W).toNat) hWS
      have hxW := hx₂ _ hWT hWt₀
      omega
    · have := mul_nonneg (by omega : (0 : ℤ) ≤ e) hxnn
      omega
  refine ⟨_, hc₁, hc₂, hres₁, hres₂, ?_, ?_, ?_, ?_⟩
  · intro W _ hW
    rw [ord_smul_of_ne_zero W hc0 hy0]
    exact hfree W hW
  · intro W hWs hWu
    rw [ord_smul_of_ne_zero W hc0 hy0]
    exact hfree W (reduceFst_eq_of_isZeroSide (P := P) hqN hWs hWu)
  · intro W _ hW
    rw [W.ord_mul hf0 h0, ord_smul_of_ne_zero W hc0 hy0]
    exact hcancel W hW
  · intro W hWs hWu
    rw [W.ord_mul hf0 h0, ord_smul_of_ne_zero W hc0 hy0]
    exact hcancel W (reduceFst_eq_of_isZeroSide (P := P) hqN hWs hWu)

include hqN in
set_option maxHeartbeats 3200000 in

private theorem cuspLawInfty_of_cuspLocalSemicontinuity_of_pullbackBalanced (hsp : ReducesDivisors P)
    (hC : NormReduction R) (hL : CuspLocalSemicontinuity R) (hB : PullbackBalanced R) (hav : SpAvoids P) :
    R.CuspLawInfty :=
  cuspLawInfty_of_cuspLocalSemicontinuity R hqN hsp hC hL (cuspPoleCancellation_of_pullbackBalanced R hqN hB hav)

end ModularCurve.PlaceSpecialization

end NR3_20_normroad

section NR3_25_penT

p2m_open "AlgebraicCurve ModularCurve~jBar P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve ModularCurve.PlaceSpecialization~IsInftySide~jFun~tInfty~tZero~IsCuspidal~IsZeroSide P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve.PlaceSpecialization"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_qExpand jNum jNumQ jq ofPowerSeries_coeff_of_neg coeff_jq_neg_one jqN evalAtJ evalAtJ_X ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffMap_algebraMap coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_eq_map_intCast modularFunctionFieldC jqModC_mem jqNModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff KroneckerCongruence ssPlaces jGeomGen jNGeomGen IsAffineGeomPlace cuspInftyGeom ord_cuspInftyGeom_jq order_jqModC_def jqModC_ne_zero_def jq_mem_full coeff_jqModC_neg_one coeffSemilinearAut.coeffMap_qExpand coeffSemilinearAut.coeffMap_jqModC coeffSemilinearAut.coeffMap_mem_modularFunctionFieldC coeffSemilinearAut arithFrobC isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_jqModC qExpandAlgHomC qExpandAlgHomC_apply divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full jqModC_mem_full coeffMap_qExpand CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.mem_localizedAtKer CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc CharPReduction.redRes_ne_zero_of_notMem CharPReduction.redLoc_spec CharPReduction.redLoc_coe CharPReduction.redLocHom_apply CharPReduction.constSeries CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.affineBaseFin CharPModel.affineBaseInf CharPModel.FibreModel modularFunctionFieldBar_eq_modularFunctionFieldC finiteAlong_heckeAlphaBar_of_prime isCurveOver_modularFunctionFieldBar arithFrobC_smul_eq_frobOnPlacesGeomLevel CharPReduction.modularRedLocHom_mem exists_mem_riemannRochSpace_notMem_sub_single_of_le_degree isAffineGeomPlace_frobOnPlacesGeomLevel coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized_mul_of_not_dvd coeffEmb_jq exists_isAtkinLehnerAutFull_of_prime_of_not_dvd exists_regularProlongation_modularFunctionFieldBar_mul_of_not_dvd geomAut_atkinLehner_comp_legs hasPrincipalDivisors_modularFunctionFieldBar_unconditional place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin finrankAlong_heckeBetaBar CharPModel.FibreModel.piFin_range_localizes_of_jqModC_mem CharPModel.exists_monic_eval2_affineBaseFin_eq_zero_of_mem_modularLocalized_of_forall_mem_of_jBar_mem arithFrobC_smul_mem_ssPlaces_univ adjoin_jBar_jNBar_eq_top nonempty_modularPolynomialData relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi CharPReduction.mem_or_inv_mem_modularLocalized pow_char_eq_coeffMap_frobenius_qExpand qExpand_jqModC_eq_pow_unconditional mem_integralCoeffs_of_integral_affineBaseInf CharPModel.exists_monic_eval2_affineBaseInf_eq_zero_of_mem_modularLocalized_of_forall_inv_jBar_mem"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.atkinLehnerBar ProlongationTuple.jFun ProlongationTuple.jQFun ProlongationTuple.tInfty ProlongationTuple.tZero ProlongationTuple.IsCuspidal ProlongationTuple.IsInftySide ProlongationTuple.IsZeroSide ProlongationTuple ProlongationTuple.residue₁_apply ProlongationTuple.residue₂_apply ProlongationTuple.OrderLawFixed ProlongationTuple.CuspLawInfty reduceFst reduceSnd IsStrictFst IsStrictSnd sp d0_j_pole d1 ReducesDivisors fibreReduction chartClosure chartLocalSetFst ChartEtaleAt IsChartAt HasCoordinates ProlongationTuple.isCuspidal_of_not_isAffineGeomPlace_reduceFst ProlongationTuple.not_isAffineGeomPlace_reduceFst_of_isCuspidal ProlongationTuple.isInftySide_or_isZeroSide_of_isCuspidal ProlongationTuple.not_isInftySide_of_isZeroSide ProlongationTuple.reduceFst_eq_frobOnPlacesGeomLevel_reduceSnd_of_isZeroSide exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace ProlongationTuple.isInftySide_atkinLehnerBar_smul_iff reduceFst_atkinLehnerBar_smul mem_chartLocalSetFst_of_split hasCoordinates_of_sp_eq_spPlace"
p2m_open "ModularCurve.PlaceSpecialization~IsInftySide~jFun~tInfty~tZero~IsCuspidal~IsZeroSide ModularCurve~jBar"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

variable {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P) (hqN : ¬ q ∣ N)

end ModularCurve.PlaceSpecialization

section

p2m_open "AlgebraicCurve ModularCurve~jBar P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve ModularCurve.CharPReduction"

private noncomputable def gaussReg_pack {A : ValuationSubring (AlgebraicClosure ℚ)}
    (x : LaurentSeries (AlgebraicClosure ℚ)) (hx : x ∈ integralCoeffs A.toSubring) :
    LaurentSeries A where
  coeff n := ⟨x.coeff n, hx n⟩
  isPWO_support' := x.isPWO_support.mono (fun _ hn h => hn (Subtype.ext h))

private theorem gaussReg_coeffMap_pack {A : ValuationSubring (AlgebraicClosure ℚ)}
    (x : LaurentSeries (AlgebraicClosure ℚ)) (hx : x ∈ integralCoeffs A.toSubring) :
    coeffMap A.subtype (gaussReg_pack x hx) = x := by
  ext n
  rfl

private theorem gaussReg_coeffMap_subtype_injective (A : ValuationSubring (AlgebraicClosure ℚ)) :
    Function.Injective (coeffMap A.subtype : LaurentSeries A → LaurentSeries (AlgebraicClosure ℚ)) := by
  intro x y h
  ext n
  have hn := congrArg (fun z : LaurentSeries (AlgebraicClosure ℚ) => z.coeff n) h
  simp only [coeffMap_coeff] at hn
  exact hn

private theorem gaussReg_redRes_eq {M : ℕ} [NeZero M] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k) (r : modularRing M A.toSubring) :
    redRes A.toSubring red (modularRing M A.toSubring) (modularRing_le_integralCoeffs M A.toSubring) r =
      coeffMap red (gaussReg_pack (r : LaurentSeries (AlgebraicClosure ℚ))
        (modularRing_le_integralCoeffs M A.toSubring r.2)) := by
  ext n
  rfl

private theorem gaussReg_coeffMap_red_ne_zero {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]
    (red : A →+* k) (y : LaurentSeries A) (hy : coeffMap (IsLocalRing.residue A) y ≠ 0) :
    coeffMap red y ≠ 0 := by
  intro h0
  apply hy
  ext n
  have hn : red (y.coeff n) = 0 := by
    have h := congrArg (fun z : LaurentSeries k => z.coeff n) h0
    simpa using h
  have hmem : y.coeff n ∈ IsLocalRing.maximalIdeal A :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top red) (RingHom.mem_ker.mpr hn)
  simpa using (IsLocalRing.residue_eq_zero_iff (y.coeff n)).mpr hmem

private theorem gaussReg_liesOverPrime {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) : A.LiesOverPrime q := by
  have hq0 : red (q : A) = 0 := by
    rw [map_natCast]
    exact CharP.cast_eq_zero k q
  show ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits
  rw [ValuationSubring.mem_nonunits_iff]
  rcases A.valuation_lt_one_or_eq_one (q : A) with h | h
  · simpa using h
  · exfalso
    have hu : IsUnit (q : A) := (A.valuation_eq_one_iff (q : A)).mpr h
    have hu' := hu.map red
    rw [hq0] at hu'
    exact not_isUnit_zero hu'

private theorem gaussReg_core {M : ℕ} [NeZero M] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k)
    {u v : LaurentSeries (AlgebraicClosure ℚ)} (huv : u * v = 1)
    {r s : modularRing M A.toSubring}
    (hus : u * (s : LaurentSeries (AlgebraicClosure ℚ)) = r)
    (hs : s ∉ redKer A.toSubring red (modularRing M A.toSubring)
      (modularRing_le_integralCoeffs M A.toSubring))
    (hr : redRes A.toSubring red (modularRing M A.toSubring)
      (modularRing_le_integralCoeffs M A.toSubring) r = 0)
    {x y : LaurentSeries A} (hy : coeffMap (IsLocalRing.residue A) y ≠ 0)
    (hvy : v * coeffMap A.subtype y = coeffMap A.subtype x) : False := by
  have hsne := redRes_ne_zero_of_notMem hs
  rw [gaussReg_redRes_eq] at hsne hr
  have hid : (s : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y =
      (r : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype x := by
    linear_combination (coeffMap A.subtype x) * hus + (u * (s : LaurentSeries (AlgebraicClosure ℚ))) * hvy
      - ((s : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y) * huv
  have hidA : gaussReg_pack (s : LaurentSeries (AlgebraicClosure ℚ))
        (modularRing_le_integralCoeffs M A.toSubring s.2) * y =
      gaussReg_pack (r : LaurentSeries (AlgebraicClosure ℚ))
        (modularRing_le_integralCoeffs M A.toSubring r.2) * x := by
    apply gaussReg_coeffMap_subtype_injective A
    rw [map_mul, map_mul, gaussReg_coeffMap_pack, gaussReg_coeffMap_pack]
    exact hid
  have hred := congrArg (coeffMap red) hidA
  rw [map_mul, map_mul, hr, zero_mul] at hred
  exact mul_ne_zero hsne (gaussReg_coeffMap_red_ne_zero red y hy) hred

private theorem gaussReg_norm {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F]
    [Algebra L F] {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar) (f : F) (hf : f ≠ 0)
    {P : F → Prop} (hP : ∀ g : F, g ∈ R.integers → P g) :
    ∃ c : L, c ≠ 0 ∧ ∃ g : F, g = c • f ∧ g * g⁻¹ = 1 ∧ P g ∧ P g⁻¹ := by
  obtain ⟨c, hcf, hres⟩ := R.exists_smul_mem f hf
  have hc : c ≠ 0 := R.smul_const_ne_zero hcf hres
  refine ⟨c, hc, c • f, rfl, mul_inv_cancel₀ (smul_ne_zero hc hf), hP _ hcf, hP _ ?_⟩
  obtain ⟨w, hw⟩ := (R.isUnit_of_residue_ne_zero hres).exists_right_inv
  have h1 : c • f * (w : F) = 1 := congrArg Subtype.val hw
  rw [← eq_inv_of_mul_eq_one_right h1]
  exact w.2

private theorem gaussReg_coe_mul_inv {M : ℕ} (g : ↥(modularFunctionFieldBar M)) (h : g * g⁻¹ = 1) :
    (g : LaurentSeries (AlgebraicClosure ℚ)) *
      ((g⁻¹ : ↥(modularFunctionFieldBar M)) : LaurentSeries (AlgebraicClosure ℚ)) = 1 := by
  exact_mod_cast h

private theorem gaussReg_ne_zero_of_mem {M : ℕ} [NeZero M] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k) {g ginv : LaurentSeries (AlgebraicClosure ℚ)} (hmul : g * ginv = 1)
    (h₁ : g ∈ modularLocalized M A.toSubring red)
    {x y : LaurentSeries A} (hy : coeffMap (IsLocalRing.residue A) y ≠ 0)
    (hvy : ginv * coeffMap A.subtype y = coeffMap A.subtype x) :
    modularRedLocHom M A.toSubring red ⟨g, h₁⟩ ≠ 0 := by
  intro hπ
  obtain ⟨r, s, hs, hgs⟩ := id h₁
  have hspec := redLoc_spec (⟨g, h₁⟩ : modularLocalized M A.toSubring red) hgs
  have hπ' : redLoc (⟨g, h₁⟩ : modularLocalized M A.toSubring red) = 0 := hπ
  rw [hπ', zero_mul] at hspec
  exact gaussReg_core red hmul hgs hs hspec.symm hy hvy

private theorem gaussReg_exists_of_inv_mem {M : ℕ} [NeZero M] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k) {g ginv : LaurentSeries (AlgebraicClosure ℚ)} (hmul : g * ginv = 1)
    (h₂ : ginv ∈ modularLocalized M A.toSubring red)
    {x y : LaurentSeries A} (hy : coeffMap (IsLocalRing.residue A) y ≠ 0)
    (hvy : g * coeffMap A.subtype y = coeffMap A.subtype x) :
    ∃ h₁ : g ∈ modularLocalized M A.toSubring red, modularRedLocHom M A.toSubring red ⟨g, h₁⟩ ≠ 0 := by
  obtain ⟨r, s, hs, hgs⟩ := h₂
  have hmul' : ginv * g = 1 := by rw [mul_comm]; exact hmul
  by_cases hr : r ∈ redKer A.toSubring red (modularRing M A.toSubring)
      (modularRing_le_integralCoeffs M A.toSubring)
  · exact (gaussReg_core red hmul' hgs hs (RingHom.mem_ker.mp hr) hy hvy).elim
  · have hgr : g * (r : LaurentSeries (AlgebraicClosure ℚ)) = s := by
      linear_combination (-g) * hgs + (s : LaurentSeries (AlgebraicClosure ℚ)) * hmul
    have h₁ : g ∈ modularLocalized M A.toSubring red :=
      (mem_localizedAtKer A.toSubring red (modularRing M A.toSubring)
        (modularRing_le_integralCoeffs M A.toSubring)).mpr ⟨s, r, hr, hgr⟩
    refine ⟨h₁, fun hπ => ?_⟩
    have hspec := redLoc_spec (⟨g, h₁⟩ : modularLocalized M A.toSubring red) hgr
    have hπ' : redLoc (⟨g, h₁⟩ : modularLocalized M A.toSubring red) = 0 := hπ
    rw [hπ', zero_mul] at hspec
    exact redRes_ne_zero_of_notMem hs hspec.symm

private theorem gaussReg_of_normalised {M : ℕ} [NeZero M] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k)
    (hval : ∀ g : modularFunctionFieldBar M,
      (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularLocalized M A.toSubring red ∨
        ((g⁻¹ : modularFunctionFieldBar M) : LaurentSeries (AlgebraicClosure ℚ))
          ∈ modularLocalized M A.toSubring red)
    (g : ↥(modularFunctionFieldBar M)) (hgg : g * g⁻¹ = 1)
    {x₁ y₁ x₂ y₂ : LaurentSeries A}
    (hy₁ : coeffMap (IsLocalRing.residue A) y₁ ≠ 0)
    (hvy₁ : (g : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y₁ = coeffMap A.subtype x₁)
    (hy₂ : coeffMap (IsLocalRing.residue A) y₂ ≠ 0)
    (hvy₂ : ((g⁻¹ : ↥(modularFunctionFieldBar M)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y₂ =
      coeffMap A.subtype x₂) :
    ∃ h₁ : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularLocalized M A.toSubring red,
      modularRedLocHom M A.toSubring red ⟨_, h₁⟩ ≠ 0 := by
  have hmul := gaussReg_coe_mul_inv g hgg
  rcases hval g with h₁ | h₂
  · exact ⟨h₁, gaussReg_ne_zero_of_mem red hmul h₁ hy₂ hvy₂⟩
  · exact gaussReg_exists_of_inv_mem red hmul h₂ hy₁ hvy₁

private theorem gaussReg_exists_smul_mem_ne_zero {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N)
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (hval : ∀ g : modularFunctionFieldBar (N * q),
      (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularLocalized (N * q) A.toSubring red ∨
        ((g⁻¹ : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
          ∈ modularLocalized (N * q) A.toSubring red)
    (f : modularFunctionFieldBar (N * q)) (hf : f ≠ 0) :
    ∃ (c : AlgebraicClosure ℚ) (_ : c ≠ 0)
      (h₁ : ((c • f : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
        modularLocalized (N * q) A.toSubring red),
      modularRedLocHom (N * q) A.toSubring red ⟨_, h₁⟩ ≠ 0 := by
  obtain ⟨R, hR₁, -⟩ :=
    ModularCurve.exists_regularProlongation_modularFunctionFieldBar_mul_of_not_dvd N q hqN A
      (gaussReg_liesOverPrime red)
  obtain ⟨c, hc, g, hg, hgg, ⟨x₁, y₁, hy₁, hvy₁⟩, ⟨x₂, y₂, hy₂, hvy₂⟩⟩ :=
    gaussReg_norm R f hf (fun g hg => (hR₁ g).mp hg)
  subst hg
  exact ⟨c, hc, gaussReg_of_normalised red hval _ hgg hy₁ hvy₁ hy₂ hvy₂⟩

end

section

p2m_open "AlgebraicCurve ModularCurve~jBar P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve ModularCurve.PlaceSpecialization~IsInftySide~jFun~tInfty~tZero~IsCuspidal~IsZeroSide P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve.PlaceSpecialization"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_qExpand jNum jNumQ jq ofPowerSeries_coeff_of_neg coeff_jq_neg_one jqN evalAtJ evalAtJ_X ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffMap_algebraMap coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_eq_map_intCast modularFunctionFieldC jqModC_mem jqNModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff KroneckerCongruence ssPlaces jGeomGen jNGeomGen IsAffineGeomPlace cuspInftyGeom ord_cuspInftyGeom_jq order_jqModC_def jqModC_ne_zero_def jq_mem_full coeff_jqModC_neg_one coeffSemilinearAut.coeffMap_qExpand coeffSemilinearAut.coeffMap_jqModC coeffSemilinearAut.coeffMap_mem_modularFunctionFieldC coeffSemilinearAut arithFrobC isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_jqModC qExpandAlgHomC qExpandAlgHomC_apply divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full jqModC_mem_full coeffMap_qExpand CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.mem_localizedAtKer CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc CharPReduction.redRes_ne_zero_of_notMem CharPReduction.redLoc_spec CharPReduction.redLoc_coe CharPReduction.redLocHom_apply CharPReduction.constSeries CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.affineBaseFin CharPModel.affineBaseInf CharPModel.FibreModel modularFunctionFieldBar_eq_modularFunctionFieldC finiteAlong_heckeAlphaBar_of_prime isCurveOver_modularFunctionFieldBar arithFrobC_smul_eq_frobOnPlacesGeomLevel CharPReduction.modularRedLocHom_mem exists_mem_riemannRochSpace_notMem_sub_single_of_le_degree isAffineGeomPlace_frobOnPlacesGeomLevel coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized_mul_of_not_dvd coeffEmb_jq exists_isAtkinLehnerAutFull_of_prime_of_not_dvd exists_regularProlongation_modularFunctionFieldBar_mul_of_not_dvd geomAut_atkinLehner_comp_legs hasPrincipalDivisors_modularFunctionFieldBar_unconditional place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin finrankAlong_heckeBetaBar CharPModel.FibreModel.piFin_range_localizes_of_jqModC_mem CharPModel.exists_monic_eval2_affineBaseFin_eq_zero_of_mem_modularLocalized_of_forall_mem_of_jBar_mem arithFrobC_smul_mem_ssPlaces_univ adjoin_jBar_jNBar_eq_top nonempty_modularPolynomialData relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi CharPReduction.mem_or_inv_mem_modularLocalized pow_char_eq_coeffMap_frobenius_qExpand qExpand_jqModC_eq_pow_unconditional mem_integralCoeffs_of_integral_affineBaseInf CharPModel.exists_monic_eval2_affineBaseInf_eq_zero_of_mem_modularLocalized_of_forall_inv_jBar_mem"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.atkinLehnerBar ProlongationTuple.jFun ProlongationTuple.jQFun ProlongationTuple.tInfty ProlongationTuple.tZero ProlongationTuple.IsCuspidal ProlongationTuple.IsInftySide ProlongationTuple.IsZeroSide ProlongationTuple ProlongationTuple.residue₁_apply ProlongationTuple.residue₂_apply ProlongationTuple.OrderLawFixed ProlongationTuple.CuspLawInfty reduceFst reduceSnd IsStrictFst IsStrictSnd sp d0_j_pole d1 ReducesDivisors fibreReduction chartClosure chartLocalSetFst ChartEtaleAt IsChartAt HasCoordinates ProlongationTuple.isCuspidal_of_not_isAffineGeomPlace_reduceFst ProlongationTuple.not_isAffineGeomPlace_reduceFst_of_isCuspidal ProlongationTuple.isInftySide_or_isZeroSide_of_isCuspidal ProlongationTuple.not_isInftySide_of_isZeroSide ProlongationTuple.reduceFst_eq_frobOnPlacesGeomLevel_reduceSnd_of_isZeroSide exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace ProlongationTuple.isInftySide_atkinLehnerBar_smul_iff reduceFst_atkinLehnerBar_smul mem_chartLocalSetFst_of_split hasCoordinates_of_sp_eq_spPlace"
p2m_open "ModularCurve.PlaceSpecialization~IsInftySide~jFun~tInfty~tZero~IsCuspidal~IsZeroSide ModularCurve~jBar"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

variable {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

end ModularCurve.PlaceSpecialization

end

section LeafPC

section LeafPCtransport

p2m_open "AlgebraicCurve ModularCurve~jBar P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve ModularCurve.CharPReduction ModularCurve.PlaceSpecialization~IsInftySide~jFun~tInfty~tZero~IsCuspidal~IsZeroSide P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve.PlaceSpecialization"

private theorem coeffMap_residue_ne_zero_of_coeffMap_red_ne_zero {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (y : LaurentSeries A) (hy : coeffMap red y ≠ 0) : coeffMap (IsLocalRing.residue A) y ≠ 0 := by
  intro h0
  apply hy
  ext n
  have hn : IsLocalRing.residue A (y.coeff n) = 0 := by
    have h := congrArg (fun z : LaurentSeries (IsLocalRing.ResidueField A) => z.coeff n) h0
    simpa using h
  have hred := ValuationSubring.ringHom_apply_eq_zero_of_mem_maximalIdeal A q red
    ((IsLocalRing.residue_eq_zero_iff (y.coeff n)).mp hn)
  simpa using hred

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_qExpand jNum jNumQ jq ofPowerSeries_coeff_of_neg coeff_jq_neg_one jqN evalAtJ evalAtJ_X ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffMap_algebraMap coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_eq_map_intCast modularFunctionFieldC jqModC_mem jqNModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff KroneckerCongruence ssPlaces jGeomGen jNGeomGen IsAffineGeomPlace cuspInftyGeom ord_cuspInftyGeom_jq order_jqModC_def jqModC_ne_zero_def jq_mem_full coeff_jqModC_neg_one coeffSemilinearAut.coeffMap_qExpand coeffSemilinearAut.coeffMap_jqModC coeffSemilinearAut.coeffMap_mem_modularFunctionFieldC coeffSemilinearAut arithFrobC isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_jqModC qExpandAlgHomC qExpandAlgHomC_apply divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full jqModC_mem_full coeffMap_qExpand CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.mem_localizedAtKer CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc CharPReduction.redRes_ne_zero_of_notMem CharPReduction.redLoc_spec CharPReduction.redLoc_coe CharPReduction.redLocHom_apply CharPReduction.constSeries CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.affineBaseFin CharPModel.affineBaseInf CharPModel.FibreModel modularFunctionFieldBar_eq_modularFunctionFieldC finiteAlong_heckeAlphaBar_of_prime isCurveOver_modularFunctionFieldBar arithFrobC_smul_eq_frobOnPlacesGeomLevel CharPReduction.modularRedLocHom_mem exists_mem_riemannRochSpace_notMem_sub_single_of_le_degree isAffineGeomPlace_frobOnPlacesGeomLevel coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized_mul_of_not_dvd coeffEmb_jq exists_isAtkinLehnerAutFull_of_prime_of_not_dvd exists_regularProlongation_modularFunctionFieldBar_mul_of_not_dvd geomAut_atkinLehner_comp_legs hasPrincipalDivisors_modularFunctionFieldBar_unconditional place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin finrankAlong_heckeBetaBar CharPModel.FibreModel.piFin_range_localizes_of_jqModC_mem CharPModel.exists_monic_eval2_affineBaseFin_eq_zero_of_mem_modularLocalized_of_forall_mem_of_jBar_mem arithFrobC_smul_mem_ssPlaces_univ adjoin_jBar_jNBar_eq_top nonempty_modularPolynomialData relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi CharPReduction.mem_or_inv_mem_modularLocalized pow_char_eq_coeffMap_frobenius_qExpand qExpand_jqModC_eq_pow_unconditional mem_integralCoeffs_of_integral_affineBaseInf CharPModel.exists_monic_eval2_affineBaseInf_eq_zero_of_mem_modularLocalized_of_forall_inv_jBar_mem"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.atkinLehnerBar ProlongationTuple.jFun ProlongationTuple.jQFun ProlongationTuple.tInfty ProlongationTuple.tZero ProlongationTuple.IsCuspidal ProlongationTuple.IsInftySide ProlongationTuple.IsZeroSide ProlongationTuple ProlongationTuple.residue₁_apply ProlongationTuple.residue₂_apply ProlongationTuple.OrderLawFixed ProlongationTuple.CuspLawInfty reduceFst reduceSnd IsStrictFst IsStrictSnd sp d0_j_pole d1 ReducesDivisors fibreReduction chartClosure chartLocalSetFst ChartEtaleAt IsChartAt HasCoordinates ProlongationTuple.isCuspidal_of_not_isAffineGeomPlace_reduceFst ProlongationTuple.not_isAffineGeomPlace_reduceFst_of_isCuspidal ProlongationTuple.isInftySide_or_isZeroSide_of_isCuspidal ProlongationTuple.not_isInftySide_of_isZeroSide ProlongationTuple.reduceFst_eq_frobOnPlacesGeomLevel_reduceSnd_of_isZeroSide exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace ProlongationTuple.isInftySide_atkinLehnerBar_smul_iff reduceFst_atkinLehnerBar_smul mem_chartLocalSetFst_of_split hasCoordinates_of_sp_eq_spPlace"
p2m_open "ModularCurve.PlaceSpecialization~IsInftySide~jFun~tInfty~tZero~IsCuspidal~IsZeroSide ModularCurve~jBar"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}

private theorem heckeBetaBar_mem_modularLocalized_of_heckeAlphaBar (hqN : ¬ q ∣ N)
    (z : modularFunctionFieldBar N)
    (h : ((heckeAlphaBar (AlgebraicClosure ℚ) N q z : modularFunctionFieldBar (N * q)) :
        LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (N * q) A.toSubring red)
    (hπ : CharPReduction.modularRedLocHom (N * q) A.toSubring red ⟨_, h⟩ ≠ 0) :
    ∃ h' : ((heckeBetaBar (AlgebraicClosure ℚ) N q z : modularFunctionFieldBar (N * q)) :
        LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (N * q) A.toSubring red,
      CharPReduction.modularRedLocHom (N * q) A.toSubring red ⟨_, h'⟩ ≠ 0 := by
  obtain ⟨r, s, hs, hFs⟩ := id h

  have hspec := redLoc_spec (⟨_, h⟩ : CharPReduction.modularLocalized (N * q) A.toSubring red) hFs
  have hπ' : redLoc (⟨_, h⟩ : CharPReduction.modularLocalized (N * q) A.toSubring red) ≠ 0 := hπ
  have hsne := redRes_ne_zero_of_notMem hs
  have hrne : redRes A.toSubring red (modularRing (N * q) A.toSubring)
      (modularRing_le_integralCoeffs (N * q) A.toSubring) r ≠ 0 := by
    rw [← hspec]
    exact mul_ne_zero hπ' hsne

  have hS : coeffMap (IsLocalRing.residue A) (gaussReg_pack (s : LaurentSeries (AlgebraicClosure ℚ))
      (modularRing_le_integralCoeffs (N * q) A.toSubring s.2)) ≠ 0 :=
    coeffMap_residue_ne_zero_of_coeffMap_red_ne_zero red _ (by rw [← gaussReg_redRes_eq]; exact hsne)
  have hT : coeffMap (IsLocalRing.residue A) (gaussReg_pack (r : LaurentSeries (AlgebraicClosure ℚ))
      (modularRing_le_integralCoeffs (N * q) A.toSubring r.2)) ≠ 0 :=
    coeffMap_residue_ne_zero_of_coeffMap_red_ne_zero red _ (by rw [← gaussReg_redRes_eq]; exact hrne)
  have hS' : coeffMap (IsLocalRing.residue A) (qExpand A q (gaussReg_pack
      (s : LaurentSeries (AlgebraicClosure ℚ)) (modularRing_le_integralCoeffs (N * q) A.toSubring s.2))) ≠ 0 := by
    rw [coeffSemilinearAut.coeffMap_qExpand]
    exact fun h0 => hS ((map_eq_zero_iff _ (qExpand_injective (R := IsLocalRing.ResidueField A) q)).mp h0)
  have hT' : coeffMap (IsLocalRing.residue A) (qExpand A q (gaussReg_pack
      (r : LaurentSeries (AlgebraicClosure ℚ)) (modularRing_le_integralCoeffs (N * q) A.toSubring r.2))) ≠ 0 := by
    rw [coeffSemilinearAut.coeffMap_qExpand]
    exact fun h0 => hT ((map_eq_zero_iff _ (qExpand_injective (R := IsLocalRing.ResidueField A) q)).mp h0)

  have hG : ((heckeBetaBar (AlgebraicClosure ℚ) N q z : modularFunctionFieldBar (N * q)) :
      LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) q
        ((heckeAlphaBar (AlgebraicClosure ℚ) N q z : modularFunctionFieldBar (N * q)) :
          LaurentSeries (AlgebraicClosure ℚ)) := by
    rw [coe_heckeBetaBar, coe_heckeAlphaBar]
  have hF0 : ((heckeAlphaBar (AlgebraicClosure ℚ) N q z : modularFunctionFieldBar (N * q)) :
      LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := by
    intro h0
    apply hrne
    have hr0 : (r : LaurentSeries (AlgebraicClosure ℚ)) = 0 := by rw [← hFs, h0, zero_mul]
    rw [show r = 0 from Subtype.ext hr0, map_zero]
  have hg0 : heckeBetaBar (AlgebraicClosure ℚ) N q z ≠ 0 := by
    intro h0
    apply hF0
    have h1 := hG
    rw [h0, ZeroMemClass.coe_zero] at h1
    exact (map_eq_zero_iff _ (qExpand_injective (R := AlgebraicClosure ℚ) q)).mp h1.symm

  have hvy₁ : ((heckeBetaBar (AlgebraicClosure ℚ) N q z : modularFunctionFieldBar (N * q)) :
      LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype (qExpand A q (gaussReg_pack
        (s : LaurentSeries (AlgebraicClosure ℚ)) (modularRing_le_integralCoeffs (N * q) A.toSubring s.2))) =
      coeffMap A.subtype (qExpand A q (gaussReg_pack (r : LaurentSeries (AlgebraicClosure ℚ))
        (modularRing_le_integralCoeffs (N * q) A.toSubring r.2))) := by
    rw [coeffSemilinearAut.coeffMap_qExpand, coeffSemilinearAut.coeffMap_qExpand, gaussReg_coeffMap_pack,
      gaussReg_coeffMap_pack, hG, ← map_mul, hFs]
  have hvy₂ : (((heckeBetaBar (AlgebraicClosure ℚ) N q z)⁻¹ : modularFunctionFieldBar (N * q)) :
      LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype (qExpand A q (gaussReg_pack
        (r : LaurentSeries (AlgebraicClosure ℚ)) (modularRing_le_integralCoeffs (N * q) A.toSubring r.2))) =
      coeffMap A.subtype (qExpand A q (gaussReg_pack (s : LaurentSeries (AlgebraicClosure ℚ))
        (modularRing_le_integralCoeffs (N * q) A.toSubring s.2))) := by
    have hmul := gaussReg_coe_mul_inv (M := N * q) (heckeBetaBar (AlgebraicClosure ℚ) N q z) (mul_inv_cancel₀ hg0)
    rw [← hvy₁]
    linear_combination (coeffMap A.subtype (qExpand A q (gaussReg_pack
      (s : LaurentSeries (AlgebraicClosure ℚ)) (modularRing_le_integralCoeffs (N * q) A.toSubring s.2)))) * hmul
  exact gaussReg_of_normalised (M := N * q) red
    (coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized_mul_of_not_dvd hqN red)
    (heckeBetaBar (AlgebraicClosure ℚ) N q z) (mul_inv_cancel₀ hg0) hS' hvy₁ hT' hvy₂

private theorem atkinLehnerBar_heckeAlphaBar (hqN : ¬ q ∣ N) (x : modularFunctionFieldBar N) :
    ProlongationTuple.atkinLehnerBar N q (heckeAlphaBar (AlgebraicClosure ℚ) N q x) =
      heckeBetaBar (AlgebraicClosure ℚ) N q x :=
  AlgHom.congr_fun (geomAut_atkinLehner_comp_legs (AlgebraicClosure ℚ) N q _
    (isAtkinLehnerAutFull_atkinLehnerInvolutionFull N q
      (exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q Fact.out hqN))).1 x

private theorem transportContent (hqN : ¬ q ∣ N) (x : modularFunctionFieldBar N) (c : AlgebraicClosure ℚ)
    (h : ((c • heckeAlphaBar (AlgebraicClosure ℚ) N q x : modularFunctionFieldBar (N * q)) :
        LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (N * q) A.toSubring red)
    (hπ : CharPReduction.modularRedLocHom (N * q) A.toSubring red ⟨_, h⟩ ≠ 0) :
    ∃ h' : ((ProlongationTuple.atkinLehnerBar N q (c • heckeAlphaBar (AlgebraicClosure ℚ) N q x) :
        modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
          CharPReduction.modularLocalized (N * q) A.toSubring red,
      CharPReduction.modularRedLocHom (N * q) A.toSubring red ⟨_, h'⟩ ≠ 0 := by
  have e₁ : c • heckeAlphaBar (AlgebraicClosure ℚ) N q x = heckeAlphaBar (AlgebraicClosure ℚ) N q (c • x) :=
    ((heckeAlphaBar (AlgebraicClosure ℚ) N q).toLinearMap.map_smul c x).symm
  have e₂ : ProlongationTuple.atkinLehnerBar N q (c • heckeAlphaBar (AlgebraicClosure ℚ) N q x) =
      heckeBetaBar (AlgebraicClosure ℚ) N q (c • x) := by
    rw [e₁, atkinLehnerBar_heckeAlphaBar hqN]
  rw [e₂]
  have h₀ : ((heckeAlphaBar (AlgebraicClosure ℚ) N q (c • x) : modularFunctionFieldBar (N * q)) :
      LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (N * q) A.toSubring red := by
    rw [← e₁]
    exact h
  have hπ₀ : CharPReduction.modularRedLocHom (N * q) A.toSubring red ⟨_, h₀⟩ ≠ 0 := by
    have hsub : (⟨_, h₀⟩ : CharPReduction.modularLocalized (N * q) A.toSubring red) = ⟨_, h⟩ :=
      Subtype.ext (congrArg Subtype.val e₁).symm
    rw [hsub]
    exact hπ
  exact heckeBetaBar_mem_modularLocalized_of_heckeAlphaBar hqN (c • x) h₀ hπ₀

end ModularCurve.PlaceSpecialization

end LeafPCtransport

section LeafSpAvoids

p2m_open "AlgebraicCurve ModularCurve~jBar P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve ModularCurve.PlaceSpecialization~IsInftySide~jFun~tInfty~tZero~IsCuspidal~IsZeroSide P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve.PlaceSpecialization"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_qExpand jNum jNumQ jq ofPowerSeries_coeff_of_neg coeff_jq_neg_one jqN evalAtJ evalAtJ_X ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffMap_algebraMap coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_eq_map_intCast modularFunctionFieldC jqModC_mem jqNModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff KroneckerCongruence ssPlaces jGeomGen jNGeomGen IsAffineGeomPlace cuspInftyGeom ord_cuspInftyGeom_jq order_jqModC_def jqModC_ne_zero_def jq_mem_full coeff_jqModC_neg_one coeffSemilinearAut.coeffMap_qExpand coeffSemilinearAut.coeffMap_jqModC coeffSemilinearAut.coeffMap_mem_modularFunctionFieldC coeffSemilinearAut arithFrobC isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_jqModC qExpandAlgHomC qExpandAlgHomC_apply divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full jqModC_mem_full coeffMap_qExpand CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.mem_localizedAtKer CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc CharPReduction.redRes_ne_zero_of_notMem CharPReduction.redLoc_spec CharPReduction.redLoc_coe CharPReduction.redLocHom_apply CharPReduction.constSeries CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.affineBaseFin CharPModel.affineBaseInf CharPModel.FibreModel modularFunctionFieldBar_eq_modularFunctionFieldC finiteAlong_heckeAlphaBar_of_prime isCurveOver_modularFunctionFieldBar arithFrobC_smul_eq_frobOnPlacesGeomLevel CharPReduction.modularRedLocHom_mem exists_mem_riemannRochSpace_notMem_sub_single_of_le_degree isAffineGeomPlace_frobOnPlacesGeomLevel coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized_mul_of_not_dvd coeffEmb_jq exists_isAtkinLehnerAutFull_of_prime_of_not_dvd exists_regularProlongation_modularFunctionFieldBar_mul_of_not_dvd geomAut_atkinLehner_comp_legs hasPrincipalDivisors_modularFunctionFieldBar_unconditional place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin finrankAlong_heckeBetaBar CharPModel.FibreModel.piFin_range_localizes_of_jqModC_mem CharPModel.exists_monic_eval2_affineBaseFin_eq_zero_of_mem_modularLocalized_of_forall_mem_of_jBar_mem arithFrobC_smul_mem_ssPlaces_univ adjoin_jBar_jNBar_eq_top nonempty_modularPolynomialData relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi CharPReduction.mem_or_inv_mem_modularLocalized pow_char_eq_coeffMap_frobenius_qExpand qExpand_jqModC_eq_pow_unconditional mem_integralCoeffs_of_integral_affineBaseInf CharPModel.exists_monic_eval2_affineBaseInf_eq_zero_of_mem_modularLocalized_of_forall_inv_jBar_mem"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.atkinLehnerBar ProlongationTuple.jFun ProlongationTuple.jQFun ProlongationTuple.tInfty ProlongationTuple.tZero ProlongationTuple.IsCuspidal ProlongationTuple.IsInftySide ProlongationTuple.IsZeroSide ProlongationTuple ProlongationTuple.residue₁_apply ProlongationTuple.residue₂_apply ProlongationTuple.OrderLawFixed ProlongationTuple.CuspLawInfty reduceFst reduceSnd IsStrictFst IsStrictSnd sp d0_j_pole d1 ReducesDivisors fibreReduction chartClosure chartLocalSetFst ChartEtaleAt IsChartAt HasCoordinates ProlongationTuple.isCuspidal_of_not_isAffineGeomPlace_reduceFst ProlongationTuple.not_isAffineGeomPlace_reduceFst_of_isCuspidal ProlongationTuple.isInftySide_or_isZeroSide_of_isCuspidal ProlongationTuple.not_isInftySide_of_isZeroSide ProlongationTuple.reduceFst_eq_frobOnPlacesGeomLevel_reduceSnd_of_isZeroSide exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace ProlongationTuple.isInftySide_atkinLehnerBar_smul_iff reduceFst_atkinLehnerBar_smul mem_chartLocalSetFst_of_split hasCoordinates_of_sp_eq_spPlace"
p2m_open "ModularCurve.PlaceSpecialization~IsInftySide~jFun~tInfty~tZero~IsCuspidal~IsZeroSide ModularCurve~jBar"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

private theorem jqModC_mem_modularFunctionFieldBar :
    jqModC (AlgebraicClosure ℚ) ∈ modularFunctionFieldBar N := by
  rw [← coeffEmb_jq]
  exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))

private theorem jqModC_mem_modularLocalized (red : A →+* k) :
    jqModC (AlgebraicClosure ℚ) ∈ CharPReduction.modularLocalized N A.toSubring red :=
  CharPReduction.subring_le_localizedAtKer A.toSubring red (CharPReduction.modularRing N A.toSubring)
    (CharPReduction.modularRing_le_integralCoeffs N A.toSubring)
    (CharPReduction.jqModC_mem_modularRing N A.toSubring)

private theorem modularRedLocHom_jqModC (red : A →+* k)
    (hj : jqModC (AlgebraicClosure ℚ) ∈ CharPReduction.modularLocalized N A.toSubring red) :
    CharPReduction.modularRedLocHom N A.toSubring red ⟨jqModC (AlgebraicClosure ℚ), hj⟩ = jqModC k := by
  have h := CharPReduction.redLoc_coe (A := A.toSubring) (red := red)
    (R := CharPReduction.modularRing N A.toSubring)
    (hR := CharPReduction.modularRing_le_integralCoeffs N A.toSubring)
    ⟨jqModC (AlgebraicClosure ℚ), CharPReduction.jqModC_mem_modularRing N A.toSubring⟩
  rw [CharPReduction.redRes_apply] at h
  refine (CharPReduction.redLocHom_apply _).trans (h.trans ?_)
  ext n
  rw [CharPReduction.coeffRed_coeff, jqModC_eq_map_intCast k, HahnSeries.map_coeff, eq_intCast,
    ← map_intCast red]
  refine congrArg red (Subtype.ext ?_)
  have hcoe : (jqModC (AlgebraicClosure ℚ)).coeff n = (((jqModC ℤ).coeff n : ℤ) : AlgebraicClosure ℚ) := by
    rw [jqModC_eq_map_intCast (AlgebraicClosure ℚ), HahnSeries.map_coeff, eq_intCast]
  simpa using hcoe

private theorem mapDomain_const_eq_single_degree (v : Place k (modularFunctionFieldC k N))
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    Finsupp.mapDomain (fun _ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) => v) D =
      Finsupp.single v (Divisor.degree D) := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D₁ D₂ h₁ h₂ => rw [Finsupp.mapDomain_add, map_add, Finsupp.single_add, h₁, h₂]
  | single t n =>
      rw [Finsupp.mapDomain_single, Divisor.degree_single, deg_eq_one_levelN, Nat.cast_one, mul_one]

private theorem spAvoids_of_reducesDivisors {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (hsp : ReducesDivisors P) : SpAvoids P := by
  intro v
  by_contra hcon
  have hv : ∀ t : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), P.sp t = v :=
    fun t => not_not.mp fun h => hcon ⟨t, h⟩
  have hfun : P.sp = fun _ => v := funext hv
  have hf : ((⟨jqModC (AlgebraicClosure ℚ), jqModC_mem_modularFunctionFieldBar⟩ :
      modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)) ∈
        CharPReduction.modularLocalized N A.toSubring red :=
    jqModC_mem_modularLocalized red
  have hred : CharPReduction.modularRedLocHom N A.toSubring red ⟨_, hf⟩ = jqModC k :=
    modularRedLocHom_jqModC red hf
  have hne : CharPReduction.modularRedLocHom N A.toSubring red ⟨_, hf⟩ ≠ 0 := by
    rw [hred]
    exact jqModC_ne_zero_def k
  have hf0 : (⟨jqModC (AlgebraicClosure ℚ), jqModC_mem_modularFunctionFieldBar⟩ :
      modularFunctionFieldBar N) ≠ 0 :=
    fun h0 => jqModC_ne_zero_def (AlgebraicClosure ℚ) (congrArg Subtype.val h0)
  haveI := hasPrincipalDivisors_modularFunctionFieldBar_unconditional N
  obtain ⟨D, hD, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) _ hf0
  have key := hsp _ hf (CharPReduction.modularRedLocHom_mem A.toSubring red N ⟨_, hf⟩) hne D hD
    (cuspInftyGeom k N)
  have hel : (⟨CharPReduction.modularRedLocHom N A.toSubring red ⟨_, hf⟩,
      CharPReduction.modularRedLocHom_mem A.toSubring red N ⟨_, hf⟩⟩ : modularFunctionFieldC k N) =
      ⟨jqModC k, jqModC_mem k N⟩ := Subtype.ext hred
  rw [hel, ord_cuspInftyGeom_jq k N, hfun, mapDomain_const_eq_single_degree, hdeg, Finsupp.single_zero,
    Finsupp.zero_apply] at key
  omega

end ModularCurve.PlaceSpecialization

end LeafSpAvoids

section LeafPullbackBalanced

p2m_open "AlgebraicCurve ModularCurve~jBar P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve ModularCurve.PlaceSpecialization~IsInftySide~jFun~tInfty~tZero~IsCuspidal~IsZeroSide P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve.PlaceSpecialization"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_qExpand jNum jNumQ jq ofPowerSeries_coeff_of_neg coeff_jq_neg_one jqN evalAtJ evalAtJ_X ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffMap_algebraMap coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_eq_map_intCast modularFunctionFieldC jqModC_mem jqNModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff KroneckerCongruence ssPlaces jGeomGen jNGeomGen IsAffineGeomPlace cuspInftyGeom ord_cuspInftyGeom_jq order_jqModC_def jqModC_ne_zero_def jq_mem_full coeff_jqModC_neg_one coeffSemilinearAut.coeffMap_qExpand coeffSemilinearAut.coeffMap_jqModC coeffSemilinearAut.coeffMap_mem_modularFunctionFieldC coeffSemilinearAut arithFrobC isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_jqModC qExpandAlgHomC qExpandAlgHomC_apply divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full jqModC_mem_full coeffMap_qExpand CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.mem_localizedAtKer CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc CharPReduction.redRes_ne_zero_of_notMem CharPReduction.redLoc_spec CharPReduction.redLoc_coe CharPReduction.redLocHom_apply CharPReduction.constSeries CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.affineBaseFin CharPModel.affineBaseInf CharPModel.FibreModel modularFunctionFieldBar_eq_modularFunctionFieldC finiteAlong_heckeAlphaBar_of_prime isCurveOver_modularFunctionFieldBar arithFrobC_smul_eq_frobOnPlacesGeomLevel CharPReduction.modularRedLocHom_mem exists_mem_riemannRochSpace_notMem_sub_single_of_le_degree isAffineGeomPlace_frobOnPlacesGeomLevel coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized_mul_of_not_dvd coeffEmb_jq exists_isAtkinLehnerAutFull_of_prime_of_not_dvd exists_regularProlongation_modularFunctionFieldBar_mul_of_not_dvd geomAut_atkinLehner_comp_legs hasPrincipalDivisors_modularFunctionFieldBar_unconditional place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin finrankAlong_heckeBetaBar CharPModel.FibreModel.piFin_range_localizes_of_jqModC_mem CharPModel.exists_monic_eval2_affineBaseFin_eq_zero_of_mem_modularLocalized_of_forall_mem_of_jBar_mem arithFrobC_smul_mem_ssPlaces_univ adjoin_jBar_jNBar_eq_top nonempty_modularPolynomialData relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi CharPReduction.mem_or_inv_mem_modularLocalized pow_char_eq_coeffMap_frobenius_qExpand qExpand_jqModC_eq_pow_unconditional mem_integralCoeffs_of_integral_affineBaseInf CharPModel.exists_monic_eval2_affineBaseInf_eq_zero_of_mem_modularLocalized_of_forall_inv_jBar_mem"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.atkinLehnerBar ProlongationTuple.jFun ProlongationTuple.jQFun ProlongationTuple.tInfty ProlongationTuple.tZero ProlongationTuple.IsCuspidal ProlongationTuple.IsInftySide ProlongationTuple.IsZeroSide ProlongationTuple ProlongationTuple.residue₁_apply ProlongationTuple.residue₂_apply ProlongationTuple.OrderLawFixed ProlongationTuple.CuspLawInfty reduceFst reduceSnd IsStrictFst IsStrictSnd sp d0_j_pole d1 ReducesDivisors fibreReduction chartClosure chartLocalSetFst ChartEtaleAt IsChartAt HasCoordinates ProlongationTuple.isCuspidal_of_not_isAffineGeomPlace_reduceFst ProlongationTuple.not_isAffineGeomPlace_reduceFst_of_isCuspidal ProlongationTuple.isInftySide_or_isZeroSide_of_isCuspidal ProlongationTuple.not_isInftySide_of_isZeroSide ProlongationTuple.reduceFst_eq_frobOnPlacesGeomLevel_reduceSnd_of_isZeroSide exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace ProlongationTuple.isInftySide_atkinLehnerBar_smul_iff reduceFst_atkinLehnerBar_smul mem_chartLocalSetFst_of_split hasCoordinates_of_sp_eq_spPlace"
p2m_open "ModularCurve.PlaceSpecialization~IsInftySide~jFun~tInfty~tZero~IsCuspidal~IsZeroSide ModularCurve~jBar"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

variable {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

private theorem residue_ne_zero_of_modularRedLocHom_ne_zero {f : modularFunctionFieldBar (N * q)}
    (hf : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (N * q) A.toSubring red)
    (hne : CharPReduction.modularRedLocHom (N * q) A.toSubring red ⟨f, hf⟩ ≠ 0)
    (h : f ∈ R.R₁.integers) : R.R₁.residue ⟨f, h⟩ ≠ 0 := by
  obtain ⟨h', hres⟩ := R.residue₁_eq_modularRedLocHom f hf
  intro h0
  have h0' : R.R₁.residue ⟨f, h'⟩ = 0 := h0
  have hz : ((R.ι (R.R₁.residue ⟨f, h'⟩) : modularFunctionFieldC k N) : LaurentSeries k) = 0 := by
    rw [h0', map_zero, ZeroMemClass.coe_zero]
  exact hne (hres.symm.trans hz)

private theorem pullbackBalanced_of_not_dvd (hqN : ¬ q ∣ N) : PullbackBalanced R := by
  intro x hx
  have hval := coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized_mul_of_not_dvd hqN red
  have hf : heckeAlphaBar (AlgebraicClosure ℚ) N q x ≠ 0 := (map_ne_zero _).mpr hx
  obtain ⟨c, -, h₁, hne₁⟩ := gaussReg_exists_smul_mem_ne_zero hqN red hval _ hf
  obtain ⟨h₂, hne₂⟩ := transportContent hqN x c h₁ hne₁
  refine ⟨c, (R.mem_integersFst_iff _).mpr h₁, (R.mem_integersSnd_iff _).mpr h₂,
    residue_ne_zero_of_modularRedLocHom_ne_zero R h₁ hne₁ _, ?_⟩
  rw [R.residue₂_eq]
  exact residue_ne_zero_of_modularRedLocHom_ne_zero R h₂ hne₂ _

end ModularCurve.PlaceSpecialization

end LeafPullbackBalanced

end LeafPC

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_qExpand jNum jNumQ jq ofPowerSeries_coeff_of_neg coeff_jq_neg_one jqN evalAtJ evalAtJ_X ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffMap_algebraMap coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_eq_map_intCast modularFunctionFieldC jqModC_mem jqNModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff KroneckerCongruence ssPlaces jGeomGen jNGeomGen IsAffineGeomPlace cuspInftyGeom ord_cuspInftyGeom_jq order_jqModC_def jqModC_ne_zero_def jq_mem_full coeff_jqModC_neg_one coeffSemilinearAut.coeffMap_qExpand coeffSemilinearAut.coeffMap_jqModC coeffSemilinearAut.coeffMap_mem_modularFunctionFieldC coeffSemilinearAut arithFrobC isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_jqModC qExpandAlgHomC qExpandAlgHomC_apply divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full jqModC_mem_full coeffMap_qExpand CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.mem_localizedAtKer CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc CharPReduction.redRes_ne_zero_of_notMem CharPReduction.redLoc_spec CharPReduction.redLoc_coe CharPReduction.redLocHom_apply CharPReduction.constSeries CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.affineBaseFin CharPModel.affineBaseInf CharPModel.FibreModel modularFunctionFieldBar_eq_modularFunctionFieldC finiteAlong_heckeAlphaBar_of_prime isCurveOver_modularFunctionFieldBar arithFrobC_smul_eq_frobOnPlacesGeomLevel CharPReduction.modularRedLocHom_mem exists_mem_riemannRochSpace_notMem_sub_single_of_le_degree isAffineGeomPlace_frobOnPlacesGeomLevel coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized_mul_of_not_dvd coeffEmb_jq exists_isAtkinLehnerAutFull_of_prime_of_not_dvd exists_regularProlongation_modularFunctionFieldBar_mul_of_not_dvd geomAut_atkinLehner_comp_legs hasPrincipalDivisors_modularFunctionFieldBar_unconditional place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin finrankAlong_heckeBetaBar CharPModel.FibreModel.piFin_range_localizes_of_jqModC_mem CharPModel.exists_monic_eval2_affineBaseFin_eq_zero_of_mem_modularLocalized_of_forall_mem_of_jBar_mem arithFrobC_smul_mem_ssPlaces_univ adjoin_jBar_jNBar_eq_top nonempty_modularPolynomialData relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi CharPReduction.mem_or_inv_mem_modularLocalized pow_char_eq_coeffMap_frobenius_qExpand qExpand_jqModC_eq_pow_unconditional mem_integralCoeffs_of_integral_affineBaseInf CharPModel.exists_monic_eval2_affineBaseInf_eq_zero_of_mem_modularLocalized_of_forall_inv_jBar_mem"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.atkinLehnerBar ProlongationTuple.jFun ProlongationTuple.jQFun ProlongationTuple.tInfty ProlongationTuple.tZero ProlongationTuple.IsCuspidal ProlongationTuple.IsInftySide ProlongationTuple.IsZeroSide ProlongationTuple ProlongationTuple.residue₁_apply ProlongationTuple.residue₂_apply ProlongationTuple.OrderLawFixed ProlongationTuple.CuspLawInfty reduceFst reduceSnd IsStrictFst IsStrictSnd sp d0_j_pole d1 ReducesDivisors fibreReduction chartClosure chartLocalSetFst ChartEtaleAt IsChartAt HasCoordinates ProlongationTuple.isCuspidal_of_not_isAffineGeomPlace_reduceFst ProlongationTuple.not_isAffineGeomPlace_reduceFst_of_isCuspidal ProlongationTuple.isInftySide_or_isZeroSide_of_isCuspidal ProlongationTuple.not_isInftySide_of_isZeroSide ProlongationTuple.reduceFst_eq_frobOnPlacesGeomLevel_reduceSnd_of_isZeroSide exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace ProlongationTuple.isInftySide_atkinLehnerBar_smul_iff reduceFst_atkinLehnerBar_smul mem_chartLocalSetFst_of_split hasCoordinates_of_sp_eq_spPlace"
p2m_open "ModularCurve.PlaceSpecialization~IsInftySide~jFun~tInfty~tZero~IsCuspidal~IsZeroSide ModularCurve~jBar"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

variable {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P) (hqN : ¬ q ∣ N)

private theorem penT_pullbackBalanced_of_not_dvd (hqN : ¬ q ∣ N) : PullbackBalanced R := by
  exact pullbackBalanced_of_not_dvd R hqN

private theorem penT_spAvoids_of_reducesDivisors (hsp : ReducesDivisors P) : SpAvoids P := by
  exact spAvoids_of_reducesDivisors hsp

end ModularCurve.PlaceSpecialization

end NR3_25_penT

section NR3_30_clause0

p2m_open "AlgebraicCurve ModularCurve~jBar P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve ModularCurve.PlaceSpecialization~IsInftySide~jFun~tInfty~tZero~IsCuspidal~IsZeroSide P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve.PlaceSpecialization"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_qExpand jNum jNumQ jq ofPowerSeries_coeff_of_neg coeff_jq_neg_one jqN evalAtJ evalAtJ_X ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffMap_algebraMap coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_eq_map_intCast modularFunctionFieldC jqModC_mem jqNModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff KroneckerCongruence ssPlaces jGeomGen jNGeomGen IsAffineGeomPlace cuspInftyGeom ord_cuspInftyGeom_jq order_jqModC_def jqModC_ne_zero_def jq_mem_full coeff_jqModC_neg_one coeffSemilinearAut.coeffMap_qExpand coeffSemilinearAut.coeffMap_jqModC coeffSemilinearAut.coeffMap_mem_modularFunctionFieldC coeffSemilinearAut arithFrobC isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_jqModC qExpandAlgHomC qExpandAlgHomC_apply divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full jqModC_mem_full coeffMap_qExpand CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.mem_localizedAtKer CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc CharPReduction.redRes_ne_zero_of_notMem CharPReduction.redLoc_spec CharPReduction.redLoc_coe CharPReduction.redLocHom_apply CharPReduction.constSeries CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.affineBaseFin CharPModel.affineBaseInf CharPModel.FibreModel modularFunctionFieldBar_eq_modularFunctionFieldC finiteAlong_heckeAlphaBar_of_prime isCurveOver_modularFunctionFieldBar arithFrobC_smul_eq_frobOnPlacesGeomLevel CharPReduction.modularRedLocHom_mem exists_mem_riemannRochSpace_notMem_sub_single_of_le_degree isAffineGeomPlace_frobOnPlacesGeomLevel coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized_mul_of_not_dvd coeffEmb_jq exists_isAtkinLehnerAutFull_of_prime_of_not_dvd exists_regularProlongation_modularFunctionFieldBar_mul_of_not_dvd geomAut_atkinLehner_comp_legs hasPrincipalDivisors_modularFunctionFieldBar_unconditional place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin finrankAlong_heckeBetaBar CharPModel.FibreModel.piFin_range_localizes_of_jqModC_mem CharPModel.exists_monic_eval2_affineBaseFin_eq_zero_of_mem_modularLocalized_of_forall_mem_of_jBar_mem arithFrobC_smul_mem_ssPlaces_univ adjoin_jBar_jNBar_eq_top nonempty_modularPolynomialData relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi CharPReduction.mem_or_inv_mem_modularLocalized pow_char_eq_coeffMap_frobenius_qExpand qExpand_jqModC_eq_pow_unconditional mem_integralCoeffs_of_integral_affineBaseInf CharPModel.exists_monic_eval2_affineBaseInf_eq_zero_of_mem_modularLocalized_of_forall_inv_jBar_mem"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.atkinLehnerBar ProlongationTuple.jFun ProlongationTuple.jQFun ProlongationTuple.tInfty ProlongationTuple.tZero ProlongationTuple.IsCuspidal ProlongationTuple.IsInftySide ProlongationTuple.IsZeroSide ProlongationTuple ProlongationTuple.residue₁_apply ProlongationTuple.residue₂_apply ProlongationTuple.OrderLawFixed ProlongationTuple.CuspLawInfty reduceFst reduceSnd IsStrictFst IsStrictSnd sp d0_j_pole d1 ReducesDivisors fibreReduction chartClosure chartLocalSetFst ChartEtaleAt IsChartAt HasCoordinates ProlongationTuple.isCuspidal_of_not_isAffineGeomPlace_reduceFst ProlongationTuple.not_isAffineGeomPlace_reduceFst_of_isCuspidal ProlongationTuple.isInftySide_or_isZeroSide_of_isCuspidal ProlongationTuple.not_isInftySide_of_isZeroSide ProlongationTuple.reduceFst_eq_frobOnPlacesGeomLevel_reduceSnd_of_isZeroSide exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace ProlongationTuple.isInftySide_atkinLehnerBar_smul_iff reduceFst_atkinLehnerBar_smul mem_chartLocalSetFst_of_split hasCoordinates_of_sp_eq_spPlace"
p2m_open "ModularCurve.PlaceSpecialization~IsInftySide~jFun~tInfty~tZero~IsCuspidal~IsZeroSide ModularCurve~jBar"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

variable {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P) (hqN : ¬ q ∣ N)

open Classical in

private def penC_InftyBound : Prop :=
  ∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      (∀ W, D W = W.ord f) →
      ∀ v : Place k (modularFunctionFieldC k N),
        (∃ c, ProlongationTuple.IsInftySide P c ∧ P.reduceFst c = v) →
        (∀ W, ProlongationTuple.IsInftySide P W → P.reduceFst W = v → 0 ≤ D W) →
        Finsupp.mapDomain P.reduceFst (D.filter (ProlongationTuple.IsInftySide P)) v ≤ v.ord (R.residue₁ ⟨f, h₁⟩)

omit [Fact (Nat.Prime q)] [NeZero N] in

private theorem penC_smul_divisor_apply (w : modularFunctionFieldBar (N * q) ≃ₐ[AlgebraicClosure ℚ]
      modularFunctionFieldBar (N * q))
    (f : modularFunctionFieldBar (N * q)) (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hD : ∀ W, D W = W.ord f) (W' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    (w • D) W' = W'.ord (w f) := by
  obtain ⟨W, rfl⟩ : ∃ W, w • W = W' := ⟨w⁻¹ • W', smul_inv_smul w W'⟩
  rw [Divisor.smul_apply_smul, hD W, Place.ord_smul]

include hqN in
open Classical in

private theorem penC_filter_inftySide_smul (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    (ProlongationTuple.atkinLehnerBar N q • D).filter (ProlongationTuple.IsInftySide P) =
      ProlongationTuple.atkinLehnerBar N q • D.filter (ProlongationTuple.IsZeroSide P) := by
  ext W'
  obtain ⟨W, rfl⟩ : ∃ W, ProlongationTuple.atkinLehnerBar N q • W = W' :=
    ⟨(ProlongationTuple.atkinLehnerBar N q)⁻¹ • W', smul_inv_smul _ W'⟩
  rw [Finsupp.filter_apply, Divisor.smul_apply_smul, Divisor.smul_apply_smul, Finsupp.filter_apply]
  by_cases h : ProlongationTuple.IsZeroSide P W <;>
    simp [h, ProlongationTuple.isInftySide_atkinLehnerBar_smul_iff P hqN W]

include hqN in

private theorem penC_mapDomain_reduceFst_smul (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    Finsupp.mapDomain P.reduceFst (ProlongationTuple.atkinLehnerBar N q • E) = Finsupp.mapDomain P.reduceSnd E := by
  rw [Divisor.smul_def, ← Finsupp.mapDomain_comp]
  have hfun : (P.reduceFst ∘ fun W => ProlongationTuple.atkinLehnerBar N q • W) = P.reduceSnd :=
    funext fun W => reduceFst_atkinLehnerBar_smul P hqN W
  rw [hfun]

include hqN in
open Classical in

private theorem penC_cuspLSC_clause0_of_inftyBound (hB : penC_InftyBound R) :
    ∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      (∀ W, D W = W.ord f) →
      ∀ u : Place k (modularFunctionFieldC k N),
        (∃ c, ProlongationTuple.IsZeroSide P c ∧ P.reduceSnd c = u) →
        (∀ W, ProlongationTuple.IsZeroSide P W → P.reduceSnd W = u → 0 ≤ D W) →
        Finsupp.mapDomain P.reduceSnd (D.filter (ProlongationTuple.IsZeroSide P)) u ≤ u.ord (R.residue₂ ⟨f, h₂⟩) := by
  intro f _h₁ h₂ _hr₁ hr₂ D hD u hu hpos
  obtain ⟨c, hc, hcu⟩ := hu
  have hg₁ : ProlongationTuple.atkinLehnerBar N q f ∈ R.R₁.integers := (R.mem_integers₂_iff f).mp h₂
  have hres : R.R₂.residue ⟨f, h₂⟩ = R.R₁.residue ⟨ProlongationTuple.atkinLehnerBar N q f, hg₁⟩ :=
    R.residue₂_eq f h₂
  have hr₁' : R.R₁.residue ⟨ProlongationTuple.atkinLehnerBar N q f, hg₁⟩ ≠ 0 := by
    rw [← hres]; exact hr₂
  have hguard : ∃ c', ProlongationTuple.IsInftySide P c' ∧ P.reduceFst c' = u :=
    ⟨ProlongationTuple.atkinLehnerBar N q • c,
      (ProlongationTuple.isInftySide_atkinLehnerBar_smul_iff P hqN c).mpr hc,
      by rw [reduceFst_atkinLehnerBar_smul P hqN c]; exact hcu⟩
  have hpos' : ∀ W', ProlongationTuple.IsInftySide P W' → P.reduceFst W' = u →
      0 ≤ (ProlongationTuple.atkinLehnerBar N q • D) W' := by
    intro W' hW' hWu
    obtain ⟨W, rfl⟩ : ∃ W, ProlongationTuple.atkinLehnerBar N q • W = W' :=
      ⟨(ProlongationTuple.atkinLehnerBar N q)⁻¹ • W', smul_inv_smul _ W'⟩
    rw [Divisor.smul_apply_smul]
    rw [reduceFst_atkinLehnerBar_smul P hqN W] at hWu
    exact hpos W ((ProlongationTuple.isInftySide_atkinLehnerBar_smul_iff P hqN W).mp hW') hWu
  have key := hB (ProlongationTuple.atkinLehnerBar N q f) hg₁ hr₁'
    (ProlongationTuple.atkinLehnerBar N q • D) (penC_smul_divisor_apply (ProlongationTuple.atkinLehnerBar N q) f D hD)
    u hguard hpos'
  rw [penC_filter_inftySide_smul hqN D, penC_mapDomain_reduceFst_smul hqN] at key
  rw [ProlongationTuple.residue₂_apply, hres, ← ProlongationTuple.residue₁_apply]
  exact key

include hqN in

private theorem penC_cuspLSC_of_inftyBound (hB : penC_InftyBound R) : CuspLocalSemicontinuity R :=
  ⟨fun f h₁ _h₂ hr₁ _hr₂ D hD v hv hpos => hB f h₁ hr₁ D hD v hv hpos,
    penC_cuspLSC_clause0_of_inftyBound R hqN hB⟩

end ModularCurve.PlaceSpecialization

end NR3_30_clause0

section NR3_40_inftybound

p2m_open "AlgebraicCurve ModularCurve~jBar P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve ModularCurve.PlaceSpecialization~IsInftySide~jFun~tInfty~tZero~IsCuspidal~IsZeroSide P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve.PlaceSpecialization"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_qExpand jNum jNumQ jq ofPowerSeries_coeff_of_neg coeff_jq_neg_one jqN evalAtJ evalAtJ_X ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffMap_algebraMap coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_eq_map_intCast modularFunctionFieldC jqModC_mem jqNModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff KroneckerCongruence ssPlaces jGeomGen jNGeomGen IsAffineGeomPlace cuspInftyGeom ord_cuspInftyGeom_jq order_jqModC_def jqModC_ne_zero_def jq_mem_full coeff_jqModC_neg_one coeffSemilinearAut.coeffMap_qExpand coeffSemilinearAut.coeffMap_jqModC coeffSemilinearAut.coeffMap_mem_modularFunctionFieldC coeffSemilinearAut arithFrobC isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_jqModC qExpandAlgHomC qExpandAlgHomC_apply divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full jqModC_mem_full coeffMap_qExpand CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.mem_localizedAtKer CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc CharPReduction.redRes_ne_zero_of_notMem CharPReduction.redLoc_spec CharPReduction.redLoc_coe CharPReduction.redLocHom_apply CharPReduction.constSeries CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.affineBaseFin CharPModel.affineBaseInf CharPModel.FibreModel modularFunctionFieldBar_eq_modularFunctionFieldC finiteAlong_heckeAlphaBar_of_prime isCurveOver_modularFunctionFieldBar arithFrobC_smul_eq_frobOnPlacesGeomLevel CharPReduction.modularRedLocHom_mem exists_mem_riemannRochSpace_notMem_sub_single_of_le_degree isAffineGeomPlace_frobOnPlacesGeomLevel coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized_mul_of_not_dvd coeffEmb_jq exists_isAtkinLehnerAutFull_of_prime_of_not_dvd exists_regularProlongation_modularFunctionFieldBar_mul_of_not_dvd geomAut_atkinLehner_comp_legs hasPrincipalDivisors_modularFunctionFieldBar_unconditional place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin finrankAlong_heckeBetaBar CharPModel.FibreModel.piFin_range_localizes_of_jqModC_mem CharPModel.exists_monic_eval2_affineBaseFin_eq_zero_of_mem_modularLocalized_of_forall_mem_of_jBar_mem arithFrobC_smul_mem_ssPlaces_univ adjoin_jBar_jNBar_eq_top nonempty_modularPolynomialData relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi CharPReduction.mem_or_inv_mem_modularLocalized pow_char_eq_coeffMap_frobenius_qExpand qExpand_jqModC_eq_pow_unconditional mem_integralCoeffs_of_integral_affineBaseInf CharPModel.exists_monic_eval2_affineBaseInf_eq_zero_of_mem_modularLocalized_of_forall_inv_jBar_mem"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.atkinLehnerBar ProlongationTuple.jFun ProlongationTuple.jQFun ProlongationTuple.tInfty ProlongationTuple.tZero ProlongationTuple.IsCuspidal ProlongationTuple.IsInftySide ProlongationTuple.IsZeroSide ProlongationTuple ProlongationTuple.residue₁_apply ProlongationTuple.residue₂_apply ProlongationTuple.OrderLawFixed ProlongationTuple.CuspLawInfty reduceFst reduceSnd IsStrictFst IsStrictSnd sp d0_j_pole d1 ReducesDivisors fibreReduction chartClosure chartLocalSetFst ChartEtaleAt IsChartAt HasCoordinates ProlongationTuple.isCuspidal_of_not_isAffineGeomPlace_reduceFst ProlongationTuple.not_isAffineGeomPlace_reduceFst_of_isCuspidal ProlongationTuple.isInftySide_or_isZeroSide_of_isCuspidal ProlongationTuple.not_isInftySide_of_isZeroSide ProlongationTuple.reduceFst_eq_frobOnPlacesGeomLevel_reduceSnd_of_isZeroSide exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace ProlongationTuple.isInftySide_atkinLehnerBar_smul_iff reduceFst_atkinLehnerBar_smul mem_chartLocalSetFst_of_split hasCoordinates_of_sp_eq_spPlace"
p2m_open "ModularCurve.PlaceSpecialization~IsInftySide~jFun~tInfty~tZero~IsCuspidal~IsZeroSide ModularCurve~jBar"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

variable {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

private noncomputable def _root_.ModularCurve.PlaceSpecialization.redLoc (f : modularFunctionFieldBar N)
    (hf : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized N A.toSubring red) :
    modularFunctionFieldC k N :=
  ⟨CharPReduction.modularRedLocHom N A.toSubring red ⟨f, hf⟩,
    CharPReduction.modularRedLocHom_mem A.toSubring red N ⟨f, hf⟩⟩

p2m_export "ModularCurve.PlaceSpecialization" "redLoc"
omit [Fact (Nat.Prime q)] [CharP k q] in

private theorem penA_isUnit_of_residue_ne_zero
    (𝒪 : RegularProlongation A (modularFunctionFieldBar (N * q))
      (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N))
    (ι : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N →+* modularFunctionFieldC k N)
    (x : 𝒪.integers) (hx : (ι.comp 𝒪.residue) x ≠ 0) : IsUnit x := by
  by_contra hnu
  apply hx
  have hmem : x ∈ IsLocalRing.maximalIdeal 𝒪.integers := hnu
  rw [← 𝒪.ker_residue] at hmem
  simp [RingHom.mem_ker.mp hmem]

private theorem _root_.AlgebraicCurve.Place.ord_nonneg_of_mem_pn {K F : Type*} [Field K] [Field F]
    [Algebra K F] (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.AlgebraicCurve.Place.ord_nonneg_of_mem_pn" "AlgebraicCurve.Place.ord_nonneg_of_mem_pn"

private theorem _root_.AlgebraicCurve.Place.mem_of_ord_nonneg_pn {K F : Type*} [Field K] [Field F]
    [Algebra K F] (v : Place K F) {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.AlgebraicCurve.Place.mem_of_ord_nonneg_pn" "AlgebraicCurve.Place.mem_of_ord_nonneg_pn"

private theorem _root_.AlgebraicCurve.Place.ne_zero_of_ord_pos_pn {K F : Type*} [Field K] [Field F]
    [Algebra K F] (v : Place K F) {f : F} (h : 0 < v.ord f) : f ≠ 0 := by
  rintro rfl
  simp at h

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.AlgebraicCurve.Place.ne_zero_of_ord_pos_pn" "AlgebraicCurve.Place.ne_zero_of_ord_pos_pn"

private theorem _root_.AlgebraicCurve.Place.isUnit_iff_ord_eq_zero_pn {K F : Type*} [Field K]
    [Field F] [Algebra K F] (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) :
    IsUnit (⟨f, hf⟩ : v.toValuationSubring) ↔ v.ord f = 0 := by
  constructor
  · intro hu
    have := v.ord_coe_unit hu.unit
    rwa [IsUnit.unit_spec] at this
  · intro h0
    obtain ⟨hm, hu⟩ := v.exists_isUnit_of_ord_eq_zero hf0 h0
    exact hu

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.AlgebraicCurve.Place.isUnit_iff_ord_eq_zero_pn" "AlgebraicCurve.Place.isUnit_iff_ord_eq_zero_pn"

private theorem _root_.AlgebraicCurve.Place.hasValue_iff_eq_or_ord_sub_pos_pn {K F : Type*} [Field K]
    [Field F] [Algebra K F] (v : Place K F) {g : F} (hg : g ∈ v.toValuationSubring) (c : K) :
    v.HasValue g c ↔ g = algebraMap K F c ∨ 0 < v.ord (g - algebraMap K F c) := by
  have hcm : algebraMap K F c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have hsub : g - algebraMap K F c ∈ v.toValuationSubring := sub_mem hg hcm
  have key : v.HasValue g c ↔
      IsLocalRing.residue v.toValuationSubring ⟨g - algebraMap K F c, hsub⟩ = 0 := by
    have hx : (⟨g - algebraMap K F c, hsub⟩ : v.toValuationSubring) =
        ⟨g, hg⟩ - algebraMap K v.toValuationSubring c := Subtype.ext (by simp)
    rw [hx, map_sub, sub_eq_zero, v.residue_algebraMap c]
    constructor
    · intro h; exact h.residue_eq
    · intro h; exact ⟨hg, h⟩
  rw [key, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rcases eq_or_ne (g - algebraMap K F c) 0 with h0 | h0
  · have hg' : g = algebraMap K F c := sub_eq_zero.mp h0
    have hz : (⟨g - algebraMap K F c, hsub⟩ : v.toValuationSubring) = 0 := Subtype.ext h0
    rw [hz]
    exact ⟨fun _ => Or.inl hg', fun _ => not_isUnit_zero⟩
  · rw [v.isUnit_iff_ord_eq_zero_pn hsub h0]
    have hnn := v.ord_nonneg_of_mem_pn hsub
    constructor
    · intro hne
      exact Or.inr (lt_of_le_of_ne hnn (Ne.symm hne))
    · rintro (hEq | hpos)
      · exact absurd (sub_eq_zero.mpr hEq) h0
      · exact ne_of_gt hpos

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.AlgebraicCurve.Place.hasValue_iff_eq_or_ord_sub_pos_pn" "AlgebraicCurve.Place.hasValue_iff_eq_or_ord_sub_pos_pn"

private theorem _root_.AlgebraicCurve.Place.hasValue_of_ord_sub_pos_pn {K F : Type*} [Field K] [Field F]
    [Algebra K F] (v : Place K F) {g : F} {c : K} (h : 0 < v.ord (g - algebraMap K F c)) :
    v.HasValue g c := by
  have hsub : g - algebraMap K F c ∈ v.toValuationSubring :=
    v.mem_of_ord_nonneg_pn (v.ne_zero_of_ord_pos_pn h) h.le
  have hg : g ∈ v.toValuationSubring := by
    have h' := add_mem hsub (v.algebraMap_mem' c)
    rwa [sub_add_cancel] at h'
  exact (v.hasValue_iff_eq_or_ord_sub_pos_pn hg c).mpr (Or.inr h)

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.AlgebraicCurve.Place.hasValue_of_ord_sub_pos_pn" "AlgebraicCurve.Place.hasValue_of_ord_sub_pos_pn"

private theorem pnN_coe_algebraMap {L : Type*} [Field L] (E : IntermediateField L (LaurentSeries L))
    (x : L) : ((algebraMap L E x : E) : LaurentSeries L) = algebraMap L (LaurentSeries L) x := by
  rw [IsScalarTower.algebraMap_apply L E (LaurentSeries L) x]
  rfl

private theorem pnN_const_mem (a : A) :
    ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ) :
        modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized N A.toSubring red := by
  rw [pnN_coe_algebraMap]
  exact CharPReduction.subring_le_localizedAtKer A.toSubring red (CharPReduction.modularRing N A.toSubring)
    (CharPReduction.modularRing_le_integralCoeffs N A.toSubring)
    (CharPReduction.constSeries_mem_modularRing N A.toSubring ⟨(a : AlgebraicClosure ℚ), a.2⟩)

private theorem pnN_red_mk_eq (x : AlgebraicClosure ℚ) (hx : x ∈ A.toSubring) (b : A)
    (e : x = (b : AlgebraicClosure ℚ)) : red ⟨x, hx⟩ = red b := by
  subst e
  rfl

private theorem pnN_modularRedLocHom_const (a : A) :
    CharPReduction.modularRedLocHom N A.toSubring red ⟨_, pnN_const_mem (N := N) (red := red) a⟩ =
      algebraMap k (LaurentSeries k) (red a) := by
  have hR : CharPReduction.constSeries A.toSubring ⟨(a : AlgebraicClosure ℚ), a.2⟩ ∈
      CharPReduction.modularRing N A.toSubring :=
    CharPReduction.constSeries_mem_modularRing N A.toSubring ⟨(a : AlgebraicClosure ℚ), a.2⟩
  have hspec := CharPReduction.redLoc_spec (A := A.toSubring) (red := red)
    (R := CharPReduction.modularRing N A.toSubring)
    (hR := CharPReduction.modularRing_le_integralCoeffs N A.toSubring)
    ⟨_, pnN_const_mem (N := N) (red := red) a⟩ (r := ⟨_, hR⟩) (s := 1)
    (by rw [OneMemClass.coe_one, mul_one, pnN_coe_algebraMap]; rfl)
  rw [map_one, mul_one] at hspec
  calc CharPReduction.modularRedLocHom N A.toSubring red ⟨_, pnN_const_mem (N := N) (red := red) a⟩
      = CharPReduction.redLoc ⟨_, pnN_const_mem (N := N) (red := red) a⟩ := rfl
    _ = CharPReduction.redRes A.toSubring red (CharPReduction.modularRing N A.toSubring)
          (CharPReduction.modularRing_le_integralCoeffs N A.toSubring) ⟨_, hR⟩ := hspec
    _ = algebraMap k (LaurentSeries k) (red a) := by
        rw [algebraMap_laurentSeries_eq_single]
        ext n
        show red ⟨(CharPReduction.constSeries A.toSubring ⟨(a : AlgebraicClosure ℚ), a.2⟩ :
            LaurentSeries (AlgebraicClosure ℚ)).coeff n, _⟩ = (HahnSeries.single 0 (red a)).coeff n
        by_cases hn : n = 0
        · subst hn
          rw [HahnSeries.coeff_single_same]
          have e : (CharPReduction.constSeries A.toSubring ⟨(a : AlgebraicClosure ℚ), a.2⟩ :
              LaurentSeries (AlgebraicClosure ℚ)).coeff 0 = (a : AlgebraicClosure ℚ) := by
            show (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))
              (a : AlgebraicClosure ℚ)).coeff 0 = (a : AlgebraicClosure ℚ)
            rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_same]
          exact pnN_red_mk_eq _ _ a e
        · rw [HahnSeries.coeff_single_of_ne hn]
          have e : (CharPReduction.constSeries A.toSubring ⟨(a : AlgebraicClosure ℚ), a.2⟩ :
              LaurentSeries (AlgebraicClosure ℚ)).coeff n = ((0 : A) : AlgebraicClosure ℚ) := by
            show (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))
              (a : AlgebraicClosure ℚ)).coeff n = ((0 : A) : AlgebraicClosure ℚ)
            rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_of_ne hn]
            rfl
          exact (pnN_red_mk_eq _ _ 0 e).trans (map_zero red)

private theorem pnN_redLoc_sub_const (T : modularFunctionFieldBar N)
    (hT : (T : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized N A.toSubring red)
    (a : A)
    (ht : ((T - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ) :
        modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized N A.toSubring red) :
    redLoc (T - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)) ht =
      redLoc T hT - algebraMap k (modularFunctionFieldC k N) (red a) := by
  apply Subtype.ext
  have hmk : (⟨_, ht⟩ : CharPReduction.modularLocalized N A.toSubring red) =
      ⟨_, hT⟩ - ⟨_, pnN_const_mem (N := N) (red := red) a⟩ :=
    Subtype.ext (by push_cast; rfl)
  show CharPReduction.modularRedLocHom N A.toSubring red ⟨_, ht⟩ =
    ((redLoc T hT : modularFunctionFieldC k N) : LaurentSeries k) -
      ((algebraMap k (modularFunctionFieldC k N) (red a) : modularFunctionFieldC k N) : LaurentSeries k)
  rw [hmk, map_sub, pnN_modularRedLocHom_const, pnN_coe_algebraMap]
  rfl

private theorem coeffMap_qExpand_g {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ)
    [NeZero n] (x : LaurentSeries R) : coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext m
  by_cases hm : (n : ℤ) ∣ m
  · obtain ⟨c, rfl⟩ := hm
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd n _ hm, qExpand_coeff_of_not_dvd n _ hm, map_zero]

private theorem coeffEmb_jq_eq_jqModC_g :
    coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ) := by
  have hmap : jNumQ.map (algebraMap ℚ (AlgebraicClosure ℚ))
      = jNum.map (Int.castRingHom (AlgebraicClosure ℚ)) := by
    ext n
    simp [jNumQ, PowerSeries.coeff_map]
  rw [jq, jqModC, map_mul]
  congr 1
  · ext m
    rw [coeffEmb_coeff]
    by_cases hm : m = (-1 : ℤ) <;> simp [hm]
  · ext m
    rw [coeffEmb_coeff]
    by_cases hm : 0 ≤ m
    · lift m to ℕ using hm
      rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, ← hmap,
        PowerSeries.coeff_map]
    · rw [ofPowerSeries_coeff_of_neg _ (by omega), ofPowerSeries_coeff_of_neg _ (by omega), map_zero]

private theorem modularRing_le_bar_g (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ)) :
    CharPReduction.modularRing N A.toSubring ≤ (modularFunctionFieldBar N).toSubring := by
  rw [CharPReduction.modularRing, Subring.closure_le]
  rintro x (⟨a, rfl⟩ | rfl | rfl)
  · exact (modularFunctionFieldBar N).algebraMap_mem _
  · rw [← coeffEmb_jq_eq_jqModC_g]
    exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))
  · have h1 : jqNModC (AlgebraicClosure ℚ) N = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq) := by
      rw [jqNModC, ← coeffEmb_jq_eq_jqModC_g, coeffEmb, coeffMap_qExpand_g]
    rw [h1]
    exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (dvd_refl N))

private noncomputable def packA_g (A : ValuationSubring (AlgebraicClosure ℚ))
    (x : CharPReduction.integralCoeffs A.toSubring) : LaurentSeries A where
  coeff n := ⟨(x : LaurentSeries (AlgebraicClosure ℚ)).coeff n, x.2 n⟩
  isPWO_support' := (x : LaurentSeries (AlgebraicClosure ℚ)).isPWO_support.mono
    (fun _ hn h => hn (Subtype.ext h))

private theorem coeffMap_subtype_packA_g (A : ValuationSubring (AlgebraicClosure ℚ))
    (x : CharPReduction.integralCoeffs A.toSubring) :
    coeffMap A.subtype (packA_g A x) = (x : LaurentSeries (AlgebraicClosure ℚ)) := by
  ext n
  rfl

private theorem coeffMap_residue_packA_g (A : ValuationSubring (AlgebraicClosure ℚ)) (red : A →+* k)
    (x : CharPReduction.integralCoeffs A.toSubring) :
    coeffMap red (packA_g A x) = CharPReduction.coeffRed A.toSubring red x := by
  ext n
  rw [coeffMap_coeff, CharPReduction.coeffRed_coeff]
  rfl

private theorem integral_glue_g (x : CharPReduction.modularRing N A.toSubring) :
    ∃ h : heckeAlphaBar (AlgebraicClosure ℚ) N q (⟨x, modularRing_le_bar_g N A x.2⟩ : modularFunctionFieldBar N)
        ∈ R.R₁.integers,
      ((R.residue₁ ⟨_, h⟩ : modularFunctionFieldC k N) : LaurentSeries k) =
        CharPReduction.redRes A.toSubring red (CharPReduction.modularRing N A.toSubring)
          (CharPReduction.modularRing_le_integralCoeffs N A.toSubring) x := by
  set xI : CharPReduction.integralCoeffs A.toSubring :=
    ⟨x, CharPReduction.modularRing_le_integralCoeffs N A.toSubring x.2⟩ with hxI
  have hy : coeffMap A.subtype (packA_g A xI) ∈ modularFunctionFieldBar (N * q) := by
    rw [coeffMap_subtype_packA_g]
    have := (heckeAlphaBar (AlgebraicClosure ℚ) N q
      (⟨x, modularRing_le_bar_g N A x.2⟩ : modularFunctionFieldBar N)).2
    rwa [coe_heckeAlphaBar] at this
  obtain ⟨h, hres⟩ := R.residue₁_coeffMap (packA_g A xI) hy
  have hel : (⟨coeffMap A.subtype (packA_g A xI), hy⟩ : modularFunctionFieldBar (N * q)) =
      heckeAlphaBar (AlgebraicClosure ℚ) N q (⟨x, modularRing_le_bar_g N A x.2⟩ : modularFunctionFieldBar N) := by
    apply Subtype.ext
    rw [coe_heckeAlphaBar]
    exact coeffMap_subtype_packA_g A xI
  refine ⟨hel ▸ h, ?_⟩

  have key : ∀ (e : modularFunctionFieldBar (N * q))
      (_ : e = (⟨coeffMap A.subtype (packA_g A xI), hy⟩ : modularFunctionFieldBar (N * q)))
      (h' : e ∈ R.R₁.integers),
      ((R.R₁.residue ⟨e, h'⟩ : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :
        LaurentSeries (IsLocalRing.ResidueField A)) = coeffMap (IsLocalRing.residue A) (packA_g A xI) := by
    rintro e rfl h'
    exact hres
  have hres' := key _ hel.symm (hel ▸ h)
  show ((R.ι (R.R₁.residue ⟨_, hel ▸ h⟩) : modularFunctionFieldC k N) : LaurentSeries k) = _
  rw [R.ι_coe, hres', coeffMap_coeffMap]
  have hcomp : R.redBar.comp (IsLocalRing.residue A) = red := RingHom.ext R.redBar_residue
  rw [hcomp, coeffMap_residue_packA_g, CharPReduction.redRes_apply]

private theorem localized_mem_g (t : modularFunctionFieldBar N)
    (r s : CharPReduction.modularRing N A.toSubring)
    (hs : s ∉ CharPReduction.redKer A.toSubring red (CharPReduction.modularRing N A.toSubring)
      (CharPReduction.modularRing_le_integralCoeffs N A.toSubring))
    (hts : (t : LaurentSeries (AlgebraicClosure ℚ)) * s = r) :
    heckeAlphaBar (AlgebraicClosure ℚ) N q t ∈ R.R₁.integers := by
  obtain ⟨hr₁, -⟩ := integral_glue_g (red := red) R r
  obtain ⟨hs₁, hsres⟩ := integral_glue_g (red := red) R s
  have hsred : CharPReduction.redRes A.toSubring red (CharPReduction.modularRing N A.toSubring)
      (CharPReduction.modularRing_le_integralCoeffs N A.toSubring) s ≠ 0 :=
    CharPReduction.redRes_ne_zero_of_notMem hs
  have hsres₀ : R.R₁.residue ⟨_, hs₁⟩ ≠ 0 := by
    intro h0
    apply hsred
    rw [← hsres]
    show ((R.ι (R.R₁.residue ⟨_, hs₁⟩) : modularFunctionFieldC k N) : LaurentSeries k) = 0
    rw [h0, map_zero]
    rfl
  obtain ⟨b, hb⟩ := (R.R₁.isUnit_of_residue_ne_zero hsres₀).exists_right_inv

  have hb' : heckeAlphaBar (AlgebraicClosure ℚ) N q ⟨s, modularRing_le_bar_g N A s.2⟩ *
      (b : modularFunctionFieldBar (N * q)) = 1 := by
    have := congrArg (fun z : R.R₁.integers => (z : modularFunctionFieldBar (N * q))) hb
    simpa using this
  have hts' : t * (⟨s, modularRing_le_bar_g N A s.2⟩ : modularFunctionFieldBar N) =
      ⟨r, modularRing_le_bar_g N A r.2⟩ := Subtype.ext hts
  have hmul : heckeAlphaBar (AlgebraicClosure ℚ) N q t *
      heckeAlphaBar (AlgebraicClosure ℚ) N q ⟨s, modularRing_le_bar_g N A s.2⟩ =
      heckeAlphaBar (AlgebraicClosure ℚ) N q ⟨r, modularRing_le_bar_g N A r.2⟩ := by
    rw [← map_mul, hts']
  have ht_eq : heckeAlphaBar (AlgebraicClosure ℚ) N q t =
      heckeAlphaBar (AlgebraicClosure ℚ) N q ⟨r, modularRing_le_bar_g N A r.2⟩ *
        (b : modularFunctionFieldBar (N * q)) := by
    calc heckeAlphaBar (AlgebraicClosure ℚ) N q t
        = heckeAlphaBar (AlgebraicClosure ℚ) N q t *
            (heckeAlphaBar (AlgebraicClosure ℚ) N q ⟨s, modularRing_le_bar_g N A s.2⟩ *
              (b : modularFunctionFieldBar (N * q))) := by rw [hb', mul_one]
      _ = _ := by rw [← mul_assoc, hmul]
  rw [ht_eq]
  exact mul_mem hr₁ b.2

private theorem localized_res_g (t : modularFunctionFieldBar N)
    (r s : CharPReduction.modularRing N A.toSubring)
    (hs : s ∉ CharPReduction.redKer A.toSubring red (CharPReduction.modularRing N A.toSubring)
      (CharPReduction.modularRing_le_integralCoeffs N A.toSubring))
    (hts : (t : LaurentSeries (AlgebraicClosure ℚ)) * s = r)
    (hmem : heckeAlphaBar (AlgebraicClosure ℚ) N q t ∈ R.R₁.integers) :
    R.residue₁ ⟨_, hmem⟩ = redLoc t ⟨r, s, hs, hts⟩ := by
  obtain ⟨hr₁, hrres⟩ := integral_glue_g (red := red) R r
  obtain ⟨hs₁, hsres⟩ := integral_glue_g (red := red) R s
  have hsred : CharPReduction.redRes A.toSubring red (CharPReduction.modularRing N A.toSubring)
      (CharPReduction.modularRing_le_integralCoeffs N A.toSubring) s ≠ 0 :=
    CharPReduction.redRes_ne_zero_of_notMem hs
  have hts' : t * (⟨s, modularRing_le_bar_g N A s.2⟩ : modularFunctionFieldBar N) =
      ⟨r, modularRing_le_bar_g N A r.2⟩ := Subtype.ext hts
  have hprod : (⟨_, hmem⟩ : R.R₁.integers) * ⟨_, hs₁⟩ = ⟨_, hr₁⟩ := by
    apply Subtype.ext
    show heckeAlphaBar (AlgebraicClosure ℚ) N q t * heckeAlphaBar (AlgebraicClosure ℚ) N q _ =
      heckeAlphaBar (AlgebraicClosure ℚ) N q _
    rw [← map_mul, hts']
  have hres_mul : R.residue₁ ⟨_, hmem⟩ * R.residue₁ ⟨_, hs₁⟩ = R.residue₁ ⟨_, hr₁⟩ := by
    rw [← map_mul, hprod]
  have hL : ((R.residue₁ ⟨_, hmem⟩ : modularFunctionFieldC k N) : LaurentSeries k) *
      CharPReduction.redRes A.toSubring red (CharPReduction.modularRing N A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs N A.toSubring) s =
      CharPReduction.redRes A.toSubring red (CharPReduction.modularRing N A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs N A.toSubring) r := by
    rw [← hsres, ← hrres, ← hres_mul]
    push_cast
    rfl
  have hR : ((redLoc t ⟨r, s, hs, hts⟩ : modularFunctionFieldC k N) : LaurentSeries k) *
      CharPReduction.redRes A.toSubring red (CharPReduction.modularRing N A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs N A.toSubring) s =
      CharPReduction.redRes A.toSubring red (CharPReduction.modularRing N A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs N A.toSubring) r := by
    have h0 := CharPReduction.redLoc_spec (A := A.toSubring) (red := red)
      (R := CharPReduction.modularRing N A.toSubring)
      (hR := CharPReduction.modularRing_le_integralCoeffs N A.toSubring) ⟨_, ⟨r, s, hs, hts⟩⟩ hts
    exact h0
  apply Subtype.ext
  exact mul_right_cancel₀ hsred (hL.trans hR.symm)

private theorem localized_glue_g (t : modularFunctionFieldBar N)
    (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized N A.toSubring red) :
    ∃ h : heckeAlphaBar (AlgebraicClosure ℚ) N q t ∈ R.R₁.integers,
      R.residue₁ ⟨_, h⟩ = redLoc t ht := by
  obtain ⟨r, s, hs, hts⟩ := ht
  exact ⟨localized_mem_g R t r s hs hts, localized_res_g R t r s hs hts _⟩

section GenericInduction
variable {F : Type*} [Field F] [Algebra (AlgebraicClosure ℚ) F] {E : Type*} [Field E] [Algebra k E]
open Classical in

private theorem penA_mapDomain_filter_apply (r : Place (AlgebraicClosure ℚ) F → Place k E)
    (S : Place (AlgebraicClosure ℚ) F → Prop) (D : Divisor (AlgebraicClosure ℚ) F) (v : Place k E) :
    Finsupp.mapDomain r (D.filter S) v = ∑ W ∈ D.support with (S W ∧ r W = v), D W := by
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum, Finsupp.support_filter, Finset.sum_filter,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun W _ => ?_
  simp only [Finsupp.single_apply, Finsupp.filter_apply]
  by_cases hS : S W <;> by_cases hr : r W = v <;> simp [hS, hr]

open Classical in

private theorem penA_lsc_sum_le_of_slots (𝒪 : ValuationSubring F) (ρ : 𝒪 →+* E)
    (hker : ∀ x : 𝒪, ρ x ≠ 0 → IsUnit x)
    (r : Place (AlgebraicClosure ℚ) F → Place k E) (S : Place (AlgebraicClosure ℚ) F → Prop) (v : Place k E)
    (hE : ∀ (f : F) (h : f ∈ 𝒪), (∀ W, S W → r W = v → 0 ≤ W.ord f) → 0 ≤ v.ord (ρ ⟨f, h⟩))
    (hP : ∀ Q, S Q → r Q = v → ∃ (s : F) (hs : s ∈ 𝒪),
      Q.ord s = 1 ∧ (∀ W, S W → r W = v → W ≠ Q → W.ord s = 0) ∧ v.ord (ρ ⟨s, hs⟩) = 1)
    (f : F) (h : f ∈ 𝒪) (hr : ρ ⟨f, h⟩ ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) F) (hD : ∀ W, D W = W.ord f)
    (hreg : ∀ W, S W → r W = v → 0 ≤ D W) :
    Finsupp.mapDomain r (D.filter S) v ≤ v.ord (ρ ⟨f, h⟩) := by
  suffices H : ∀ n : ℕ, ∀ (f : F) (h : f ∈ 𝒪), ρ ⟨f, h⟩ ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) F,
        (∀ W, S W → r W = v → D W = W.ord f) → (∀ W, S W → r W = v → 0 ≤ D W) →
        Finsupp.mapDomain r (D.filter S) v = n → (n : ℤ) ≤ v.ord (ρ ⟨f, h⟩) by
    have hnn : 0 ≤ Finsupp.mapDomain r (D.filter S) v := by
      rw [penA_mapDomain_filter_apply]
      exact Finset.sum_nonneg fun W hW =>
        hreg W (Finset.mem_filter.mp hW).2.1 (Finset.mem_filter.mp hW).2.2
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hnn
    rw [hn]
    exact H n f h hr D (fun W _ _ => hD W) hreg hn
  intro n
  induction n with
  | zero =>
    intro f h _ D hD hreg _
    exact_mod_cast hE f h fun W hW hWv => (hD W hW hWv) ▸ hreg W hW hWv
  | succ n ih =>
    intro f h hr D hD hreg hn
    obtain ⟨Q, hQmem, hQpos⟩ : ∃ Q ∈ D.support.filter (fun W => S W ∧ r W = v), 0 < D Q := by
      by_contra hcon
      simp only [not_exists, not_and, not_lt] at hcon
      have hle : ∑ W ∈ D.support with (S W ∧ r W = v), D W ≤ 0 := Finset.sum_nonpos hcon
      rw [← penA_mapDomain_filter_apply, hn] at hle
      omega
    obtain ⟨-, hSQ, hrQ⟩ := Finset.mem_filter.mp hQmem
    obtain ⟨s, hs, hsQ, hsW, hsv⟩ := hP Q hSQ hrQ
    have hρs : ρ ⟨s, hs⟩ ≠ 0 := fun h0 => by rw [h0, Place.ord_zero] at hsv; exact zero_ne_one hsv
    obtain ⟨τ, hut⟩ := (hker ⟨s, hs⟩ hρs).exists_right_inv
    have hst : s * (τ : F) = 1 := congrArg Subtype.val hut
    have hs0 : s ≠ 0 := left_ne_zero_of_mul_eq_one hst
    have hτ0 : (τ : F) ≠ 0 := right_ne_zero_of_mul_eq_one hst
    have hf0 : f ≠ 0 := by
      rintro rfl
      exact hr (by rw [show (⟨(0 : F), h⟩ : 𝒪) = 0 from Subtype.ext rfl, map_zero])
    have hg : f * (τ : F) ∈ 𝒪 := mul_mem h τ.2
    have hρg : ρ ⟨f * τ, hg⟩ = ρ ⟨f, h⟩ * ρ τ := by rw [← map_mul]; rfl
    have hρτ : ρ ⟨s, hs⟩ * ρ τ = 1 := by rw [← map_mul, hut, map_one]
    have hρτ0 : ρ τ ≠ 0 := right_ne_zero_of_mul_eq_one hρτ
    have hordτ : v.ord (ρ τ) = -1 := by
      have h1 := v.ord_mul hρs hρτ0
      rw [hρτ, Place.ord_one, hsv] at h1
      omega
    have hρg0 : ρ ⟨f * τ, hg⟩ ≠ 0 := by rw [hρg]; exact mul_ne_zero hr hρτ0
    have hordg : v.ord (ρ ⟨f * τ, hg⟩) = v.ord (ρ ⟨f, h⟩) - 1 := by
      rw [hρg, v.ord_mul hr hρτ0, hordτ]; ring
    have hordτW : ∀ W : Place (AlgebraicClosure ℚ) F, W.ord (τ : F) = -W.ord s := by
      intro W
      have h1 := W.ord_mul hs0 hτ0
      rw [hst, Place.ord_one] at h1
      omega
    set D' : Divisor (AlgebraicClosure ℚ) F := D - Finsupp.single Q (1 : ℤ) with hD'def
    have hD' : ∀ W, S W → r W = v → D' W = W.ord (f * τ) := by
      intro W hW hWv
      rw [hD'def, Finsupp.sub_apply, W.ord_mul hf0 hτ0, hordτW W, ← hD W hW hWv, Finsupp.single_apply]
      by_cases hQW : Q = W
      · subst hQW; rw [if_pos rfl, hsQ]; omega
      · rw [if_neg hQW, hsW W hW hWv (Ne.symm hQW)]; simp
    have hreg' : ∀ W, S W → r W = v → 0 ≤ D' W := by
      intro W hW hWv
      rw [hD'def, Finsupp.sub_apply, Finsupp.single_apply]
      by_cases hQW : Q = W
      · subst hQW; simp; omega
      · rw [if_neg hQW]; simpa using hreg W hW hWv
    have hn' : Finsupp.mapDomain r (D'.filter S) v = n := by
      have h1 : Finsupp.mapDomain r
          ((Finsupp.single Q (1 : ℤ) : Divisor (AlgebraicClosure ℚ) F).filter S) v = 1 := by
        simp [Finsupp.filter_single_of_pos, hSQ, hrQ]
      rw [hD'def, Finsupp.filter_sub, Finsupp.mapDomain_sub, Finsupp.sub_apply, hn, h1]
      push_cast; ring
    have hih := ih (f * τ) hg hρg0 D' hD' hreg' hn'
    rw [hordg] at hih
    push_cast
    omega

end GenericInduction

private theorem penC_ramification_alpha_pos (h : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    0 < W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) := by
  letI := algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q)
  haveI := isScalarTower_along (heckeAlphaBar (AlgebraicClosure ℚ) N q)
  haveI := isIntegral_along (heckeAlphaBar (AlgebraicClosure ℚ) N q) h
  exact Place.ramificationIndex_pos (F := modularFunctionFieldBar N) W

private theorem penC_heckeAlphaBar_jN :
    heckeAlphaBar (AlgebraicClosure ℚ) N q
        (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
      = ProlongationTuple.jFun N q := by
  exact Subtype.ext (coe_heckeAlphaBar N q _)

private theorem penC_ord_jN_sub_nonpos_of_isCuspidal
    {Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))}
    (hQ : ProlongationTuple.IsCuspidal P Q) (a : A) :
    (Q.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα).ord
        ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)) ≤ 0 := by
  have hup : Q.ord (ProlongationTuple.jFun N q
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)) ≤ 0 := hQ a
  have hpull : heckeAlphaBar (AlgebraicClosure ℚ) N q
      ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ))
      = ProlongationTuple.jFun N q
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) := by
    rw [map_sub, AlgHom.commutes, penC_heckeAlphaBar_jN]
  rw [← hpull, Place.ord_restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα Q] at hup
  have he : (0 : ℤ) < (Q.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) := by
    exact_mod_cast penC_ramification_alpha_pos hα Q
  by_contra hx
  exact absurd hup (not_le.mpr (mul_pos he (not_le.mp hx)))

private theorem penC_split (hqN : ¬ q ∣ N) {v : Place k (modularFunctionFieldC k N)}
    (hv : ∃ c, ProlongationTuple.IsInftySide P c ∧ P.reduceFst c = v)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hW : P.reduceFst W = v) :
    ProlongationTuple.IsInftySide P W ∨ ProlongationTuple.IsZeroSide P W := by
  obtain ⟨c, hc, hcv⟩ := hv
  obtain ⟨hcc, -⟩ := id hc
  have hna : ¬ IsAffineGeomPlace k N v := by
    rw [← hcv]
    exact ProlongationTuple.not_isAffineGeomPlace_reduceFst_of_isCuspidal P c hcc
  have hWc : ProlongationTuple.IsCuspidal P W :=
    ProlongationTuple.isCuspidal_of_not_isAffineGeomPlace_reduceFst P W (by rw [hW]; exact hna)
  exact ProlongationTuple.isInftySide_or_isZeroSide_of_isCuspidal P hqN W hWc

section LocalSet

variable {v : Place k (modularFunctionFieldC k N)} {S : Set (modularFunctionFieldBar (N * q))}

private theorem penC_chartLocalSetFst_subset_integers (hint : ∀ s ∈ S, s ∈ R.R₁.integers)
    {f : modularFunctionFieldBar (N * q)} (hf : f ∈ chartLocalSetFst R v S) : f ∈ R.R₁.integers := by
  obtain ⟨g, u, hg, hu, hu₁, hu0, hfu⟩ := hf
  have hle : chartClosure S ≤ R.R₁.integers.toSubring :=
    Subring.closure_le.mpr fun s hs => hint s hs
  have hgI : g ∈ R.R₁.integers := hle hg
  have hres0 : (R.ι.comp R.R₁.residue) ⟨u, hu₁⟩ ≠ 0 := by
    intro h0
    apply hu0
    have h00 : v.HasValue (0 : modularFunctionFieldC k N) 0 := by
      simpa using v.hasValue_algebraMap (0 : k)
    have : R.residue₁ ⟨u, hu₁⟩ = 0 := h0
    rw [this]; exact h00
  obtain ⟨τ, hut⟩ := (penA_isUnit_of_residue_ne_zero R.R₁ R.ι ⟨u, hu₁⟩ hres0).exists_right_inv
  have hut' : u * (τ : modularFunctionFieldBar (N * q)) = 1 := congrArg Subtype.val hut
  have hfg : f = g * τ := by rw [← hfu, mul_assoc, hut', mul_one]
  rw [hfg]
  exact mul_mem hgI τ.2

private theorem penC_residue₁_mem_of_mem_chartClosure (hint : ∀ s ∈ S, s ∈ R.R₁.integers)
    (hregv : ∀ (s : modularFunctionFieldBar (N * q)) (hs : s ∈ S),
      (R.residue₁ ⟨s, hint s hs⟩ : modularFunctionFieldC k N) ∈ v.toValuationSubring)
    {g : modularFunctionFieldBar (N * q)} (hg : g ∈ chartClosure S) (hgI : g ∈ R.R₁.integers) :
    (R.residue₁ ⟨g, hgI⟩ : modularFunctionFieldC k N) ∈ v.toValuationSubring := by
  have hST : S ⊆ ((v.toValuationSubring.toSubring.comap R.residue₁).map R.R₁.integers.subtype :
      Set (modularFunctionFieldBar (N * q))) := by
    intro s hs
    rw [SetLike.mem_coe, Subring.mem_map]
    exact ⟨⟨s, hint s hs⟩, (Subring.mem_comap).mpr (hregv s hs), rfl⟩
  have hgT := (Subring.closure_le.mpr hST) hg
  rw [Subring.mem_map] at hgT
  obtain ⟨y, hy, hyg⟩ := hgT
  rw [Subring.mem_comap] at hy
  have hyg' : (⟨g, hgI⟩ : R.R₁.integers) = y := Subtype.ext hyg.symm
  rw [hyg']
  exact hy

private theorem penC_residue₁_mem_of_mem_chartLocalSetFst (hint : ∀ s ∈ S, s ∈ R.R₁.integers)
    (hregv : ∀ (s : modularFunctionFieldBar (N * q)) (hs : s ∈ S),
      (R.residue₁ ⟨s, hint s hs⟩ : modularFunctionFieldC k N) ∈ v.toValuationSubring)
    {f : modularFunctionFieldBar (N * q)} (hf : f ∈ chartLocalSetFst R v S) :
    (R.residue₁ ⟨f, penC_chartLocalSetFst_subset_integers R hint hf⟩ : modularFunctionFieldC k N) ∈
      v.toValuationSubring := by
  obtain ⟨g, u, hg, hu, hu₁, hu0, hfu⟩ := hf
  have hfI : f ∈ R.R₁.integers :=
    penC_chartLocalSetFst_subset_integers R hint ⟨g, u, hg, hu, hu₁, hu0, hfu⟩
  have hgI : g ∈ R.R₁.integers :=
    (Subring.closure_le.mpr (fun s hs => hint s hs) : chartClosure S ≤ R.R₁.integers.toSubring) hg
  have hrg : (R.residue₁ ⟨g, hgI⟩ : modularFunctionFieldC k N) ∈ v.toValuationSubring :=
    penC_residue₁_mem_of_mem_chartClosure R hint hregv hg hgI
  have hru : (R.residue₁ ⟨u, hu₁⟩ : modularFunctionFieldC k N) ∈ v.toValuationSubring :=
    penC_residue₁_mem_of_mem_chartClosure R hint hregv hu hu₁
  have hunit : IsUnit (⟨R.residue₁ ⟨u, hu₁⟩, hru⟩ : v.toValuationSubring) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    intro h0
    exact hu0 ⟨hru, by rw [h0, map_zero]⟩
  obtain ⟨w, hw⟩ := hunit.exists_right_inv
  have hw' : R.residue₁ ⟨u, hu₁⟩ * (w : modularFunctionFieldC k N) = 1 := congrArg Subtype.val hw
  have hmul : R.residue₁ ⟨f, hfI⟩ * R.residue₁ ⟨u, hu₁⟩ = R.residue₁ ⟨g, hgI⟩ := by
    rw [← map_mul]; congr 1; exact Subtype.ext hfu
  have hf' : R.residue₁ ⟨f, hfI⟩ = R.residue₁ ⟨g, hgI⟩ * (w : modularFunctionFieldC k N) := by
    rw [← hmul, mul_assoc, hw', mul_one]
  show (R.residue₁ ⟨f, hfI⟩ : modularFunctionFieldC k N) ∈ v.toValuationSubring
  rw [hf']
  exact mul_mem hrg w.2

end LocalSet

private structure penC_ChartAt (v : Place k (modularFunctionFieldC k N))
    (S : Set (modularFunctionFieldBar (N * q))) : Prop where
  hint : ∀ s ∈ S, s ∈ R.R₁.integers
  hregv : ∀ (s : modularFunctionFieldBar (N * q)) (hs : s ∈ S),
    (R.residue₁ ⟨s, hint s hs⟩ : modularFunctionFieldC k N) ∈ v.toValuationSubring
  hregOver : ∀ s ∈ S, ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
    P.reduceFst W = v → s ∈ W.toValuationSubring
  hnIncl : ∀ φ : modularFunctionFieldBar N,
    heckeAlphaBar (AlgebraicClosure ℚ) N q φ ∈ R.R₁.integers →
    (∀ u₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), P.sp u₀ = v → φ ∈ u₀.toValuationSubring) →
    ∃ (s : modularFunctionFieldBar (N * q)) (_ : s ∈ S) (e : modularFunctionFieldBar (N * q)) (he : e ∈ S),
      ¬ v.HasValue (R.residue₁ ⟨e, hint e he⟩) (0 : k) ∧ heckeAlphaBar (AlgebraicClosure ℚ) N q φ * e = s
  hE : ChartEtaleAt R v S
  hsep : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
    ProlongationTuple.IsZeroSide P W → P.reduceFst W = v →
      ∃ (u : modularFunctionFieldBar (N * q)) (hu : u ∈ S),
        ¬ v.HasValue (R.residue₁ ⟨u, hint u hu⟩) (0 : k) ∧ 0 < W.ord u

private theorem penC_poleFree_inf (hqN : ¬ q ∣ N) {v : Place k (modularFunctionFieldC k N)}
    (hv : ∃ c, ProlongationTuple.IsInftySide P c ∧ P.reduceFst c = v)
    {S : Set (modularFunctionFieldBar (N * q))} (hS : penC_ChartAt R v S)
    (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers)
    (hreg : ∀ W, ProlongationTuple.IsInftySide P W → P.reduceFst W = v → 0 ≤ W.ord f) :
    0 ≤ v.ord (R.residue₁ ⟨f, h₁⟩) := by
  have hmem : f ∈ chartLocalSetFst R v S :=
    mem_chartLocalSetFst_of_split R hqN hS.hint hS.hregv hS.hregOver hS.hnIncl hS.hE
      (good := ProlongationTuple.IsInftySide P) (bad := ProlongationTuple.IsZeroSide P)
      (penC_split hqN hv) hS.hsep f h₁ hreg
  exact v.ord_nonneg_of_mem_pn (penC_residue₁_mem_of_mem_chartLocalSetFst R hS.hint hS.hregv hmem)

private theorem penC_sectionN (hsp : ReducesDivisors P) (hcoord : HasCoordinates P)
    {v : Place k (modularFunctionFieldC k N)}
    {u : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)} (hu : P.sp u = v) :
    ∃ (t : modularFunctionFieldBar N)
      (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized N A.toSubring red),
      redLoc t ht ≠ 0 ∧
      u.ord t = 1 ∧
      (∀ u' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), P.sp u' = v → u' ≠ u → u'.ord t = 0) ∧
      v.ord (redLoc t ht) = 1 := by
  classical
  obtain ⟨T, hT, hmem, ⟨c, hc⟩, hval⟩ := hcoord v
  have hfr : fibreReduction T hT hmem = redLoc T hT := rfl
  rw [hfr] at hc
  simp only [hfr] at hval
  obtain ⟨a, hua, hva⟩ := hval u hu
  have hac : red a = c :=
    (v.hasValue_of_ord_sub_pos_pn hva).unique (v.hasValue_of_ord_sub_pos_pn (by omega))
  have ht : ((T - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ) :
        modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized N A.toSubring red := by
    push_cast
    exact sub_mem hT (pnN_const_mem a)
  have hred : redLoc _ ht = redLoc T hT - algebraMap k (modularFunctionFieldC k N) c := by
    rw [pnN_redLoc_sub_const T hT a ht, hac]
  have h4 : v.ord (redLoc _ ht) = 1 := by rw [hred]; exact hc
  have hne : redLoc _ ht ≠ 0 := v.ne_zero_of_ord_pos_pn (by omega)
  refine ⟨T - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ), ht, hne,
    ?_⟩
  have hnn : ∀ u' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), P.sp u' = v →
      0 ≤ u'.ord (T - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)) := by
    intro u' hu'
    obtain ⟨a', hua', -⟩ := hval u' hu'
    have hmem' : T - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a' : AlgebraicClosure ℚ) ∈
        u'.toValuationSubring :=
      u'.mem_of_ord_nonneg_pn (u'.ne_zero_of_ord_pos_pn hua') hua'.le
    have hTmem : T ∈ u'.toValuationSubring := by
      have h' := add_mem hmem' (u'.algebraMap_mem' (a' : AlgebraicClosure ℚ))
      rwa [sub_add_cancel] at h'
    exact u'.ord_nonneg_of_mem_pn (sub_mem hTmem (u'.algebraMap_mem' _))
  have ht0 : T - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ) ≠ 0 :=
    u.ne_zero_of_ord_pos_pn hua
  obtain ⟨D, hD, -⟩ := (hasPrincipalDivisors_modularFunctionFieldBar_unconditional N).exists_divisor _ ht0
  have hne' : CharPReduction.modularRedLocHom N A.toSubring red ⟨_, ht⟩ ≠ 0 := by
    intro h0
    apply hne
    apply Subtype.ext
    rw [ZeroMemClass.coe_zero]
    exact h0
  have hlaw : Finsupp.mapDomain P.sp D v = v.ord (redLoc _ ht) :=
    hsp _ ht (CharPReduction.modularRedLocHom_mem A.toSubring red N ⟨_, ht⟩) hne' D hD v
  let g : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → ℤ :=
    fun u' => if P.sp u' = v then D u' else 0
  have hgnn : ∀ u', 0 ≤ g u' := by
    intro u'
    show 0 ≤ (if P.sp u' = v then D u' else 0)
    split_ifs with h1
    · rw [hD]; exact hnn u' h1
    · exact le_refl _
  have hsum : ∑ u' ∈ D.support, g u' = 1 := by
    rw [← h4, ← hlaw]
    unfold Finsupp.mapDomain
    rw [Finsupp.sum_apply, Finsupp.sum]
    apply Finset.sum_congr rfl
    intro u' _
    simp only [g, Finsupp.single_apply]
  have hgu : g u = u.ord (T - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
      (a : AlgebraicClosure ℚ)) := by
    show (if P.sp u = v then D u else 0) = _
    rw [if_pos hu, hD]
  have humem : u ∈ D.support := by
    rw [Finsupp.mem_support_iff, hD]; exact ne_of_gt hua
  have h2 : u.ord (T - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)) = 1 := by
    have h1 := Finset.single_le_sum (f := g) (s := D.support) (fun u' _ => hgnn u') humem
    rw [hsum, hgu] at h1
    omega
  refine ⟨h2, ?_, h4⟩
  intro u' hu' hne_u
  by_cases hsupp : u' ∈ D.support
  · have hsub : ({u, u'} : Finset _) ⊆ D.support := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact humem
      · exact hsupp
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hgnn x)
    rw [Finset.sum_pair (Ne.symm hne_u), hsum, hgu, h2] at hle
    have hgu' : g u' = u'.ord (T - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
        (a : AlgebraicClosure ℚ)) := by
      show (if P.sp u' = v then D u' else 0) = _
      rw [if_pos hu', hD]
    have h0 := hgnn u'
    rw [hgu'] at hle h0
    omega
  · rw [← hD]
    exact Finsupp.notMem_support_iff.mp hsupp

open Classical in

private theorem penC_section_inf
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))]
    (hsp : ReducesDivisors P) (hcoord : HasCoordinates P)
    (hlab : ∀ b : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ a : A, b.ord
        ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)) ≤ 0) →
      (∑ W ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b).filter
          (ProlongationTuple.IsInftySide P),
        (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ)) = 1)
    {v : Place k (modularFunctionFieldC k N)}
    {Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))}
    (hQ : ProlongationTuple.IsInftySide P Q) (hQv : P.reduceFst Q = v) :
    ∃ (s : modularFunctionFieldBar (N * q)) (hs : s ∈ R.R₁.integers),
      Q.ord s = 1 ∧
      (∀ W, ProlongationTuple.IsInftySide P W → P.reduceFst W = v → W ≠ Q → W.ord s = 0) ∧
      v.ord (R.residue₁ ⟨s, hs⟩) = 1 := by
  obtain ⟨hQc, -⟩ := id hQ
  have hone := hlab (Q.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα)
    (fun a => penC_ord_jN_sub_nonpos_of_isCuspidal hQc a)
  have hpos : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      (0 : ℤ) < (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) := fun W => by
    exact_mod_cast penC_ramification_alpha_pos hα W
  have hQmem : Q ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα
      (Q.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα)).filter
        (ProlongationTuple.IsInftySide P) := by
    rw [Finset.mem_filter, Place.mem_fiberAlong]
    exact ⟨rfl, hQ⟩

  have heQ : (Q.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) = 1 := by
    have h1 : (Q.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) ≤ 1 := by
      have h := Finset.single_le_sum
        (f := fun W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) =>
          (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ))
        (fun W _ => (hpos W).le) hQmem
      rwa [hone] at h
    have h2 := hpos Q
    omega

  have huniq : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      ProlongationTuple.IsInftySide P W →
      W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα =
        Q.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα → W = Q := by
    intro W hW hWb
    by_contra hne
    have hWmem : W ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα
        (Q.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα)).filter
          (ProlongationTuple.IsInftySide P) := by
      rw [Finset.mem_filter, Place.mem_fiberAlong]
      exact ⟨hWb, hW⟩
    have hsub : ({Q, W} : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) ⊆
        (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα
          (Q.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα)).filter
            (ProlongationTuple.IsInftySide P) := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hQmem
      · exact hWmem
    have hle : (Q.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) +
        (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) ≤ 1 := by
      have h := Finset.sum_le_sum_of_subset_of_nonneg
        (f := fun W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) =>
          (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ))
        hsub (fun x _ _ => (hpos x).le)
      rwa [Finset.sum_pair (Ne.symm hne), hone] at h
    have h3 := hpos W
    omega

  obtain ⟨t, ht, -, hQt, hothers, hvt⟩ :=
    penC_sectionN hsp hcoord (u := Q.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα) hQv
  obtain ⟨hs, hres⟩ := localized_glue_g R t ht
  refine ⟨heckeAlphaBar (AlgebraicClosure ℚ) N q t, hs, ?_, ?_, ?_⟩
  · rw [Place.ord_restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα Q t, hQt, heQ, mul_one]
  · intro W hW hWv hWQ
    rw [Place.ord_restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα W t]
    have hWb : W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα ≠
        Q.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα :=
      fun h => hWQ (huniq W hW h)
    rw [hothers _ hWv hWb, mul_zero]
  · rw [hres]
    exact hvt

open Classical in

private theorem penC_inftyBound_of_charts
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))]
    (hqN : ¬ q ∣ N) (hsp : ReducesDivisors P) (hcoord : HasCoordinates P)
    (hcharts : ∀ v : Place k (modularFunctionFieldC k N),
      (∃ c, ProlongationTuple.IsInftySide P c ∧ P.reduceFst c = v) →
      ∃ S : Set (modularFunctionFieldBar (N * q)), penC_ChartAt R v S)
    (hlab : ∀ b : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ a : A, b.ord
        ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)) ≤ 0) →
      (∑ W ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b).filter
          (ProlongationTuple.IsInftySide P),
        (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ)) = 1) :
    penC_InftyBound R := by
  intro f h₁ hr₁ D hD v hv hpos
  obtain ⟨S, hS⟩ := hcharts v hv
  have hr₁' : R.residue₁ ⟨f, h₁⟩ ≠ 0 := by
    simpa [ProlongationTuple.residue₁_apply] using (map_ne_zero R.ι).mpr hr₁
  exact penA_lsc_sum_le_of_slots R.R₁.integers R.residue₁ (penA_isUnit_of_residue_ne_zero R.R₁ R.ι)
    P.reduceFst (ProlongationTuple.IsInftySide P) v
    (fun g hg hreg => penC_poleFree_inf R hqN hv hS g hg hreg)
    (fun Q hQ hQv => penC_section_inf R hsp hcoord hlab hQ hQv)
    f h₁ hr₁' D hD hpos

end ModularCurve.PlaceSpecialization

end NR3_40_inftybound

section NR3_50_package

section
open AlgebraicCurve Polynomial

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_qExpand jNum jNumQ jq ofPowerSeries_coeff_of_neg coeff_jq_neg_one jqN evalAtJ evalAtJ_X ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffMap_algebraMap coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_eq_map_intCast modularFunctionFieldC jqModC_mem jqNModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff KroneckerCongruence ssPlaces jGeomGen jNGeomGen IsAffineGeomPlace cuspInftyGeom ord_cuspInftyGeom_jq order_jqModC_def jqModC_ne_zero_def jq_mem_full coeff_jqModC_neg_one coeffSemilinearAut.coeffMap_qExpand coeffSemilinearAut.coeffMap_jqModC coeffSemilinearAut.coeffMap_mem_modularFunctionFieldC coeffSemilinearAut arithFrobC isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_jqModC qExpandAlgHomC qExpandAlgHomC_apply divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full jqModC_mem_full coeffMap_qExpand CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.mem_localizedAtKer CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc CharPReduction.redRes_ne_zero_of_notMem CharPReduction.redLoc_spec CharPReduction.redLoc_coe CharPReduction.redLocHom_apply CharPReduction.constSeries CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.affineBaseFin CharPModel.affineBaseInf CharPModel.FibreModel modularFunctionFieldBar_eq_modularFunctionFieldC finiteAlong_heckeAlphaBar_of_prime isCurveOver_modularFunctionFieldBar arithFrobC_smul_eq_frobOnPlacesGeomLevel CharPReduction.modularRedLocHom_mem exists_mem_riemannRochSpace_notMem_sub_single_of_le_degree isAffineGeomPlace_frobOnPlacesGeomLevel coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized_mul_of_not_dvd coeffEmb_jq exists_isAtkinLehnerAutFull_of_prime_of_not_dvd exists_regularProlongation_modularFunctionFieldBar_mul_of_not_dvd geomAut_atkinLehner_comp_legs hasPrincipalDivisors_modularFunctionFieldBar_unconditional place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin finrankAlong_heckeBetaBar CharPModel.FibreModel.piFin_range_localizes_of_jqModC_mem CharPModel.exists_monic_eval2_affineBaseFin_eq_zero_of_mem_modularLocalized_of_forall_mem_of_jBar_mem arithFrobC_smul_mem_ssPlaces_univ adjoin_jBar_jNBar_eq_top nonempty_modularPolynomialData relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi CharPReduction.mem_or_inv_mem_modularLocalized pow_char_eq_coeffMap_frobenius_qExpand qExpand_jqModC_eq_pow_unconditional mem_integralCoeffs_of_integral_affineBaseInf CharPModel.exists_monic_eval2_affineBaseInf_eq_zero_of_mem_modularLocalized_of_forall_inv_jBar_mem"
namespace AlphaEngine
p2m_open "ModularCurve~jBar"

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fb₁ Fb₂ : Type*} [Field Fb₁] [Field Fb₂]
  [Algebra (IsLocalRing.ResidueField A) Fb₁] [Algebra (IsLocalRing.ResidueField A) Fb₂]
variable (R₁ : RegularProlongation A F Fb₁) (R₂ : RegularProlongation A F Fb₂)

section Coordinates

variable {E : IntermediateField L F} (hE₂ : ∀ e ∈ E, e ∈ R₁.integers → e ∈ R₂.integers)
  (σ : Fb₁ →+* Fb₂)
  (hσ : ∀ e (he : e ∈ E) (h₁ : e ∈ R₁.integers), R₂.residue ⟨e, hE₂ e he h₁⟩ = σ (R₁.residue ⟨e, h₁⟩))
  {q : ℕ} (hq : q.Prime) [CharP Fb₂ q] (hpi : ∀ y : Fb₂, y ^ q ∈ σ.range)
  {z : F} (hz₁ : z ∈ R₁.integers) (hz₂ : z ∈ R₂.integers)
  (hzr₂ : R₂.residue ⟨z, hz₂⟩ ∉ σ.range)

include hσ hq hpi hz₁ hzr₂ in

private theorem residue_coeff_eq_zero_of_residues_eq_zero (γ : Fin (q + 1) → F) (hγE : ∀ i, γ i ∈ E)
    (hγ₁ : ∀ i, γ i ∈ R₁.integers) {θ : F} (hθ : θ = ∑ i, γ i * z ^ (i : ℕ))
    (hθ₁ : θ ∈ R₁.integers) (hθ₂ : θ ∈ R₂.integers)
    (h₁ : R₁.residue ⟨θ, hθ₁⟩ = 0) (h₂ : R₂.residue ⟨θ, hθ₂⟩ = 0) :
    ∀ i, R₁.residue ⟨γ i, hγ₁ i⟩ = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, (Nat.succ_pred_eq_of_pos hq.pos).symm⟩

  obtain ⟨η, hη⟩ := RingHom.mem_range.mp (hpi (R₂.residue ⟨z, hz₂⟩))
  haveI : Fact (m + 1).Prime := ⟨hq⟩
  have hfrob : ∀ a b : Fb₂, a ^ (m + 1) = b ^ (m + 1) → a = b := by
    intro a b hab
    have h : (a - b) ^ (m + 1) = a ^ (m + 1) - b ^ (m + 1) := by rw [sub_pow_char]
    rw [hab, sub_self] at h
    exact sub_eq_zero.mp (pow_eq_zero_iff (Nat.succ_ne_zero m) |>.mp h)
  have hηq : ∀ b : Fb₁, b ^ (m + 1) ≠ η := by
    intro b hb
    apply hzr₂
    refine RingHom.mem_range.mpr ⟨b, hfrob _ _ ?_⟩
    rw [← map_pow, hb, hη]
  have hζ : R₁.residue ⟨z, hz₁⟩ ^ (m + 1) ≠ η := by
    intro hc
    apply hzr₂
    refine RingHom.mem_range.mpr ⟨R₁.residue ⟨z, hz₁⟩, hfrob _ _ ?_⟩
    rw [← map_pow, hc, hη]
  set xb := η with hxb
  set ζ := R₁.residue ⟨z, hz₁⟩ with hζdef
  set ξ := R₂.residue ⟨z, hz₂⟩ with hξ
  set δ : Fin (m + 1 + 1) → Fb₁ := fun i => R₁.residue ⟨γ i, hγ₁ i⟩ with hδ

  have hI : ∑ i, δ i * ζ ^ (i : ℕ) = 0 := by
    have hsub : (⟨θ, hθ₁⟩ : R₁.integers) = ∑ i : Fin (m + 1 + 1), ⟨γ i, hγ₁ i⟩ * ⟨z, hz₁⟩ ^ (i : ℕ) := by
      apply Subtype.ext
      push_cast
      exact hθ
    rw [hsub, map_sum] at h₁
    simpa only [map_mul, map_pow] using h₁
  have hII : ∑ i, σ (δ i) * ξ ^ (i : ℕ) = 0 := by
    have hsub : (⟨θ, hθ₂⟩ : R₂.integers)
        = ∑ i : Fin (m + 1 + 1), ⟨γ i, hE₂ (γ i) (hγE i) (hγ₁ i)⟩ * ⟨z, hz₂⟩ ^ (i : ℕ) := by
      apply Subtype.ext
      push_cast
      exact hθ
    rw [hsub, map_sum] at h₂
    simp only [map_mul, map_pow] at h₂
    rw [← h₂]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hσ (γ i) (hγE i) (hγ₁ i), hδ, hξ]

  letI : Algebra Fb₁ Fb₂ := σ.toAlgebra
  have hmin : minpoly Fb₁ ξ = X ^ (m + 1) - C xb := by
    refine (minpoly.eq_of_irreducible_of_monic (X_pow_sub_C_irreducible_of_prime hq hηq) ?_
      (monic_X_pow_sub_C xb (Nat.succ_ne_zero m))).symm
    simp [RingHom.algebraMap_toAlgebra, hη]
  have hli : LinearIndependent Fb₁ fun i : Fin (m + 1) => ξ ^ (i : ℕ) := by
    have h := linearIndependent_pow (K := Fb₁) ξ
    rwa [hmin, natDegree_X_pow_sub_C] at h

  set g : Fin (m + 1) → Fb₁ :=
    fun i => δ (Fin.castSucc i) + if i = 0 then δ (Fin.last _) * xb else 0 with hg
  have hg0 : ∀ i, g i = 0 := by
    refine Fintype.linearIndependent_iff.mp hli g ?_
    simp only [hg, Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_add, add_mul, Finset.sum_add_distrib]
    rw [Fin.sum_univ_castSucc] at hII
    have hlast : σ (δ (Fin.last (m + 1))) * ξ ^ ((Fin.last (m + 1) : ℕ)) = σ (δ (Fin.last _) * xb) := by
      rw [Fin.val_last, ← hη, map_mul]
    rw [hlast] at hII
    convert hII using 2 <;> first | rfl | simp [Finset.sum_ite_eq', apply_ite σ]
  have hmid : ∀ i : Fin (m + 1), i ≠ 0 → δ (Fin.castSucc i) = 0 := by
    intro i hi
    simpa [hg, hi] using hg0 i
  have h0 : δ 0 = -(δ (Fin.last _) * xb) := by
    have h := hg0 0
    simp only [hg, if_true, Fin.castSucc_zero] at h
    exact eq_neg_of_add_eq_zero_left h

  have hlastzero : δ (Fin.last _) = 0 := by
    rw [Fin.sum_univ_castSucc, Finset.sum_eq_single (0 : Fin (m + 1))] at hI
    · simp only [Fin.castSucc_zero, Fin.val_zero, pow_zero, mul_one, Fin.val_last, h0] at hI
      have hI' : δ (Fin.last _) * (ζ ^ (m + 1) - xb) = 0 := by
        rw [mul_sub]
        linear_combination hI
      exact (mul_eq_zero.mp hI').resolve_right (sub_ne_zero.mpr hζ)
    · intro b _ hb
      rw [hmid b hb, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  intro i
  show δ i = 0
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · by_cases hj : j = 0
    · subst hj
      rw [Fin.castSucc_zero, h0, hlastzero, zero_mul, neg_zero]
    · exact hmid j hj
  · exact hlastzero

end Coordinates

section Gauss

variable {E : IntermediateField L F} (hE₂ : ∀ e ∈ E, e ∈ R₁.integers → e ∈ R₂.integers)
  (σ : Fb₁ →+* Fb₂)
  (hσ : ∀ e (he : e ∈ E) (h₁ : e ∈ R₁.integers), R₂.residue ⟨e, hE₂ e he h₁⟩ = σ (R₁.residue ⟨e, h₁⟩))
  {q : ℕ} (hq : q.Prime) [CharP Fb₂ q] (hpi : ∀ y : Fb₂, y ^ q ∈ σ.range)
  {z : F} (hz₁ : z ∈ R₁.integers) (hz₂ : z ∈ R₂.integers)
  (hzr₂ : R₂.residue ⟨z, hz₂⟩ ∉ σ.range)

private theorem const_smul_mem {c : L} (hc : c ∈ A) {f : F} (hf : f ∈ R₁.integers) :
    c • f ∈ R₁.integers := by
  rw [Algebra.smul_def]
  exact mul_mem ((R₁.algebraMap_mem_iff c).mpr hc) hf

include hσ hq hpi hz₁ hzr₂ in

private theorem coeff_mem_integers_of_mem_integers (γ : Fin (q + 1) → F) (hγE : ∀ i, γ i ∈ E) {h : F}
    (hh : h = ∑ i, γ i * z ^ (i : ℕ)) (hh₁ : h ∈ R₁.integers) (hh₂ : h ∈ R₂.integers) :
    ∀ i, γ i ∈ R₁.integers := by
  classical
  by_cases hzero : ∀ i, γ i = 0
  · intro i
    rw [hzero i]
    exact zero_mem _
  obtain ⟨i₁, hi₁⟩ := not_forall.mp hzero

  have hsc : ∀ i, ∃ c : L, ∃ hc : c • γ i ∈ R₁.integers, γ i ≠ 0 → R₁.residue ⟨c • γ i, hc⟩ ≠ 0 := by
    intro i
    by_cases hi : γ i = 0
    · exact ⟨1, by rw [hi, smul_zero]; exact zero_mem _, fun h => absurd hi h⟩
    · obtain ⟨c, hc, hres⟩ := R₁.exists_smul_mem (γ i) hi
      exact ⟨c, hc, fun _ => hres⟩
  choose cs hcs hcsres using hsc
  have hcs0 : ∀ i, γ i ≠ 0 → cs i ≠ 0 := fun i hi => R₁.smul_const_ne_zero (hcs i) (hcsres i hi)

  obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image (Finset.univ.filter fun i => γ i ≠ 0)
    (fun i => A.valuation (cs i)) ⟨i₁, by simpa using hi₁⟩
  have hγi₀ : γ i₀ ≠ 0 := by simpa using hi₀
  set c := cs i₀ with hc
  have hc0 : c ≠ 0 := hcs0 i₀ hγi₀

  have hcγ : ∀ i, c • γ i ∈ R₁.integers := by
    intro i
    by_cases hi : γ i = 0
    · rw [hi, smul_zero]; exact zero_mem _
    have hdiv : c / cs i ∈ A := by
      rw [← A.valuation_le_one_iff, map_div₀,
        div_le_one₀ (by rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).mpr (hcs0 i hi))]
      exact hmin i (by simpa using hi)
    have : c • γ i = (c / cs i) • (cs i • γ i) := by
      rw [smul_smul, div_mul_cancel₀ _ (hcs0 i hi)]
    rw [this]
    exact const_smul_mem R₁ hdiv (hcs i)
  rcases A.mem_or_inv_mem c with hcA | hcinv
  swap
  ·
    intro i
    have : γ i = c⁻¹ • (c • γ i) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [this]
    exact const_smul_mem R₁ hcinv (hcγ i)

  by_cases hunit : c⁻¹ ∈ A
  · intro i
    have : γ i = c⁻¹ • (c • γ i) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [this]
    exact const_smul_mem R₁ hunit (hcγ i)
  exfalso
  have hcmax : (⟨c, hcA⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    apply hunit
    have hmul : ((u⁻¹ : Aˣ) : A) * ⟨c, hcA⟩ = 1 := by rw [← hu, Units.inv_mul]
    have hmul' : ((u⁻¹ : Aˣ) : L) * c = 1 := by
      have h := congrArg (fun a : A => (a : L)) hmul
      simpa using h
    rw [← eq_inv_of_mul_eq_one_left hmul']
    exact ((u⁻¹ : Aˣ) : A).2
  have hcres : IsLocalRing.residue A ⟨c, hcA⟩ = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hcmax

  set θ := c • h with hθdef
  have hθ : θ = ∑ i, (c • γ i) * z ^ (i : ℕ) := by
    rw [hθdef, hh, Finset.smul_sum]
    simp only [smul_mul_assoc]
  have hθ₁ : θ ∈ R₁.integers := const_smul_mem R₁ hcA hh₁
  have hθ₂ : θ ∈ R₂.integers := by
    rw [hθdef, Algebra.smul_def]
    exact mul_mem ((R₂.algebraMap_mem_iff c).mpr hcA) hh₂
  have hres₁ : R₁.residue ⟨θ, hθ₁⟩ = 0 := by
    have hsub : (⟨θ, hθ₁⟩ : R₁.integers)
        = ⟨algebraMap L F c, (R₁.algebraMap_mem_iff c).mpr hcA⟩ * ⟨h, hh₁⟩ := by
      apply Subtype.ext
      simp [hθdef, Algebra.smul_def]
    rw [hsub, map_mul, R₁.residue_algebraMap ⟨c, hcA⟩, hcres, map_zero, zero_mul]
  have hres₂ : R₂.residue ⟨θ, hθ₂⟩ = 0 := by
    have hsub : (⟨θ, hθ₂⟩ : R₂.integers)
        = ⟨algebraMap L F c, (R₂.algebraMap_mem_iff c).mpr hcA⟩ * ⟨h, hh₂⟩ := by
      apply Subtype.ext
      simp [hθdef, Algebra.smul_def]
    rw [hsub, map_mul, R₂.residue_algebraMap ⟨c, hcA⟩, hcres, map_zero, zero_mul]
  have hall := residue_coeff_eq_zero_of_residues_eq_zero R₁ R₂ hE₂ σ hσ hq hpi hz₁ hz₂ hzr₂
    (fun i => c • γ i) (fun i => E.smul_mem (hγE i)) hcγ hθ hθ₁ hθ₂ hres₁ hres₂ i₀
  exact hcsres i₀ hγi₀ hall

include hσ hq hpi hz₁ hzr₂ in

private theorem eq_zero_of_sum_mul_pow_eq_zero (γ : Fin (q + 1) → F) (hγE : ∀ i, γ i ∈ E)
    (hsum : ∑ i, γ i * z ^ (i : ℕ) = 0) : ∀ i, γ i = 0 := by
  by_contra hne
  obtain ⟨i₀, hi₀⟩ := not_forall.mp hne
  set γ' : Fin (q + 1) → F := fun i => (γ i₀)⁻¹ * γ i with hγ'
  have hγ'E : ∀ i, γ' i ∈ E := fun i => E.mul_mem (E.inv_mem (hγE i₀)) (hγE i)
  have hsum' : (0 : F) = ∑ i, γ' i * z ^ (i : ℕ) := by
    simp only [hγ', mul_assoc, ← Finset.mul_sum, hsum, mul_zero]
  have hγ'₁ := coeff_mem_integers_of_mem_integers R₁ R₂ hE₂ σ hσ hq hpi hz₁ hz₂ hzr₂ γ' hγ'E hsum'
    (zero_mem _) (zero_mem _)
  have hres := residue_coeff_eq_zero_of_residues_eq_zero R₁ R₂ hE₂ σ hσ hq hpi hz₁ hz₂ hzr₂ γ' hγ'E hγ'₁
    hsum' (zero_mem _) (zero_mem _) (map_zero _) (map_zero _) i₀
  have h1 : γ' i₀ = 1 := inv_mul_cancel₀ hi₀
  have hone : (⟨γ' i₀, hγ'₁ i₀⟩ : R₁.integers) = 1 := Subtype.ext h1
  rw [hone, map_one] at hres
  exact one_ne_zero hres

end Gauss

end ModularCurve.AlphaEngine

end

section
open AlgebraicCurve Polynomial

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_qExpand jNum jNumQ jq ofPowerSeries_coeff_of_neg coeff_jq_neg_one jqN evalAtJ evalAtJ_X ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffMap_algebraMap coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_eq_map_intCast modularFunctionFieldC jqModC_mem jqNModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff KroneckerCongruence ssPlaces jGeomGen jNGeomGen IsAffineGeomPlace cuspInftyGeom ord_cuspInftyGeom_jq order_jqModC_def jqModC_ne_zero_def jq_mem_full coeff_jqModC_neg_one coeffSemilinearAut.coeffMap_qExpand coeffSemilinearAut.coeffMap_jqModC coeffSemilinearAut.coeffMap_mem_modularFunctionFieldC coeffSemilinearAut arithFrobC isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_jqModC qExpandAlgHomC qExpandAlgHomC_apply divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full jqModC_mem_full coeffMap_qExpand CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.mem_localizedAtKer CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc CharPReduction.redRes_ne_zero_of_notMem CharPReduction.redLoc_spec CharPReduction.redLoc_coe CharPReduction.redLocHom_apply CharPReduction.constSeries CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.affineBaseFin CharPModel.affineBaseInf CharPModel.FibreModel modularFunctionFieldBar_eq_modularFunctionFieldC finiteAlong_heckeAlphaBar_of_prime isCurveOver_modularFunctionFieldBar arithFrobC_smul_eq_frobOnPlacesGeomLevel CharPReduction.modularRedLocHom_mem exists_mem_riemannRochSpace_notMem_sub_single_of_le_degree isAffineGeomPlace_frobOnPlacesGeomLevel coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized_mul_of_not_dvd coeffEmb_jq exists_isAtkinLehnerAutFull_of_prime_of_not_dvd exists_regularProlongation_modularFunctionFieldBar_mul_of_not_dvd geomAut_atkinLehner_comp_legs hasPrincipalDivisors_modularFunctionFieldBar_unconditional place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin finrankAlong_heckeBetaBar CharPModel.FibreModel.piFin_range_localizes_of_jqModC_mem CharPModel.exists_monic_eval2_affineBaseFin_eq_zero_of_mem_modularLocalized_of_forall_mem_of_jBar_mem arithFrobC_smul_mem_ssPlaces_univ adjoin_jBar_jNBar_eq_top nonempty_modularPolynomialData relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi CharPReduction.mem_or_inv_mem_modularLocalized pow_char_eq_coeffMap_frobenius_qExpand qExpand_jqModC_eq_pow_unconditional mem_integralCoeffs_of_integral_affineBaseInf CharPModel.exists_monic_eval2_affineBaseInf_eq_zero_of_mem_modularLocalized_of_forall_inv_jBar_mem"
namespace AlphaEngine
p2m_open "ModularCurve~jBar"

private theorem map_derivative_eval {S T : Type*} [CommRing S] [CommRing T] (ρ : S →+* T) (p : Polynomial S)
    (a : S) : ρ ((derivative p).eval a) = (derivative (p.map ρ)).eval (ρ a) := by
  rw [derivative_map, eval_map, eval₂_at_apply]

private theorem map_eval' {S T : Type*} [CommRing S] [CommRing T] (ρ : S →+* T) (p : Polynomial S) (a : S) :
    ρ (p.eval a) = (p.map ρ).eval (ρ a) := by
  rw [eval_map, eval₂_at_apply]

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fb₁ Fb₂ : Type*} [Field Fb₁] [Field Fb₂]
  [Algebra (IsLocalRing.ResidueField A) Fb₁] [Algebra (IsLocalRing.ResidueField A) Fb₂]
variable (R₁ : RegularProlongation A F Fb₁) (R₂ : RegularProlongation A F Fb₂)
variable {E : IntermediateField L F} (hE₂ : ∀ e ∈ E, e ∈ R₁.integers → e ∈ R₂.integers)
  (σ : Fb₁ →+* Fb₂)
  (hσ : ∀ e (he : e ∈ E) (h₁ : e ∈ R₁.integers), R₂.residue ⟨e, hE₂ e he h₁⟩ = σ (R₁.residue ⟨e, h₁⟩))
  {q : ℕ} (hq : q.Prime) [CharP Fb₂ q] (hpi : ∀ y : Fb₂, y ^ q ∈ σ.range)
  {z : F} (hz₂ : z ∈ R₂.integers) (hzr₂ : R₂.residue ⟨z, hz₂⟩ ∉ σ.range)

include hσ hq hpi hzr₂ in

private theorem core (P₁ : Polynomial R₁.integers) (hPE : ∀ i, ((P₁.coeff i : R₁.integers) : F) ∈ E)
    (hroot : (P₁.map R₁.integers.subtype).eval z = 0) :
    ∃ (η : Fb₁) (Q : Polynomial Fb₁), σ η = R₂.residue ⟨z, hz₂⟩ ^ q ∧
      P₁.map R₁.residue = (X ^ q - C η) * Q ∧
      ∃ hD : (derivative (P₁.map R₁.integers.subtype)).eval z ∈ R₂.integers,
        R₂.residue ⟨_, hD⟩ = (derivative ((P₁.map R₁.residue).map σ)).eval (R₂.residue ⟨z, hz₂⟩) := by
  set P : Polynomial F := P₁.map R₁.integers.subtype with hPdef
  have hc₁ : ∀ i, ((P₁.coeff i : R₁.integers) : F) = P.coeff i := fun i => by
    rw [hPdef, coeff_map]
    rfl

  obtain ⟨P₂, hP₂map⟩ := (mem_lifts (f := R₂.integers.subtype) P).mp
    ((lifts_iff_coeff_lifts (f := R₂.integers.subtype) P).mpr
      fun i => ⟨⟨P.coeff i, hE₂ _ (hc₁ i ▸ hPE i) (hc₁ i ▸ (P₁.coeff i).2)⟩, rfl⟩)
  have hc₂ : ∀ i, ((P₂.coeff i : R₂.integers) : F) = P.coeff i := fun i => by
    rw [← hP₂map, coeff_map]
    rfl
  set zI : R₂.integers := ⟨z, hz₂⟩ with hzI

  have hbar : P₂.map R₂.residue = (P₁.map R₁.residue).map σ := by
    ext i
    rw [coeff_map, coeff_map, coeff_map]
    have h₂ : P₂.coeff i = ⟨P.coeff i, hE₂ _ (hc₁ i ▸ hPE i) (hc₁ i ▸ (P₁.coeff i).2)⟩ :=
      Subtype.ext (hc₂ i)
    have h₁ : P₁.coeff i = ⟨P.coeff i, hc₁ i ▸ (P₁.coeff i).2⟩ := Subtype.ext (hc₁ i)
    rw [h₁, h₂]
    exact hσ (P.coeff i) (hc₁ i ▸ hPE i) (hc₁ i ▸ (P₁.coeff i).2)

  have hroot₂ : (P₂.map R₂.residue).eval (R₂.residue zI) = 0 := by
    have h0 : P₂.eval zI = 0 := by
      apply Subtype.ext
      have h := map_eval' R₂.integers.subtype P₂ zI
      rw [hP₂map] at h
      exact h.trans hroot
    rw [← map_eval', h0, map_zero]

  letI : Algebra Fb₁ Fb₂ := σ.toAlgebra
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨η, hη⟩ := RingHom.mem_range.mp (hpi (R₂.residue zI))
  have hfrob : ∀ a b : Fb₂, a ^ q = b ^ q → a = b := by
    intro a b hab
    have h : (a - b) ^ q = a ^ q - b ^ q := by rw [sub_pow_char]
    rw [hab, sub_self] at h
    exact sub_eq_zero.mp ((pow_eq_zero_iff hq.ne_zero).mp h)
  have hηq : ∀ b : Fb₁, b ^ q ≠ η := by
    intro b hb
    apply hzr₂
    refine RingHom.mem_range.mpr ⟨b, hfrob _ _ ?_⟩
    rw [← map_pow, hb, hη]
  have hmin : minpoly Fb₁ (R₂.residue zI) = X ^ q - C η := by
    refine (minpoly.eq_of_irreducible_of_monic (X_pow_sub_C_irreducible_of_prime hq hηq) ?_
      (monic_X_pow_sub_C η hq.ne_zero)).symm
    simp [RingHom.algebraMap_toAlgebra, hη]
  have haeval : aeval (R₂.residue zI) (P₁.map R₁.residue) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, RingHom.algebraMap_toAlgebra, ← hbar]
    exact hroot₂
  have hdvd := minpoly.dvd Fb₁ (R₂.residue zI) haeval
  rw [hmin] at hdvd
  obtain ⟨Q, hQ⟩ := hdvd

  have hDeq : (derivative P).eval z = (((derivative P₂).eval zI : R₂.integers) : F) := by
    rw [← hP₂map]
    exact (map_derivative_eval R₂.integers.subtype P₂ zI).symm
  have hmem : (derivative P).eval z ∈ R₂.integers := hDeq ▸ ((derivative P₂).eval zI).2
  refine ⟨η, Q, hη, hQ, hmem, ?_⟩
  have hel : (⟨(derivative P).eval z, hmem⟩ : R₂.integers) = (derivative P₂).eval zI := Subtype.ext hDeq
  rw [hel, map_derivative_eval, hbar]

include hσ hq hpi hzr₂ in

private theorem exists_mem_and_residue_derivative_eval_eq_zero (P : Polynomial F) (hPE : ∀ i, P.coeff i ∈ E)
    (hP₁ : ∀ i, P.coeff i ∈ R₁.integers) (hroot : P.eval z = 0) :
    ∃ hD : (derivative P).eval z ∈ R₂.integers, R₂.residue ⟨_, hD⟩ = 0 := by
  obtain ⟨P₁, rfl⟩ := (mem_lifts (f := R₁.integers.subtype) P).mp
    ((lifts_iff_coeff_lifts (f := R₁.integers.subtype) P).mpr fun i => ⟨⟨P.coeff i, hP₁ i⟩, rfl⟩)
  have hPE' : ∀ i, ((P₁.coeff i : R₁.integers) : F) ∈ E := fun i => by
    have h := hPE i
    rw [coeff_map] at h
    exact h
  obtain ⟨η, Q, hη, hQ, hD, hres⟩ := core R₁ R₂ hE₂ σ hσ hq hpi hz₂ hzr₂ P₁ hPE' hroot
  refine ⟨hD, ?_⟩
  rw [hres, hQ, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
    derivative_mul, eval_add, eval_mul, eval_mul, eval_sub, eval_pow, eval_X, eval_C, hη, sub_self, zero_mul,
    add_zero, derivative_sub, derivative_C, sub_zero, derivative_X_pow, eval_mul, eval_C,
    CharP.cast_eq_zero Fb₂ q, zero_mul, zero_mul]

include hσ hq hpi hzr₂ in

private theorem exists_residue_derivative_eval_eq_pow_sub (hz₁ : z ∈ R₁.integers) (P : Polynomial F)
    (hPE : ∀ i, P.coeff i ∈ E) (hP₁ : ∀ i, P.coeff i ∈ R₁.integers) (hmonic : P.Monic)
    (hdeg : P.natDegree = q + 1) (hroot : P.eval z = 0) :
    ∃ η : Fb₁, σ η = R₂.residue ⟨z, hz₂⟩ ^ q ∧
      ∀ hD : (derivative P).eval z ∈ R₁.integers, R₁.residue ⟨_, hD⟩ = R₁.residue ⟨z, hz₁⟩ ^ q - η := by
  obtain ⟨P₁, rfl, hP₁deg, hP₁monic⟩ := lifts_and_natDegree_eq_and_monic
    ((lifts_iff_coeff_lifts (f := R₁.integers.subtype) P).mpr fun i => ⟨⟨P.coeff i, hP₁ i⟩, rfl⟩) hmonic
  have hPE' : ∀ i, ((P₁.coeff i : R₁.integers) : F) ∈ E := fun i => by
    have h := hPE i
    rw [coeff_map] at h
    exact h
  obtain ⟨η, Q, hη, hQ, -, -⟩ := core R₁ R₂ hE₂ σ hσ hq hpi hz₂ hzr₂ P₁ hPE' hroot
  refine ⟨η, hη, fun hD => ?_⟩

  have hbar_monic : (P₁.map R₁.residue).Monic := hP₁monic.map _
  have hXq : (X ^ q - C η : Polynomial Fb₁).Monic := monic_X_pow_sub_C η hq.ne_zero
  have hQmonic : Q.Monic := hXq.of_mul_monic_left (hQ ▸ hbar_monic)
  have hQdeg : Q.natDegree = 1 := by
    have h := congrArg natDegree hQ
    rw [hP₁monic.natDegree_map, hP₁deg, hdeg, hXq.natDegree_mul hQmonic, natDegree_X_pow_sub_C] at h
    omega
  have hq1 : ((q : ℕ) : Fb₁) = 0 := by
    apply σ.injective
    rw [map_natCast, map_zero]
    exact CharP.cast_eq_zero Fb₂ q

  set zI₁ : R₁.integers := ⟨z, hz₁⟩ with hzI₁
  have hDeq : (derivative (P₁.map R₁.integers.subtype)).eval z = (((derivative P₁).eval zI₁ : R₁.integers) : F) :=
    (map_derivative_eval R₁.integers.subtype P₁ zI₁).symm
  have hel : (⟨(derivative (P₁.map R₁.integers.subtype)).eval z, hD⟩ : R₁.integers) = (derivative P₁).eval zI₁ :=
    Subtype.ext hDeq
  rw [hel, map_derivative_eval, hQ, hQmonic.eq_X_add_C hQdeg, derivative_mul, derivative_X_add_C, eval_add,
    eval_mul, eval_mul, eval_one, mul_one, derivative_sub, derivative_C, sub_zero, derivative_X_pow, eval_mul,
    eval_C, hq1, zero_mul, zero_mul, zero_add, eval_sub, eval_pow, eval_X, eval_C]

end ModularCurve.AlphaEngine
end

section
open AlgebraicCurve

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_qExpand jNum jNumQ jq ofPowerSeries_coeff_of_neg coeff_jq_neg_one jqN evalAtJ evalAtJ_X ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffMap_algebraMap coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_eq_map_intCast modularFunctionFieldC jqModC_mem jqNModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff KroneckerCongruence ssPlaces jGeomGen jNGeomGen IsAffineGeomPlace cuspInftyGeom ord_cuspInftyGeom_jq order_jqModC_def jqModC_ne_zero_def jq_mem_full coeff_jqModC_neg_one coeffSemilinearAut.coeffMap_qExpand coeffSemilinearAut.coeffMap_jqModC coeffSemilinearAut.coeffMap_mem_modularFunctionFieldC coeffSemilinearAut arithFrobC isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_jqModC qExpandAlgHomC qExpandAlgHomC_apply divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full jqModC_mem_full coeffMap_qExpand CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.mem_localizedAtKer CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc CharPReduction.redRes_ne_zero_of_notMem CharPReduction.redLoc_spec CharPReduction.redLoc_coe CharPReduction.redLocHom_apply CharPReduction.constSeries CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.affineBaseFin CharPModel.affineBaseInf CharPModel.FibreModel modularFunctionFieldBar_eq_modularFunctionFieldC finiteAlong_heckeAlphaBar_of_prime isCurveOver_modularFunctionFieldBar arithFrobC_smul_eq_frobOnPlacesGeomLevel CharPReduction.modularRedLocHom_mem exists_mem_riemannRochSpace_notMem_sub_single_of_le_degree isAffineGeomPlace_frobOnPlacesGeomLevel coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized_mul_of_not_dvd coeffEmb_jq exists_isAtkinLehnerAutFull_of_prime_of_not_dvd exists_regularProlongation_modularFunctionFieldBar_mul_of_not_dvd geomAut_atkinLehner_comp_legs hasPrincipalDivisors_modularFunctionFieldBar_unconditional place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin finrankAlong_heckeBetaBar CharPModel.FibreModel.piFin_range_localizes_of_jqModC_mem CharPModel.exists_monic_eval2_affineBaseFin_eq_zero_of_mem_modularLocalized_of_forall_mem_of_jBar_mem arithFrobC_smul_mem_ssPlaces_univ adjoin_jBar_jNBar_eq_top nonempty_modularPolynomialData relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi CharPReduction.mem_or_inv_mem_modularLocalized pow_char_eq_coeffMap_frobenius_qExpand qExpand_jqModC_eq_pow_unconditional mem_integralCoeffs_of_integral_affineBaseInf CharPModel.exists_monic_eval2_affineBaseInf_eq_zero_of_mem_modularLocalized_of_forall_inv_jBar_mem"
namespace AlphaEngine
p2m_open "ModularCurve~jBar"

variable {A : ValuationSubring (AlgebraicClosure ℚ)}

private theorem natCast_mem_nonunits_of_charP {k : Type*} [Field k] {q : ℕ} [CharP k q] (red : A →+* k) :
    ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits := by
  have hqA : ((q : ℕ) : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro h
    have h' := h.map red
    rw [map_natCast, CharP.cast_eq_zero k q] at h'
    exact not_isUnit_zero h'
  have h := (ValuationSubring.coe_mem_nonunits_iff (A := A) (a := ((q : ℕ) : A))).mpr hqA
  simpa using h

variable {F : Type*} [Field F] [Algebra (AlgebraicClosure ℚ) F]
  {Fb : Type*} [Field Fb] [Algebra (IsLocalRing.ResidueField A) Fb] (R : RegularProlongation A F Fb)

private theorem const_smul_mem' {c : AlgebraicClosure ℚ} (hc : c ∈ A) {f : F} (hf : f ∈ R.integers) :
    c • f ∈ R.integers := by
  rw [Algebra.smul_def]
  exact mul_mem ((R.algebraMap_mem_iff c).mpr hc) hf

private theorem exists_const_smul_mem (f : F) : ∃ d : A, d ≠ 0 ∧ (d : AlgebraicClosure ℚ) • f ∈ R.integers := by
  by_cases hf : f = 0
  · exact ⟨1, one_ne_zero, by rw [hf, smul_zero]; exact zero_mem _⟩
  obtain ⟨c, hc, hres⟩ := R.exists_smul_mem f hf
  have hc0 : c ≠ 0 := R.smul_const_ne_zero hc hres
  rcases A.mem_or_inv_mem c with hcA | hcinv
  · exact ⟨⟨c, hcA⟩, fun h => hc0 (congrArg Subtype.val h), hc⟩
  · refine ⟨1, one_ne_zero, ?_⟩
    have : f = c⁻¹ • (c • f) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [OneMemClass.coe_one, one_smul, this]
    exact const_smul_mem' R hcinv hc

private theorem exists_const_smul_eq_of_residue_eq_zero {g : F} (hg : g ∈ R.integers) (hg0 : R.residue ⟨g, hg⟩ = 0)
    (hgne : g ≠ 0) :
    ∃ (c : A) (u : F) (hu : u ∈ R.integers),
      c ∈ IsLocalRing.maximalIdeal A ∧ c ≠ 0 ∧ R.residue ⟨u, hu⟩ ≠ 0 ∧ g = (c : AlgebraicClosure ℚ) • u := by
  obtain ⟨c₁, hc₁, hres⟩ := R.exists_smul_mem g hgne
  have hc₁0 : c₁ ≠ 0 := R.smul_const_ne_zero hc₁ hres

  have hinv : c₁⁻¹ ∈ A := by
    by_contra hnot
    have hc₁A : c₁ ∈ A := (A.mem_or_inv_mem c₁).resolve_right hnot
    apply hres
    have hsub : (⟨c₁ • g, hc₁⟩ : R.integers)
        = ⟨algebraMap (AlgebraicClosure ℚ) F c₁, (R.algebraMap_mem_iff c₁).mpr hc₁A⟩ * ⟨g, hg⟩ := by
      apply Subtype.ext
      simp [Algebra.smul_def]
    rw [hsub, map_mul, hg0, mul_zero]
  have hgeq : g = c₁⁻¹ • (c₁ • g) := by rw [smul_smul, inv_mul_cancel₀ hc₁0, one_smul]
  refine ⟨⟨c₁⁻¹, hinv⟩, c₁ • g, hc₁, ?_, fun h => inv_ne_zero hc₁0 (congrArg Subtype.val h), hres, hgeq⟩

  rw [← IsLocalRing.residue_eq_zero_iff]
  have hsub : (⟨g, hg⟩ : R.integers)
      = ⟨algebraMap (AlgebraicClosure ℚ) F c₁⁻¹, (R.algebraMap_mem_iff c₁⁻¹).mpr hinv⟩ * ⟨c₁ • g, hc₁⟩ := by
    apply Subtype.ext
    simp only [MulMemClass.coe_mul]
    rw [← Algebra.smul_def]
    exact hgeq
  have h := hg0
  rw [hsub, map_mul, R.residue_algebraMap ⟨c₁⁻¹, hinv⟩] at h
  rcases mul_eq_zero.mp h with h0 | h0
  · exact (algebraMap (IsLocalRing.ResidueField A) Fb).injective (by rw [h0, map_zero])
  · exact absurd h0 hres

private theorem exists_pow_mul_mem {q : ℕ} [Fact q.Prime] (hq : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits) (f : F)
    {g : F} (hg : g ∈ R.integers) (hg0 : R.residue ⟨g, hg⟩ = 0) (hgne : g ≠ 0) :
    ∃ M : ℕ, g ^ M * f ∈ R.integers := by
  obtain ⟨d, hd0, hdf⟩ := exists_const_smul_mem R f
  obtain ⟨c, u, hu, hcm, hc0, -, rfl⟩ := exists_const_smul_eq_of_residue_eq_zero R hg hg0 hgne
  obtain ⟨M, a, ha⟩ := ValuationSubring.exists_dvd_pow_of_mem_maximalIdeal A hq d hd0 c hcm hc0
  refine ⟨M, ?_⟩
  have hcM : (c : AlgebraicClosure ℚ) ^ M = (d : AlgebraicClosure ℚ) * (a : AlgebraicClosure ℚ) := by
    have h := congrArg (fun x : A => (x : AlgebraicClosure ℚ)) ha
    simpa using h
  have hrepr : ((c : AlgebraicClosure ℚ) • u) ^ M * f
      = (a : AlgebraicClosure ℚ) • (u ^ M * ((d : AlgebraicClosure ℚ) • f)) := by
    rw [smul_pow, hcM, mul_comm (d : AlgebraicClosure ℚ), mul_smul, smul_mul_assoc, smul_mul_assoc]
    congr 1
    rw [mul_smul_comm]
  rw [hrepr]
  exact const_smul_mem' R a.2 (mul_mem (pow_mem hu M) hdf)

end ModularCurve.AlphaEngine
end

section
p2m_open "AlgebraicCurve ModularCurve~jBar P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_qExpand jNum jNumQ jq ofPowerSeries_coeff_of_neg coeff_jq_neg_one jqN evalAtJ evalAtJ_X ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffMap_algebraMap coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_eq_map_intCast modularFunctionFieldC jqModC_mem jqNModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff KroneckerCongruence ssPlaces jGeomGen jNGeomGen IsAffineGeomPlace cuspInftyGeom ord_cuspInftyGeom_jq order_jqModC_def jqModC_ne_zero_def jq_mem_full coeff_jqModC_neg_one coeffSemilinearAut.coeffMap_qExpand coeffSemilinearAut.coeffMap_jqModC coeffSemilinearAut.coeffMap_mem_modularFunctionFieldC coeffSemilinearAut arithFrobC isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_jqModC qExpandAlgHomC qExpandAlgHomC_apply divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full jqModC_mem_full coeffMap_qExpand CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.mem_localizedAtKer CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc CharPReduction.redRes_ne_zero_of_notMem CharPReduction.redLoc_spec CharPReduction.redLoc_coe CharPReduction.redLocHom_apply CharPReduction.constSeries CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.affineBaseFin CharPModel.affineBaseInf CharPModel.FibreModel modularFunctionFieldBar_eq_modularFunctionFieldC finiteAlong_heckeAlphaBar_of_prime isCurveOver_modularFunctionFieldBar arithFrobC_smul_eq_frobOnPlacesGeomLevel CharPReduction.modularRedLocHom_mem exists_mem_riemannRochSpace_notMem_sub_single_of_le_degree isAffineGeomPlace_frobOnPlacesGeomLevel coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized_mul_of_not_dvd coeffEmb_jq exists_isAtkinLehnerAutFull_of_prime_of_not_dvd exists_regularProlongation_modularFunctionFieldBar_mul_of_not_dvd geomAut_atkinLehner_comp_legs hasPrincipalDivisors_modularFunctionFieldBar_unconditional place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin finrankAlong_heckeBetaBar CharPModel.FibreModel.piFin_range_localizes_of_jqModC_mem CharPModel.exists_monic_eval2_affineBaseFin_eq_zero_of_mem_modularLocalized_of_forall_mem_of_jBar_mem arithFrobC_smul_mem_ssPlaces_univ adjoin_jBar_jNBar_eq_top nonempty_modularPolynomialData relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi CharPReduction.mem_or_inv_mem_modularLocalized pow_char_eq_coeffMap_frobenius_qExpand qExpand_jqModC_eq_pow_unconditional mem_integralCoeffs_of_integral_affineBaseInf CharPModel.exists_monic_eval2_affineBaseInf_eq_zero_of_mem_modularLocalized_of_forall_inv_jBar_mem"
namespace AlphaEngine
p2m_open "ModularCurve~jBar"

private theorem finrankAlong_algEquiv_toAlgHom {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F]
    [Algebra K F'] (e : F ≃ₐ[K] F') : finrankAlong K e.toAlgHom = 1 := by
  have h := finrankAlong_comp e.toAlgHom e.symm.toAlgHom
  have hid : e.symm.toAlgHom.comp e.toAlgHom = AlgHom.id K F := by
    ext x
    simp
  rw [hid, finrankAlong_id] at h
  exact Nat.eq_one_of_mul_eq_one_right h.symm

private theorem finrankAlong_heckeAlphaBar_of_not_dvd (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) :
    finrankAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) = q + 1 := by
  obtain ⟨σ, hσ⟩ := exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q (Fact.out : q.Prime) hqN
  have hlegs := (geomAut_atkinLehner_comp_legs (AlgebraicClosure ℚ) N q σ hσ).1
  have hβ := finrankAlong_heckeBetaBar (AlgebraicClosure ℚ) N q
  rw [if_neg hqN, ← hlegs, finrankAlong_comp, finrankAlong_algEquiv_toAlgHom, mul_one] at hβ
  exact hβ

end ModularCurve.AlphaEngine
end

section
p2m_open "ModularCurve~jBar P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_qExpand jNum jNumQ jq ofPowerSeries_coeff_of_neg coeff_jq_neg_one jqN evalAtJ evalAtJ_X ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffMap_algebraMap coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_eq_map_intCast modularFunctionFieldC jqModC_mem jqNModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff KroneckerCongruence ssPlaces jGeomGen jNGeomGen IsAffineGeomPlace cuspInftyGeom ord_cuspInftyGeom_jq order_jqModC_def jqModC_ne_zero_def jq_mem_full coeff_jqModC_neg_one coeffSemilinearAut.coeffMap_qExpand coeffSemilinearAut.coeffMap_jqModC coeffSemilinearAut.coeffMap_mem_modularFunctionFieldC coeffSemilinearAut arithFrobC isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_jqModC qExpandAlgHomC qExpandAlgHomC_apply divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full jqModC_mem_full coeffMap_qExpand CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.mem_localizedAtKer CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc CharPReduction.redRes_ne_zero_of_notMem CharPReduction.redLoc_spec CharPReduction.redLoc_coe CharPReduction.redLocHom_apply CharPReduction.constSeries CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.affineBaseFin CharPModel.affineBaseInf CharPModel.FibreModel modularFunctionFieldBar_eq_modularFunctionFieldC finiteAlong_heckeAlphaBar_of_prime isCurveOver_modularFunctionFieldBar arithFrobC_smul_eq_frobOnPlacesGeomLevel CharPReduction.modularRedLocHom_mem exists_mem_riemannRochSpace_notMem_sub_single_of_le_degree isAffineGeomPlace_frobOnPlacesGeomLevel coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized_mul_of_not_dvd coeffEmb_jq exists_isAtkinLehnerAutFull_of_prime_of_not_dvd exists_regularProlongation_modularFunctionFieldBar_mul_of_not_dvd geomAut_atkinLehner_comp_legs hasPrincipalDivisors_modularFunctionFieldBar_unconditional place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin finrankAlong_heckeBetaBar CharPModel.FibreModel.piFin_range_localizes_of_jqModC_mem CharPModel.exists_monic_eval2_affineBaseFin_eq_zero_of_mem_modularLocalized_of_forall_mem_of_jBar_mem arithFrobC_smul_mem_ssPlaces_univ adjoin_jBar_jNBar_eq_top nonempty_modularPolynomialData relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi CharPReduction.mem_or_inv_mem_modularLocalized pow_char_eq_coeffMap_frobenius_qExpand qExpand_jqModC_eq_pow_unconditional mem_integralCoeffs_of_integral_affineBaseInf CharPModel.exists_monic_eval2_affineBaseInf_eq_zero_of_mem_modularLocalized_of_forall_inv_jBar_mem"
namespace AlphaEngine
p2m_open "ModularCurve~jBar"

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

omit [NeZero N] in

private theorem coeffMap_mem_fullC (τ : K →+* K) {x : LaurentSeries K} (hx : x ∈ modularFunctionFieldFullC K N) :
    coeffMap τ x ∈ modularFunctionFieldFullC K N := by
  change x ∈ Subfield.closure (Set.range (algebraMap K (LaurentSeries K)) ∪ divisorExpansionsC K N) at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨d, hd0, hdN, rfl⟩
      · rw [coeffMap_algebraMap]
        exact (modularFunctionFieldFullC K N).algebraMap_mem _
      · haveI := hd0
        rw [coeffSemilinearAut.coeffMap_qExpand, coeffSemilinearAut.coeffMap_jqModC]
        exact jqModCd_mem_full K N hdN
  | one => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | neg x _ hx => simpa using neg_mem hx
  | inv x _ hx => simpa using inv_mem hx
  | mul x y _ _ hx hy => simpa using mul_mem hx hy

variable (q : ℕ) [Fact q.Prime] [CharP K q]

omit [NeZero N] in

private theorem qExpand_mem_fullC {x : LaurentSeries K} (hx : x ∈ modularFunctionFieldFullC K N) :
    qExpand K q x ∈ modularFunctionFieldFullC K N := by
  have hle : (modularFunctionFieldFullC K N).map (qExpandAlgHomC K q) ≤ modularFunctionFieldFullC K N := by
    rw [modularFunctionFieldFullC, IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
    rintro _ ⟨_, ⟨d, hd0, hdN, rfl⟩, rfl⟩
    haveI := hd0
    show qExpandAlgHomC K q (qExpand K d (jqModC K)) ∈ modularFunctionFieldFullC K N
    have hcomm : qExpand K q (qExpand K d (jqModC K)) = qExpand K d (qExpand K q (jqModC K)) := by
      rw [qExpand_qExpand, qExpand_qExpand]
      simp only [Nat.mul_comm]
    rw [qExpandAlgHomC_apply, hcomm, qExpand_jqModC_eq_pow_unconditional, map_pow]
    exact pow_mem (jqModCd_mem_full K N hdN) q
  exact hle ⟨x, hx, rfl⟩

private noncomputable def twist : modularFunctionFieldFullC K N →+* modularFunctionFieldFullC K N where
  toFun x := ⟨qExpand K q (x : LaurentSeries K), qExpand_mem_fullC K N q x.2⟩
  map_one' := Subtype.ext (map_one (qExpand K q))
  map_mul' x y := Subtype.ext (map_mul (qExpand K q) (x : LaurentSeries K) y)
  map_zero' := Subtype.ext (map_zero (qExpand K q))
  map_add' x y := Subtype.ext (map_add (qExpand K q) (x : LaurentSeries K) y)

omit [NeZero N] in
@[scoped simp]
private theorem coe_twist (x : modularFunctionFieldFullC K N) :
    (twist K N q x : LaurentSeries K) = qExpand K q (x : LaurentSeries K) :=
  rfl

omit [NeZero N] in

private theorem pow_mem_range_twist (y : modularFunctionFieldFullC K N) : y ^ q ∈ (twist K N q).range := by
  refine RingHom.mem_range.mpr ⟨⟨coeffMap (frobenius K q) (y : LaurentSeries K), coeffMap_mem_fullC K N _ y.2⟩, ?_⟩
  apply Subtype.ext
  show qExpand K q (coeffMap (frobenius K q) (y : LaurentSeries K)) = ((y ^ q : modularFunctionFieldFullC K N) :
    LaurentSeries K)
  rw [← coeffSemilinearAut.coeffMap_qExpand, ← pow_char_eq_coeffMap_frobenius_qExpand q]
  norm_cast

omit [NeZero N] in

private theorem notMem_range_twist_of_coeff_ne_zero {y : modularFunctionFieldFullC K N} {n : ℤ} (hn : ¬ (q : ℤ) ∣ n)
    (hy : (y : LaurentSeries K).coeff n ≠ 0) : y ∉ (twist K N q).range := by
  intro hmem
  obtain ⟨w, hw⟩ := RingHom.mem_range.mp hmem
  apply hy
  rw [← hw, coe_twist, qExpand_coeff_of_not_dvd q _ hn]

omit [NeZero N] in

private theorem jqModC_notMem_range_twist :
    (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) ∉ (twist K N q).range := by
  refine notMem_range_twist_of_coeff_ne_zero K N q (n := -1) ?_ ?_
  · intro h
    rw [Int.dvd_neg] at h
    have h1 : q ∣ 1 := by exact_mod_cast h
    exact (Fact.out : q.Prime).one_lt.ne' (Nat.dvd_one.mp h1)
  · show (jqModC K).coeff (-1) ≠ 0
    rw [coeff_jqModC_neg_one]
    exact one_ne_zero

private theorem jqNModC_notMem_range_twist (hqN : ¬ q ∣ N) :
    (⟨jqNModC K N, jqModCd_mem_full K N (dvd_refl N)⟩ : modularFunctionFieldFullC K N) ∉ (twist K N q).range := by
  refine notMem_range_twist_of_coeff_ne_zero K N q (n := -(N : ℤ)) ?_ ?_
  · intro h
    rw [Int.dvd_neg] at h
    exact hqN (by exact_mod_cast h)
  · show (qExpand K N (jqModC K)).coeff (-(N : ℤ)) ≠ 0
    rw [show (-(N : ℤ)) = (N : ℤ) * (-1) by ring, qExpand_coeff_mul, coeff_jqModC_neg_one]
    exact one_ne_zero

end ModularCurve.AlphaEngine
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve.AlphaEngine"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve"
end
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve.AlphaEngine"

section
p2m_open "Polynomial AlgebraicCurve ModularCurve~jBar P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_qExpand jNum jNumQ jq ofPowerSeries_coeff_of_neg coeff_jq_neg_one jqN evalAtJ evalAtJ_X ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffMap_algebraMap coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_eq_map_intCast modularFunctionFieldC jqModC_mem jqNModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff KroneckerCongruence ssPlaces jGeomGen jNGeomGen IsAffineGeomPlace cuspInftyGeom ord_cuspInftyGeom_jq order_jqModC_def jqModC_ne_zero_def jq_mem_full coeff_jqModC_neg_one coeffSemilinearAut.coeffMap_qExpand coeffSemilinearAut.coeffMap_jqModC coeffSemilinearAut.coeffMap_mem_modularFunctionFieldC coeffSemilinearAut arithFrobC isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_jqModC qExpandAlgHomC qExpandAlgHomC_apply divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full jqModC_mem_full coeffMap_qExpand CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.mem_localizedAtKer CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc CharPReduction.redRes_ne_zero_of_notMem CharPReduction.redLoc_spec CharPReduction.redLoc_coe CharPReduction.redLocHom_apply CharPReduction.constSeries CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.affineBaseFin CharPModel.affineBaseInf CharPModel.FibreModel modularFunctionFieldBar_eq_modularFunctionFieldC finiteAlong_heckeAlphaBar_of_prime isCurveOver_modularFunctionFieldBar arithFrobC_smul_eq_frobOnPlacesGeomLevel CharPReduction.modularRedLocHom_mem exists_mem_riemannRochSpace_notMem_sub_single_of_le_degree isAffineGeomPlace_frobOnPlacesGeomLevel coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized_mul_of_not_dvd coeffEmb_jq exists_isAtkinLehnerAutFull_of_prime_of_not_dvd exists_regularProlongation_modularFunctionFieldBar_mul_of_not_dvd geomAut_atkinLehner_comp_legs hasPrincipalDivisors_modularFunctionFieldBar_unconditional place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin finrankAlong_heckeBetaBar CharPModel.FibreModel.piFin_range_localizes_of_jqModC_mem CharPModel.exists_monic_eval2_affineBaseFin_eq_zero_of_mem_modularLocalized_of_forall_mem_of_jBar_mem arithFrobC_smul_mem_ssPlaces_univ adjoin_jBar_jNBar_eq_top nonempty_modularPolynomialData relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi CharPReduction.mem_or_inv_mem_modularLocalized pow_char_eq_coeffMap_frobenius_qExpand qExpand_jqModC_eq_pow_unconditional mem_integralCoeffs_of_integral_affineBaseInf CharPModel.exists_monic_eval2_affineBaseInf_eq_zero_of_mem_modularLocalized_of_forall_inv_jBar_mem"
namespace AlphaEngine
p2m_open "ModularCurve~jBar"

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

private theorem coeff_minpolyDiv_mem_subring (x : L) (B : Subring L) (hx : x ∈ B)
    (hf : ∀ n, algebraMap K L ((minpoly K x).coeff n) ∈ B) (i : ℕ) : (minpolyDiv K x).coeff i ∈ B := by
  suffices H : ∀ j i : ℕ, (minpolyDiv K x).natDegree < i + j → (minpolyDiv K x).coeff i ∈ B from
    H ((minpolyDiv K x).natDegree + 1) i (by omega)
  intro j
  induction j with
  | zero =>
    intro i hi
    rw [coeff_eq_zero_of_natDegree_lt (by simpa using hi)]
    exact zero_mem _
  | succ j ih =>
    intro i hi
    rw [coeff_minpolyDiv]
    exact add_mem (hf (i + 1)) (mul_mem (ih (i + 1) (by omega)) hx)

variable [Algebra.IsSeparable K L]

private theorem repr_eq_trace_mul (pb : PowerBasis K L) (h : L) (i : Fin pb.dim) :
    pb.basis.repr h i = Algebra.trace K L
      (h * ((minpolyDiv K pb.gen).coeff i / aeval pb.gen (derivative (minpoly K pb.gen)))) := by
  haveI := pb.finite
  rw [← Module.Basis.traceDual_powerBasis_eq pb i, ← Algebra.traceForm_apply,
    ← Module.Basis.traceDual_repr_apply, Module.Basis.traceDual_traceDual]

variable {O : Type*} [CommRing O] [Algebra O K] [Algebra O L] [IsScalarTower O K L]
  [IsIntegrallyClosed O] [IsFractionRing O K]

private theorem exists_algebraMap_eq_repr_of_isIntegral (pb : PowerBasis K L) (h : L)
    (hint : ∀ i : Fin pb.dim,
      IsIntegral O (h * ((minpolyDiv K pb.gen).coeff i / aeval pb.gen (derivative (minpoly K pb.gen)))))
    (i : Fin pb.dim) : ∃ y : O, algebraMap O K y = pb.basis.repr h i := by
  haveI := pb.finite
  rw [repr_eq_trace_mul]
  exact IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_trace (hint i))

section Generic

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

private theorem ord_nonneg_of_mem' (v : Place K L) {f : L} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : L) * ((π : L) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

private theorem mem_of_ord_nonneg' (v : Place K L) {f : L} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm, zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

private theorem minpoly_eq_of_monic_of_natDegree_eq {x : L} {m : Polynomial K} (hm : m.Monic) (hroot : aeval x m = 0)
    (hdeg : m.natDegree = Module.finrank K L)
    (hgen : IntermediateField.adjoin K ({x} : Set L) = ⊤) : minpoly K x = m := by
  have hint : IsIntegral K x := ⟨m, hm, by rwa [← aeval_def]⟩
  have hnat : (minpoly K x).natDegree = Module.finrank K L := by
    rw [← IntermediateField.adjoin.finrank hint, hgen, IntermediateField.finrank_top']
  refine (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hm (minpoly.dvd _ _ hroot) ?_).symm
  rw [hdeg, hnat]

private theorem exists_powerBasis_of_adjoin_eq_top {x : L} (hint : IsIntegral K x)
    (hgen : IntermediateField.adjoin K ({x} : Set L) = ⊤) :
    ∃ pb : PowerBasis K L, pb.gen = x ∧ pb.dim = (minpoly K x).natDegree :=
  ⟨(IntermediateField.adjoin.powerBasis hint).map
    ((IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv), rfl, rfl⟩

private theorem eq_sum_repr_mul_pow (pb : PowerBasis K L) {n : ℕ} (hdim : pb.dim = n) (h : L) :
    h = ∑ i : Fin n, algebraMap K L (pb.basis.repr h (Fin.cast hdim.symm i)) * pb.gen ^ (i : ℕ) := by
  conv_lhs => rw [← pb.basis.sum_repr h]
  subst hdim
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pb.basis_eq_pow, Algebra.smul_def]
  rfl

private theorem coeff_minpoly_mem_of_isIntegral {K₀ : Type*} [Field K₀] [Algebra K₀ K] (v : Place K₀ K) (x : L)
    (hx : IsIntegral v.toValuationSubring x) (i : ℕ) : (minpoly K x).coeff i ∈ v.toValuationSubring := by
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hx, coeff_map]
  exact ((minpoly v.toValuationSubring x).coeff i).2

private theorem natDegree_minpoly_of_adjoin_eq_top [FiniteDimensional K L] (x : L)
    (hx : IntermediateField.adjoin K ({x} : Set L) = ⊤) : (minpoly K x).natDegree = Module.finrank K L := by
  rw [← IntermediateField.adjoin.finrank (IsIntegral.of_finite K x), hx, IntermediateField.finrank_top']

private theorem pow_eq_sum_neg_coeff_minpoly (x : L) (hx : IsIntegral K x) {n : ℕ} (hn : (minpoly K x).natDegree = n) :
    x ^ n = ∑ i : Fin n, (-(algebraMap K L ((minpoly K x).coeff i))) * x ^ (i : ℕ) := by
  have h0 := minpoly.aeval K x
  rw [(minpoly.monic hx).as_sum, hn] at h0
  simp only [map_add, map_pow, aeval_X, map_sum, map_mul, aeval_C] at h0
  rw [Finset.sum_range] at h0
  rw [eq_neg_of_add_eq_zero_left h0, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [neg_mul]

end Generic
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve.AlphaEngine"

section AtPlace

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F']
  [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [HasPrincipalDivisors K F']

private theorem isIntegral_of_forall_ord_fiber_nonneg (v : Place K F) {y : F'} (hy : ∀ w ∈ v.fiber F', 0 ≤ w.ord y) :
    IsIntegral v.toValuationSubring y := by
  rcases eq_or_ne y 0 with rfl | hy0
  · exact isIntegral_zero
  obtain ⟨c, hc⟩ := Place.exists_integralClosureAt_of_ord_fiber_nonneg hy0 hy
  rw [← hc]
  exact c.2

private theorem repr_mem_of_forall_ord_fiber_nonneg (v : Place K F) (pb : PowerBasis F F') (h : F')
    (hint : ∀ j : Fin pb.dim, ∀ w ∈ v.fiber F',
      0 ≤ w.ord (h * ((minpolyDiv F pb.gen).coeff j / aeval pb.gen (derivative (minpoly F pb.gen)))))
    (i : Fin pb.dim) : pb.basis.repr h i ∈ v.toValuationSubring := by
  obtain ⟨y, hy⟩ := exists_algebraMap_eq_repr_of_isIntegral (O := v.toValuationSubring) pb h
    (fun j => isIntegral_of_forall_ord_fiber_nonneg v (hint j)) i
  rw [← hy]
  exact y.2

private theorem repr_mem_of_forall_mem_fiber (v : Place K F) (pb : PowerBasis F F') (h : F')
    (hint : ∀ j : Fin pb.dim, ∀ w ∈ v.fiber F',
      h * ((minpolyDiv F pb.gen).coeff j / aeval pb.gen (derivative (minpoly F pb.gen))) ∈ w.toValuationSubring)
    (i : Fin pb.dim) : pb.basis.repr h i ∈ v.toValuationSubring :=
  repr_mem_of_forall_ord_fiber_nonneg v pb h (fun j w hw => ord_nonneg_of_mem' w (hint j w hw)) i

end AtPlace
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve.AlphaEngine"

section Modular

variable (N q : ℕ) [NeZero N] [Fact q.Prime]

@[reducible] private noncomputable def alongAlgebra : Algebra (modularFunctionFieldBar N) (modularFunctionFieldBar (N * q)) :=
  algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q)

attribute [local instance] alongAlgebra

private theorem alongTower :
    IsScalarTower (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (modularFunctionFieldBar (N * q)) :=
  isScalarTower_along _

attribute [local instance] alongTower

variable {N q}

private theorem algebraMap_along :
    algebraMap (modularFunctionFieldBar N) (modularFunctionFieldBar (N * q)) =
      (heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom :=
  rfl

private theorem algebraMap_along_apply (c : modularFunctionFieldBar N) :
    algebraMap (modularFunctionFieldBar N) (modularFunctionFieldBar (N * q)) c =
      heckeAlphaBar (AlgebraicClosure ℚ) N q c := by
  rw [algebraMap_along, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]

private theorem alpha_injective : Function.Injective (heckeAlphaBar (AlgebraicClosure ℚ) N q) := by
  rw [← AlgHom.coe_toRingHom]
  exact (heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom.injective

private theorem finrank_along
    (hdeg : finrankAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) = q + 1) :
    Module.finrank (modularFunctionFieldBar N) (modularFunctionFieldBar (N * q)) = q + 1 :=
  hdeg

private theorem finiteDimensional_along
    (hdeg : finrankAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) = q + 1) :
    FiniteDimensional (modularFunctionFieldBar N) (modularFunctionFieldBar (N * q)) := by
  have h := finrank_along hdeg
  exact Module.finite_of_finrank_pos (by omega)

omit [NeZero N] in
private theorem charZero_bar : CharZero (modularFunctionFieldBar N) :=
  charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)).injective

private theorem isSeparable_along
    (hdeg : finrankAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) = q + 1) :
    Algebra.IsSeparable (modularFunctionFieldBar N) (modularFunctionFieldBar (N * q)) := by
  haveI := finiteDimensional_along hdeg
  haveI := Algebra.IsAlgebraic.of_finite (modularFunctionFieldBar N) (modularFunctionFieldBar (N * q))
  haveI := charZero_bar (N := N)
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

private theorem adjoin_along_eq_top (z : modularFunctionFieldBar (N * q))
    (hgen : IntermediateField.adjoin (AlgebraicClosure ℚ)
      (Set.range (heckeAlphaBar (AlgebraicClosure ℚ) N q) ∪ {z}) = ⊤) :
    IntermediateField.adjoin (modularFunctionFieldBar N) ({z} : Set (modularFunctionFieldBar (N * q))) = ⊤ := by
  have hle : IntermediateField.adjoin (AlgebraicClosure ℚ)
      (Set.range (heckeAlphaBar (AlgebraicClosure ℚ) N q) ∪ {z}) ≤
        (IntermediateField.adjoin (modularFunctionFieldBar N)
          ({z} : Set (modularFunctionFieldBar (N * q)))).restrictScalars (AlgebraicClosure ℚ) := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ (⟨a, rfl⟩ | rfl)
    · exact (IntermediateField.mem_restrictScalars _).mpr (IntermediateField.algebraMap_mem _ a)
    · exact (IntermediateField.mem_restrictScalars _).mpr
        (IntermediateField.subset_adjoin _ _ (Set.mem_singleton _))
  rw [hgen] at hle
  rw [eq_top_iff]
  intro f _
  exact (IntermediateField.mem_restrictScalars _).mp (hle IntermediateField.mem_top)

private theorem aeval_along_eq (m : Polynomial (modularFunctionFieldBar N)) (z : modularFunctionFieldBar (N * q)) :
    aeval z m = (m.map (heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom).eval z := by
  rw [aeval_def, eval₂_eq_eval_map]
  rfl

private theorem exists_powerBasis_along
    (hdeg : finrankAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) = q + 1)
    (z : modularFunctionFieldBar (N * q))
    (hgen : IntermediateField.adjoin (AlgebraicClosure ℚ)
      (Set.range (heckeAlphaBar (AlgebraicClosure ℚ) N q) ∪ {z}) = ⊤)
    (m : Polynomial (modularFunctionFieldBar N)) (hm : m.Monic) (hdegm : m.natDegree = q + 1)
    (hroot : (m.map (heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom).eval z = 0) :
    ∃ pb : PowerBasis (modularFunctionFieldBar N) (modularFunctionFieldBar (N * q)),
      pb.gen = z ∧ pb.dim = q + 1 ∧ minpoly (modularFunctionFieldBar N) z = m := by
  have hgen' := adjoin_along_eq_top z hgen
  have haeval : aeval z m = 0 := by rw [aeval_along_eq]; exact hroot
  have hfin := finrank_along hdeg
  have hmin : minpoly (modularFunctionFieldBar N) z = m :=
    minpoly_eq_of_monic_of_natDegree_eq hm haeval (by rw [hdegm, hfin]) hgen'
  have hint : IsIntegral (modularFunctionFieldBar N) z := ⟨m, hm, by rwa [← aeval_def]⟩
  obtain ⟨pb, hpb, hdim⟩ := exists_powerBasis_of_adjoin_eq_top hint hgen'
  exact ⟨pb, hpb, by rw [hdim, hmin, hdegm], hmin⟩

private theorem adjoin_union_eq_top_of_linearIndependent
    (hdeg : finrankAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) = q + 1)
    (z : modularFunctionFieldBar (N * q))
    (hli : LinearIndependent (modularFunctionFieldBar N) fun i : Fin (q + 1) => z ^ (i : ℕ)) :
    IntermediateField.adjoin (AlgebraicClosure ℚ)
      (Set.range (heckeAlphaBar (AlgebraicClosure ℚ) N q) ∪ {z}) = ⊤ := by
  haveI := finiteDimensional_along hdeg
  have hspan := hli.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin, finrank_along hdeg])
  rw [eq_top_iff]
  intro f _
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (modularFunctionFieldBar N)).mp
    (hspan ▸ Submodule.mem_top : f ∈ Submodule.span (modularFunctionFieldBar N)
      (Set.range fun i : Fin (q + 1) => z ^ (i : ℕ)))
  refine sum_mem fun i _ => ?_
  rw [Algebra.smul_def, algebraMap_along_apply]
  have hz : z ∈ IntermediateField.adjoin (AlgebraicClosure ℚ)
      (Set.range (heckeAlphaBar (AlgebraicClosure ℚ) N q) ∪ {z}) :=
    IntermediateField.subset_adjoin _ _ (Or.inr rfl)
  have hc : heckeAlphaBar (AlgebraicClosure ℚ) N q (c i) ∈ IntermediateField.adjoin (AlgebraicClosure ℚ)
      (Set.range (heckeAlphaBar (AlgebraicClosure ℚ) N q) ∪ {z}) :=
    IntermediateField.subset_adjoin _ _ (Or.inl ⟨c i, rfl⟩)
  exact mul_mem hc (pow_mem hz _)

private theorem exists_monic_data_of_linearIndependent
    (hdeg : finrankAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) = q + 1)
    (z : modularFunctionFieldBar (N * q))
    (hli : LinearIndependent (modularFunctionFieldBar N) fun i : Fin (q + 1) => z ^ (i : ℕ)) :
    IntermediateField.adjoin (AlgebraicClosure ℚ)
        (Set.range (heckeAlphaBar (AlgebraicClosure ℚ) N q) ∪ {z}) = ⊤ ∧
      ∃ m : Polynomial (modularFunctionFieldBar N), m.Monic ∧ m.natDegree = q + 1 ∧
        (m.map (heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom).eval z = 0 ∧
        z ^ (q + 1) =
          ∑ i : Fin (q + 1), (-(heckeAlphaBar (AlgebraicClosure ℚ) N q (m.coeff i))) * z ^ (i : ℕ) := by
  haveI := finiteDimensional_along hdeg
  have hgen := adjoin_union_eq_top_of_linearIndependent hdeg z hli
  have hint : IsIntegral (modularFunctionFieldBar N) z := IsIntegral.of_finite (modularFunctionFieldBar N) z
  have hnat : (minpoly (modularFunctionFieldBar N) z).natDegree = q + 1 := by
    rw [natDegree_minpoly_of_adjoin_eq_top z (adjoin_along_eq_top z hgen), finrank_along hdeg]
  refine ⟨hgen, minpoly (modularFunctionFieldBar N) z, minpoly.monic hint, hnat, ?_, ?_⟩
  · rw [← aeval_along_eq]
    exact minpoly.aeval _ _
  · have h := pow_eq_sum_neg_coeff_minpoly z hint hnat
    simp only [algebraMap_along_apply] at h
    exact h

private theorem coeff_mem_of_forall_mem (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
    (hdeg : finrankAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) = q + 1)
    (z : modularFunctionFieldBar (N * q))
    (hgen : IntermediateField.adjoin (AlgebraicClosure ℚ)
      (Set.range (heckeAlphaBar (AlgebraicClosure ℚ) N q) ∪ {z}) = ⊤)
    (m : Polynomial (modularFunctionFieldBar N)) (hm : m.Monic) (hdegm : m.natDegree = q + 1)
    (hroot : (m.map (heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom).eval z = 0)
    (u₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hz : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα = u₀ → z ∈ W.toValuationSubring)
    (i : ℕ) : m.coeff i ∈ u₀.toValuationSubring := by
  haveI := finiteDimensional_along hdeg
  haveI := isSeparable_along hdeg
  haveI := hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)
  obtain ⟨-, -, -, hmin⟩ := exists_powerBasis_along hdeg z hgen m hm hdegm hroot
  rw [← hmin]
  refine coeff_minpoly_mem_of_isIntegral u₀ z (isIntegral_of_forall_ord_fiber_nonneg u₀ fun W hW => ?_) i
  exact ord_nonneg_of_mem' W (hz W (Place.mem_fiber.mp hW))

private theorem coeff_mem_of_forall_mem_affine (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
    (hdeg : finrankAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) = q + 1)
    (z : modularFunctionFieldBar (N * q))
    (hgen : IntermediateField.adjoin (AlgebraicClosure ℚ)
      (Set.range (heckeAlphaBar (AlgebraicClosure ℚ) N q) ∪ {z}) = ⊤)
    (m : Polynomial (modularFunctionFieldBar N)) (hm : m.Monic) (hdegm : m.natDegree = q + 1)
    (hroot : (m.map (heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom).eval z = 0)
    (hzreg : ∀ u₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      CharPModel.jBar N ∈ u₀.toValuationSubring →
      ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα = u₀ → z ∈ W.toValuationSubring) :
    ∀ i : ℕ, ∀ u₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      CharPModel.jBar N ∈ u₀.toValuationSubring → m.coeff i ∈ u₀.toValuationSubring :=
  fun i u₀ hu₀ => coeff_mem_of_forall_mem hα hdeg z hgen m hm hdegm hroot u₀ (hzreg u₀ hu₀) i

end Modular
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve.AlphaEngine"

end ModularCurve.AlphaEngine
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve.AlphaEngine"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve.AlphaEngine"
end
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve.AlphaEngine"

p2m_open "AlgebraicCurve ModularCurve~jBar P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve ModularCurve.CharPModel ModularCurve.PlaceSpecialization~IsInftySide~jFun~tInfty~tZero~IsCuspidal~IsZeroSide P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve.PlaceSpecialization"

private theorem penC_FIN
    (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (k : Type*) [Field k] [CharP k ℓ] (red : A →+* k) (fm : FibreModel N A ℓ k red)
    (v : Place k (modularFunctionFieldC k N))
    (hv : (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ∈ v.toValuationSubring) :
    (∀ b : fm.BFin, fm.piFin b ∈ v.toValuationSubring) ∧
      ∀ g : modularFunctionFieldC k N, g ∈ v.toValuationSubring →
        ∃ b b' : fm.BFin, ¬ v.HasValue (fm.piFin b') (0 : k) ∧ g * fm.piFin b' = fm.piFin b :=
  ModularCurve.CharPModel.FibreModel.piFin_range_localizes_of_jqModC_mem N A ℓ hℓN k red fm v hv

private theorem penC_GLN
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) (hqN : ¬ q ∣ N) :
    ∀ t : modularFunctionFieldBar N,
      (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (N * q) A.toSubring red →
      (∀ u₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        CharPModel.jBar N ∈ u₀.toValuationSubring → t ∈ u₀.toValuationSubring) →
      ∃ p : Polynomial (CharPModel.affineBaseFin N A), p.Monic ∧
        Polynomial.eval₂ (CharPModel.affineBaseFin N A).subtype t p = 0 :=
  ModularCurve.CharPModel.exists_monic_eval2_affineBaseFin_eq_zero_of_mem_modularLocalized_of_forall_mem_of_jBar_mem red hqN

private theorem deuring_ker_eq_maximalIdeal {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k) (hred : Function.Surjective red) :
    RingHom.ker red = IsLocalRing.maximalIdeal A :=
  ((IsLocalRing.maximal_ideal_unique A).unique (RingHom.ker_isMaximal_of_surjective red hred)
    (IsLocalRing.maximalIdeal.isMaximal A))

private noncomputable def deuring_redBarEquiv {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k) (hred : Function.Surjective red) :
    IsLocalRing.ResidueField A ≃+* k :=
  (Ideal.quotEquivOfEq (deuring_ker_eq_maximalIdeal red hred).symm).trans
    (RingHom.quotientKerEquivOfSurjective hred)

private theorem deuring_isAlgClosed_of_ringEquiv {K : Type*} {k : Type*} [Field K] [Field k] [IsAlgClosed k]
    (σ : K ≃+* k) : IsAlgClosed K := by
  refine IsAlgClosed.of_exists_root (k := K) fun p _ hirr => ?_
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root (p.map (σ : K →+* k))
    (by rw [Polynomial.degree_map]; exact (Polynomial.degree_pos_of_irreducible hirr).ne')
  refine ⟨σ.symm y, ?_⟩
  have h1 : (σ : K →+* k) (p.eval (σ.symm y)) = 0 := by
    rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]
    have h2 : (σ : K →+* k) (σ.symm y) = y := σ.apply_symm_apply y
    rw [h2]
    exact hy
  exact (map_eq_zero_iff (σ : K →+* k) (σ : K →+* k).injective).mp h1

private theorem penC_isAlgClosed_of_surjective {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]
    (red : A →+* k) (hred : Function.Surjective red) : IsAlgClosed k :=
  deuring_isAlgClosed_of_ringEquiv (deuring_redBarEquiv red hred).symm

private theorem penC_arithFrobC_smul_mem_ssPlaces_univ (q N : ℕ) [NeZero N] (K : Type*) [Field K]
    [DecidableEq K] [Fact q.Prime] [CharP K q] [PerfectField K] :
    ∀ w ∈ ModularCurve.ssPlaces q N K,
      ModularCurve.arithFrobC q K N • w ∈ ModularCurve.ssPlaces q N K :=
  ModularCurve.arithFrobC_smul_mem_ssPlaces_univ q N K

private theorem penC_gaussLemma_inf
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) (hqN : ¬ q ∣ N) :
    ∀ t : modularFunctionFieldBar N,
      (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (N * q) A.toSubring red →
      (∀ u₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        (CharPModel.jBar N)⁻¹ ∈ u₀.toValuationSubring → t ∈ u₀.toValuationSubring) →
      ∃ p : Polynomial (CharPModel.affineBaseInf N A), p.Monic ∧
        Polynomial.eval₂ (CharPModel.affineBaseInf N A).subtype t p = 0 := by
  intro t ht hu
  exact ModularCurve.CharPModel.exists_monic_eval2_affineBaseInf_eq_zero_of_mem_modularLocalized_of_forall_inv_jBar_mem red hqN t ht hu

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_qExpand jNum jNumQ jq ofPowerSeries_coeff_of_neg coeff_jq_neg_one jqN evalAtJ evalAtJ_X ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffMap_algebraMap coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_eq_map_intCast modularFunctionFieldC jqModC_mem jqNModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff KroneckerCongruence ssPlaces jGeomGen jNGeomGen IsAffineGeomPlace cuspInftyGeom ord_cuspInftyGeom_jq order_jqModC_def jqModC_ne_zero_def jq_mem_full coeff_jqModC_neg_one coeffSemilinearAut.coeffMap_qExpand coeffSemilinearAut.coeffMap_jqModC coeffSemilinearAut.coeffMap_mem_modularFunctionFieldC coeffSemilinearAut arithFrobC isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_jqModC qExpandAlgHomC qExpandAlgHomC_apply divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full jqModC_mem_full coeffMap_qExpand CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.mem_localizedAtKer CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc CharPReduction.redRes_ne_zero_of_notMem CharPReduction.redLoc_spec CharPReduction.redLoc_coe CharPReduction.redLocHom_apply CharPReduction.constSeries CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.affineBaseFin CharPModel.affineBaseInf CharPModel.FibreModel modularFunctionFieldBar_eq_modularFunctionFieldC finiteAlong_heckeAlphaBar_of_prime isCurveOver_modularFunctionFieldBar arithFrobC_smul_eq_frobOnPlacesGeomLevel CharPReduction.modularRedLocHom_mem exists_mem_riemannRochSpace_notMem_sub_single_of_le_degree isAffineGeomPlace_frobOnPlacesGeomLevel coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized_mul_of_not_dvd coeffEmb_jq exists_isAtkinLehnerAutFull_of_prime_of_not_dvd exists_regularProlongation_modularFunctionFieldBar_mul_of_not_dvd geomAut_atkinLehner_comp_legs hasPrincipalDivisors_modularFunctionFieldBar_unconditional place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin finrankAlong_heckeBetaBar CharPModel.FibreModel.piFin_range_localizes_of_jqModC_mem CharPModel.exists_monic_eval2_affineBaseFin_eq_zero_of_mem_modularLocalized_of_forall_mem_of_jBar_mem arithFrobC_smul_mem_ssPlaces_univ adjoin_jBar_jNBar_eq_top nonempty_modularPolynomialData relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi CharPReduction.mem_or_inv_mem_modularLocalized pow_char_eq_coeffMap_frobenius_qExpand qExpand_jqModC_eq_pow_unconditional mem_integralCoeffs_of_integral_affineBaseInf CharPModel.exists_monic_eval2_affineBaseInf_eq_zero_of_mem_modularLocalized_of_forall_inv_jBar_mem"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.atkinLehnerBar ProlongationTuple.jFun ProlongationTuple.jQFun ProlongationTuple.tInfty ProlongationTuple.tZero ProlongationTuple.IsCuspidal ProlongationTuple.IsInftySide ProlongationTuple.IsZeroSide ProlongationTuple ProlongationTuple.residue₁_apply ProlongationTuple.residue₂_apply ProlongationTuple.OrderLawFixed ProlongationTuple.CuspLawInfty reduceFst reduceSnd IsStrictFst IsStrictSnd sp d0_j_pole d1 ReducesDivisors fibreReduction chartClosure chartLocalSetFst ChartEtaleAt IsChartAt HasCoordinates ProlongationTuple.isCuspidal_of_not_isAffineGeomPlace_reduceFst ProlongationTuple.not_isAffineGeomPlace_reduceFst_of_isCuspidal ProlongationTuple.isInftySide_or_isZeroSide_of_isCuspidal ProlongationTuple.not_isInftySide_of_isZeroSide ProlongationTuple.reduceFst_eq_frobOnPlacesGeomLevel_reduceSnd_of_isZeroSide exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace ProlongationTuple.isInftySide_atkinLehnerBar_smul_iff reduceFst_atkinLehnerBar_smul mem_chartLocalSetFst_of_split hasCoordinates_of_sp_eq_spPlace"
p2m_open "ModularCurve.PlaceSpecialization~IsInftySide~jFun~tInfty~tZero~IsCuspidal~IsZeroSide ModularCurve~jBar"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

variable {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

private def penA_EtaleAt (v : Place k (modularFunctionFieldC k N))
    (S : Set (modularFunctionFieldBar (N * q))) : Prop :=
  ∃ (z : modularFunctionFieldBar (N * q)) (m : Polynomial (modularFunctionFieldBar N)),
    z ∈ S ∧
    (∃ hz₂ : z ∈ R.R₂.integers, ∃ n : ℤ, ¬ (q : ℤ) ∣ n ∧
      ((R.residue₂ ⟨z, hz₂⟩ : modularFunctionFieldC k N) : LaurentSeries k).coeff n ≠ 0) ∧
    IntermediateField.adjoin (AlgebraicClosure ℚ)
      (Set.range (heckeAlphaBar (AlgebraicClosure ℚ) N q) ∪ {z}) = ⊤ ∧
    m.Monic ∧ m.natDegree = q + 1 ∧
    (m.map (heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom).eval z = 0 ∧
    (∀ i : ℕ, heckeAlphaBar (AlgebraicClosure ℚ) N q (m.coeff i) ∈ Subring.closure S) ∧
    ∀ h : (Polynomial.derivative (m.map (heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom)).eval z
        ∈ R.R₁.integers,
      ¬ v.HasValue (R.residue₁ ⟨_, h⟩) (0 : k)

private noncomputable def penC_gens (fm : FibreModel N A q k red) : Set (modularFunctionFieldBar (N * q)) :=
  Set.range (fun b : fm.BFin =>
      heckeAlphaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)))
    ∪ Set.range (fun b : fm.BFin =>
      heckeBetaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)))

private noncomputable def penC_ring (fm : FibreModel N A q k red) : Subring (modularFunctionFieldBar (N * q)) :=
  Subring.closure (penC_gens fm)

private noncomputable def penC_S (fm : FibreModel N A q k red) : Set (modularFunctionFieldBar (N * q)) :=
  (penC_ring fm : Set (modularFunctionFieldBar (N * q)))

private theorem penC_mem_S_iff (fm : FibreModel N A q k red) {s : modularFunctionFieldBar (N * q)} :
    s ∈ penC_S fm ↔ s ∈ penC_ring fm := Iff.rfl

private def penC_Good (v : Place k (modularFunctionFieldC k N)) (s : modularFunctionFieldBar (N * q)) : Prop :=
  ∃ h : s ∈ R.R₁.integers,
    (R.residue₁ ⟨s, h⟩ : modularFunctionFieldC k N) ∈ v.toValuationSubring ∧
    (∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      P.IsStrictFst W → P.reduceFst W = v →
        ∃ a : A, W.HasValue s (a : AlgebraicClosure ℚ) ∧ v.HasValue (R.residue₁ ⟨s, h⟩) (red a)) ∧
    (∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      P.reduceFst W = v → s ∈ W.toValuationSubring)

omit [Fact (Nat.Prime q)] [CharP k q] in

private theorem penA_hasValue_add {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)
    {x y : F} {a b : K} (hx : w.HasValue x a) (hy : w.HasValue y b) : w.HasValue (x + y) (a + b) := by
  obtain ⟨hxm, hxr⟩ := hx
  obtain ⟨hym, hyr⟩ := hy
  refine ⟨add_mem hxm hym, ?_⟩
  have e : (⟨x + y, add_mem hxm hym⟩ : w.toValuationSubring) = ⟨x, hxm⟩ + ⟨y, hym⟩ := rfl
  rw [e, map_add, hxr, hyr, map_add]

omit [Fact (Nat.Prime q)] [CharP k q] in

private theorem penA_hasValue_neg {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)
    {x : F} {a : K} (hx : w.HasValue x a) : w.HasValue (-x) (-a) := by
  obtain ⟨hxm, hxr⟩ := hx
  refine ⟨neg_mem hxm, ?_⟩
  have e : (⟨-x, neg_mem hxm⟩ : w.toValuationSubring) = -⟨x, hxm⟩ := rfl
  rw [e, map_neg, hxr, map_neg]

section ValueSteps

variable {v : Place k (modularFunctionFieldC k N)}

variable {Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))}

private theorem penA_valued_zero (h0 : (0 : modularFunctionFieldBar (N * q)) ∈ R.R₁.integers) :
    ∃ c : A, Q.HasValue (0 : modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ) ∧
      v.HasValue (R.residue₁ ⟨0, h0⟩) (red c) := by
  refine ⟨0, ?_, ?_⟩
  · rw [ZeroMemClass.coe_zero]
    have h := Q.hasValue_algebraMap (0 : AlgebraicClosure ℚ)
    rwa [map_zero] at h
  · have e : R.residue₁ ⟨0, h0⟩ = 0 := map_zero R.residue₁
    rw [e, map_zero]
    have h := v.hasValue_algebraMap (0 : k)
    rwa [map_zero] at h

private theorem penA_valued_one (h1 : (1 : modularFunctionFieldBar (N * q)) ∈ R.R₁.integers) :
    ∃ c : A, Q.HasValue (1 : modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ) ∧
      v.HasValue (R.residue₁ ⟨1, h1⟩) (red c) := by
  refine ⟨1, ?_, ?_⟩
  · rw [OneMemClass.coe_one]
    exact Q.hasValue_one
  · have e : R.residue₁ ⟨1, h1⟩ = 1 := map_one R.residue₁
    rw [e, map_one]
    exact v.hasValue_one

private theorem penA_valued_add {x y : modularFunctionFieldBar (N * q)} (hxI : x ∈ R.R₁.integers)
    (hyI : y ∈ R.R₁.integers)
    (hx : ∃ c : A, Q.HasValue x (c : AlgebraicClosure ℚ) ∧ v.HasValue (R.residue₁ ⟨x, hxI⟩) (red c))
    (hy : ∃ c : A, Q.HasValue y (c : AlgebraicClosure ℚ) ∧ v.HasValue (R.residue₁ ⟨y, hyI⟩) (red c)) :
    ∃ c : A, Q.HasValue (x + y) (c : AlgebraicClosure ℚ) ∧
      v.HasValue (R.residue₁ ⟨x + y, add_mem hxI hyI⟩) (red c) := by
  obtain ⟨c₁, hc₁, hc₁'⟩ := hx
  obtain ⟨c₂, hc₂, hc₂'⟩ := hy
  refine ⟨c₁ + c₂, ?_, ?_⟩
  · have hcoe : ((c₁ + c₂ : A) : AlgebraicClosure ℚ) = (c₁ : AlgebraicClosure ℚ) + c₂ := rfl
    rw [hcoe]
    exact penA_hasValue_add Q hc₁ hc₂
  · have e : R.residue₁ ⟨x + y, add_mem hxI hyI⟩ = R.residue₁ ⟨x, hxI⟩ + R.residue₁ ⟨y, hyI⟩ :=
      map_add R.residue₁ ⟨x, hxI⟩ ⟨y, hyI⟩
    rw [e, map_add]
    exact penA_hasValue_add v hc₁' hc₂'

private theorem penA_valued_neg {x : modularFunctionFieldBar (N * q)} (hxI : x ∈ R.R₁.integers)
    (hx : ∃ c : A, Q.HasValue x (c : AlgebraicClosure ℚ) ∧ v.HasValue (R.residue₁ ⟨x, hxI⟩) (red c)) :
    ∃ c : A, Q.HasValue (-x) (c : AlgebraicClosure ℚ) ∧
      v.HasValue (R.residue₁ ⟨-x, neg_mem hxI⟩) (red c) := by
  obtain ⟨c, hc, hc'⟩ := hx
  refine ⟨-c, ?_, ?_⟩
  · have hcoe : ((-c : A) : AlgebraicClosure ℚ) = -(c : AlgebraicClosure ℚ) := rfl
    rw [hcoe]
    exact penA_hasValue_neg Q hc
  · have e : R.residue₁ ⟨-x, neg_mem hxI⟩ = -R.residue₁ ⟨x, hxI⟩ := map_neg R.residue₁ ⟨x, hxI⟩
    rw [e, map_neg]
    exact penA_hasValue_neg v hc'

private theorem penA_valued_mul {x y : modularFunctionFieldBar (N * q)} (hxI : x ∈ R.R₁.integers)
    (hyI : y ∈ R.R₁.integers)
    (hx : ∃ c : A, Q.HasValue x (c : AlgebraicClosure ℚ) ∧ v.HasValue (R.residue₁ ⟨x, hxI⟩) (red c))
    (hy : ∃ c : A, Q.HasValue y (c : AlgebraicClosure ℚ) ∧ v.HasValue (R.residue₁ ⟨y, hyI⟩) (red c)) :
    ∃ c : A, Q.HasValue (x * y) (c : AlgebraicClosure ℚ) ∧
      v.HasValue (R.residue₁ ⟨x * y, mul_mem hxI hyI⟩) (red c) := by
  obtain ⟨c₁, hc₁, hc₁'⟩ := hx
  obtain ⟨c₂, hc₂, hc₂'⟩ := hy
  refine ⟨c₁ * c₂, ?_, ?_⟩
  · have hcoe : ((c₁ * c₂ : A) : AlgebraicClosure ℚ) = (c₁ : AlgebraicClosure ℚ) * c₂ := rfl
    rw [hcoe]
    exact hc₁.mul hc₂
  · have e : R.residue₁ ⟨x * y, mul_mem hxI hyI⟩ = R.residue₁ ⟨x, hxI⟩ * R.residue₁ ⟨y, hyI⟩ :=
        R.residue₁.map_mul ⟨x, hxI⟩ ⟨y, hyI⟩
    rw [e, map_mul]
    exact hc₁'.mul hc₂'

end ValueSteps
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve.AlphaEngine"

private theorem penC_good_zero (v : Place k (modularFunctionFieldC k N)) : penC_Good R v 0 := by
  refine ⟨zero_mem _, ?_, ?_, ?_⟩
  · have e : R.residue₁ ⟨0, zero_mem _⟩ = 0 := map_zero R.residue₁
    rw [e]
    exact zero_mem _
  · intro W _ _
    exact penA_valued_zero R (zero_mem _)
  · intro W _
    exact zero_mem _

private theorem penC_good_one (v : Place k (modularFunctionFieldC k N)) : penC_Good R v 1 := by
  refine ⟨one_mem _, ?_, ?_, ?_⟩
  · have e : R.residue₁ ⟨1, one_mem _⟩ = 1 := map_one R.residue₁
    rw [e]
    exact one_mem _
  · intro W _ _
    exact penA_valued_one R (one_mem _)
  · intro W _
    exact one_mem _

private theorem penC_good_add (v : Place k (modularFunctionFieldC k N)) {s t : modularFunctionFieldBar (N * q)}
    (hs : penC_Good R v s) (ht : penC_Good R v t) : penC_Good R v (s + t) := by
  obtain ⟨hsI, hsr, hsv, hso⟩ := hs
  obtain ⟨htI, htr, htv, hto⟩ := ht
  refine ⟨add_mem hsI htI, ?_, ?_, ?_⟩
  · have e : R.residue₁ ⟨s + t, add_mem hsI htI⟩ = R.residue₁ ⟨s, hsI⟩ + R.residue₁ ⟨t, htI⟩ :=
      map_add R.residue₁ ⟨s, hsI⟩ ⟨t, htI⟩
    rw [e]
    exact add_mem hsr htr
  · intro W hW hWv
    exact penA_valued_add R hsI htI (hsv W hW hWv) (htv W hW hWv)
  · intro W hW
    exact add_mem (hso W hW) (hto W hW)

private theorem penC_good_neg (v : Place k (modularFunctionFieldC k N)) {s : modularFunctionFieldBar (N * q)}
    (hs : penC_Good R v s) : penC_Good R v (-s) := by
  obtain ⟨hsI, hsr, hsv, hso⟩ := hs
  refine ⟨neg_mem hsI, ?_, ?_, ?_⟩
  · have e : R.residue₁ ⟨-s, neg_mem hsI⟩ = -R.residue₁ ⟨s, hsI⟩ := map_neg R.residue₁ ⟨s, hsI⟩
    rw [e]
    exact neg_mem hsr
  · intro W hW hWv
    exact penA_valued_neg R hsI (hsv W hW hWv)
  · intro W hW
    exact neg_mem (hso W hW)

private theorem penC_good_mul (v : Place k (modularFunctionFieldC k N)) {s t : modularFunctionFieldBar (N * q)}
    (hs : penC_Good R v s) (ht : penC_Good R v t) : penC_Good R v (s * t) := by
  obtain ⟨hsI, hsr, hsv, hso⟩ := hs
  obtain ⟨htI, htr, htv, hto⟩ := ht
  refine ⟨mul_mem hsI htI, ?_, ?_, ?_⟩
  · have e : R.residue₁ ⟨s * t, mul_mem hsI htI⟩ = R.residue₁ ⟨s, hsI⟩ * R.residue₁ ⟨t, htI⟩ :=
        R.residue₁.map_mul ⟨s, hsI⟩ ⟨t, htI⟩
    rw [e]
    exact mul_mem hsr htr
  · intro W hW hWv
    exact penA_valued_mul R hsI htI (hsv W hW hWv) (htv W hW hWv)
  · intro W hW
    exact mul_mem (hso W hW) (hto W hW)

private def penC_goodSubring (v : Place k (modularFunctionFieldC k N)) : Subring (modularFunctionFieldBar (N * q)) where
  carrier := {s | penC_Good R v s}
  zero_mem' := penC_good_zero R v
  one_mem' := penC_good_one R v
  add_mem' := penC_good_add R v
  neg_mem' := penC_good_neg R v
  mul_mem' := penC_good_mul R v

private theorem penC_alpha_mem (fm : FibreModel N A q k red) (b : fm.BFin) :
    heckeAlphaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
      ∈ penC_S fm :=
  Subring.subset_closure (Or.inl ⟨b, rfl⟩)

private theorem penC_beta_mem (fm : FibreModel N A q k red) (b : fm.BFin) :
    heckeBetaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
      ∈ penC_S fm :=
  Subring.subset_closure (Or.inr ⟨b, rfl⟩)

private theorem penC_const_mem (fm : FibreModel N A q k red) (a : A) :
    algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ penC_S fm := by
  have hconst := penC_alpha_mem fm ⟨CharPModel.constantsHom N A a, fm.constFin_mem a⟩
  have hcomm : heckeAlphaBar (AlgebraicClosure ℚ) N q
      (CharPModel.constantsHom N A a : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) := by
    exact (heckeAlphaBar (AlgebraicClosure ℚ) N q).commutes (a : AlgebraicClosure ℚ)
  rw [hcomm] at hconst
  exact hconst

private theorem _root_.AlgebraicCurve.Place.ord_algebraMap_pn {K F : Type*} [Field K] [Field F]
    [Algebra K F] (v : Place K F) (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · exact (v.hasValue_algebraMap c).ord_eq_zero hc

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.AlgebraicCurve.Place.ord_algebraMap_pn" "AlgebraicCurve.Place.ord_algebraMap_pn"

private theorem penS_lsc_coeffEmb_qExpand (n : ℕ) [NeZero n] (x : LaurentSeries ℚ) :
    coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ n x)
      = qExpand (AlgebraicClosure ℚ) n (coeffEmb (AlgebraicClosure ℚ) x) := by
  ext m
  by_cases hm : (n : ℤ) ∣ m
  · obtain ⟨m, rfl⟩ := hm
    rw [coeffEmb_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffEmb_coeff]
  · rw [coeffEmb_coeff, qExpand_coeff_of_not_dvd n _ hm, qExpand_coeff_of_not_dvd n _ hm, map_zero]

private theorem penC_residue_surjective [IsAlgClosed k] (v : Place k (modularFunctionFieldC k N)) :
    Function.Surjective (algebraMap k v.ResidueField) := by
  have h1 : Module.finrank k v.ResidueField = 1 := place_deg_eq_one_of_isAlgClosed k N v
  intro x
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : v.ResidueField) one_ne_zero).mp h1 x
  exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩

private theorem penC_exists_j_value (v : Place k (modularFunctionFieldC k N)) (hv1 : jGeomGen k N ∈ v.toValuationSubring)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hw : P.sp w = v) :
    ∃ a₀ : A, 0 < w.ord (CharPModel.jBar N - algebraMap (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) (a₀ : AlgebraicClosure ℚ)) := by
  by_contra hcon
  have hle : ∀ a : A, w.ord (CharPModel.jBar N - algebraMap (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) (a : AlgebraicClosure ℚ)) ≤ 0 :=
    fun a => not_lt.mp (fun h => hcon ⟨a, h⟩)
  have hpole := P.d0_j_pole w hle
  rw [hw] at hpole
  have hnn : (0 : ℤ) ≤ v.ord (jGeomGen k N) := v.ord_nonneg_of_mem_pn hv1
  exact absurd hnn (not_le.mpr hpole)

private theorem penC_sub_mem_nonunits_of_hasValue {K F : Type*} [Field K] [Field F] [Algebra K F]
    (u : Place K F) {g : F} {c : K} (h : u.HasValue g c) :
    g - algebraMap K F c ∈ u.toValuationSubring.nonunits := by
  have hmem : g - algebraMap K F c ∈ u.toValuationSubring := sub_mem h.mem (u.algebraMap_mem' c)
  have hres : IsLocalRing.residue u.toValuationSubring ⟨g - algebraMap K F c, hmem⟩ = 0 := by
    have e : (⟨g - algebraMap K F c, hmem⟩ : u.toValuationSubring)
        = ⟨g, h.mem⟩ - algebraMap K u.toValuationSubring c := rfl
    rw [e, map_sub, h.residue_eq, u.residue_algebraMap, sub_self]
  exact ValuationSubring.coe_mem_nonunits_iff.mpr ((IsLocalRing.residue_eq_zero_iff _).mp hres)

private theorem penC_hasValue_of_sub_mem_nonunits {K F : Type*} [Field K] [Field F] [Algebra K F]
    (u : Place K F) {g : F} {c : K} (h : g - algebraMap K F c ∈ u.toValuationSubring.nonunits) :
    u.HasValue g c := by
  by_cases hgc : g = algebraMap K F c
  · rw [hgc]
    exact u.hasValue_algebraMap c
  · have hne : g - algebraMap K F c ≠ 0 := sub_ne_zero.mpr hgc
    obtain ⟨hmem, hmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp h
    exact u.hasValue_of_ord_sub_pos_pn ((u.mem_maximalIdeal_iff_ord_pos hne hmem).mp hmax)

private theorem penC_red_eq_zero_of_mem_maximalIdeal (hred : Function.Surjective red) {a : A}
    (ha : a ∈ IsLocalRing.maximalIdeal A) : red a = 0 := by
  have hker : RingHom.ker red = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective red hred)
  rw [← RingHom.mem_ker, hker]
  exact ha

private theorem penC_not_hasValue_zero_of_ne {K F : Type*} [Field K] [Field F] [Algebra K F] (u : Place K F)
    {g : F} {c : K} (h : u.HasValue g c) (hc : c ≠ 0) : ¬ u.HasValue g 0 :=
  fun h0 => hc (h.unique h0)

private theorem penC_frob_mem_nonunits (u : Place k (modularFunctionFieldC k N)) {x : modularFunctionFieldC k N}
    (hx : x ∈ (frobOnPlacesGeomLevel k N data hKr u).toValuationSubring.nonunits) :
    frobeniusGeomLevel k N data hKr x ∈ u.toValuationSubring.nonunits := by
  by_cases hx0 : x = 0
  · rw [hx0, map_zero]
    exact ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr ⟨zero_mem _, Ideal.zero_mem _⟩
  obtain ⟨hmem, hmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hx
  have hord : 0 < (frobOnPlacesGeomLevel k N data hKr u).ord x :=
    ((frobOnPlacesGeomLevel k N data hKr u).mem_maximalIdeal_iff_ord_pos hx0 hmem).mp hmax

  have hinv : x⁻¹ ∉ (frobOnPlacesGeomLevel k N data hKr u).toValuationSubring := by
    intro hmem'
    have h1 := (frobOnPlacesGeomLevel k N data hKr u).ord_nonneg_of_mem_pn hmem'
    rw [Place.ord_inv] at h1
    omega
  rw [mem_frobOnPlacesGeomLevel_iff, map_inv₀] at hinv

  have hFx0 : frobeniusGeomLevel k N data hKr x ≠ 0 := by
    intro h0
    apply hinv
    rw [h0, inv_zero]
    exact zero_mem _
  have hFmem : frobeniusGeomLevel k N data hKr x ∈ u.toValuationSubring :=
    (u.toValuationSubring.mem_or_inv_mem _).resolve_right hinv
  have hFord : 0 < u.ord (frobeniusGeomLevel k N data hKr x) := by
    by_contra hle
    apply hinv
    apply u.mem_of_ord_nonneg_pn (inv_ne_zero hFx0)
    rw [Place.ord_inv]
    omega
  exact ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr
    ⟨hFmem, (u.mem_maximalIdeal_iff_ord_pos hFx0 hFmem).mpr hFord⟩

private theorem penC_mem_nonunits_frob_of (u : Place k (modularFunctionFieldC k N)) {x : modularFunctionFieldC k N}
    (hx : frobeniusGeomLevel k N data hKr x ∈ u.toValuationSubring.nonunits) :
    x ∈ (frobOnPlacesGeomLevel k N data hKr u).toValuationSubring.nonunits := by
  by_cases hx0 : x = 0
  · rw [hx0]
    exact ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr ⟨zero_mem _, Ideal.zero_mem _⟩
  have hFx0 : frobeniusGeomLevel k N data hKr x ≠ 0 := (map_ne_zero _).mpr hx0
  obtain ⟨hmem, hmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hx
  have hord : 0 < u.ord (frobeniusGeomLevel k N data hKr x) := (u.mem_maximalIdeal_iff_ord_pos hFx0 hmem).mp hmax

  have hinv : x⁻¹ ∉ (frobOnPlacesGeomLevel k N data hKr u).toValuationSubring := by
    rw [mem_frobOnPlacesGeomLevel_iff, map_inv₀]
    intro hmem'
    have h1 := u.ord_nonneg_of_mem_pn hmem'
    rw [Place.ord_inv] at h1
    omega
  have hxmem : x ∈ (frobOnPlacesGeomLevel k N data hKr u).toValuationSubring :=
    ((frobOnPlacesGeomLevel k N data hKr u).toValuationSubring.mem_or_inv_mem x).resolve_right hinv
  have hxord : 0 < (frobOnPlacesGeomLevel k N data hKr u).ord x := by
    by_contra hle
    apply hinv
    apply (frobOnPlacesGeomLevel k N data hKr u).mem_of_ord_nonneg_pn (inv_ne_zero hx0)
    rw [Place.ord_inv]
    omega
  exact ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr
    ⟨hxmem, ((frobOnPlacesGeomLevel k N data hKr u).mem_maximalIdeal_iff_ord_pos hx0 hxmem).mpr hxord⟩

private theorem penC_isAffine_of_isAffine_frob (u : Place k (modularFunctionFieldC k N))
    (h : IsAffineGeomPlace k N (frobOnPlacesGeomLevel k N data hKr u)) : IsAffineGeomPlace k N u := by
  obtain ⟨hj, hjN⟩ := h
  have hq : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  refine ⟨?_, ?_⟩
  · have h1 : jGeomGen k N ∈ (frobOnPlacesGeomLevel k N data hKr u).toValuationSubring := hj
    rw [mem_frobOnPlacesGeomLevel_iff] at h1
    have h2 : frobeniusGeomLevel k N data hKr (jGeomGen k N) = jGeomGen k N ^ q := frobeniusGeomLevel_jq k N data hKr
    rw [h2] at h1
    exact u.toValuationSubring.mem_of_pow_mem' hq h1
  · have h1 : jNGeomGen k N ∈ (frobOnPlacesGeomLevel k N data hKr u).toValuationSubring := hjN
    rw [mem_frobOnPlacesGeomLevel_iff] at h1
    have h2 : frobeniusGeomLevel k N data hKr (jNGeomGen k N) = jNGeomGen k N ^ q := frobeniusGeomLevel_jqN k N data hKr
    rw [h2] at h1
    exact u.toValuationSubring.mem_of_pow_mem' hq h1

private theorem penC_isAffine_frob_of_isAffine (u : Place k (modularFunctionFieldC k N))
    (h : IsAffineGeomPlace k N u) : IsAffineGeomPlace k N (frobOnPlacesGeomLevel k N data hKr u) := by
  obtain ⟨hj, hjN⟩ := h
  refine ⟨?_, ?_⟩
  · show jGeomGen k N ∈ (frobOnPlacesGeomLevel k N data hKr u).toValuationSubring
    rw [mem_frobOnPlacesGeomLevel_iff]
    have h2 : frobeniusGeomLevel k N data hKr (jGeomGen k N) = jGeomGen k N ^ q := frobeniusGeomLevel_jq k N data hKr
    rw [h2]
    exact pow_mem hj q
  · show jNGeomGen k N ∈ (frobOnPlacesGeomLevel k N data hKr u).toValuationSubring
    rw [mem_frobOnPlacesGeomLevel_iff]
    have h2 : frobeniusGeomLevel k N data hKr (jNGeomGen k N) = jNGeomGen k N ^ q := frobeniusGeomLevel_jqN k N data hKr
    rw [h2]
    exact pow_mem hjN q

private theorem penC_reduceSnd_affine (v : Place k (modularFunctionFieldC k N)) (hvaff : IsAffineGeomPlace k N v)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hW : P.reduceFst W = v) :
    IsAffineGeomPlace k N (P.reduceSnd W) := by
  rcases P.d1 W with h | h
  · have h₁ : P.reduceFst W = frobOnPlacesGeomLevel k N data hKr (P.reduceSnd W) := h
    rw [hW] at h₁
    refine penC_isAffine_of_isAffine_frob (data := data) (hKr := hKr) _ ?_
    rw [← h₁]
    exact hvaff
  · have h₁ : frobOnPlacesGeomLevel k N data hKr (P.reduceFst W) = P.reduceSnd W := h
    rw [hW] at h₁
    rw [← h₁]
    exact penC_isAffine_frob_of_isAffine v hvaff

omit [Fact q.Prime] [NeZero N] in

private theorem penC_ramificationIndexAlong_pos' (φ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)
      →ₐ[AlgebraicClosure ℚ] laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)))
    (hφ : φ.toRingHom.IsIntegral) (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    0 < Place.ramificationIndexAlong φ W := by
  unfold Place.ramificationIndexAlong
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact W.ramificationIndex_pos (F := laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))

omit [Fact q.Prime] [NeZero N] in

private theorem penC_hasValue_of_restrictAlong
    (φ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)
      →ₐ[AlgebraicClosure ℚ] laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)))
    (hφ : φ.toRingHom.IsIntegral) (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    {x : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)} {c : AlgebraicClosure ℚ}
    (h : (W.restrictAlong φ hφ).HasValue x c) : W.HasValue (φ x) c := by
  by_cases hxc : x = algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) c
  · rw [hxc, φ.commutes]
    exact W.hasValue_algebraMap c
  · have hne : x - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) c ≠ 0 :=
      sub_ne_zero.mpr hxc
    have hmem : x - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) c
        ∈ (W.restrictAlong φ hφ).toValuationSubring :=
      sub_mem h.mem ((W.restrictAlong φ hφ).algebraMap_mem' c)
    have hmax : (⟨_, hmem⟩ : (W.restrictAlong φ hφ).toValuationSubring) ∈ IsLocalRing.maximalIdeal _ :=
      ValuationSubring.coe_mem_nonunits_iff.mp (penC_sub_mem_nonunits_of_hasValue _ h)
    have hord := ((W.restrictAlong φ hφ).mem_maximalIdeal_iff_ord_pos hne hmem).mp hmax
    apply W.hasValue_of_ord_sub_pos_pn
    rw [← φ.commutes, ← map_sub, W.ord_restrictAlong φ hφ]
    exact mul_pos (by exact_mod_cast penC_ramificationIndexAlong_pos' φ hφ W) hord

private theorem penC_hasValue_pow {K F : Type*} [Field K] [Field F] [Algebra K F] (u : Place K F)
    {g : F} {c : K} (h : u.HasValue g c) (n : ℕ) : u.HasValue (g ^ n) (c ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    exact u.hasValue_one
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul h

private theorem penC_mem_nonunits_of_pow_mem {K F : Type*} [Field K] [Field F] [Algebra K F] (u : Place K F)
    {g : F} {n : ℕ} (hn : n ≠ 0) (h : g ^ n ∈ u.toValuationSubring.nonunits) : g ∈ u.toValuationSubring.nonunits := by
  obtain ⟨hmem, hmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp h
  have hg : g ∈ u.toValuationSubring := u.toValuationSubring.mem_of_pow_mem' hn hmem
  have hpow : (⟨g ^ n, hmem⟩ : u.toValuationSubring) = (⟨g, hg⟩ : u.toValuationSubring) ^ n := by
    apply Subtype.ext
    simp
  rw [hpow] at hmax
  exact ValuationSubring.coe_mem_nonunits_iff.mpr
    ((IsLocalRing.maximalIdeal.isMaximal _).isPrime.mem_of_pow_mem n hmax)

private theorem penC_hasValue_frob_apply (u : Place k (modularFunctionFieldC k N)) {x : modularFunctionFieldC k N} {t : k}
    (h : (frobOnPlacesGeomLevel k N data hKr u).HasValue x t) : u.HasValue (frobeniusGeomLevel k N data hKr x) t := by
  have h1 := penC_frob_mem_nonunits u (penC_sub_mem_nonunits_of_hasValue _ h)
  rw [map_sub, AlgHom.commutes] at h1
  exact penC_hasValue_of_sub_mem_nonunits u h1

private theorem penC_hasValue_frobOnPlaces (u : Place k (modularFunctionFieldC k N)) {x : modularFunctionFieldC k N} {t : k}
    (h : u.HasValue (frobeniusGeomLevel k N data hKr x) t) : (frobOnPlacesGeomLevel k N data hKr u).HasValue x t := by
  have h1 := penC_sub_mem_nonunits_of_hasValue u h
  rw [← AlgHom.commutes (frobeniusGeomLevel k N data hKr) t, ← map_sub] at h1
  exact penC_hasValue_of_sub_mem_nonunits _ (penC_mem_nonunits_frob_of u h1)

private theorem penC_redBar_comp_residue : R.redBar.comp (IsLocalRing.residue A) = red :=
  RingHom.ext fun a => R.redBar_residue a

private theorem penC_good_residue_of_coe_eq (g : modularFunctionFieldBar (N * q)) (y : LaurentSeries A)
    (hg : (g : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype y) :
    ∃ h : g ∈ R.R₁.integers, ((R.residue₁ ⟨g, h⟩ : modularFunctionFieldC k N) : LaurentSeries k) = coeffMap red y := by
  have hy : coeffMap A.subtype y ∈ modularFunctionFieldBar (N * q) := hg ▸ g.2
  obtain ⟨h, hres⟩ := R.residue₁_coeffMap y hy
  have hgeq : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar (N * q)) = g := Subtype.ext hg.symm
  have key : ∃ h : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar (N * q)) ∈ R.R₁.integers,
      ((R.residue₁ ⟨_, h⟩ : modularFunctionFieldC k N) : LaurentSeries k) = coeffMap red y := by
    refine ⟨h, ?_⟩
    rw [R.residue₁_apply, R.ι_coe, hres, coeffMap_coeffMap, penC_redBar_comp_residue]
  exact hgeq ▸ key

private theorem penC_bfin_coe_mem_integralCoeffs (fm : FibreModel N A q k red) (b : fm.BFin) :
    ((b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) : LaurentSeries (AlgebraicClosure ℚ))
      ∈ CharPReduction.integralCoeffs A.toSubring :=
  mem_integralCoeffs_of_integral_affineBaseFin A N _ (fm.integralFin b)

private theorem penC_residue_alpha (fm : FibreModel N A q k red) (b : fm.BFin) :
    ∃ h : heckeAlphaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        ∈ R.R₁.integers,
      R.residue₁ ⟨_, h⟩ = fm.piFin b := by
  have hint := penC_bfin_coe_mem_integralCoeffs fm b
  have hcoe : ((heckeAlphaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) :
      modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype (packA_g A ⟨_, hint⟩) := by
    rw [coe_heckeAlphaBar, coeffMap_subtype_packA_g]
  obtain ⟨h, hres⟩ := penC_good_residue_of_coe_eq R _ _ hcoe
  refine ⟨h, Subtype.ext (hres.trans ?_)⟩
  rw [coeffMap_residue_packA_g, FibreModel.coe_piFin_eq_coeffRed N A q k red fm b hint]

private theorem penC_residue_beta (fm : FibreModel N A q k red) (b : fm.BFin) :
    ∃ h : heckeBetaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        ∈ R.R₁.integers,
      R.residue₁ ⟨_, h⟩ = frobeniusGeomLevel k N data hKr (fm.piFin b) := by
  have hint := penC_bfin_coe_mem_integralCoeffs fm b
  have hcoe : ((heckeBetaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) :
      modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
        = coeffMap A.subtype (qExpand A q (packA_g A ⟨_, hint⟩)) := by
    rw [coe_heckeBetaBar, coeffMap_qExpand, coeffMap_subtype_packA_g]
  obtain ⟨h, hres⟩ := penC_good_residue_of_coe_eq R _ _ hcoe
  refine ⟨h, Subtype.ext (hres.trans ?_)⟩
  rw [coeffMap_qExpand, coeffMap_residue_packA_g, frobeniusGeomLevel_apply_coe,
    FibreModel.coe_piFin_eq_coeffRed N A q k red fm b hint]

private theorem penC_residue_const (a : A) :
    ∃ h : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₁.integers,
      R.residue₁ ⟨_, h⟩ = algebraMap k (modularFunctionFieldC k N) (red a) := by
  have hcoe : ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) :
      modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype (HahnSeries.single 0 a) := by
    rw [pnN_coe_algebraMap, algebraMap_laurentSeries_eq_single, coeffMap_single]
    rfl
  obtain ⟨h, hres⟩ := penC_good_residue_of_coe_eq R _ _ hcoe
  refine ⟨h, Subtype.ext ?_⟩
  rw [hres, coeffMap_single, pnN_coe_algebraMap, algebraMap_laurentSeries_eq_single]

private theorem penC_bfin_values [IsAlgClosed k] (fm : FibreModel N A q k red) (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hP : P.sp = fm.spPlace hred dataAll hsep) (hqN : ¬ q ∣ N)
    (v : Place k (modularFunctionFieldC k N)) (hv1 : jGeomGen k N ∈ v.toValuationSubring) (b : fm.BFin)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hw : P.sp w = v) :
    ∃ a : A, w.HasValue (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) (a : AlgebraicClosure ℚ) ∧
      v.HasValue (fm.piFin b) (red a) := by
  obtain ⟨a₀, ha₀⟩ := penC_exists_j_value v hv1 _ hw

  have hreg : fm.piFin b ∈ v.toValuationSubring := (penC_FIN N A q hqN k red fm v hv1).1 b
  obtain ⟨c, hc, -⟩ := v.exists_hasValue_of_surjective (penC_residue_surjective v) hreg
  obtain ⟨a₁, rfl⟩ := hred c

  set b₁ : fm.BFin := b - ⟨CharPModel.constantsHom N A a₁, fm.constFin_mem a₁⟩ with hb₁
  have hpi : (fm.piFin b₁ : modularFunctionFieldC k N)
      = fm.piFin b - algebraMap k (modularFunctionFieldC k N) (red a₁) := by
    rw [hb₁, map_sub, fm.piFin_const]
  have hnu : (fm.piFin b₁ : modularFunctionFieldC k N) ∈ v.toValuationSubring.nonunits := by
    rw [hpi]
    exact penC_sub_mem_nonunits_of_hasValue v hc
  have hsp : fm.spPlace hred dataAll hsep w = v := by
    rw [← hP]
    exact hw
  rw [← hsp] at hnu
  obtain ⟨a₂, ha₂m, ha₂⟩ := (fm.piFin_mem_spPlace_nonunits_iff hred dataAll hsep _ a₀ ha₀ b₁).mp hnu

  have hdiff : (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
      - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
          ((a₁ + a₂ : A) : AlgebraicClosure ℚ)
      = (b₁ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
            (a₂ : AlgebraicClosure ℚ) := by
    have hcoe : ((a₁ + a₂ : A) : AlgebraicClosure ℚ) = (a₁ : AlgebraicClosure ℚ) + a₂ := rfl
    have hb₁' : (b₁ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        = (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
          - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
              (a₁ : AlgebraicClosure ℚ) := by
      rw [hb₁]
      push_cast
      rfl
    rw [hcoe, hb₁', map_add, sub_sub]
  have ha₂' : (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
      - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
          ((a₁ + a₂ : A) : AlgebraicClosure ℚ)
        ∈ w.toValuationSubring.nonunits := by
    rw [hdiff]
    exact ha₂
  have hval_w : w.HasValue
      (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) ((a₁ + a₂ : A) : AlgebraicClosure ℚ) :=
    penC_hasValue_of_sub_mem_nonunits _ ha₂'
  refine ⟨a₁ + a₂, hval_w, ?_⟩

  rw [map_add, penC_red_eq_zero_of_mem_maximalIdeal hred ha₂m, add_zero]
  exact hc

private theorem penC_alpha_values [IsAlgClosed k] (fm : FibreModel N A q k red) (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hP : P.sp = fm.spPlace hred dataAll hsep) (hqN : ¬ q ∣ N)
    (v : Place k (modularFunctionFieldC k N)) (hvaff : IsAffineGeomPlace k N v) (b : fm.BFin)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hW : P.reduceFst W = v) :
    ∃ a : A, W.HasValue (heckeAlphaBar (AlgebraicClosure ℚ) N q
        (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))) (a : AlgebraicClosure ℚ) ∧
      v.HasValue (fm.piFin b) (red a) := by
  obtain ⟨a, haw, hav⟩ := penC_bfin_values fm hred dataAll hsep hP hqN v hvaff.1 b
    (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα) hW
  exact ⟨a, penC_hasValue_of_restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα W haw, hav⟩

private theorem penC_beta_values [IsAlgClosed k] (fm : FibreModel N A q k red) (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hP : P.sp = fm.spPlace hred dataAll hsep) (hqN : ¬ q ∣ N)
    (v : Place k (modularFunctionFieldC k N)) (hvaff : IsAffineGeomPlace k N v) (b : fm.BFin)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hW : P.reduceFst W = v) :
    ∃ a : A, W.HasValue (heckeBetaBar (AlgebraicClosure ℚ) N q
        (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))) (a : AlgebraicClosure ℚ) ∧
      (P.reduceSnd W).HasValue (fm.piFin b) (red a) := by
  obtain ⟨a, haw, hau⟩ := penC_bfin_values fm hred dataAll hsep hP hqN (P.reduceSnd W) (penC_reduceSnd_affine v hvaff W hW).1 b
    (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ) rfl
  exact ⟨a, penC_hasValue_of_restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ W haw, hau⟩

private theorem penC_good_alpha [IsAlgClosed k] (fm : FibreModel N A q k red) (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hP : P.sp = fm.spPlace hred dataAll hsep) (hqN : ¬ q ∣ N)
    (v : Place k (modularFunctionFieldC k N)) (hvaff : IsAffineGeomPlace k N v) (b : fm.BFin) :
    penC_Good R v (heckeAlphaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))) := by
  obtain ⟨hI, hres⟩ := penC_residue_alpha R fm b
  refine ⟨hI, ?_, ?_, ?_⟩
  · rw [hres]
    exact (penC_FIN N A q hqN k red fm v hvaff.1).1 b
  · intro W _ hWv
    rw [hres]
    exact penC_alpha_values fm hred dataAll hsep hP hqN v hvaff b W hWv
  · intro W hWv
    obtain ⟨a, haW, -⟩ := penC_alpha_values fm hred dataAll hsep hP hqN v hvaff b W hWv
    exact haW.mem

private theorem penC_good_beta [IsAlgClosed k] (fm : FibreModel N A q k red) (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hP : P.sp = fm.spPlace hred dataAll hsep) (hqN : ¬ q ∣ N)
    (v : Place k (modularFunctionFieldC k N)) (hvaff : IsAffineGeomPlace k N v) (b : fm.BFin) :
    penC_Good R v (heckeBetaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))) := by
  obtain ⟨hI, hres⟩ := penC_residue_beta R fm b
  refine ⟨hI, ?_, ?_, ?_⟩
  · rw [hres]
    have h1 : fm.piFin b ∈ (frobOnPlacesGeomLevel k N data hKr v).toValuationSubring :=
      (penC_FIN N A q hqN k red fm _ (penC_isAffine_frob_of_isAffine v hvaff).1).1 b
    rwa [mem_frobOnPlacesGeomLevel_iff] at h1
  · intro W hWs hWv
    obtain ⟨a, haW, hau⟩ := penC_beta_values fm hred dataAll hsep hP hqN v hvaff b W hWv
    refine ⟨a, haW, ?_⟩
    rw [hres]
    have hu : P.reduceSnd W = frobOnPlacesGeomLevel k N data hKr v := by
      have h₁ : frobOnPlacesGeomLevel k N data hKr (P.reduceFst W) = P.reduceSnd W := hWs.1
      rw [← h₁, hWv]
    rw [hu] at hau
    exact penC_hasValue_frob_apply v hau
  · intro W hWv
    obtain ⟨a, haW, -⟩ := penC_beta_values fm hred dataAll hsep hP hqN v hvaff b W hWv
    exact haW.mem

private theorem penC_exists_separator [IsAlgClosed k] (fm : FibreModel N A q k red) (hqN : ¬ q ∣ N)
    (v v' : Place k (modularFunctionFieldC k N)) (hv : jGeomGen k N ∈ v.toValuationSubring)
    (hv' : jGeomGen k N ∈ v'.toValuationSubring) (hne : v' ≠ v) :
    ∃ b : fm.BFin, v'.HasValue (fm.piFin b) (0 : k) ∧ ¬ v.HasValue (fm.piFin b) (0 : k) := by
  by_contra hcon
  have hall : ∀ b : fm.BFin, v'.HasValue (fm.piFin b) (0 : k) → v.HasValue (fm.piFin b) (0 : k) :=
    fun b h1 => Classical.byContradiction fun h2 => hcon ⟨b, h1, h2⟩
  apply hne
  have hle : v.toValuationSubring ≤ v'.toValuationSubring := by
    intro g hg
    obtain ⟨b, b', hb', hgb⟩ := (penC_FIN N A q hqN k red fm v hv).2 g hg
    have hb'mem : fm.piFin b' ∈ v'.toValuationSubring := (penC_FIN N A q hqN k red fm v' hv').1 b'
    obtain ⟨c, hc, -⟩ := v'.exists_hasValue_of_surjective (penC_residue_surjective v') hb'mem
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hb' (hall b' hc)
    have hg' : g = fm.piFin b * (fm.piFin b')⁻¹ := (eq_mul_inv_iff_mul_eq₀ (hc.ne_zero hc0)).mpr hgb
    rw [hg']
    exact mul_mem ((penC_FIN N A q hqN k red fm v' hv').1 b) (hc.inv hc0).mem
  exact (Place.ext (ValuationSubring.eq_of_le_of_ne_top _ hle v'.ne_top')).symm

private theorem penC_separates [IsAlgClosed k] (fm : FibreModel N A q k red) (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hP : P.sp = fm.spPlace hred dataAll hsep) (hqN : ¬ q ∣ N)
    (v : Place k (modularFunctionFieldC k N)) (hvaff : IsAffineGeomPlace k N v)
    (hint : ∀ s ∈ penC_S fm, s ∈ R.R₁.integers)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hWs : P.IsStrictSnd W) (hW : P.reduceFst W = v) :
    ∃ (u : modularFunctionFieldBar (N * q)) (hu : u ∈ penC_S fm),
      ¬ v.HasValue (R.residue₁ ⟨u, hint u hu⟩) (0 : k) ∧ 0 < W.ord u := by
  have hu_eq : frobOnPlacesGeomLevel k N data hKr (P.reduceSnd W) = v := by
    have h₁ : P.reduceFst W = frobOnPlacesGeomLevel k N data hKr (P.reduceSnd W) := hWs.1
    rw [← h₁, hW]
  have hguard : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceSnd W)) ≠ P.reduceSnd W := hWs.2
  have huaff := penC_reduceSnd_affine v hvaff W hW
  have hu2aff : IsAffineGeomPlace k N (frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceSnd W))) :=
    penC_isAffine_frob_of_isAffine _ (penC_isAffine_frob_of_isAffine _ huaff)
  obtain ⟨b, hb2, hbu⟩ := penC_exists_separator fm hqN (P.reduceSnd W) _ huaff.1 hu2aff.1 hguard
  obtain ⟨c, hWc, huc⟩ := penC_beta_values fm hred dataAll hsep hP hqN v hvaff b W hW
  have hc0 : red c ≠ 0 := fun h0 => hbu (h0 ▸ huc)
  obtain ⟨hβI, hβres⟩ := penC_residue_beta R fm b
  obtain ⟨hcI, hcres⟩ := penC_residue_const R (N := N) (q := q) c
  have hwit : heckeBetaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ) ∈ penC_S fm :=
    (penC_mem_S_iff fm).mpr (sub_mem ((penC_mem_S_iff fm).mp (penC_beta_mem fm b)) ((penC_mem_S_iff fm).mp (penC_const_mem fm c)))

  have hres : R.residue₁ ⟨heckeBetaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ), hint _ hwit⟩
      = frobeniusGeomLevel k N data hKr (fm.piFin b) - algebraMap k (modularFunctionFieldC k N) (red c) :=
    (R.residue₁.map_sub ⟨_, hβI⟩ ⟨_, hcI⟩).trans (congrArg₂ (· - ·) hβres hcres)

  have h2 : (frobOnPlacesGeomLevel k N data hKr v).HasValue (fm.piFin b) (0 : k) := by
    rw [← hu_eq]
    exact hb2
  have h3 : v.HasValue (frobeniusGeomLevel k N data hKr (fm.piFin b)) (0 : k) := penC_hasValue_frob_apply v h2
  refine ⟨_, hwit, ?_, ?_⟩
  · rw [hres]
    have h4 : v.HasValue (frobeniusGeomLevel k N data hKr (fm.piFin b) - algebraMap k (modularFunctionFieldC k N) (red c))
        ((0 : k) - red c) := by
      rw [sub_eq_add_neg, sub_eq_add_neg]
      exact penA_hasValue_add v h3 (penA_hasValue_neg v (v.hasValue_algebraMap (red c)))
    refine penC_not_hasValue_zero_of_ne v h4 ?_
    rw [zero_sub]
    exact neg_ne_zero.mpr hc0
  ·
    have hne0 : heckeBetaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ) ≠ 0 := by
      intro h0
      have hg : heckeBetaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
          = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ) := sub_eq_zero.mp h0
      have h6 : R.residue₁ ⟨_, hβI⟩ = R.residue₁ ⟨_, hcI⟩ := congrArg R.residue₁ (Subtype.ext hg)
      have h7 : frobeniusGeomLevel k N data hKr (fm.piFin b) = algebraMap k (modularFunctionFieldC k N) (red c) :=
        hβres.symm.trans (h6.trans hcres)
      have h5 : v.HasValue (frobeniusGeomLevel k N data hKr (fm.piFin b)) (red c) := by
        rw [h7]
        exact v.hasValue_algebraMap (red c)
      exact hc0 (h5.unique h3)

    have hmem : heckeBetaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ) ∈ W.toValuationSubring := sub_mem hWc.mem (W.algebraMap_mem' _)
    have hmax : (⟨_, hmem⟩ : W.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ :=
      ValuationSubring.coe_mem_nonunits_iff.mp (penC_sub_mem_nonunits_of_hasValue W hWc)
    exact (W.mem_maximalIdeal_iff_ord_pos hne0 hmem).mp hmax

private theorem penC_bar_residue_surjective (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    Function.Surjective (algebraMap (AlgebraicClosure ℚ) w.ResidueField) := by
  have key : ∀ E : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)),
      E = modularFunctionFieldC (AlgebraicClosure ℚ) N →
        ∀ w' : Place (AlgebraicClosure ℚ) E, Module.finrank (AlgebraicClosure ℚ) w'.ResidueField = 1 := by
    rintro E rfl w'
    exact place_deg_eq_one_of_isAlgClosed (AlgebraicClosure ℚ) N w'
  have h1 := key (modularFunctionFieldBar N) (modularFunctionFieldBar_eq_modularFunctionFieldC N) w
  intro x
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : w.ResidueField) one_ne_zero).mp h1 x
  exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩

private theorem penC_jBar_ne_algebraMap (t : AlgebraicClosure ℚ) :
    CharPModel.jBar N ≠ algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) t := by
  intro h
  have h1 : ((CharPModel.jBar N : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)).coeff (-1 : ℤ)
      = ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) t : modularFunctionFieldBar N) :
          LaurentSeries (AlgebraicClosure ℚ)).coeff (-1 : ℤ) := by
    rw [h]
  have h2 : ((CharPModel.jBar N : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)).coeff (-1 : ℤ) = 1 := by
    show (coeffEmb (AlgebraicClosure ℚ) jq).coeff (-1 : ℤ) = 1
    rw [coeffEmb_coeff, coeff_jq_neg_one, map_one]
  rw [h2, pnN_coe_algebraMap, algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_of_ne (by decide)] at h1
  exact one_ne_zero h1

private theorem penC_bfin_mem_of_jBar_mem (fm : FibreModel N A q k red) (b : fm.BFin)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hw : CharPModel.jBar N ∈ w.toValuationSubring) :
    (b : modularFunctionFieldBar N) ∈ w.toValuationSubring := by
  refine w.mem_toValuationSubring_of_isIntegral_adjoin hw ?_
  have hle : CharPModel.affineBaseFin N A
      ≤ (Algebra.adjoin (AlgebraicClosure ℚ) ({CharPModel.jBar N} : Set (modularFunctionFieldBar N))).toSubring := by
    rw [CharPModel.affineBaseFin, Subring.closure_le]
    rintro x (⟨a, rfl⟩ | rfl)
    · exact Subalgebra.algebraMap_mem _ (a : AlgebraicClosure ℚ)
    · exact Algebra.subset_adjoin (Set.mem_singleton _)
  obtain ⟨p, hp, hpb⟩ := fm.integralFin b
  let ι : CharPModel.affineBaseFin N A
      →+* Algebra.adjoin (AlgebraicClosure ℚ) ({CharPModel.jBar N} : Set (modularFunctionFieldBar N)) :=
    (CharPModel.affineBaseFin N A).subtype.codRestrict _ (fun x => hle x.2)
  have hcomp : (algebraMap (Algebra.adjoin (AlgebraicClosure ℚ) ({CharPModel.jBar N} : Set (modularFunctionFieldBar N)))
      (modularFunctionFieldBar N)).comp ι = (CharPModel.affineBaseFin N A).subtype :=
    RingHom.ext fun _ => rfl
  refine ⟨p.map ι, hp.map ι, ?_⟩
  rw [Polynomial.eval₂_map, hcomp]
  exact hpb

private theorem h1_atkinLehnerBar_heckeAlphaBar (hqN : ¬ q ∣ N) (t : modularFunctionFieldBar N) :
    ProlongationTuple.atkinLehnerBar N q (heckeAlphaBar (AlgebraicClosure ℚ) N q t) =
      heckeBetaBar (AlgebraicClosure ℚ) N q t := by
  have hex := exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q (Fact.out : q.Prime) hqN
  have hσ := isAtkinLehnerAutFull_atkinLehnerInvolutionFull N q hex
  have hlegs := (geomAut_atkinLehner_comp_legs (AlgebraicClosure ℚ) N q _ hσ).1
  exact AlgHom.congr_fun hlegs t

private theorem h1_residue_mul {x y z : modularFunctionFieldBar (N * q)} (hx : x ∈ R.R₁.integers)
    (hy : y ∈ R.R₁.integers) (hz : z ∈ R.R₁.integers) (h : x * y = z) :
    R.R₁.residue ⟨x, hx⟩ * R.R₁.residue ⟨y, hy⟩ = R.R₁.residue ⟨z, hz⟩ := by
  rw [← map_mul]
  congr 1
  exact Subtype.ext h

private theorem h1_mem_of_mul {x y z : modularFunctionFieldBar (N * q)} (hy : y ∈ R.R₁.integers)
    (hy0 : R.R₁.residue ⟨y, hy⟩ ≠ 0) (hz : z ∈ R.R₁.integers) (h : x * y = z) : x ∈ R.R₁.integers := by
  obtain ⟨b, hb⟩ := (R.R₁.isUnit_of_residue_ne_zero hy0).exists_right_inv
  have hb' : y * (b : modularFunctionFieldBar (N * q)) = 1 := by
    have := congrArg (fun w : R.R₁.integers => (w : modularFunctionFieldBar (N * q))) hb
    simpa using this
  have hx : x = z * (b : modularFunctionFieldBar (N * q)) := by
    rw [← h, mul_assoc, hb', mul_one]
  rw [hx]
  exact mul_mem hz b.2

include R in

private theorem h1_pack_res_ne_zero (x : CharPReduction.modularRing N A.toSubring)
    (hx : x ∉ CharPReduction.redKer A.toSubring red (CharPReduction.modularRing N A.toSubring)
      (CharPReduction.modularRing_le_integralCoeffs N A.toSubring)) :
    coeffMap (IsLocalRing.residue A)
      (packA_g A ⟨x, CharPReduction.modularRing_le_integralCoeffs N A.toSubring x.2⟩) ≠ 0 := by
  intro h0
  apply CharPReduction.redRes_ne_zero_of_notMem hx
  rw [CharPReduction.redRes_apply, ← coeffMap_residue_packA_g]
  have hcomp : red = R.redBar.comp (IsLocalRing.residue A) := (RingHom.ext R.redBar_residue).symm
  rw [hcomp, ← coeffMap_coeffMap, h0, map_zero]

private theorem h1_alpha_pack (x : CharPReduction.modularRing N A.toSubring) :
    ∃ h : heckeAlphaBar (AlgebraicClosure ℚ) N q (⟨x, modularRing_le_bar_g N A x.2⟩ : modularFunctionFieldBar N)
        ∈ R.R₁.integers,
      ((R.R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :
          LaurentSeries (IsLocalRing.ResidueField A)) =
        coeffMap (IsLocalRing.residue A)
          (packA_g A ⟨x, CharPReduction.modularRing_le_integralCoeffs N A.toSubring x.2⟩) := by
  set xI : CharPReduction.integralCoeffs A.toSubring :=
    ⟨x, CharPReduction.modularRing_le_integralCoeffs N A.toSubring x.2⟩ with hxI
  have hy : coeffMap A.subtype (packA_g A xI) ∈ modularFunctionFieldBar (N * q) := by
    rw [coeffMap_subtype_packA_g]
    have := (heckeAlphaBar (AlgebraicClosure ℚ) N q
      (⟨x, modularRing_le_bar_g N A x.2⟩ : modularFunctionFieldBar N)).2
    rwa [coe_heckeAlphaBar] at this
  obtain ⟨h, hres⟩ := R.residue₁_coeffMap (packA_g A xI) hy
  have hel : (⟨coeffMap A.subtype (packA_g A xI), hy⟩ : modularFunctionFieldBar (N * q)) =
      heckeAlphaBar (AlgebraicClosure ℚ) N q (⟨x, modularRing_le_bar_g N A x.2⟩ : modularFunctionFieldBar N) := by
    apply Subtype.ext
    rw [coe_heckeAlphaBar]
    exact coeffMap_subtype_packA_g A xI
  have key : ∀ (e : modularFunctionFieldBar (N * q))
      (_ : e = (⟨coeffMap A.subtype (packA_g A xI), hy⟩ : modularFunctionFieldBar (N * q)))
      (h' : e ∈ R.R₁.integers),
      ((R.R₁.residue ⟨e, h'⟩ : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :
        LaurentSeries (IsLocalRing.ResidueField A)) = coeffMap (IsLocalRing.residue A) (packA_g A xI) := by
    rintro e rfl h'
    exact hres
  exact ⟨hel ▸ h, key _ hel.symm (hel ▸ h)⟩

private theorem h1_beta_pack (x : CharPReduction.modularRing N A.toSubring) :
    ∃ h : heckeBetaBar (AlgebraicClosure ℚ) N q (⟨x, modularRing_le_bar_g N A x.2⟩ : modularFunctionFieldBar N)
        ∈ R.R₁.integers,
      ((R.R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :
          LaurentSeries (IsLocalRing.ResidueField A)) =
        qExpand (IsLocalRing.ResidueField A) q (coeffMap (IsLocalRing.residue A)
          (packA_g A ⟨x, CharPReduction.modularRing_le_integralCoeffs N A.toSubring x.2⟩)) := by
  set xI : CharPReduction.integralCoeffs A.toSubring :=
    ⟨x, CharPReduction.modularRing_le_integralCoeffs N A.toSubring x.2⟩ with hxI
  set y : LaurentSeries A := qExpand A q (packA_g A xI) with hydef
  have hcoe : coeffMap A.subtype y = (heckeBetaBar (AlgebraicClosure ℚ) N q
      (⟨x, modularRing_le_bar_g N A x.2⟩ : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)) := by
    rw [coe_heckeBetaBar, hydef, coeffMap_qExpand_g, coeffMap_subtype_packA_g]
  have hy : coeffMap A.subtype y ∈ modularFunctionFieldBar (N * q) := by
    rw [hcoe]
    exact (heckeBetaBar (AlgebraicClosure ℚ) N q (⟨x, modularRing_le_bar_g N A x.2⟩ : modularFunctionFieldBar N)).2
  obtain ⟨h, hres⟩ := R.residue₁_coeffMap y hy
  have hel : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar (N * q)) =
      heckeBetaBar (AlgebraicClosure ℚ) N q (⟨x, modularRing_le_bar_g N A x.2⟩ : modularFunctionFieldBar N) :=
    Subtype.ext hcoe
  have key : ∀ (e : modularFunctionFieldBar (N * q))
      (_ : e = (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar (N * q))) (h' : e ∈ R.R₁.integers),
      ((R.R₁.residue ⟨e, h'⟩ : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :
        LaurentSeries (IsLocalRing.ResidueField A)) = coeffMap (IsLocalRing.residue A) y := by
    rintro e rfl h'
    exact hres
  refine ⟨hel ▸ h, ?_⟩
  rw [key _ hel.symm (hel ▸ h), hydef, coeffMap_qExpand_g]

private theorem h1_beta_of_mem_localized (t : modularFunctionFieldBar N)
    (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized N A.toSubring red)
    (hα : heckeAlphaBar (AlgebraicClosure ℚ) N q t ∈ R.R₁.integers) :
    ∃ hβ : heckeBetaBar (AlgebraicClosure ℚ) N q t ∈ R.R₁.integers,
      ((R.R₁.residue ⟨_, hβ⟩ : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :
          LaurentSeries (IsLocalRing.ResidueField A)) =
        qExpand (IsLocalRing.ResidueField A) q
          ((R.R₁.residue ⟨_, hα⟩ : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :
            LaurentSeries (IsLocalRing.ResidueField A)) := by
  obtain ⟨r, s, hs, hts⟩ := ht
  set rB : modularFunctionFieldBar N := ⟨r, modularRing_le_bar_g N A r.2⟩ with hrB
  set sB : modularFunctionFieldBar N := ⟨s, modularRing_le_bar_g N A s.2⟩ with hsB
  have htsB : t * sB = rB := Subtype.ext hts
  obtain ⟨hr₁, hrres⟩ := h1_alpha_pack (red := red) R r
  obtain ⟨hs₁, hsres⟩ := h1_alpha_pack (red := red) R s
  obtain ⟨hr₂, hrres'⟩ := h1_beta_pack (red := red) R r
  obtain ⟨hs₂, hsres'⟩ := h1_beta_pack (red := red) R s
  have hPs : coeffMap (IsLocalRing.residue A)
      (packA_g A ⟨s, CharPReduction.modularRing_le_integralCoeffs N A.toSubring s.2⟩) ≠ 0 :=
    h1_pack_res_ne_zero R s hs
  have hqPs : qExpand (IsLocalRing.ResidueField A) q (coeffMap (IsLocalRing.residue A)
      (packA_g A ⟨s, CharPReduction.modularRing_le_integralCoeffs N A.toSubring s.2⟩)) ≠ 0 := by
    intro h0
    apply hPs
    exact (qExpand_injective q) (by rw [h0, map_zero])
  have hsres₂ : R.R₁.residue ⟨_, hs₂⟩ ≠ 0 := by
    intro h0
    apply hqPs
    rw [← hsres', h0]
    rfl
  have hmulβ : heckeBetaBar (AlgebraicClosure ℚ) N q t * heckeBetaBar (AlgebraicClosure ℚ) N q sB =
      heckeBetaBar (AlgebraicClosure ℚ) N q rB := by rw [← map_mul, htsB]
  have hmulα : heckeAlphaBar (AlgebraicClosure ℚ) N q t * heckeAlphaBar (AlgebraicClosure ℚ) N q sB =
      heckeAlphaBar (AlgebraicClosure ℚ) N q rB := by rw [← map_mul, htsB]
  refine ⟨h1_mem_of_mul R hs₂ hsres₂ hr₂ hmulβ, ?_⟩

  have hα' := congrArg (fun w : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N =>
    (w : LaurentSeries (IsLocalRing.ResidueField A))) (h1_residue_mul R hα hs₁ hr₁ hmulα)
  have hβ' := congrArg (fun w : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N =>
    (w : LaurentSeries (IsLocalRing.ResidueField A))) (h1_residue_mul R (h1_mem_of_mul R hs₂ hsres₂ hr₂ hmulβ)
      hs₂ hr₂ hmulβ)
  push_cast at hα' hβ'
  rw [hsres, hrres] at hα'
  rw [hsres', hrres', ← hα', map_mul] at hβ'
  exact mul_right_cancel₀ hqPs hβ'

private theorem h1_inv_mem_localized (t : modularFunctionFieldBar N)
    (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized N A.toSubring red)
    (hα : heckeAlphaBar (AlgebraicClosure ℚ) N q t ∈ R.R₁.integers) (hres : R.R₁.residue ⟨_, hα⟩ ≠ 0) :
    ((t⁻¹ : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
      ∈ CharPReduction.modularLocalized N A.toSubring red := by
  obtain ⟨r, s, hs, hts⟩ := ht
  have hres₁ : R.residue₁ ⟨_, hα⟩ ≠ 0 := by
    show R.ι (R.R₁.residue ⟨_, hα⟩) ≠ 0
    exact (map_ne_zero R.ι).mpr hres
  rw [localized_res_g R t r s hs hts hα] at hres₁
  have hspec := CharPReduction.redLoc_spec (A := A.toSubring) (red := red)
    (R := CharPReduction.modularRing N A.toSubring) (hR := CharPReduction.modularRing_le_integralCoeffs N A.toSubring)
    ⟨_, ⟨r, s, hs, hts⟩⟩ hts
  have hloc : CharPReduction.redLoc (A := A.toSubring) (red := red) (R := CharPReduction.modularRing N A.toSubring)
      (hR := CharPReduction.modularRing_le_integralCoeffs N A.toSubring) ⟨_, ⟨r, s, hs, hts⟩⟩ ≠ 0 :=
    fun h0 => hres₁ (Subtype.ext h0)
  have hr : r ∉ CharPReduction.redKer A.toSubring red (CharPReduction.modularRing N A.toSubring)
      (CharPReduction.modularRing_le_integralCoeffs N A.toSubring) := by
    rw [CharPReduction.notMem_redKer_iff, ← hspec]
    exact mul_ne_zero hloc (CharPReduction.redRes_ne_zero_of_notMem hs)
  have ht0 : (t : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := by
    intro h0
    apply hloc
    have hr0 : CharPReduction.redRes A.toSubring red (CharPReduction.modularRing N A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs N A.toSubring) r = 0 := by
      have : (r : LaurentSeries (AlgebraicClosure ℚ)) = 0 := by rw [← hts, h0, zero_mul]
      have hr' : r = 0 := Subtype.ext this
      rw [hr', map_zero]
    exact absurd hr0 (CharPReduction.redRes_ne_zero_of_notMem hr)
  refine ⟨s, r, hr, ?_⟩
  rw [IntermediateField.coe_inv, inv_mul_eq_iff_eq_mul₀ ht0]
  exact hts.symm

private theorem h1_coe_mem_adjoin (t : modularFunctionFieldBar N) :
    (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ IntermediateField.adjoin (AlgebraicClosure ℚ)
      {jqModC (AlgebraicClosure ℚ), jqNModC (AlgebraicClosure ℚ) N} := by
  have htop := adjoin_jBar_jNBar_eq_top (AlgebraicClosure ℚ) N
  have ht : t ∈ (⊤ : IntermediateField (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) := trivial
  rw [← htop] at ht
  have hmap : (modularFunctionFieldBar N).val t ∈
      (IntermediateField.adjoin (AlgebraicClosure ℚ) _).map (modularFunctionFieldBar N).val := ⟨t, ht, rfl⟩
  rw [IntermediateField.adjoin_map, Set.image_insert_eq, Set.image_singleton] at hmap
  have h1 : (modularFunctionFieldBar N).val ⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ = jqModC (AlgebraicClosure ℚ) :=
    coeffEmb_jq_eq_jqModC_g
  have h2 : (modularFunctionFieldBar N).val ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (dvd_refl N))⟩ =
        jqNModC (AlgebraicClosure ℚ) N := by
    show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq) = jqNModC (AlgebraicClosure ℚ) N
    rw [jqNModC, ← coeffEmb_jq_eq_jqModC_g, coeffEmb, coeffMap_qExpand_g]
  rw [h1, h2] at hmap
  exact hmap

private theorem h1_mem_localized_of_alpha_mem (hqN : ¬ q ∣ N) (t : modularFunctionFieldBar N)
    (hα : heckeAlphaBar (AlgebraicClosure ℚ) N q t ∈ R.R₁.integers) :
    (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized N A.toSubring red := by
  by_cases ht0 : t = 0
  · rw [ht0]
    exact zero_mem _
  obtain ⟨dataN⟩ := nonempty_modularPolynomialData N
  have hdeg := relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi k N q hqN
  rcases CharPReduction.mem_or_inv_mem_modularLocalized A red N dataN hdeg (h1_coe_mem_adjoin t) with h | h
  · exact h

  have hinv : ((t⁻¹ : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
      ∈ CharPReduction.modularLocalized N A.toSubring red := by
    rw [IntermediateField.coe_inv]
    exact h
  obtain ⟨hα', -⟩ := localized_glue_g R t⁻¹ hinv
  have hmul : heckeAlphaBar (AlgebraicClosure ℚ) N q t⁻¹ * heckeAlphaBar (AlgebraicClosure ℚ) N q t = 1 := by
    rw [← map_mul, inv_mul_cancel₀ ht0, map_one]
  have hres : R.R₁.residue ⟨_, hα'⟩ ≠ 0 := by
    intro h0
    have h1 := h1_residue_mul R hα' hα (one_mem _) hmul
    rw [h0, zero_mul] at h1
    have h2 : R.R₁.residue ⟨(1 : modularFunctionFieldBar (N * q)), one_mem _⟩ = 1 := by
      rw [show (⟨(1 : modularFunctionFieldBar (N * q)), one_mem _⟩ : R.R₁.integers) = 1 from rfl, map_one]
    rw [h2] at h1
    exact zero_ne_one h1
  have := h1_inv_mem_localized R t⁻¹ hinv hα' hres
  rwa [inv_inv] at this

private theorem h1_alpha_mem_snd (hqN : ¬ q ∣ N) (t : modularFunctionFieldBar N)
    (hα : heckeAlphaBar (AlgebraicClosure ℚ) N q t ∈ R.R₁.integers) :
    heckeAlphaBar (AlgebraicClosure ℚ) N q t ∈ R.R₂.integers := by
  obtain ⟨hβ, -⟩ := h1_beta_of_mem_localized R t (h1_mem_localized_of_alpha_mem R hqN t hα) hα
  rw [R.mem_integersSnd_iff, h1_atkinLehnerBar_heckeAlphaBar hqN]
  exact (R.mem_integersFst_iff _).mp hβ

private theorem h1_coe_residue_snd (hqN : ¬ q ∣ N) (t : modularFunctionFieldBar N)
    (hα : heckeAlphaBar (AlgebraicClosure ℚ) N q t ∈ R.R₁.integers)
    (h₂ : heckeAlphaBar (AlgebraicClosure ℚ) N q t ∈ R.R₂.integers) :
    ((R.R₂.residue ⟨_, h₂⟩ : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :
        LaurentSeries (IsLocalRing.ResidueField A)) =
      qExpand (IsLocalRing.ResidueField A) q
        ((R.R₁.residue ⟨_, hα⟩ : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :
          LaurentSeries (IsLocalRing.ResidueField A)) := by
  obtain ⟨hβ, hβres⟩ := h1_beta_of_mem_localized R t (h1_mem_localized_of_alpha_mem R hqN t hα) hα
  have hw : ProlongationTuple.atkinLehnerBar N q (heckeAlphaBar (AlgebraicClosure ℚ) N q t) ∈ R.R₁.integers := by
    rw [h1_atkinLehnerBar_heckeAlphaBar hqN]
    exact hβ
  have hel : (⟨_, hw⟩ : R.R₁.integers) = ⟨heckeBetaBar (AlgebraicClosure ℚ) N q t, hβ⟩ :=
    Subtype.ext (h1_atkinLehnerBar_heckeAlphaBar hqN t)
  rw [R.residue₂_eq, hel]
  exact hβres

section GenericValues

variable {E : Type*} [Field E] [Algebra k E]

omit [Fact (Nat.Prime q)] [CharP k q] in

private theorem penA_not_hasValue_zero_mul (w : Place k E) {x y : E}
    (hx : x ∈ w.toValuationSubring) (hy : y ∈ w.toValuationSubring)
    (hx0 : ¬ w.HasValue x 0) (hy0 : ¬ w.HasValue y 0) : ¬ w.HasValue (x * y) 0 := by
  rintro ⟨_, hxy⟩
  rw [map_zero] at hxy
  have hmul : IsLocalRing.residue w.toValuationSubring ⟨x * y, mul_mem hx hy⟩ =
      IsLocalRing.residue w.toValuationSubring ⟨x, hx⟩ *
        IsLocalRing.residue w.toValuationSubring ⟨y, hy⟩ := by
    rw [← map_mul]; rfl
  rw [hmul] at hxy
  rcases mul_eq_zero.mp hxy with h | h
  · exact hx0 ⟨hx, by rw [h, map_zero]⟩
  · exact hy0 ⟨hy, by rw [h, map_zero]⟩

omit [Fact (Nat.Prime q)] [CharP k q] in

private theorem penA_not_hasValue_one_zero (w : Place k E) : ¬ w.HasValue (1 : E) 0 :=
  fun h => zero_ne_one (h.unique w.hasValue_one)

end GenericValues
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve.AlphaEngine"

omit [Fact (Nat.Prime q)] in
include red in

private theorem penA_natCast_q_mem_nonunits : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits := by
  have h : ((q : ℕ) : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    have h1 : IsUnit (red ((q : ℕ) : A)) := hunit.map red
    rw [map_natCast, CharP.cast_eq_zero k q] at h1
    exact not_isUnit_zero h1
  have h' := A.coe_mem_nonunits_iff.mpr h
  simpa using h'

omit R in

private noncomputable def penA_chartRing (S : Set (modularFunctionFieldBar (N * q))) :
    Subring (modularFunctionFieldBar (N * q)) :=
  Subring.closure S

private def penA_localSet_fst (v : Place k (modularFunctionFieldC k N))
    (S : Set (modularFunctionFieldBar (N * q))) : Set (modularFunctionFieldBar (N * q)) :=
  {f | ∃ (g u : modularFunctionFieldBar (N * q)) (_ : g ∈ penA_chartRing S) (_ : u ∈ penA_chartRing S)
      (hu₁ : u ∈ R.R₁.integers),
      ¬ v.HasValue (R.residue₁ ⟨u, hu₁⟩) (0 : k) ∧ f * u = g}

section H1Division

attribute [local instance] AlphaEngine.alongAlgebra AlphaEngine.alongTower

include R in

private theorem h1_charP_residueField : CharP (IsLocalRing.ResidueField A) q :=
  RingHom.charP R.redBar R.redBar.injective q

include R in
private theorem h1_charP_fullC : CharP (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) q := by
  haveI := h1_charP_residueField R
  exact charP_of_injective_ringHom
    (algebraMap (IsLocalRing.ResidueField A) (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N)).injective q

private theorem h1_hE₂ (hqN : ¬ q ∣ N) :
    ∀ e ∈ (heckeAlphaBar (AlgebraicClosure ℚ) N q).fieldRange, e ∈ R.R₁.integers → e ∈ R.R₂.integers := by
  intro e he h₁
  obtain ⟨t, rfl⟩ := AlgHom.mem_fieldRange.mp he
  exact h1_alpha_mem_snd R hqN t h₁

private theorem h1_exists_gauss_data (hqN : ¬ q ∣ N) {z : modularFunctionFieldBar (N * q)} (hz₂ : z ∈ R.R₂.integers)
    {n : ℤ} (hn : ¬ (q : ℤ) ∣ n)
    (hc : ((R.residue₂ ⟨z, hz₂⟩ : modularFunctionFieldC k N) : LaurentSeries k).coeff n ≠ 0) :
    ∃ σ : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N →+*
        modularFunctionFieldFullC (IsLocalRing.ResidueField A) N,
      (∀ e (he : e ∈ (heckeAlphaBar (AlgebraicClosure ℚ) N q).fieldRange) (h₁ : e ∈ R.R₁.integers),
        R.R₂.residue ⟨e, h1_hE₂ R hqN e he h₁⟩ = σ (R.R₁.residue ⟨e, h₁⟩)) ∧
      (∀ y, y ^ q ∈ σ.range) ∧
      (R.R₂.residue ⟨z, hz₂⟩ ∉ σ.range) ∧
      ∀ y, ((σ y : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :
          LaurentSeries (IsLocalRing.ResidueField A)) =
        qExpand (IsLocalRing.ResidueField A) q (y : LaurentSeries (IsLocalRing.ResidueField A)) := by
  haveI := h1_charP_residueField R
  refine ⟨AlphaEngine.twist (IsLocalRing.ResidueField A) N q, ?_, AlphaEngine.pow_mem_range_twist _ N q, ?_,
    AlphaEngine.coe_twist _ N q⟩
  · intro e he h₁
    obtain ⟨t, rfl⟩ := AlgHom.mem_fieldRange.mp he
    apply Subtype.ext
    rw [AlphaEngine.coe_twist]
    exact h1_coe_residue_snd R hqN t h₁ _
  · refine AlphaEngine.notMem_range_twist_of_coeff_ne_zero _ N q hn ?_
    intro h0
    apply hc
    rw [R.residue₂_apply, R.ι_coe, coeffMap_coeff, h0, map_zero]

variable {v : Place k (modularFunctionFieldC k N)} {S : Set (modularFunctionFieldBar (N * q))}

private theorem h1_powers_linearIndependent (hqN : ¬ q ∣ N)
    (z : modularFunctionFieldBar (N * q)) (hz₁ : z ∈ R.R₁.integers) (hz₂ : z ∈ R.R₂.integers)
    (hz : ∃ n : ℤ, ¬ (q : ℤ) ∣ n ∧
      ((R.residue₂ ⟨z, hz₂⟩ : modularFunctionFieldC k N) : LaurentSeries k).coeff n ≠ 0) :
    LinearIndependent (modularFunctionFieldBar N) fun i : Fin (q + 1) => z ^ (i : ℕ) := by
  haveI := h1_charP_fullC R
  obtain ⟨n, hn, hc⟩ := hz
  obtain ⟨σ, hσ, hpi, hzr, -⟩ := h1_exists_gauss_data R hqN hz₂ hn hc
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  simp only [Algebra.smul_def, AlphaEngine.algebraMap_along_apply] at hg
  have h0 := AlphaEngine.eq_zero_of_sum_mul_pow_eq_zero R.R₁ R.R₂ (h1_hE₂ R hqN) σ hσ Fact.out hpi hz₁ hz₂ hzr
    (fun i => heckeAlphaBar (AlgebraicClosure ℚ) N q (g i)) (fun i => AlgHom.mem_fieldRange.mpr ⟨g i, rfl⟩) hg i
  exact AlphaEngine.alpha_injective (h0.trans (map_zero (heckeAlphaBar (AlgebraicClosure ℚ) N q)).symm)

private theorem h1_generator_data (hqN : ¬ q ∣ N)
    (z : modularFunctionFieldBar (N * q)) (hz₁ : z ∈ R.R₁.integers) (hz₂ : z ∈ R.R₂.integers)
    (hz : ∃ n : ℤ, ¬ (q : ℤ) ∣ n ∧
      ((R.residue₂ ⟨z, hz₂⟩ : modularFunctionFieldC k N) : LaurentSeries k).coeff n ≠ 0) :
    IntermediateField.adjoin (AlgebraicClosure ℚ)
        (Set.range (heckeAlphaBar (AlgebraicClosure ℚ) N q) ∪ {z}) = ⊤ ∧
      ∃ m : Polynomial (modularFunctionFieldBar N), m.Monic ∧ m.natDegree = q + 1 ∧
        (m.map (heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom).eval z = 0 ∧
        ∀ i : ℕ, heckeAlphaBar (AlgebraicClosure ℚ) N q (m.coeff i) ∈ R.R₁.integers := by
  haveI := h1_charP_fullC R
  have hli := h1_powers_linearIndependent R hqN z hz₁ hz₂ hz
  obtain ⟨n, hn, hc⟩ := hz
  obtain ⟨σ, hσ, hpi, hzr, -⟩ := h1_exists_gauss_data R hqN hz₂ hn hc
  obtain ⟨hgen, m, hm, hdegm, hroot, hsum⟩ :=
    AlphaEngine.exists_monic_data_of_linearIndependent (AlphaEngine.finrankAlong_heckeAlphaBar_of_not_dvd N q hqN) z hli
  refine ⟨hgen, m, hm, hdegm, hroot, ?_⟩

  have hcoef := AlphaEngine.coeff_mem_integers_of_mem_integers R.R₁ R.R₂ (h1_hE₂ R hqN) σ hσ Fact.out hpi hz₁ hz₂ hzr
    (fun i => -(heckeAlphaBar (AlgebraicClosure ℚ) N q (m.coeff i)))
    (fun i => neg_mem (AlgHom.mem_fieldRange.mpr ⟨m.coeff i, rfl⟩)) hsum (pow_mem hz₁ _) (pow_mem hz₂ _)
  intro i
  rcases lt_trichotomy i (q + 1) with hi | rfl | hi
  · exact neg_mem_iff.mp (hcoef ⟨i, hi⟩)
  · rw [← hdegm, hm.coeff_natDegree, map_one]
    exact one_mem _
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdegm]; exact hi), map_zero]
    exact zero_mem _

private theorem h1_exists_residue_derivative_eq (hqN : ¬ q ∣ N)
    (z : modularFunctionFieldBar (N * q)) (hz₁ : z ∈ R.R₁.integers) (hz₂ : z ∈ R.R₂.integers)
    (hz : ∃ n : ℤ, ¬ (q : ℤ) ∣ n ∧
      ((R.residue₂ ⟨z, hz₂⟩ : modularFunctionFieldC k N) : LaurentSeries k).coeff n ≠ 0)
    (m : Polynomial (modularFunctionFieldBar N)) (hm : m.Monic) (hdeg : m.natDegree = q + 1)
    (hroot : (m.map (heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom).eval z = 0)
    (hcoef : ∀ i : ℕ, heckeAlphaBar (AlgebraicClosure ℚ) N q (m.coeff i) ∈ R.R₁.integers) :
    ∃ η : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N,
      qExpand (IsLocalRing.ResidueField A) q (η : LaurentSeries (IsLocalRing.ResidueField A)) =
          ((R.R₂.residue ⟨z, hz₂⟩ ^ q : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :
            LaurentSeries (IsLocalRing.ResidueField A)) ∧
        ∀ hD : (Polynomial.derivative (m.map (heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom)).eval z
            ∈ R.R₁.integers,
          R.R₁.residue ⟨_, hD⟩ = R.R₁.residue ⟨z, hz₁⟩ ^ q - η := by
  haveI := h1_charP_fullC R
  obtain ⟨n, hn, hc⟩ := hz
  obtain ⟨σ, hσ, hpi, hzr, hcoe⟩ := h1_exists_gauss_data R hqN hz₂ hn hc
  obtain ⟨η, hη, hres⟩ := AlphaEngine.exists_residue_derivative_eval_eq_pow_sub R.R₁ R.R₂ (h1_hE₂ R hqN) σ hσ Fact.out hpi
    hz₂ hzr hz₁ (m.map (heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom)
    (fun i => by rw [Polynomial.coeff_map]; exact AlgHom.mem_fieldRange.mpr ⟨m.coeff i, rfl⟩)
    (fun i => by rw [Polynomial.coeff_map]; exact hcoef i) (hm.map _) (by rw [hm.natDegree_map, hdeg]) hroot
  refine ⟨η, ?_, hres⟩
  rw [← hcoe, hη]

end H1Division
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve.AlphaEngine"

private theorem finrankAlong_algEquiv_toAlgHom {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F]
    [Algebra K F'] (e : F ≃ₐ[K] F') : finrankAlong K e.toAlgHom = 1 := by
  have h := finrankAlong_comp e.toAlgHom e.symm.toAlgHom
  have hid : e.symm.toAlgHom.comp e.toAlgHom = AlgHom.id K F := by
    ext x
    simp
  rw [hid, finrankAlong_id] at h
  exact Nat.eq_one_of_mul_eq_one_right h.symm

private theorem _root_.ModularCurve.PlaceSpecialization.finrankAlong_heckeAlphaBar_of_not_dvd (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) :
    finrankAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) = q + 1 := by
  obtain ⟨σ, hσ⟩ := exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q (Fact.out : q.Prime) hqN
  have hlegs := (geomAut_atkinLehner_comp_legs (AlgebraicClosure ℚ) N q σ hσ).1
  have hβ := finrankAlong_heckeBetaBar (AlgebraicClosure ℚ) N q
  rw [if_neg hqN, ← hlegs, finrankAlong_comp, finrankAlong_algEquiv_toAlgHom, mul_one] at hβ
  exact hβ

p2m_export "ModularCurve.PlaceSpecialization" "finrankAlong_heckeAlphaBar_of_not_dvd"

private theorem atkinLehnerBar_heckeBetaBar_g (hqN : ¬ q ∣ N) (t : modularFunctionFieldBar N) :
    ProlongationTuple.atkinLehnerBar N q (heckeBetaBar (AlgebraicClosure ℚ) N q t) =
      heckeAlphaBar (AlgebraicClosure ℚ) N q t := by
  have hex := exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q (Fact.out : q.Prime) hqN
  have hσ := isAtkinLehnerAutFull_atkinLehnerInvolutionFull N q hex
  have hlegs := (geomAut_atkinLehner_comp_legs (AlgebraicClosure ℚ) N q _ hσ).2
  exact AlgHom.congr_fun hlegs t

private theorem penC_beta_mem_snd (hqN : ¬ q ∣ N) (fm : FibreModel N A q k red) (b : fm.BFin) :
    heckeBetaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
      ∈ R.R₂.integers := by
  obtain ⟨hαI, -⟩ := penC_residue_alpha R fm b
  rw [R.mem_integersSnd_iff, atkinLehnerBar_heckeBetaBar_g hqN]
  exact (R.mem_integersFst_iff _).mp hαI

private theorem penC_residue₂_beta (hqN : ¬ q ∣ N) (fm : FibreModel N A q k red) (b : fm.BFin)
    (h : heckeBetaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
      ∈ R.R₂.integers) :
    R.residue₂ ⟨_, h⟩ = fm.piFin b := by
  obtain ⟨hαI, hαres⟩ := penC_residue_alpha R fm b
  have hAL := atkinLehnerBar_heckeBetaBar_g hqN (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
  have h2 : R.residue₂ ⟨_, h⟩ = R.residue₁ ⟨_, hαI⟩ := by
    show R.ι (R.R₂.residue ⟨_, h⟩) = R.ι (R.R₁.residue ⟨_, hαI⟩)
    rw [R.residue₂_eq]
    exact congrArg R.ι (congrArg R.R₁.residue (Subtype.ext hAL))
  rw [h2, hαres]

private theorem penC_frob_ι_eq (z : modularFunctionFieldBar (N * q)) (hz₂ : z ∈ R.R₂.integers)
    (η : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N)
    (hη : qExpand (IsLocalRing.ResidueField A) q (η : LaurentSeries (IsLocalRing.ResidueField A)) =
      ((R.R₂.residue ⟨z, hz₂⟩ ^ q : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :
        LaurentSeries (IsLocalRing.ResidueField A))) :
    frobeniusGeomLevel k N data hKr (R.ι η) = R.residue₂ ⟨z, hz₂⟩ ^ q := by
  apply Subtype.ext
  rw [frobeniusGeomLevel_apply_coe, R.ι_coe, ← coeffMap_qExpand, hη]
  push_cast
  rw [map_pow, ← R.ι_coe]
  rfl

omit [Fact (Nat.Prime q)] [NeZero N] in

private theorem penC_mem_restrictAlong_iff (φ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N) →ₐ[AlgebraicClosure ℚ] laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)))
    (hφ : φ.toRingHom.IsIntegral) (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (x : modularFunctionFieldBar N) :
    x ∈ (W.restrictAlong φ hφ).toValuationSubring ↔ φ x ∈ W.toValuationSubring := by
  by_cases hx : x = 0
  · subst hx
    rw [map_zero]
    exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
  have hφx : φ x ≠ 0 := (map_ne_zero φ).mpr hx
  have he : (0 : ℤ) < (Place.ramificationIndexAlong φ W : ℤ) := by
    exact_mod_cast penC_ramificationIndexAlong_pos' φ hφ W
  constructor
  · intro h
    refine W.mem_of_ord_nonneg_pn hφx ?_
    rw [W.ord_restrictAlong φ hφ x]
    exact mul_nonneg he.le ((W.restrictAlong φ hφ).ord_nonneg_of_mem_pn h)
  · intro h
    have h1 := W.ord_nonneg_of_mem_pn h
    rw [W.ord_restrictAlong φ hφ x] at h1
    refine (W.restrictAlong φ hφ).mem_of_ord_nonneg_pn hx ?_
    by_contra hneg
    have h2 := mul_neg_of_pos_of_neg he (not_le.mp hneg)
    linarith

private theorem penC_beta_jBar_isIntegral (dq : ModularPolynomialData q) :
    IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ) ({heckeAlphaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N)} : Set (modularFunctionFieldBar (N * q))))
      (heckeBetaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N)) := by
  let ev : Polynomial ℤ →+* Algebra.adjoin (AlgebraicClosure ℚ) ({heckeAlphaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N)} : Set (modularFunctionFieldBar (N * q))) :=
    (Polynomial.aeval (⟨heckeAlphaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N), Algebra.subset_adjoin (Set.mem_singleton _)⟩ :
      Algebra.adjoin (AlgebraicClosure ℚ) ({heckeAlphaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N)} : Set (modularFunctionFieldBar (N * q))))).toRingHom
  refine ⟨dq.Φ.map ev, dq.monic.map ev, ?_⟩
  have key : (modularFunctionFieldBar (N * q)).val.toRingHom
      (Polynomial.eval₂ (algebraMap _ (modularFunctionFieldBar (N * q))) (heckeBetaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N)) (dq.Φ.map ev)) = 0 := by
    rw [Polynomial.hom_eval₂, Polynomial.eval₂_map]
    have hcomp : ((modularFunctionFieldBar (N * q)).val.toRingHom.comp (algebraMap _ (modularFunctionFieldBar (N * q)))).comp ev
        = (coeffEmb (AlgebraicClosure ℚ)).comp evalAtJ := by
      refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
      show ((algebraMap _ (modularFunctionFieldBar (N * q)) (ev Polynomial.X) : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
        = coeffEmb (AlgebraicClosure ℚ) (evalAtJ Polynomial.X)
      have hX : ev Polynomial.X = ⟨heckeAlphaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N), Algebra.subset_adjoin (Set.mem_singleton _)⟩ :=
        Polynomial.aeval_X _
      rw [evalAtJ_X, hX]
      show ((heckeAlphaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N) : modularFunctionFieldBar (N * q)) :
        LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) jq
      exact coe_heckeAlphaBar ..
    rw [hcomp]
    have hβ : (modularFunctionFieldBar (N * q)).val.toRingHom (heckeBetaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N)) = coeffEmb (AlgebraicClosure ℚ) (jqN q) := by
      rw [jqN, penS_lsc_coeffEmb_qExpand]
      exact coe_heckeBetaBar ..
    rw [hβ, ← Polynomial.hom_eval₂, dq.eval_eq_zero, map_zero]
  exact Subtype.ext key

include hβ in

private theorem penC_beta_regular (dq : ModularPolynomialData q) (fm : FibreModel N A q k red) (y : fm.BFin)
    (u₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hu₀ : CharPModel.jBar N ∈ u₀.toValuationSubring)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hW : W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα = u₀) :
    heckeBetaBar (AlgebraicClosure ℚ) N q (y : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) ∈ W.toValuationSubring := by
  have hαj : heckeAlphaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N) ∈ W.toValuationSubring := by
    refine (penC_mem_restrictAlong_iff _ hα W _).mp ?_
    rw [hW]
    exact hu₀
  have hβj : heckeBetaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N) ∈ W.toValuationSubring :=
    W.mem_toValuationSubring_of_isIntegral_adjoin hαj (penC_beta_jBar_isIntegral dq)
  have hj' : CharPModel.jBar N ∈ (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ).toValuationSubring :=
    (penC_mem_restrictAlong_iff _ hβ W _).mpr hβj
  exact (penC_mem_restrictAlong_iff _ hβ W _).mp (penC_bfin_mem_of_jBar_mem fm y _ hj')

private theorem penC_jBar_mul_eq_alpha :
    CharPModel.jBar (N * q) = heckeAlphaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N) := by
  apply Subtype.ext
  show coeffEmb (AlgebraicClosure ℚ) jq = _
  exact (coe_heckeAlphaBar N q (CharPModel.jBar N)).symm

section Closers

private theorem penC_mem_of_monic {E : Type*} [Field E] (O : ValuationSubring E) {T : Type*} [CommRing T]
    (g : T →+* E) (hg : ∀ t, g t ∈ O) {x : E} {p : Polynomial T} (hp : p.Monic) (hx : Polynomial.eval₂ g x p = 0) :
    x ∈ O := by
  let g' : T →+* O := g.codRestrict O hg
  have hcomp : (algebraMap O E).comp g' = g := RingHom.ext fun t => rfl
  have hint : IsIntegral O x := by
    refine ⟨p.map g', hp.map g', ?_⟩
    rw [Polynomial.eval₂_map, hcomp]
    exact hx
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hy]
  exact y.2

private theorem penC_residue_mem_of_monic (v : Place k (modularFunctionFieldC k N)) {T : Type*} [CommRing T] (g : T →+* modularFunctionFieldBar (N * q))
    (hgI : ∀ t, g t ∈ R.R₁.integers) (hgv : ∀ t, (R.residue₁ ⟨g t, hgI t⟩ : modularFunctionFieldC k N) ∈ v.toValuationSubring)
    {x : modularFunctionFieldBar (N * q)} (hx : x ∈ R.R₁.integers) {p : Polynomial T} (hp : p.Monic) (hroot : Polynomial.eval₂ g x p = 0) :
    (R.residue₁ ⟨x, hx⟩ : modularFunctionFieldC k N) ∈ v.toValuationSubring := by
  let g₁ : T →+* R.R₁.integers := g.codRestrict R.R₁.integers hgI
  have h2 : (R.R₁.integers.subtype).comp g₁ = g := RingHom.ext fun t => rfl
  have h1 : Polynomial.eval₂ g₁ ⟨x, hx⟩ p = 0 := by
    apply Subtype.ext
    show R.R₁.integers.subtype (Polynomial.eval₂ g₁ ⟨x, hx⟩ p) = 0
    rw [Polynomial.hom_eval₂, h2]
    exact hroot
  have h3 : Polynomial.eval₂ (R.residue₁.comp g₁) (R.residue₁ ⟨x, hx⟩) p = 0 := by
    rw [← Polynomial.hom_eval₂, h1, map_zero]
  exact penC_mem_of_monic v.toValuationSubring (R.residue₁.comp g₁) hgv hp h3

end Closers
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve.AlphaEngine"

private theorem penC_binf_coe_mem_integralCoeffs (fm : FibreModel N A q k red) (b : fm.BInf) :
    ((b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) : LaurentSeries (AlgebraicClosure ℚ))
      ∈ CharPReduction.integralCoeffs A.toSubring :=
  mem_integralCoeffs_of_integral_affineBaseInf A N _ (fm.integralInf b)

private theorem penC_residue_alpha_inf (fm : FibreModel N A q k red) (hcc : fm.CuspChart) (dN : ModularPolynomialData N)
    (hsepN : ((dN.Φ.map (Polynomial.mapRingHom (Int.castRingHom k))).map (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (b : fm.BInf) :
    ∃ h : heckeAlphaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        ∈ R.R₁.integers,
      R.residue₁ ⟨_, h⟩ = fm.piInf b := by
  have hint := penC_binf_coe_mem_integralCoeffs fm b
  have hcoe : ((heckeAlphaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) :
      modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype (packA_g A ⟨_, hint⟩) := by
    rw [coe_heckeAlphaBar, coeffMap_subtype_packA_g]
  obtain ⟨h, hres⟩ := penC_good_residue_of_coe_eq R _ _ hcoe
  refine ⟨h, Subtype.ext (hres.trans ?_)⟩
  rw [coeffMap_residue_packA_g, FibreModel.coe_piInf_eq_coeffRed_of_cuspChart N A q k red fm hcc dN hsepN b hint]

private theorem penC_residue_beta_inf (fm : FibreModel N A q k red) (hcc : fm.CuspChart) (dN : ModularPolynomialData N)
    (hsepN : ((dN.Φ.map (Polynomial.mapRingHom (Int.castRingHom k))).map (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (b : fm.BInf) :
    ∃ h : heckeBetaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        ∈ R.R₁.integers,
      R.residue₁ ⟨_, h⟩ = frobeniusGeomLevel k N data hKr (fm.piInf b) := by
  have hint := penC_binf_coe_mem_integralCoeffs fm b
  have hcoe : ((heckeBetaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) :
      modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
        = coeffMap A.subtype (qExpand A q (packA_g A ⟨_, hint⟩)) := by
    rw [coe_heckeBetaBar, coeffMap_qExpand, coeffMap_subtype_packA_g]
  obtain ⟨h, hres⟩ := penC_good_residue_of_coe_eq R _ _ hcoe
  refine ⟨h, Subtype.ext (hres.trans ?_)⟩
  rw [coeffMap_qExpand, coeffMap_residue_packA_g, frobeniusGeomLevel_apply_coe,
    FibreModel.coe_piInf_eq_coeffRed_of_cuspChart N A q k red fm hcc dN hsepN b hint]

private theorem penC_residue₂_alpha_inf (hqN : ¬ q ∣ N) (fm : FibreModel N A q k red) (hcc : fm.CuspChart)
    (dN : ModularPolynomialData N)
    (hsepN : ((dN.Φ.map (Polynomial.mapRingHom (Int.castRingHom k))).map (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (b : fm.BInf)
    (h : heckeAlphaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
      ∈ R.R₂.integers) :
    R.residue₂ ⟨_, h⟩ = frobeniusGeomLevel k N data hKr (fm.piInf b) := by
  obtain ⟨hβI, hβres⟩ := penC_residue_beta_inf R fm hcc dN hsepN b
  have hAL := h1_atkinLehnerBar_heckeAlphaBar hqN (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
  have h2 : R.residue₂ ⟨_, h⟩ = R.residue₁ ⟨_, hβI⟩ := by
    show R.ι (R.R₂.residue ⟨_, h⟩) = R.ι (R.R₁.residue ⟨_, hβI⟩)
    rw [R.residue₂_eq]
    exact congrArg R.ι (congrArg R.R₁.residue (Subtype.ext hAL))
  rw [h2, hβres]

private def penC_ICInf (A : ValuationSubring (AlgebraicClosure ℚ)) :
    Set (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) :=
  {s | ∃ p : Polynomial (CharPModel.affineBaseInf N A), p.Monic ∧
    Polynomial.eval₂ (CharPModel.affineBaseInf N A).subtype s p = 0}

private theorem penC_binf_mem_ICInf (fm : FibreModel N A q k red) (b : fm.BInf) :
    (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) ∈ penC_ICInf A :=
  fm.integralInf b

private theorem penC_affineBaseInf_le (fm : FibreModel N A q k red) : CharPModel.affineBaseInf N A ≤ fm.BInf := by
  rw [CharPModel.affineBaseInf, Subring.closure_le]
  rintro x (⟨a, rfl⟩ | rfl)
  · exact fm.constInf_mem a
  · exact fm.jInvBar_mem

private theorem penC_binf_mem_of_jInvBar_mem (fm : FibreModel N A q k red) (b : fm.BInf)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hw : (CharPModel.jBar N)⁻¹ ∈ w.toValuationSubring) :
    (b : modularFunctionFieldBar N) ∈ w.toValuationSubring := by
  refine w.mem_toValuationSubring_of_isIntegral_adjoin hw ?_
  have hle : CharPModel.affineBaseInf N A
      ≤ (Algebra.adjoin (AlgebraicClosure ℚ) ({(CharPModel.jBar N)⁻¹} : Set (modularFunctionFieldBar N))).toSubring := by
    rw [CharPModel.affineBaseInf, Subring.closure_le]
    rintro x (⟨a, rfl⟩ | rfl)
    · exact Subalgebra.algebraMap_mem _ (a : AlgebraicClosure ℚ)
    · exact Algebra.subset_adjoin (Set.mem_singleton _)
  obtain ⟨p, hp, hpb⟩ := fm.integralInf b
  let ι : CharPModel.affineBaseInf N A
      →+* Algebra.adjoin (AlgebraicClosure ℚ) ({(CharPModel.jBar N)⁻¹} : Set (modularFunctionFieldBar N)) :=
    (CharPModel.affineBaseInf N A).subtype.codRestrict _ (fun x => hle x.2)
  have hcomp : (algebraMap (Algebra.adjoin (AlgebraicClosure ℚ) ({(CharPModel.jBar N)⁻¹} : Set (modularFunctionFieldBar N)))
      (modularFunctionFieldBar N)).comp ι = (CharPModel.affineBaseInf N A).subtype :=
    RingHom.ext fun _ => rfl
  refine ⟨p.map ι, hp.map ι, ?_⟩
  rw [Polynomial.eval₂_map, hcomp]
  exact hpb

private theorem penC_root_map_inf {s : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)}
    {p : Polynomial (CharPModel.affineBaseInf N A)} (hs : Polynomial.eval₂ (CharPModel.affineBaseInf N A).subtype s p = 0) :
    Polynomial.eval₂ ((heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom.comp (CharPModel.affineBaseInf N A).subtype)
      (heckeAlphaBar (AlgebraicClosure ℚ) N q s) p = 0 := by
  have h := congrArg (heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom hs
  rw [Polynomial.hom_eval₂, map_zero] at h
  exact h

private noncomputable def penC_jF (fm : FibreModel N A q k red) : fm.BFin := ⟨CharPModel.jBar N, fm.jBar_mem⟩

private noncomputable def penC_jI (fm : FibreModel N A q k red) : fm.BInf := ⟨(CharPModel.jBar N)⁻¹, fm.jInvBar_mem⟩

private noncomputable def penC_t : modularFunctionFieldBar (N * q) :=
  heckeBetaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N)
    * heckeAlphaBar (AlgebraicClosure ℚ) N q ((CharPModel.jBar N)⁻¹) ^ q

private theorem penC_jFun_eq_alpha :
    ProlongationTuple.jFun N q = heckeAlphaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N) := by
  apply Subtype.ext
  show coeffEmb (AlgebraicClosure ℚ) jq = _
  exact (coe_heckeAlphaBar N q (CharPModel.jBar N)).symm

private theorem penC_jQFun_eq_beta :
    ProlongationTuple.jQFun N q = heckeBetaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N) := by
  apply Subtype.ext
  show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) = _
  rw [penS_lsc_coeffEmb_qExpand]
  exact (coe_heckeBetaBar N q (CharPModel.jBar N)).symm

private theorem penC_jBar_ne_zero : CharPModel.jBar N ≠ 0 := by
  intro h
  exact penC_jBar_ne_algebraMap (N := N) 0 (by rw [h, map_zero])

private theorem penC_jFun_ne_zero : ProlongationTuple.jFun N q ≠ 0 := by
  rw [penC_jFun_eq_alpha]
  exact (map_ne_zero _).mpr penC_jBar_ne_zero

private theorem penC_jQFun_ne_zero : ProlongationTuple.jQFun N q ≠ 0 := by
  rw [penC_jQFun_eq_beta]
  exact (map_ne_zero _).mpr penC_jBar_ne_zero

private theorem penC_tInfty_eq : ProlongationTuple.tInfty N q = (penC_t : modularFunctionFieldBar (N * q)) := by
  rw [ProlongationTuple.tInfty, penC_jFun_eq_alpha, penC_jQFun_eq_beta, penC_t, map_inv₀, div_eq_mul_inv, inv_pow]

private theorem penC_t_ne_zero : (penC_t : modularFunctionFieldBar (N * q)) ≠ 0 := by
  rw [← penC_tInfty_eq, ProlongationTuple.tInfty]
  exact div_ne_zero penC_jQFun_ne_zero (pow_ne_zero _ penC_jFun_ne_zero)

private theorem penC_jqModC_ne_zero : (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ≠ 0 := by
  intro h
  have h1 := congrArg (fun x : modularFunctionFieldC k N => (x : LaurentSeries k).coeff (-1 : ℤ)) h
  simp [coeff_jqModC_neg_one] at h1

private theorem penC_t_fst (fm : FibreModel N A q k red) (hcc : fm.CuspChart) (dN : ModularPolynomialData N)
    (hsepN : ((dN.Φ.map (Polynomial.mapRingHom (Int.castRingHom k))).map (algebraMap (Polynomial k) (RatFunc k))).Separable) :
    ∃ h : (penC_t : modularFunctionFieldBar (N * q)) ∈ R.R₁.integers, R.residue₁ ⟨_, h⟩ = 1 := by
  obtain ⟨hβ₁, hβres⟩ := penC_residue_beta R fm (penC_jF fm)
  obtain ⟨hα₁, hαres⟩ := penC_residue_alpha_inf R fm hcc dN hsepN (penC_jI fm)
  refine ⟨mul_mem hβ₁ (pow_mem hα₁ q), ?_⟩
  have hmul : (⟨penC_t, mul_mem hβ₁ (pow_mem hα₁ q)⟩ : R.R₁.integers) = ⟨_, hβ₁⟩ * ⟨_, hα₁⟩ ^ q := rfl
  rw [hmul, map_mul, map_pow, hβres, hαres]
  have h1 : fm.piFin (penC_jF fm) = ⟨jqModC k, jqModC_mem k N⟩ := fm.piFin_j
  have h2 : fm.piInf (penC_jI fm) = (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)⁻¹ := fm.piInf_jInv
  rw [h1, h2, frobeniusGeomLevel_jq, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ penC_jqModC_ne_zero)]

private theorem penC_t_snd (hqN : ¬ q ∣ N) (fm : FibreModel N A q k red) (hcc : fm.CuspChart) (dN : ModularPolynomialData N)
    (hsepN : ((dN.Φ.map (Polynomial.mapRingHom (Int.castRingHom k))).map (algebraMap (Polynomial k) (RatFunc k))).Separable) :
    ∃ h : (penC_t : modularFunctionFieldBar (N * q)) ∈ R.R₂.integers,
      R.residue₂ ⟨_, h⟩ = (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)
        * (((⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ^ q)⁻¹) ^ q := by
  have hβ₂ := penC_beta_mem_snd R hqN fm (penC_jF fm)
  obtain ⟨hα₁, -⟩ := penC_residue_alpha_inf R fm hcc dN hsepN (penC_jI fm)
  have hα₂ := h1_alpha_mem_snd R hqN _ hα₁
  refine ⟨mul_mem hβ₂ (pow_mem hα₂ q), ?_⟩
  have hmul : (⟨penC_t, mul_mem hβ₂ (pow_mem hα₂ q)⟩ : R.R₂.integers) = ⟨_, hβ₂⟩ * ⟨_, hα₂⟩ ^ q := rfl
  rw [hmul, map_mul, map_pow, penC_residue₂_beta R hqN fm (penC_jF fm) hβ₂,
    penC_residue₂_alpha_inf R hqN fm hcc dN hsepN (penC_jI fm) hα₂]
  have h1 : fm.piFin (penC_jF fm) = ⟨jqModC k, jqModC_mem k N⟩ := fm.piFin_j
  have h2 : fm.piInf (penC_jI fm) = (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)⁻¹ := fm.piInf_jInv
  rw [h1, h2, map_inv₀, frobeniusGeomLevel_jq]

private theorem penC_order_pow {x : LaurentSeries k} (hx : x ≠ 0) (n : ℕ) : (x ^ n).order = n * x.order := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, HahnSeries.order_mul (pow_ne_zero _ hx) hx, ih]
    push_cast
    ring

private theorem penC_t_hz (hqN : ¬ q ∣ N) (fm : FibreModel N A q k red) (hcc : fm.CuspChart) (dN : ModularPolynomialData N)
    (hsepN : ((dN.Φ.map (Polynomial.mapRingHom (Int.castRingHom k))).map (algebraMap (Polynomial k) (RatFunc k))).Separable) :
    ∃ h : (penC_t : modularFunctionFieldBar (N * q)) ∈ R.R₂.integers, ∃ n : ℤ, ¬ (q : ℤ) ∣ n ∧
      ((R.residue₂ ⟨_, h⟩ : modularFunctionFieldC k N) : LaurentSeries k).coeff n ≠ 0 := by
  obtain ⟨h, hres⟩ := penC_t_snd R hqN fm hcc dN hsepN
  have hj0 : jqModC k ≠ 0 := fun h0 => penC_jqModC_ne_zero (N := N) (Subtype.ext h0)

  have hkey' : R.residue₂ ⟨_, h⟩ * (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ^ (q * q)
      = ⟨jqModC k, jqModC_mem k N⟩ := by
    rw [hres, pow_mul, mul_assoc, ← mul_pow, inv_mul_cancel₀ (pow_ne_zero _ penC_jqModC_ne_zero), one_pow, mul_one]
  have hkey : ((R.residue₂ ⟨_, h⟩ : modularFunctionFieldC k N) : LaurentSeries k) * jqModC k ^ (q * q) = jqModC k := by
    have h2 := congrArg (fun x : modularFunctionFieldC k N => (x : LaurentSeries k)) hkey'
    simpa using h2
  refine ⟨h, ?_⟩
  generalize hyd : ((R.residue₂ ⟨_, h⟩ : modularFunctionFieldC k N) : LaurentSeries k) = y at hkey ⊢
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hkey
    exact hj0 hkey.symm
  have hord : y.order = (q : ℤ) * q - 1 := by
    have h1 := congrArg HahnSeries.order hkey
    rw [HahnSeries.order_mul hy0 (pow_ne_zero _ hj0), penC_order_pow hj0, order_jqModC_def] at h1
    push_cast at h1
    linarith
  refine ⟨y.order, ?_, HahnSeries.coeff_order_eq_zero.not.mpr hy0⟩
  rw [hord]
  intro hdvd
  have h2 : (q : ℤ) ∣ (q : ℤ) * q - ((q : ℤ) * q - 1) := dvd_sub (dvd_mul_right _ _) hdvd
  simp only [sub_sub_cancel] at h2
  have h3 : (q : ℤ) = 1 := by
    have := Int.eq_one_of_dvd_one (by positivity) h2
    exact this
  exact (Fact.out : q.Prime).one_lt.ne' (by exact_mod_cast h3)

private def penC_SInf (A : ValuationSubring (AlgebraicClosure ℚ)) : Set (modularFunctionFieldBar (N * q)) :=
  ((fun s : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N) => heckeAlphaBar (AlgebraicClosure ℚ) N q s)
      '' penC_ICInf A) ∪
    Set.range (fun a : A => (penC_t : modularFunctionFieldBar (N * q))
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ))

private theorem penC_alpha_mem_SInf {s : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)}
    (hs : s ∈ penC_ICInf A) : heckeAlphaBar (AlgebraicClosure ℚ) N q s ∈ penC_SInf A :=
  Or.inl ⟨s, hs, rfl⟩

private theorem penC_t_sub_mem_SInf (A : ValuationSubring (AlgebraicClosure ℚ)) (a : A) :
    (penC_t : modularFunctionFieldBar (N * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)
      ∈ penC_SInf A :=
  Or.inr ⟨a, rfl⟩

private theorem penC_t_mem_SInf (A : ValuationSubring (AlgebraicClosure ℚ)) : (penC_t : modularFunctionFieldBar (N * q)) ∈ penC_SInf A := by
  have h := penC_t_sub_mem_SInf (q := q) (N := N) A 0
  simpa using h

private def penC_GoodInf (v : Place k (modularFunctionFieldC k N)) (s : modularFunctionFieldBar (N * q)) : Prop :=
  ∃ h : s ∈ R.R₁.integers,
    (R.residue₁ ⟨s, h⟩ : modularFunctionFieldC k N) ∈ v.toValuationSubring ∧
    ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)), P.reduceFst W = v → s ∈ W.toValuationSubring

private theorem penC_alpha_jInv_mem_of_reduceFst {v : Place k (modularFunctionFieldC k N)} (hv : ¬ IsAffineGeomPlace k N v)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hW : P.reduceFst W = v) :
    heckeAlphaBar (AlgebraicClosure ℚ) N q ((CharPModel.jBar N)⁻¹) ∈ W.toValuationSubring := by
  have hcusp := ProlongationTuple.isCuspidal_of_not_isAffineGeomPlace_reduceFst P W (by rw [hW]; exact hv)
  have h0 : W.ord (ProlongationTuple.jFun N q) ≤ 0 := by simpa using hcusp 0
  rw [map_inv₀, ← penC_jFun_eq_alpha]
  refine W.mem_of_ord_nonneg_pn (inv_ne_zero penC_jFun_ne_zero) ?_
  rw [W.ord_inv]
  exact neg_nonneg.mpr h0

private theorem penC_goodInf_binf (fm : FibreModel N A q k red) (hcc : fm.CuspChart) (hqN : ¬ q ∣ N)
    (dN : ModularPolynomialData N)
    (hsepN : ((dN.Φ.map (Polynomial.mapRingHom (Int.castRingHom k))).map (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (v : Place k (modularFunctionFieldC k N)) (hv : ¬ IsAffineGeomPlace k N v) (b : fm.BInf) :
    penC_GoodInf R v (heckeAlphaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))) := by
  obtain ⟨h, hres⟩ := penC_residue_alpha_inf R fm hcc dN hsepN b
  refine ⟨h, ?_, ?_⟩
  · rw [hres]
    exact (FibreModel.piInf_range_localizes_of_not_affine N A q hqN k red fm v hv).1 b
  · intro W hW
    have hj := penC_alpha_jInv_mem_of_reduceFst (P := P) hv W hW
    rw [← penC_mem_restrictAlong_iff _ hα W] at hj ⊢
    exact penC_binf_mem_of_jInvBar_mem fm b _ hj

private theorem penC_goodInf_ICInf (fm : FibreModel N A q k red) (hcc : fm.CuspChart) (hqN : ¬ q ∣ N)
    (dN : ModularPolynomialData N)
    (hsepN : ((dN.Φ.map (Polynomial.mapRingHom (Int.castRingHom k))).map (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (v : Place k (modularFunctionFieldC k N)) (hv : ¬ IsAffineGeomPlace k N v)
    {s : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)} (hs : s ∈ penC_ICInf A) :
    penC_GoodInf R v (heckeAlphaBar (AlgebraicClosure ℚ) N q s) := by
  obtain ⟨p, hp, hsp⟩ := hs
  have hroot := penC_root_map_inf (q := q) hsp
  have hgood : ∀ x : CharPModel.affineBaseInf N A,
      penC_GoodInf R v (((heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom.comp (CharPModel.affineBaseInf N A).subtype) x) :=
    fun x => penC_goodInf_binf R fm hcc hqN dN hsepN v hv ⟨x, penC_affineBaseInf_le fm x.2⟩
  have hgI : ∀ x, ((heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom.comp (CharPModel.affineBaseInf N A).subtype) x
      ∈ R.R₁.integers := fun x => (hgood x).choose
  have hI : heckeAlphaBar (AlgebraicClosure ℚ) N q s ∈ R.R₁.integers :=
    penC_mem_of_monic R.R₁.integers _ hgI hp hroot
  refine ⟨hI, ?_, ?_⟩
  · exact penC_residue_mem_of_monic R v _ hgI (fun x => (hgood x).choose_spec.1) hI hp hroot
  · intro W hW
    exact penC_mem_of_monic W.toValuationSubring _ (fun x => (hgood x).choose_spec.2 W hW) hp hroot

private theorem penC_ord_pow {K F : Type*} [Field K] [Field F] [Algebra K F] (W : Place K F) (f : F) (n : ℕ) :
    W.ord (f ^ n) = n * W.ord f := by
  rw [← zpow_natCast, W.ord_zpow]

private theorem penC_tInfty_mem_of_isCuspidal (hqN : ¬ q ∣ N)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hW : ProlongationTuple.IsCuspidal P W) :
    ProlongationTuple.tInfty N q ∈ W.toValuationSubring := by
  rcases ProlongationTuple.isInftySide_or_isZeroSide_of_isCuspidal P hqN W hW with hinf | hzero
  · obtain ⟨-, τ, -, hτ⟩ := hinf
    exact hτ.mem
  · obtain ⟨hcusp', τ, hτ1, hτ⟩ := hzero
    have hτ0 : (τ : AlgebraicClosure ℚ) ≠ 0 := by
      intro h0
      have : τ = 0 := Subtype.ext h0
      rw [this, map_zero] at hτ1
      exact zero_ne_one hτ1
    have hjQ : W.ord (ProlongationTuple.jQFun N q) ≤ 0 := by
      have h0 := hcusp' 0
      simpa using h0
    have ht0 : W.ord (ProlongationTuple.tZero N q) = 0 := hτ.ord_eq_zero hτ0
    have hjF0 := penC_jFun_ne_zero (N := N) (q := q)
    have hjQ0 := penC_jQFun_ne_zero (N := N) (q := q)

    have hordJ : W.ord (ProlongationTuple.jFun N q) = q * W.ord (ProlongationTuple.jQFun N q) := by
      have h := ht0
      rw [ProlongationTuple.tZero, div_eq_mul_inv, W.ord_mul hjF0 (inv_ne_zero (pow_ne_zero _ hjQ0)), W.ord_inv,
        penC_ord_pow] at h
      linarith
    have hordT : W.ord (ProlongationTuple.tInfty N q)
        = W.ord (ProlongationTuple.jQFun N q) - q * W.ord (ProlongationTuple.jFun N q) := by
      rw [ProlongationTuple.tInfty, div_eq_mul_inv, W.ord_mul hjQ0 (inv_ne_zero (pow_ne_zero _ hjF0)), W.ord_inv,
        penC_ord_pow]
      ring
    refine W.mem_of_ord_nonneg_pn (by rw [penC_tInfty_eq]; exact penC_t_ne_zero) ?_
    rw [hordT, hordJ]
    have hq1 : (1 : ℤ) ≤ q := by exact_mod_cast (Fact.out : q.Prime).one_lt.le
    have hqq : (1 : ℤ) ≤ q * q := by nlinarith
    nlinarith [mul_nonneg (neg_nonneg.mpr hjQ) (sub_nonneg.mpr hqq)]

private theorem penC_goodInf_t_sub (fm : FibreModel N A q k red) (hcc : fm.CuspChart) (hqN : ¬ q ∣ N)
    (dN : ModularPolynomialData N)
    (hsepN : ((dN.Φ.map (Polynomial.mapRingHom (Int.castRingHom k))).map (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (v : Place k (modularFunctionFieldC k N)) (hv : ¬ IsAffineGeomPlace k N v) (a : A) :
    penC_GoodInf R v ((penC_t : modularFunctionFieldBar (N * q))
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)) := by
  obtain ⟨ht, htres⟩ := penC_t_fst R fm hcc dN hsepN
  obtain ⟨ha, hares⟩ := penC_residue_const R a
  refine ⟨sub_mem ht ha, ?_, ?_⟩
  · have hsub : (⟨_, sub_mem ht ha⟩ : R.R₁.integers) = ⟨_, ht⟩ - ⟨_, ha⟩ := rfl
    rw [hsub, map_sub, htres, hares]
    exact sub_mem (one_mem _) (v.algebraMap_mem' _)
  · intro W hW
    refine sub_mem ?_ (W.algebraMap_mem' _)
    rw [← penC_tInfty_eq]
    exact penC_tInfty_mem_of_isCuspidal hqN W
      (ProlongationTuple.isCuspidal_of_not_isAffineGeomPlace_reduceFst P W (by rw [hW]; exact hv))

private theorem penC_goodInf_SInf (fm : FibreModel N A q k red) (hcc : fm.CuspChart) (hqN : ¬ q ∣ N)
    (dN : ModularPolynomialData N)
    (hsepN : ((dN.Φ.map (Polynomial.mapRingHom (Int.castRingHom k))).map (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (v : Place k (modularFunctionFieldC k N)) (hv : ¬ IsAffineGeomPlace k N v)
    {s : modularFunctionFieldBar (N * q)} (hs : s ∈ penC_SInf A) : penC_GoodInf R v s := by
  rcases hs with ⟨x, hx, rfl⟩ | ⟨a, rfl⟩
  · exact penC_goodInf_ICInf R fm hcc hqN dN hsepN v hv hx
  · exact penC_goodInf_t_sub R fm hcc hqN dN hsepN v hv a

private theorem penC_exists_value_bar (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    {g : modularFunctionFieldBar (N * q)} (hg : g ∈ W.toValuationSubring) :
    ∃ c : AlgebraicClosure ℚ, W.HasValue g c := by
  haveI := isCurveOver_modularFunctionFieldBar (N * q)
  have h1 : Module.finrank (AlgebraicClosure ℚ) W.ResidueField = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed W
  have hsurj : Function.Surjective (algebraMap (AlgebraicClosure ℚ) W.ResidueField) := by
    intro x
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : W.ResidueField) one_ne_zero).mp h1 x
    exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩
  obtain ⟨c, hc, -⟩ := W.exists_hasValue_of_surjective hsurj hg
  exact ⟨c, hc⟩

private theorem penC_jFun_ne_algebraMap (c : AlgebraicClosure ℚ) :
    ProlongationTuple.jFun N q ≠ algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) c := by
  rw [penC_jFun_eq_alpha]
  intro h
  have h2 : (heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom (CharPModel.jBar N)
      = (heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom
          (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c) := by
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [h, (heckeAlphaBar (AlgebraicClosure ℚ) N q).commutes c]
  exact penC_jBar_ne_algebraMap c ((heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom.injective h2)

private theorem penC_jFun_not_hasValue_of_isCuspidal
    {W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))} (hc : ProlongationTuple.IsCuspidal P W) (a : A) :
    ¬ W.HasValue (ProlongationTuple.jFun N q) (a : AlgebraicClosure ℚ) := by
  intro h
  rcases (W.hasValue_iff_eq_or_ord_sub_pos_pn h.mem _).mp h with heq | hpos
  · exact penC_jFun_ne_algebraMap _ heq
  · exact absurd (hc a) (not_le.mpr hpos)

private theorem penC_ne_zero_of_red_eq_one {τ : A} (hτ : red τ = 1) : (τ : AlgebraicClosure ℚ) ≠ 0 := by
  intro h0
  have h : τ = 0 := Subtype.ext h0
  rw [h, map_zero] at hτ
  exact zero_ne_one hτ

include R in

private theorem penC_isUnit_of_red_eq_one {τ : A} (hτ : red τ = 1) : IsUnit τ := by
  by_contra hnot
  have hm : τ ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal τ).mpr (mem_nonunits_iff.mpr hnot)
  have hres : IsLocalRing.residue A τ = 0 := (IsLocalRing.residue_eq_zero_iff τ).mpr hm
  have h := RingHom.congr_fun (penC_redBar_comp_residue R) τ
  rw [RingHom.comp_apply, hres, map_zero, hτ] at h
  exact zero_ne_one h

include R in

private theorem penC_t_hasValue_of_isZeroSide (hqN : ¬ q ∣ N)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hc : ProlongationTuple.IsCuspidal P W)
    (hW : ProlongationTuple.IsZeroSide P W) :
    ∃ b : A, W.HasValue (penC_t : modularFunctionFieldBar (N * q)) (b : AlgebraicClosure ℚ) := by
  obtain ⟨-, τ, hτ1, hτ⟩ := hW
  have hjF0 := penC_jFun_ne_zero (N := N) (q := q)
  have hjQ0 := penC_jQFun_ne_zero (N := N) (q := q)

  have htmem : (penC_t : modularFunctionFieldBar (N * q)) ∈ W.toValuationSubring := by
    rw [← penC_tInfty_eq]
    exact penC_tInfty_mem_of_isCuspidal hqN W hc
  obtain ⟨c, hcval⟩ := penC_exists_value_bar W htmem

  have hjinv_mem : (ProlongationTuple.jFun N q)⁻¹ ∈ W.toValuationSubring := by
    refine W.mem_of_ord_nonneg_pn (inv_ne_zero hjF0) ?_
    rw [W.ord_inv]
    exact neg_nonneg.mpr (by simpa using hc 0)
  obtain ⟨d, hdval⟩ := penC_exists_value_bar W hjinv_mem
  have hdA : d ∈ A := by
    rcases A.mem_or_inv_mem d with hd | hd
    · exact hd
    · by_cases hd0 : d = 0
      · rw [hd0]
        exact zero_mem _
      · exfalso
        have hjval : W.HasValue (ProlongationTuple.jFun N q) d⁻¹ := by
          have h := hdval.inv hd0
          rwa [inv_inv] at h
        exact penC_jFun_not_hasValue_of_isCuspidal hc ⟨d⁻¹, hd⟩ hjval

  have hτ0 : (τ : AlgebraicClosure ℚ) ≠ 0 := penC_ne_zero_of_red_eq_one hτ1
  have hτinv : ((τ : AlgebraicClosure ℚ))⁻¹ ∈ A := by
    obtain ⟨u, hu⟩ := penC_isUnit_of_red_eq_one R hτ1
    have h1 : (((u⁻¹ : Aˣ) : A) : AlgebraicClosure ℚ) * (τ : AlgebraicClosure ℚ) = 1 := by
      rw [← hu]
      exact_mod_cast congrArg (fun x : A => (x : AlgebraicClosure ℚ)) u.inv_mul
    rw [← eq_inv_of_mul_eq_one_left h1]
    exact ((u⁻¹ : Aˣ) : A).2

  have hq1 : 1 ≤ q * q := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : q.Prime).ne_zero)
  obtain ⟨e, he⟩ : ∃ e : ℕ, e + 1 = q * q := ⟨q * q - 1, Nat.sub_add_cancel hq1⟩
  have hid : (penC_t : modularFunctionFieldBar (N * q)) ^ q * ProlongationTuple.tZero N q
      = (ProlongationTuple.jFun N q)⁻¹ ^ e := by
    rw [← penC_tInfty_eq, ProlongationTuple.tInfty, ProlongationTuple.tZero, inv_pow, div_pow, ← pow_mul, ← he, pow_succ]
    field_simp
  have hval₁ : W.HasValue ((ProlongationTuple.jFun N q)⁻¹ ^ e) (c ^ q * (τ : AlgebraicClosure ℚ)) := by
    rw [← hid]
    exact (penC_hasValue_pow W hcval q).mul hτ
  have hval₂ : W.HasValue ((ProlongationTuple.jFun N q)⁻¹ ^ e) (d ^ e) := penC_hasValue_pow W hdval e
  have hcq : c ^ q = d ^ e * ((τ : AlgebraicClosure ℚ))⁻¹ := by
    rw [← hval₁.unique hval₂, mul_inv_cancel_right₀ hτ0]
  have hcqA : c ^ q ∈ A := by
    rw [hcq]
    exact mul_mem (pow_mem hdA e) hτinv

  have hcA : c ∈ A := by
    refine penC_mem_of_monic A A.subtype (fun t => t.2) (x := c)
      (p := Polynomial.X ^ q - Polynomial.C (⟨c ^ q, hcqA⟩ : A))
      (Polynomial.monic_X_pow_sub_C _ (Fact.out : q.Prime).ne_zero) ?_
    simp
  exact ⟨⟨c, hcA⟩, hcval⟩

private theorem penC_sep_inf (fm : FibreModel N A q k red) (hcc : fm.CuspChart) (hqN : ¬ q ∣ N) (dN : ModularPolynomialData N)
    (hsepN : ((dN.Φ.map (Polynomial.mapRingHom (Int.castRingHom k))).map (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (v : Place k (modularFunctionFieldC k N)) (hv : ¬ IsAffineGeomPlace k N v)
    (hint : ∀ s ∈ penC_SInf A, s ∈ R.R₁.integers)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hbad : ProlongationTuple.IsZeroSide P W)
    (hW : P.reduceFst W = v) :
    ∃ (u : modularFunctionFieldBar (N * q)) (hu : u ∈ penC_SInf A),
      ¬ v.HasValue (R.residue₁ ⟨u, hint u hu⟩) (0 : k) ∧ 0 < W.ord u := by
  have hc : ProlongationTuple.IsCuspidal P W :=
    ProlongationTuple.isCuspidal_of_not_isAffineGeomPlace_reduceFst P W (by rw [hW]; exact hv)
  obtain ⟨b, hb⟩ := penC_t_hasValue_of_isZeroSide R hqN W hc hbad
  have hb1 : red b ≠ 1 := by
    intro h1
    refine ProlongationTuple.not_isInftySide_of_isZeroSide P W hbad ⟨hc, b, h1, ?_⟩
    rw [penC_tInfty_eq]
    exact hb
  obtain ⟨ht, htres⟩ := penC_t_fst R fm hcc dN hsepN
  obtain ⟨ha, hares⟩ := penC_residue_const R b
  have hres : R.residue₁ ⟨_, hint _ (penC_t_sub_mem_SInf A b)⟩
      = algebraMap k (modularFunctionFieldC k N) (1 - red b) := by
    have hsub : (⟨_, hint _ (penC_t_sub_mem_SInf A b)⟩ : R.R₁.integers) = ⟨_, ht⟩ - ⟨_, ha⟩ := rfl
    rw [hsub, map_sub, htres, hares, map_sub, map_one]
  refine ⟨_, penC_t_sub_mem_SInf A b, ?_, ?_⟩
  · rw [hres]
    exact penC_not_hasValue_zero_of_ne v (v.hasValue_algebraMap _) (sub_ne_zero.mpr hb1.symm)
  · rcases (W.hasValue_iff_eq_or_ord_sub_pos_pn hb.mem _).mp hb with heq | hpos
    · exfalso
      apply hb1
      have h1 : R.residue₁ ⟨_, ht⟩ = R.residue₁ ⟨_, ha⟩ := congrArg R.residue₁ (Subtype.ext heq)
      rw [htres, hares] at h1
      have h2 : algebraMap k (modularFunctionFieldC k N) (red b) = algebraMap k (modularFunctionFieldC k N) 1 := by
        rw [map_one]
        exact h1.symm
      exact (algebraMap k (modularFunctionFieldC k N)).injective h2
    · exact hpos

private theorem penC_jq_not_mem_of_not_affine (fm : FibreModel N A q k red) (hqN : ¬ q ∣ N)
    (v : Place k (modularFunctionFieldC k N)) (hv : ¬ IsAffineGeomPlace k N v) :
    (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ∉ v.toValuationSubring := by
  intro hj
  apply hv
  refine ⟨hj, ?_⟩
  have h := (penC_FIN N A q hqN k red fm v hj).1 ⟨CharPModel.jNBar N, fm.jNBar_mem⟩
  rw [fm.piFin_jN] at h
  exact h

private theorem penC_ord_jq_neg_of_frob_eq (fm : FibreModel N A q k red) (hqN : ¬ q ∣ N)
    {v w : Place k (modularFunctionFieldC k N)} (hv : ¬ IsAffineGeomPlace k N v)
    (hw : frobOnPlacesGeomLevel k N data hKr w = v) :
    w.ord (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) < 0 := by
  by_contra hle
  have hmem : (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ∈ w.toValuationSubring :=
    w.mem_of_ord_nonneg_pn penC_jqModC_ne_zero (not_lt.mp hle)
  apply penC_jq_not_mem_of_not_affine fm hqN v hv
  rw [← hw, mem_frobOnPlacesGeomLevel_iff, frobeniusGeomLevel_jq]
  exact pow_mem hmem q

private theorem penC_residue₂_t_hasValue_zero (hqN : ¬ q ∣ N) (fm : FibreModel N A q k red) (hcc : fm.CuspChart)
    (dN : ModularPolynomialData N)
    (hsepN : ((dN.Φ.map (Polynomial.mapRingHom (Int.castRingHom k))).map (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hz₂ : (penC_t : modularFunctionFieldBar (N * q)) ∈ R.R₂.integers)
    {w : Place k (modularFunctionFieldC k N)} (hw : w.ord (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) < 0) :
    w.HasValue (R.residue₂ ⟨_, hz₂⟩) (0 : k) := by
  obtain ⟨h', hres⟩ := penC_t_snd R hqN fm hcc dN hsepN
  have hres' : R.residue₂ ⟨_, hz₂⟩ = (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)
      * (((⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ^ q)⁻¹) ^ q := hres
  have hj0 := penC_jqModC_ne_zero (N := N) (k := k)
  have hord : w.ord (R.residue₂ ⟨_, hz₂⟩)
      = w.ord (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)
        - q * (q * w.ord (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)) := by
    rw [hres', w.ord_mul hj0 (pow_ne_zero _ (inv_ne_zero (pow_ne_zero _ hj0))), penC_ord_pow, w.ord_inv, penC_ord_pow]
    ring
  refine w.hasValue_of_ord_sub_pos_pn ?_
  rw [map_zero, sub_zero, hord]
  have hq2 : (2 : ℤ) ≤ q := by exact_mod_cast (Fact.out : q.Prime).two_le
  nlinarith [mul_pos (neg_pos.mpr hw) (by nlinarith : (0 : ℤ) < q * q - 1)]

private theorem penC_etale_coeffs_inf (fm : FibreModel N A q k red) (hqN : ¬ q ∣ N)
    (m : Polynomial (modularFunctionFieldBar N))
    (hgen : IntermediateField.adjoin (AlgebraicClosure ℚ)
      (Set.range (heckeAlphaBar (AlgebraicClosure ℚ) N q) ∪ {(penC_t : modularFunctionFieldBar (N * q))}) = ⊤)
    (hm : m.Monic) (hdegm : m.natDegree = q + 1)
    (hroot : (m.map (heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom).eval (penC_t : modularFunctionFieldBar (N * q)) = 0)
    (hcoef : ∀ i : ℕ, heckeAlphaBar (AlgebraicClosure ℚ) N q (m.coeff i) ∈ R.R₁.integers) (i : ℕ) :
    (m.coeff i : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) ∈ penC_ICInf A := by
  have hloc : ((m.coeff i : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
      ∈ CharPReduction.modularLocalized (N * q) A.toSubring red := by
    have h := (R.mem_integersFst_iff _).mp (hcoef i)
    rwa [coe_heckeAlphaBar] at h
  have hreg : ∀ u₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (CharPModel.jBar N)⁻¹ ∈ u₀.toValuationSubring → m.coeff i ∈ u₀.toValuationSubring := by
    intro u₀ hu₀
    refine AlphaEngine.coeff_mem_of_forall_mem hα (finrankAlong_heckeAlphaBar_of_not_dvd N q hqN) _ hgen m hm hdegm hroot u₀ ?_ i
    intro W hW
    by_cases hc : ProlongationTuple.IsCuspidal P W
    · rw [← penC_tInfty_eq]
      exact penC_tInfty_mem_of_isCuspidal hqN W hc
    ·
      have hjinv : heckeAlphaBar (AlgebraicClosure ℚ) N q ((CharPModel.jBar N)⁻¹) ∈ W.toValuationSubring := by
        rw [← penC_mem_restrictAlong_iff _ hα W, hW]
        exact hu₀
      obtain ⟨a, ha⟩ : ∃ a : A, 0 < W.ord (ProlongationTuple.jFun N q
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)) := by
        by_contra hcon
        exact hc (fun a => not_lt.mp (fun h => hcon ⟨a, h⟩))
      have hjW : ProlongationTuple.jFun N q ∈ W.toValuationSubring := by
        have h1 := W.mem_of_ord_nonneg_pn (W.ne_zero_of_ord_pos_pn ha) ha.le
        have h2 := W.algebraMap_mem' (a : AlgebraicClosure ℚ)
        simpa using add_mem h1 h2
      have hju₀ : CharPModel.jBar N ∈ (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα).toValuationSubring := by
        rw [penC_mem_restrictAlong_iff _ hα W, ← penC_jFun_eq_alpha]
        exact hjW
      have hjQ : heckeBetaBar (AlgebraicClosure ℚ) N q
          ((penC_jF fm : fm.BFin) : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) ∈ W.toValuationSubring :=
        penC_beta_regular (hβ := hβ) data fm (penC_jF fm) _ hju₀ W rfl
      show heckeBetaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N)
        * heckeAlphaBar (AlgebraicClosure ℚ) N q ((CharPModel.jBar N)⁻¹) ^ q ∈ W.toValuationSubring
      exact mul_mem hjQ (pow_mem hjinv q)
  exact penC_gaussLemma_inf red hqN _ hloc hreg

private theorem penC_etale_inf [IsAlgClosed k] (fm : FibreModel N A q k red) (hcc : fm.CuspChart) (hqN : ¬ q ∣ N)
    (dN : ModularPolynomialData N)
    (hsepN : ((dN.Φ.map (Polynomial.mapRingHom (Int.castRingHom k))).map (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (v : Place k (modularFunctionFieldC k N)) (hv : ¬ IsAffineGeomPlace k N v) :
    ChartEtaleAt R v (penC_SInf A) := by
  obtain ⟨hz₁, hz₁res⟩ := penC_t_fst R fm hcc dN hsepN
  obtain ⟨hz₂, hz⟩ := penC_t_hz R hqN fm hcc dN hsepN
  obtain ⟨hgen, m, hm, hdegm, hroot, hcoef⟩ := h1_generator_data R hqN penC_t hz₁ hz₂ hz
  refine ⟨penC_t, m, penC_t_mem_SInf A, ⟨hz₂, hz⟩, hgen, hm, hdegm, hroot, ?_, ?_⟩
  · intro i
    exact Subring.subset_closure (penC_alpha_mem_SInf (penC_etale_coeffs_inf R fm hqN m hgen hm hdegm hroot hcoef i))
  · intro hD
    obtain ⟨η, hη, hres⟩ := h1_exists_residue_derivative_eq R hqN penC_t hz₁ hz₂ hz m hm hdegm hroot hcoef
    have hres' : R.residue₁ ⟨_, hD⟩ = 1 - R.ι η := by
      rw [R.residue₁_apply, hres hD, map_sub, map_pow, ← R.residue₁_apply, hz₁res, one_pow]
    rw [hres']

    obtain ⟨w, hw⟩ : ∃ w, frobOnPlacesGeomLevel k N data hKr w = v := by
      have hbij : Function.Bijective (frobOnPlacesGeomLevel k N data hKr) := by
        have h : frobOnPlacesGeomLevel k N data hKr = fun w => arithFrobC q k N • w :=
          funext (fun w => (arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr w).symm)
        rw [h]
        exact MulAction.bijective _
      exact hbij.2 v
    have hη0 : w.HasValue (frobeniusGeomLevel k N data hKr (R.ι η)) 0 := by
      rw [penC_frob_ι_eq R penC_t hz₂ η hη]
      have h0 := penC_hasValue_pow w (penC_residue₂_t_hasValue_zero R hqN fm hcc dN hsepN hz₂
        (penC_ord_jq_neg_of_frob_eq fm hqN hv hw)) q
      rwa [zero_pow (Fact.out : q.Prime).ne_zero] at h0
    have hηv : v.HasValue (R.ι η) 0 := by
      rw [← hw]
      exact penC_hasValue_frobOnPlaces w hη0
    have h1 : v.HasValue (1 - R.ι η) (1 - 0) := by
      rw [sub_eq_add_neg, sub_eq_add_neg]
      exact penA_hasValue_add v v.hasValue_one (penA_hasValue_neg v hηv)
    exact penC_not_hasValue_zero_of_ne v h1 (by norm_num)

private theorem penW_jqInv_hasValue_zero (fm : FibreModel N A q k red) (hqN : ¬ q ∣ N)
    (v : Place k (modularFunctionFieldC k N)) (hv : ¬ IsAffineGeomPlace k N v) :
    v.HasValue ((⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)⁻¹) (0 : k) := by
  have hnot := penC_jq_not_mem_of_not_affine fm hqN v hv
  have hneg : v.ord (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) < 0 := by
    by_contra hge
    exact hnot (v.mem_of_ord_nonneg_pn penC_jqModC_ne_zero (not_lt.mp hge))
  apply v.hasValue_of_ord_sub_pos_pn
  rw [map_zero, sub_zero, v.ord_inv]
  omega

private theorem penW_not_isAffine_sp_of_pole (u₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hpole : ∀ a : A, u₀.ord (CharPModel.jBar N
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)) ≤ 0) :
    ¬ IsAffineGeomPlace k N (P.sp u₀) := by
  intro haff
  have h1 := P.d0_j_pole u₀ hpole
  have h2 : (0 : ℤ) ≤ (P.sp u₀).ord (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) :=
    (P.sp u₀).ord_nonneg_of_mem_pn haff.1
  omega

private theorem penW_exists_separator_inf [IsAlgClosed k] (fm : FibreModel N A q k red) (hqN : ¬ q ∣ N)
    (v v' : Place k (modularFunctionFieldC k N)) (hv : ¬ IsAffineGeomPlace k N v)
    (hv' : ¬ IsAffineGeomPlace k N v') (hne : v' ≠ v) :
    ∃ b : fm.BInf, v'.HasValue (fm.piInf b) (0 : k) ∧ ¬ v.HasValue (fm.piInf b) (0 : k) := by
  by_contra hcon
  have hall : ∀ b : fm.BInf, v'.HasValue (fm.piInf b) (0 : k) → v.HasValue (fm.piInf b) (0 : k) :=
    fun b h1 => Classical.byContradiction fun h2 => hcon ⟨b, h1, h2⟩
  apply hne
  have hle : v.toValuationSubring ≤ v'.toValuationSubring := by
    intro g hg
    obtain ⟨b, b', hb', hgb⟩ := (FibreModel.piInf_range_localizes_of_not_affine N A q hqN k red fm v hv).2 g hg
    have hb'mem : fm.piInf b' ∈ v'.toValuationSubring :=
      (FibreModel.piInf_range_localizes_of_not_affine N A q hqN k red fm v' hv').1 b'
    obtain ⟨c, hc, -⟩ := v'.exists_hasValue_of_surjective (penC_residue_surjective v') hb'mem
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hb' (hall b' hc)
    have hg' : g = fm.piInf b * (fm.piInf b')⁻¹ := (eq_mul_inv_iff_mul_eq₀ (hc.ne_zero hc0)).mpr hgb
    rw [hg']
    exact mul_mem ((FibreModel.piInf_range_localizes_of_not_affine N A q hqN k red fm v' hv').1 b) (hc.inv hc0).mem
  exact (Place.ext (ValuationSubring.eq_of_le_of_ne_top _ hle v'.ne_top')).symm

private theorem penW_binf_values [IsAlgClosed k] (fm : FibreModel N A q k red) (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hP : P.sp = fm.spPlace hred dataAll hsep) (hqN : ¬ q ∣ N)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hpole : ∀ a : A, w.ord (CharPModel.jBar N
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)) ≤ 0)
    (b : fm.BInf) :
    ∃ a : A,
      w.HasValue (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) (a : AlgebraicClosure ℚ) ∧
      (P.sp w).HasValue (fm.piInf b) (red a) := by
  have hv' : ¬ IsAffineGeomPlace k N (P.sp w) := penW_not_isAffine_sp_of_pole w hpole

  have hreg : fm.piInf b ∈ (P.sp w).toValuationSubring :=
    (FibreModel.piInf_range_localizes_of_not_affine N A q hqN k red fm (P.sp w) hv').1 b
  obtain ⟨c, hc, -⟩ := (P.sp w).exists_hasValue_of_surjective (penC_residue_surjective (P.sp w)) hreg
  obtain ⟨a₁, rfl⟩ := hred c

  set b₁ : fm.BInf := b - ⟨CharPModel.constantsHom N A a₁, fm.constInf_mem a₁⟩ with hb₁
  have hpi : (fm.piInf b₁ : modularFunctionFieldC k N)
      = fm.piInf b - algebraMap k (modularFunctionFieldC k N) (red a₁) := by
    rw [hb₁, map_sub, fm.piInf_const]
  have hnu : (fm.piInf b₁ : modularFunctionFieldC k N) ∈ (P.sp w).toValuationSubring.nonunits := by
    rw [hpi]
    exact penC_sub_mem_nonunits_of_hasValue (P.sp w) hc
  have hsp : fm.spPlace hred dataAll hsep w = P.sp w := by
    rw [hP]
  rw [← hsp] at hnu
  obtain ⟨a₂, ha₂m, ha₂⟩ := (fm.piInf_mem_spPlace_nonunits_iff hred dataAll hsep w hpole b₁).mp hnu

  have hdiff : (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
      - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
          ((a₁ + a₂ : A) : AlgebraicClosure ℚ)
      = (b₁ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
            (a₂ : AlgebraicClosure ℚ) := by
    have hcoe : ((a₁ + a₂ : A) : AlgebraicClosure ℚ) = (a₁ : AlgebraicClosure ℚ) + a₂ := rfl
    have hb₁' : (b₁ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        = (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
          - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
              (a₁ : AlgebraicClosure ℚ) := by
      rw [hb₁]
      push_cast
      rfl
    rw [hcoe, hb₁', map_add, sub_sub]
  have ha₂' : (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
      - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
          ((a₁ + a₂ : A) : AlgebraicClosure ℚ)
        ∈ w.toValuationSubring.nonunits := by
    rw [hdiff]
    exact ha₂
  refine ⟨a₁ + a₂, penC_hasValue_of_sub_mem_nonunits _ ha₂', ?_⟩

  rw [map_add, penC_red_eq_zero_of_mem_maximalIdeal hred ha₂m, add_zero]
  exact hc

private theorem penW_killer_of_value (fm : FibreModel N A q k red) (hqN : ¬ q ∣ N)
    (v : Place k (modularFunctionFieldC k N)) (hv : ¬ IsAffineGeomPlace k N v)
    (u₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hu₀j : (CharPModel.jBar N)⁻¹ ∈ u₀.toValuationSubring) (a : A)
    (ha : 0 < u₀.ord (CharPModel.jBar N
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ))) :
    ∃ b : fm.BInf, 0 < u₀.ord (b : modularFunctionFieldBar N) ∧ ∃ t : k, t ≠ 0 ∧ v.HasValue (fm.piInf b) t := by
  set b : fm.BInf :=
    ⟨CharPModel.constantsHom N A a, fm.constInf_mem a⟩ * ⟨(CharPModel.jBar N)⁻¹, fm.jInvBar_mem⟩ - 1 with hb
  have hbcoe : (b : modularFunctionFieldBar N)
      = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)
          * (CharPModel.jBar N)⁻¹ - 1 := by
    rw [hb]
    push_cast
    rfl
  refine ⟨b, ?_, ?_⟩
  ·
    have hfactor : (b : modularFunctionFieldBar N)
        = -((CharPModel.jBar N)⁻¹ * (CharPModel.jBar N
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ))) := by
      rw [hbcoe, mul_sub, inv_mul_cancel₀ penC_jBar_ne_zero]
      ring
    have hj0 : (CharPModel.jBar N)⁻¹ ≠ 0 := inv_ne_zero penC_jBar_ne_zero
    have hja : CharPModel.jBar N
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ) ≠ 0 :=
      u₀.ne_zero_of_ord_pos_pn ha
    have hinv : (0 : ℤ) ≤ u₀.ord (CharPModel.jBar N)⁻¹ := u₀.ord_nonneg_of_mem_pn hu₀j
    rw [hfactor, u₀.ord_neg, u₀.ord_mul hj0 hja]
    omega
  ·
    have hpi : fm.piInf b
        = algebraMap k (modularFunctionFieldC k N) (red a)
            * (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)⁻¹ + (-1) := by
      rw [hb, map_sub, map_mul, map_one, fm.piInf_const, fm.piInf_jInv, sub_eq_add_neg]
    refine ⟨red a * 0 + -1, by simp, ?_⟩
    rw [hpi]
    exact penA_hasValue_add v ((v.hasValue_algebraMap (red a)).mul (penW_jqInv_hasValue_zero fm hqN v hv))
      (penA_hasValue_neg v v.hasValue_one)

private theorem penW_killer_of_pole [IsAlgClosed k] (fm : FibreModel N A q k red) (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hP : P.sp = fm.spPlace hred dataAll hsep) (hqN : ¬ q ∣ N)
    (v : Place k (modularFunctionFieldC k N)) (hv : ¬ IsAffineGeomPlace k N v)
    (u₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hu₀v : P.sp u₀ ≠ v)
    (hpole : ∀ a : A, u₀.ord (CharPModel.jBar N
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)) ≤ 0) :
    ∃ b : fm.BInf, 0 < u₀.ord (b : modularFunctionFieldBar N) ∧ ∃ t : k, t ≠ 0 ∧ v.HasValue (fm.piInf b) t := by
  have hv' : ¬ IsAffineGeomPlace k N (P.sp u₀) := penW_not_isAffine_sp_of_pole u₀ hpole
  obtain ⟨b, hbsp, hbv⟩ := penW_exists_separator_inf fm hqN v (P.sp u₀) hv hv' hu₀v
  obtain ⟨c, hu₀c, hspc⟩ := penW_binf_values fm hred dataAll hsep hP hqN u₀ hpole b
  have hc0 : red c = 0 := hspc.unique hbsp
  set b' : fm.BInf := b - ⟨CharPModel.constantsHom N A c, fm.constInf_mem c⟩ with hb'
  have hb'coe : (b' : modularFunctionFieldBar N)
      = (b : modularFunctionFieldBar N)
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (c : AlgebraicClosure ℚ) := by
    rw [hb']
    push_cast
    rfl
  have hpi : fm.piInf b' = fm.piInf b := by
    rw [hb', map_sub, fm.piInf_const, hc0, map_zero, sub_zero]
  refine ⟨b', ?_, ?_⟩
  · have hne0 : (b' : modularFunctionFieldBar N) ≠ 0 := by
      intro h0
      have hb'0 : b' = 0 := Subtype.ext h0
      have hpi0 : fm.piInf b = 0 := by
        rw [← hpi, hb'0, map_zero]
      apply hbv
      rw [hpi0]
      have h1 := v.hasValue_algebraMap (0 : k)
      rwa [map_zero] at h1
    have h2 := penC_sub_mem_nonunits_of_hasValue u₀ hu₀c
    rw [← hb'coe] at h2
    have hmem : (b' : modularFunctionFieldBar N) ∈ u₀.toValuationSubring := by
      rw [hb'coe]
      exact sub_mem hu₀c.mem (u₀.algebraMap_mem' _)
    have hmax : (⟨_, hmem⟩ : u₀.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ :=
      ValuationSubring.coe_mem_nonunits_iff.mp h2
    exact (u₀.mem_maximalIdeal_iff_ord_pos hne0 hmem).mp hmax
  · rw [hpi]
    obtain ⟨t, ht, -⟩ := v.exists_hasValue_of_surjective (penC_residue_surjective v)
      ((FibreModel.piInf_range_localizes_of_not_affine N A q hqN k red fm v hv).1 b)
    exact ⟨t, fun ht0 => hbv (ht0 ▸ ht), ht⟩

private theorem penW_exists_killer_inf [IsAlgClosed k] (fm : FibreModel N A q k red) (hcc : fm.CuspChart)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hP : P.sp = fm.spPlace hred dataAll hsep) (hqN : ¬ q ∣ N)
    (v : Place k (modularFunctionFieldC k N)) (hv : ¬ IsAffineGeomPlace k N v)
    (u₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hu₀j : (CharPModel.jBar N)⁻¹ ∈ u₀.toValuationSubring)
    (hu₀v : P.sp u₀ ≠ v) :
    ∃ b : fm.BInf, 0 < u₀.ord (b : modularFunctionFieldBar N) ∧ ∃ t : k, t ≠ 0 ∧ v.HasValue (fm.piInf b) t := by
  have _ := hcc
  by_cases hA : ∃ a : A, 0 < u₀.ord (CharPModel.jBar N
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ))
  · obtain ⟨a, ha⟩ := hA
    exact penW_killer_of_value fm hqN v hv u₀ hu₀j a ha
  · have hpole : ∀ a : A, u₀.ord (CharPModel.jBar N
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)) ≤ 0 :=
      fun a => not_lt.mp fun h => hA ⟨a, h⟩
    exact penW_killer_of_pole fm hred dataAll hsep hP hqN v hv u₀ hu₀v hpole

private theorem penW_not_isAffineGeomPlace_of_isInftySide
    (c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hc : ProlongationTuple.IsInftySide P c) :
    ¬ IsAffineGeomPlace k N (P.reduceFst c) := by
  apply penW_not_isAffine_sp_of_pole
  intro a
  have hcusp : c.ord (ProlongationTuple.jFun N q
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)) ≤ 0 := hc.1 a
  rw [penC_jFun_eq_alpha, ← (heckeAlphaBar (AlgebraicClosure ℚ) N q).commutes, ← map_sub,
    c.ord_restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα] at hcusp
  have he : (0 : ℤ) < (Place.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) c : ℤ) := by
    exact_mod_cast penC_ramificationIndexAlong_pos' (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα c
  by_contra hpos
  push Not at hpos
  exact absurd hcusp (not_le.mpr (mul_pos he hpos))

private theorem penC_ne_zero_of_value (fm : FibreModel N A q k red) (v : Place k (modularFunctionFieldC k N))
    {e : fm.BInf} {t : k} (ht0 : t ≠ 0) (ht : v.HasValue (fm.piInf e) t) : (e : modularFunctionFieldBar N) ≠ 0 := by
  intro h0
  have he : e = 0 := Subtype.ext h0
  rw [he, map_zero] at ht
  have h1 := v.hasValue_algebraMap (0 : k)
  rw [map_zero] at h1
  exact ht0 (ht.unique h1)

private theorem penC_value_mul (fm : FibreModel N A q k red) (v : Place k (modularFunctionFieldC k N)) {e e' : fm.BInf}
    (h : ∃ t : k, t ≠ 0 ∧ v.HasValue (fm.piInf e) t) (h' : ∃ t : k, t ≠ 0 ∧ v.HasValue (fm.piInf e') t) :
    ∃ t : k, t ≠ 0 ∧ v.HasValue (fm.piInf (e * e')) t := by
  obtain ⟨t, ht0, ht⟩ := h
  obtain ⟨t', ht0', ht'⟩ := h'
  refine ⟨t * t', mul_ne_zero ht0 ht0', ?_⟩
  rw [map_mul]
  exact ht.mul ht'

private theorem penC_value_pow (fm : FibreModel N A q k red) (v : Place k (modularFunctionFieldC k N)) {e : fm.BInf}
    (h : ∃ t : k, t ≠ 0 ∧ v.HasValue (fm.piInf e) t) (n : ℕ) :
    ∃ t : k, t ≠ 0 ∧ v.HasValue (fm.piInf (e ^ n)) t := by
  obtain ⟨t, ht0, ht⟩ := h
  refine ⟨t ^ n, pow_ne_zero n ht0, ?_⟩
  rw [map_pow]
  exact penC_hasValue_pow v ht n

private theorem penC_exists_clearing_aux [IsAlgClosed k] (fm : FibreModel N A q k red) (hcc : fm.CuspChart)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hP : P.sp = fm.spPlace hred dataAll hsep) (hqN : ¬ q ∣ N)
    (v : Place k (modularFunctionFieldC k N)) (hv : ¬ IsAffineGeomPlace k N v)
    (n : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → ℕ)
    (T : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)))
    (hT : ∀ u ∈ T, (CharPModel.jBar N)⁻¹ ∈ u.toValuationSubring ∧ P.sp u ≠ v) :
    ∃ e : fm.BInf, (∃ t : k, t ≠ 0 ∧ v.HasValue (fm.piInf e) t) ∧
      ∀ u ∈ T, (n u : ℤ) ≤ u.ord (e : modularFunctionFieldBar N) := by
  classical
  revert hT
  refine Finset.induction_on T ?_ ?_
  · intro _
    refine ⟨1, ⟨1, one_ne_zero, ?_⟩, fun u hu => absurd hu (by simp)⟩
    rw [map_one]
    exact v.hasValue_one
  · intro u T huT ih hT
    obtain ⟨e₁, he₁, hbound⟩ := ih fun w hw => hT w (Finset.mem_insert_of_mem hw)
    obtain ⟨huj, huv⟩ := hT u (Finset.mem_insert_self u T)
    obtain ⟨b, hbu, hbval⟩ := penW_exists_killer_inf fm hcc hred dataAll hsep hP hqN v hv u huj huv
    refine ⟨b ^ n u * e₁, penC_value_mul fm v (penC_value_pow fm v hbval _) he₁, ?_⟩
    have hcoe : ((b ^ n u * e₁ : fm.BInf) : modularFunctionFieldBar N)
        = (b : modularFunctionFieldBar N) ^ n u * (e₁ : modularFunctionFieldBar N) := by
      simp
    have hb0 : (b : modularFunctionFieldBar N) ≠ 0 := u.ne_zero_of_ord_pos_pn hbu
    obtain ⟨t₁, ht₁0, ht₁⟩ := he₁
    have he₁0 : (e₁ : modularFunctionFieldBar N) ≠ 0 := penC_ne_zero_of_value fm v ht₁0 ht₁
    intro w hw
    rw [hcoe, w.ord_mul (pow_ne_zero _ hb0) he₁0, penC_ord_pow]
    rcases Finset.mem_insert.mp hw with hwu | hwT
    ·
      rw [hwu]
      have h1 : (0 : ℤ) ≤ u.ord (e₁ : modularFunctionFieldBar N) :=
        u.ord_nonneg_of_mem_pn (penC_binf_mem_of_jInvBar_mem fm e₁ u huj)
      have h2 : (n u : ℤ) * 1 ≤ (n u : ℤ) * u.ord (b : modularFunctionFieldBar N) :=
        mul_le_mul_of_nonneg_left hbu (Int.natCast_nonneg _)
      linarith
    ·
      have h1 : (0 : ℤ) ≤ w.ord (b : modularFunctionFieldBar N) :=
        w.ord_nonneg_of_mem_pn (penC_binf_mem_of_jInvBar_mem fm b w (hT w (Finset.mem_insert_of_mem hwT)).1)
      have h2 : (0 : ℤ) ≤ (n u : ℤ) * w.ord (b : modularFunctionFieldBar N) :=
        mul_nonneg (Int.natCast_nonneg _) h1
      have h3 := hbound w hwT
      linarith

private theorem penC_exists_clearing [IsAlgClosed k] (fm : FibreModel N A q k red) (hcc : fm.CuspChart)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hP : P.sp = fm.spPlace hred dataAll hsep) (hqN : ¬ q ∣ N)
    (v : Place k (modularFunctionFieldC k N)) (hv : ¬ IsAffineGeomPlace k N v)
    (φ : modularFunctionFieldBar N)
    (hreg : ∀ u₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), P.sp u₀ = v → φ ∈ u₀.toValuationSubring) :
    ∃ e : fm.BInf, (∃ t : k, t ≠ 0 ∧ v.HasValue (fm.piInf e) t) ∧
      ∀ u₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        (CharPModel.jBar N)⁻¹ ∈ u₀.toValuationSubring → φ * (e : modularFunctionFieldBar N) ∈ u₀.toValuationSubring := by
  classical
  by_cases hφ0 : φ = 0
  · refine ⟨1, ⟨1, one_ne_zero, ?_⟩, fun u₀ _ => ?_⟩
    · rw [map_one]
      exact v.hasValue_one
    · rw [hφ0, zero_mul]
      exact zero_mem _
  haveI := hasPrincipalDivisors_modularFunctionFieldBar_unconditional N
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) φ hφ0
  set T : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :=
    D.support.filter (fun u => (CharPModel.jBar N)⁻¹ ∈ u.toValuationSubring ∧ u.ord φ < 0) with hT
  have hTprop : ∀ u ∈ T, (CharPModel.jBar N)⁻¹ ∈ u.toValuationSubring ∧ P.sp u ≠ v := by
    intro u hu
    obtain ⟨-, huj, huord⟩ := Finset.mem_filter.mp hu
    refine ⟨huj, fun huv => ?_⟩
    have := u.ord_nonneg_of_mem_pn (hreg u huv)
    omega
  obtain ⟨e, he, hbound⟩ := penC_exists_clearing_aux fm hcc hred dataAll hsep hP hqN v hv (fun u => (-u.ord φ).toNat) T hTprop
  refine ⟨e, he, fun u₀ hu₀ => ?_⟩
  have he_mem : (e : modularFunctionFieldBar N) ∈ u₀.toValuationSubring := penC_binf_mem_of_jInvBar_mem fm e u₀ hu₀
  by_cases hpole : u₀.ord φ < 0
  · have hu₀T : u₀ ∈ T := by
      rw [hT, Finset.mem_filter, Finsupp.mem_support_iff, hD u₀]
      exact ⟨by omega, hu₀, hpole⟩
    have h1 : (((-u₀.ord φ).toNat : ℕ) : ℤ) ≤ u₀.ord (e : modularFunctionFieldBar N) := hbound u₀ hu₀T
    rw [Int.toNat_of_nonneg (by omega)] at h1
    obtain ⟨t, ht0, ht⟩ := he
    have he0 : (e : modularFunctionFieldBar N) ≠ 0 := penC_ne_zero_of_value fm v ht0 ht
    refine u₀.mem_of_ord_nonneg_pn (mul_ne_zero hφ0 he0) ?_
    rw [u₀.ord_mul hφ0 he0]
    omega
  · exact mul_mem (u₀.mem_of_ord_nonneg_pn hφ0 (not_lt.mp hpole)) he_mem

private theorem penC_nIncl_inf [IsAlgClosed k] (fm : FibreModel N A q k red) (hcc : fm.CuspChart) (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hP : P.sp = fm.spPlace hred dataAll hsep) (hqN : ¬ q ∣ N)
    (v : Place k (modularFunctionFieldC k N)) (hv : ¬ IsAffineGeomPlace k N v)
    (hint : ∀ s ∈ penC_SInf A, s ∈ R.R₁.integers)
    (φ : modularFunctionFieldBar N) (hφ : heckeAlphaBar (AlgebraicClosure ℚ) N q φ ∈ R.R₁.integers)
    (hreg : ∀ u₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), P.sp u₀ = v → φ ∈ u₀.toValuationSubring) :
    ∃ (s : modularFunctionFieldBar (N * q)) (_ : s ∈ penC_SInf A) (e : modularFunctionFieldBar (N * q)) (he : e ∈ penC_SInf A),
      ¬ v.HasValue (R.residue₁ ⟨e, hint e he⟩) (0 : k) ∧ heckeAlphaBar (AlgebraicClosure ℚ) N q φ * e = s := by
  obtain ⟨e₀, ⟨t, ht0, ht⟩, hclear⟩ := penC_exists_clearing fm hcc hred dataAll hsep hP hqN v hv φ hreg

  obtain ⟨he₀I, he₀res⟩ := penC_residue_alpha_inf R fm hcc (dataAll N (dvd_refl N)) hsep e₀
  have hψint : heckeAlphaBar (AlgebraicClosure ℚ) N q (φ * (e₀ : modularFunctionFieldBar N)) ∈ R.R₁.integers := by
    rw [map_mul]
    exact mul_mem hφ he₀I
  have hψloc : ((φ * (e₀ : modularFunctionFieldBar N) : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
      ∈ CharPReduction.modularLocalized (N * q) A.toSubring red := by
    have h := (R.mem_integersFst_iff _).mp hψint
    rwa [coe_heckeAlphaBar] at h
  have hψIC : (φ * (e₀ : modularFunctionFieldBar N) : modularFunctionFieldBar N) ∈ penC_ICInf A :=
    penC_gaussLemma_inf red hqN _ hψloc hclear
  refine ⟨_, penC_alpha_mem_SInf hψIC, _, penC_alpha_mem_SInf (penC_binf_mem_ICInf fm e₀), ?_, ?_⟩
  · have hres : R.residue₁ ⟨_, hint _ (penC_alpha_mem_SInf (penC_binf_mem_ICInf fm e₀))⟩ = fm.piInf e₀ := he₀res
    rw [hres]
    exact penC_not_hasValue_zero_of_ne v ht ht0
  · exact (map_mul (heckeAlphaBar (AlgebraicClosure ℚ) N q) φ (e₀ : modularFunctionFieldBar N)).symm

private structure penC_CuspChartFields (v : Place k (modularFunctionFieldC k N)) (S : Set (modularFunctionFieldBar (N * q))) :
    Prop where
  hint : ∀ s ∈ S, s ∈ R.R₁.integers
  hregv : ∀ (s : modularFunctionFieldBar (N * q)) (hs : s ∈ S),
    (R.residue₁ ⟨s, hint s hs⟩ : modularFunctionFieldC k N) ∈ v.toValuationSubring
  hregOver : ∀ s ∈ S, ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
    P.reduceFst W = v → s ∈ W.toValuationSubring
  hnIncl : ∀ φ : modularFunctionFieldBar N,
    heckeAlphaBar (AlgebraicClosure ℚ) N q φ ∈ R.R₁.integers →
    (∀ u₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), P.sp u₀ = v → φ ∈ u₀.toValuationSubring) →
    ∃ (s : modularFunctionFieldBar (N * q)) (_ : s ∈ S) (e : modularFunctionFieldBar (N * q)) (he : e ∈ S),
      ¬ v.HasValue (R.residue₁ ⟨e, hint e he⟩) (0 : k) ∧ heckeAlphaBar (AlgebraicClosure ℚ) N q φ * e = s
  hE : ChartEtaleAt R v S
  hsep : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
    ProlongationTuple.IsZeroSide P W → P.reduceFst W = v →
      ∃ (u : modularFunctionFieldBar (N * q)) (hu : u ∈ S),
        ¬ v.HasValue (R.residue₁ ⟨u, hint u hu⟩) (0 : k) ∧ 0 < W.ord u

private def penC_CuspChartAt (v : Place k (modularFunctionFieldC k N)) : Prop :=
  ∃ S : Set (modularFunctionFieldBar (N * q)), penC_CuspChartFields R v S

private theorem penC_exists_cuspChartAt_of_not_affine [IsAlgClosed k] (fm : FibreModel N A q k red) (hcc : fm.CuspChart)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hP : P.sp = fm.spPlace hred dataAll hsep) (hqN : ¬ q ∣ N)
    (v : Place k (modularFunctionFieldC k N)) (hv : ¬ IsAffineGeomPlace k N v) :
    penC_CuspChartAt R v := by
  have hgood : ∀ s ∈ penC_SInf A, penC_GoodInf R v s :=
    fun _ hs => penC_goodInf_SInf R fm hcc hqN (dataAll N (dvd_refl N)) hsep v hv hs
  have hint : ∀ s ∈ penC_SInf A, s ∈ R.R₁.integers := fun s hs => (hgood s hs).choose
  refine ⟨penC_SInf A,
    { hint := hint
      hregv := fun s hs => (hgood s hs).choose_spec.1
      hregOver := fun s hs W hW => (hgood s hs).choose_spec.2 W hW
      hnIncl := fun φ hφ hreg => penC_nIncl_inf R fm hcc hred dataAll hsep hP hqN v hv hint φ hφ hreg
      hE := penC_etale_inf R fm hcc hqN (dataAll N (dvd_refl N)) hsep v hv
      hsep := fun W hbad hW => penC_sep_inf R fm hcc hqN (dataAll N (dvd_refl N)) hsep v hv hint W hbad hW }⟩

private theorem penC_not_affine_of_isInftySide
    (c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hc : ProlongationTuple.IsInftySide P c) :
    ¬ IsAffineGeomPlace k N (P.reduceFst c) := by
  obtain ⟨hcusp, -⟩ := hc
  have hres : ∀ a : A, (c.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα).ord (CharPModel.jBar N
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)) ≤ 0 := by
    intro a
    have h : c.ord (ProlongationTuple.jFun N q
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)) ≤ 0 := hcusp a
    rw [penC_jFun_eq_alpha, ← (heckeAlphaBar (AlgebraicClosure ℚ) N q).commutes, ← map_sub,
      c.ord_restrictAlong _ hα] at h
    have he : (0 : ℤ) < Place.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) c := by
      exact_mod_cast penC_ramificationIndexAlong_pos' (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα c
    by_contra hnot
    exact absurd h (not_le.mpr (mul_pos he (not_le.mp hnot)))
  have hpole := P.d0_j_pole _ hres
  intro haff
  obtain ⟨hj, -⟩ := haff
  have h2 : (0 : ℤ) ≤ (P.sp (c.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα)).ord
      (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) :=
    (P.reduceFst c).ord_nonneg_of_mem_pn hj
  exact absurd h2 (not_le.mpr hpole)

private theorem penC_exists_cuspChartAt [IsAlgClosed k] (fm : FibreModel N A q k red) (hcc : fm.CuspChart)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hP : P.sp = fm.spPlace hred dataAll hsep) (hqN : ¬ q ∣ N)
    (v : Place k (modularFunctionFieldC k N))
    (hv : ∃ c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)), ProlongationTuple.IsInftySide P c ∧ P.reduceFst c = v) :
    penC_CuspChartAt R v := by
  obtain ⟨c, hc, rfl⟩ := hv
  exact penC_exists_cuspChartAt_of_not_affine R fm hcc hred dataAll hsep hP hqN _ (penC_not_affine_of_isInftySide c hc)

end ModularCurve.PlaceSpecialization
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve.AlphaEngine"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve.AlphaEngine"

end NR3_50_package
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve.AlphaEngine"

p2m_open "AlgebraicCurve ModularCurve~jBar P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve"
p2m_open "ModularCurve.PlaceSpecialization~IsInftySide~jFun~tInfty~tZero~IsCuspidal~IsZeroSide P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart.ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple"

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [IsAlgClosed k] (hqN : ¬ q ∣ N) (fm : CharPModel.FibreModel N A q k red)
    (hcc : fm.CuspChart)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hP : P.sp = fm.spPlace hred dataAll hsep)
    (R : ProlongationTuple P) : R.CuspLawInfty := by
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) :=
    hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)

  have hC : NormReduction R := by
    intro f h₁ h₂ hr₁ hr₂
    exact normReduction_of_not_dvd_of_surjective hqN hred P R f h₁ h₂ hr₁ hr₂

  have hsp : ReducesDivisors P := by
    intro f hf hmem hne D hD v
    rw [hP]
    exact penS_mapDomain_spPlace_eq_ord_modularRedLocHom red hred hqN fm hcc dataAll hsep f hf hne D hD v

  have hcoord : HasCoordinates P := hasCoordinates_of_sp_eq_spPlace fm hcc hred dataAll hsep hP hqN

  have hcharts : ∀ v : Place k (modularFunctionFieldC k N),
      (∃ c, ProlongationTuple.IsInftySide P c ∧ P.reduceFst c = v) →
      ∃ S : Set (modularFunctionFieldBar (N * q)), penC_ChartAt R v S := fun v hv => by
    obtain ⟨S, hS⟩ := penC_exists_cuspChartAt R fm hcc hred dataAll hsep hP hqN v hv
    exact ⟨S, ⟨hS.hint, hS.hregv, hS.hregOver, hS.hnIncl, hS.hE, hS.hsep⟩⟩

  have hB : penC_InftyBound R :=
    penC_inftyBound_of_charts R hqN hsp hcoord hcharts
      (fun b hb =>
        sum_ramificationIndexAlong_heckeAlphaBar_filter_isInftySide_fiberAlong_eq_one_of_forall_ord_jq_sub_nonpos
          hqN P b hb)
  have hL : CuspLocalSemicontinuity R := penC_cuspLSC_of_inftyBound R hqN hB
  exact cuspLawInfty_of_cuspLocalSemicontinuity_of_pullbackBalanced R hqN hsp hC hL
    (penT_pullbackBalanced_of_not_dvd R hqN) (penT_spAvoids_of_reducesDivisors hsp)

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_of_sp_eq_spPlace_of_cuspChart (solution)
