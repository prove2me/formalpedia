-- Prove2me | solution 1 for ModularCurve.exists_linearEquiv_kaehlerH0_baseChange_intLattice_of_ratCurveModel_of_cuspSection_compat_of_neZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/ed3088dd-2f07-5c0a-967f-e9ae991dfc22

import Mathlib
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_ModularCurve_HeckeProj
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_JacJ1Iface
import Definitions.Def_ModularCurve_QAdicPlace
import Theorems.Thm_ModularCurve_coeffMap_diffQExpBar_heckeDiffBar_eq_qExpansion_latticeRestrictHom_heckeProj_heckeGen
import Theorems.Thm_ModularCurve_diffQExpBar_injective_of_neZero
import Theorems.Thm_ModularCurve_exists_ringHom_cover_modularFunctionFieldBar_of_ratCurveModel_of_neZero
import Theorems.Thm_CuspForm_exists_addMonoidHom_baseChange_intLattice_qExpansion_injective_of_ratLocalizedAt
import Theorems.Thm_ModularCurve_kaehlerH0_res_injective_of_injective_chartMap_of_neZero
import Theorems.Thm_ModularCurve_exists_powerSeries_diffQExpBar_eq_ofPowerSeries_map_of_kaehlerH0_of_ratCurveModel_of_cuspSection_compat_of_neZero
import Theorems.Thm_ModularCurve_exists_kaehlerH0_coeffMap_diffQExpBar_eq_qExpansion_of_mem_intLattice_of_ratCurveModel_of_cuspSection_compat_of_neZero
import Theorems.Thm_ModularCurve_res_mem_regularDifferentialsBar_of_chartMap_of_neZero
import Theorems.Thm_ModularCurve_exists_cuspForm_coeffMap_diffQExpBar_eq_qExpansion_of_mem_regularDifferentialsBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_linearEquiv_kaehlerH0_baseChange_intLattice_of_ratCurveModel_of_cuspSection_compat_of_neZero
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation NeronModelInfra.isOpenImmersion_specGenericFibreInclusion NeronModelInfra.isLocalizationAway_uniformizer_zp HeckeEis.instFiniteProjLineCusps ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.Gamma0Pair.isElliptic AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar"
p2m_attr_erase "instance" "ModularCurve.instIsScalarTowerJAdjoin ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.numberField_of_finiteDimensional AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ HeckeEis.binaryFormEval_mk HeckeEis.binaryFormAlphaAdj_apply_coe HeckeEis.binaryFormRepSL_apply_coe ModularCurve.ProjectiveLine.vecMulRow_snd HeckeEis.projLineRepSL_apply HeckeEis.projLineAct_one HeckeEis.projLineRep_apply HeckeEis.projLineAlphaAdj_apply ModularCurve.ProjectiveLine.vecMulRow_fst ModularCurve.ProjectiveLine.vecMul_mk ModularCurve.ProjectiveLine.map_mk HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply"
p2m_attr_erase "simp" "HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero HeckeEis.coe_linePow ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"
p2m_attr_erase "simp" "WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.symPoly_zero AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk"
p2m_attr_erase "simp" "AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra ModularCurve AlgebraicCurve IsLocalRing CuspForm

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) (ι₀ : AlgebraicClosure ℚ →+* ℂ)
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))) [IsIntegral X] [IsProper c]
    [SmoothOfRelativeDimension 1 c] (𝒱 : X.TwoAffineOpenCover)

    (M₀ : CurveModel ℚ ↥(modularFunctionFieldFull N))
    (e₀ : M₀.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))) [IsIso e₀]
    (he₀ : e₀ ≫ pullback.snd c _ = M₀.toBase)
    (hgen0 : genericPoint M₀.C ∈ (e₀ ≫ pullback.fst c _) ⁻¹ᵁ 𝒱.U0)
    (hgen01 : genericPoint M₀.C ∈ (e₀ ≫ pullback.fst c _) ⁻¹ᵁ (𝒱.U0 ⊓ 𝒱.U1))

    (ι : (𝒱.cover c).A0 →+* ↥(modularFunctionFieldBar N))
    (hιdef : ∀ a : (𝒱.cover c).A0, ((ι a : ↥(modularFunctionFieldBar N)) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) (((M₀.ffEquiv.symm ((M₀.C.presheaf.germ ((e₀ ≫ pullback.fst c _) ⁻¹ᵁ 𝒱.U0) (genericPoint M₀.C) hgen0).hom (((e₀ ≫ pullback.fst c _).app (𝒱.U0)).hom a))) : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ))
    (hιR : ι.comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (𝒱.cover c).A0) =
      (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))
    (res : ↥((𝒱.kaehlerSections c).H0) →+ Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ])
    (hres : ∀ ω : ↥((𝒱.kaehlerSections c).H0),
      res ω = KaehlerDifferential.mapOfRingHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) ι hιR ω.val.1)

    (εinf : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))) c)
    (x₀ : closedPoints M₀.C)
    (y : Spec (CommRingCat.of ℚ) ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))))
    (hx₀ : M₀.placeOfPoint x₀ = cuspInftyFull N)
    (hy : y ≫ pullback.snd c _ = 𝟙 _)
    (hyε : y ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)) ≫ εinf.1)
    (hyx₀ : (y ≫ inv e₀).base (IsLocalRing.closedPoint ℚ) = x₀.1)

    (Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (eη : Mη.C ⟶ pullback c (Spec.map (CommRingCat.ofHom
      (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))))) [IsIso eη]
    (heη : eη ≫ pullback.snd c _ = Mη.toBase)

    (hgal : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst c _ =
        Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
          x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x' =
        arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) g • Mη.pointEquivPlace x)
    (hcompat : ∀ (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
        (y : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
          pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))))
        (x₀ : closedPoints M₀.C),
      y ≫ pullback.fst c _ = x.1 ≫ eη ≫ pullback.fst c _ →
      (y ≫ inv e₀).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) = x₀.1 →
      ((Mη.pointEquivPlace x).toValuationSubring.toSubring.comap
          ((baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull N)).toAlgHom.toRingHom.comp
            (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ)
              (B := ↥(modularFunctionFieldFull N))).toRingHom) =
        (M₀.placeOfPoint x₀).toValuationSubring.toSubring))
    (ρ : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p → (↥(GaloisRep.ratLocalizedAt p) →+* ↥A))
    (hρ : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p),
      A.subtype.comp (ρ A hA) = algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))
    (Ms : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
      CurveModel (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N))
    (es : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p), (Ms A hA).C ⟶ pullback c (Spec.map (CommRingCat.ofHom
      ((residue ↥A).comp (ρ A hA)))))
    (hes_iso : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p), IsIso (es A hA))
    (hes : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p),
      es A hA ≫ pullback.snd c _ = (Ms A hA).toBase)

    (hsp : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
      [IsAlgClosed (ResidueField ↥A)],
      ∃ r : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
          Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N),
        IsPlaceReductionModL A N r ∧
        ∀ (xA : SchemeHomOver (Spec.map (CommRingCat.ofHom (ρ A hA))) c)
          (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
          (y : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (Ms A hA).C //
            q ≫ (Ms A hA).toBase = 𝟙 _}),
          x.1 ≫ eη ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom A.subtype) ≫ xA.1 →
          y.1 ≫ es A hA ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ xA.1 →
          (Ms A hA).pointEquivPlace y = r (Mη.pointEquivPlace x)) :
    Function.Injective res ∧
    ∃ Θ : ↥((𝒱.kaehlerSections c).H0) ≃ₗ[↥(GaloisRep.ratLocalizedAt p)] (↥(GaloisRep.ratLocalizedAt p) ⊗[ℤ] ↥(CuspForm.intLattice N 2)),
      (∀ (ω : ↥((𝒱.kaehlerSections c).H0)) (f : ↥(CuspForm.intLattice N 2)), Θ ω = (1 : ↥(GaloisRep.ratLocalizedAt p)) ⊗ₜ[ℤ] f →
        coeffMap ι₀ (diffQExpBar N (res ω)) =
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2))) ∧
      (∀ (ℓ : Nat.Primes) (ω : ↥((𝒱.kaehlerSections c).H0)), ∃ ω' : ↥((𝒱.kaehlerSections c).H0),
        res ω' = heckeDiffBar N ℓ (res ω) ∧
        Θ ω' = ((((CuspForm.latticeRestrictHom N ∅).toRingHom.comp (heckeProj N)) (heckeGen ℓ)).val).baseChange ↥(GaloisRep.ratLocalizedAt p) (Θ ω))  := by
  classical

  obtain ⟨ι', ι₀₁, hι'def, -, -, hι'R, -, hι'inj, -, hι'rat, hι'frac⟩ :=
    ModularCurve.exists_ringHom_cover_modularFunctionFieldBar_of_ratCurveModel_of_neZero N p c 𝒱 M₀ e₀ he₀ hgen0 hgen01
  have hιι' : ι' = ι := by
    refine RingHom.ext fun a => Subtype.ext ?_
    rw [hι'def a, hιdef a]
  subst hιι'
  have hιinj : Function.Injective ι' := hι'inj

  have hres_inj : Function.Injective res :=
    ModularCurve.kaehlerH0_res_injective_of_injective_chartMap_of_neZero N p c 𝒱 ι' hιR hιinj res hres
  have hreg : ∀ ω, res ω ∈ regularDifferentialsBar N := fun ω =>
    ModularCurve.res_mem_regularDifferentialsBar_of_chartMap_of_neZero N p c 𝒱 ι' hιR hιinj hι'rat hι'frac res hres ω
  have hres_smul : ∀ (r : ↥(GaloisRep.ratLocalizedAt p)) (ω : ↥((𝒱.kaehlerSections c).H0)),
      res (r • ω) = (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ) r) • res ω := by
    intro r ω
    rw [hres, hres]
    exact LinearMap.map_smulₛₗ _ r ω.val.1

  have hdQ_smul : ∀ (a : AlgebraicClosure ℚ) (η : Ω[↥(modularFunctionFieldBar N)⁄AlgebraicClosure ℚ]) (k : ℤ),
      (coeffMap ι₀ (diffQExpBar N (a • η))).coeff k = ι₀ a * (coeffMap ι₀ (diffQExpBar N η)).coeff k := by
    intro a η k
    rw [← IsScalarTower.algebraMap_smul (↥(modularFunctionFieldBar N)) a η, LinearMap.map_smul, IsScalarTower.algebraMap_smul,
      coeffMap_coeff, HahnSeries.coeff_smul, coeffMap_coeff, smul_eq_mul, map_mul]

  let Q : ↥((𝒱.kaehlerSections c).H0) → LaurentSeries ℂ := fun ω => coeffMap ι₀ (diffQExpBar N (res ω))
  have hQ_def : ∀ ω, Q ω = coeffMap ι₀ (diffQExpBar N (res ω)) := fun _ => rfl
  have hQ_add : ∀ ω₁ ω₂, Q (ω₁ + ω₂) = Q ω₁ + Q ω₂ := by
    intro ω₁ ω₂; simp only [Q, map_add]
  have hQ_smul : ∀ (r : ↥(GaloisRep.ratLocalizedAt p)) ω, Q (r • ω) =
      HahnSeries.C (ι₀ (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ) r)) * Q ω := by
    intro r ω
    ext k
    rw [hQ_def, hQ_def, hres_smul, hdQ_smul, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
  have hQ_inj : ∀ ω, Q ω = 0 → ω = 0 := by
    intro ω hω
    apply hres_inj
    rw [map_zero]
    apply ModularCurve.diffQExpBar_injective_of_neZero N
    rw [map_zero]
    ext k
    have := congrArg (fun x : LaurentSeries ℂ => x.coeff k) hω
    simp only [Q, coeffMap_coeff] at this
    simpa using this

  obtain ⟨E, hE, hEinj, hEsurj⟩ := CuspForm.exists_addMonoidHom_baseChange_intLattice_qExpansion_injective_of_ratLocalizedAt N p ι₀
  have hE_smul : ∀ (r : ↥(GaloisRep.ratLocalizedAt p)) (g : ↥(GaloisRep.ratLocalizedAt p) ⊗[ℤ] ↥(CuspForm.intLattice N 2)),
      E (r • g) = PowerSeries.C (ι₀ (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ) r)) * E g := by
    intro r g
    induction g using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, mul_zero]
    | tmul r' f => rw [TensorProduct.smul_tmul', smul_eq_mul, hE, hE, map_mul, map_mul, map_mul, mul_assoc]
    | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, mul_add]
  have hE_one : ∀ f : ↥(CuspForm.intLattice N 2),
      E ((1 : ↥(GaloisRep.ratLocalizedAt p)) ⊗ₜ[ℤ] f) = UpperHalfPlane.qExpansion 1 (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) := by
    intro f; rw [hE, map_one, map_one, map_one, one_mul]

  have hex : ∀ ω, ∃ g : ↥(GaloisRep.ratLocalizedAt p) ⊗[ℤ] ↥(CuspForm.intLattice N 2), HahnSeries.ofPowerSeries ℤ ℂ (E g) = Q ω := by
    intro ω
    obtain ⟨F, hF⟩ := ModularCurve.exists_cuspForm_coeffMap_diffQExpBar_eq_qExpansion_of_mem_regularDifferentialsBar
      N ι₀ (res ω) (hreg ω)
    obtain ⟨P, hP⟩ := ModularCurve.exists_powerSeries_diffQExpBar_eq_ofPowerSeries_map_of_kaehlerH0_of_ratCurveModel_of_cuspSection_compat_of_neZero N p hpN ι₀ c 𝒱 M₀ e₀ he₀ hgen0 ι' hιdef hιR res hres εinf x₀ y hx₀ hy hyε hyx₀ Mη eη heη hgal hcompat ρ hρ Ms es hes_iso hes hsp ω
    have hcoef : ∀ n : ℕ, ∃ r : ↥(GaloisRep.ratLocalizedAt p),
        PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 F) = ι₀ (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ) r) := by
      intro n
      refine ⟨PowerSeries.coeff n P, ?_⟩
      have h1 := congrArg (fun x : LaurentSeries ℂ => x.coeff (n : ℤ)) hF
      simp only [coeffMap_coeff, HahnSeries.ofPowerSeries_apply_coeff] at h1
      rw [← h1, hP, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]
    obtain ⟨g, hg⟩ := hEsurj F hcoef
    exact ⟨g, by rw [hg]; exact hF.symm⟩
  have huniq : ∀ g g' : ↥(GaloisRep.ratLocalizedAt p) ⊗[ℤ] ↥(CuspForm.intLattice N 2),
      HahnSeries.ofPowerSeries ℤ ℂ (E g) = HahnSeries.ofPowerSeries ℤ ℂ (E g') → g = g' := fun g g' h =>
    hEinj (HahnSeries.ofPowerSeries_injective h)
  choose θ hθ using hex

  have hθ_add : ∀ ω₁ ω₂, θ (ω₁ + ω₂) = θ ω₁ + θ ω₂ := by
    intro ω₁ ω₂
    apply huniq
    rw [hθ, hQ_add, ← hθ ω₁, ← hθ ω₂, map_add, map_add]
  have hθ_smul : ∀ (r : ↥(GaloisRep.ratLocalizedAt p)) ω, θ (r • ω) = r • θ ω := by
    intro r ω
    apply huniq
    rw [hθ, hQ_smul, ← hθ ω, hE_smul, map_mul, HahnSeries.ofPowerSeries_C]
  let Θₗ : ↥((𝒱.kaehlerSections c).H0) →ₗ[↥(GaloisRep.ratLocalizedAt p)] ↥(GaloisRep.ratLocalizedAt p) ⊗[ℤ] ↥(CuspForm.intLattice N 2) :=
    { toFun := θ, map_add' := hθ_add, map_smul' := hθ_smul }
  have hΘₗ : ∀ ω, Θₗ ω = θ ω := fun _ => rfl
  have hinj : Function.Injective Θₗ := by
    intro ω₁ ω₂ h
    rw [hΘₗ, hΘₗ] at h
    have hQ12 : Q ω₁ = Q ω₂ := by rw [← hθ ω₁, ← hθ ω₂, h]
    have h0 : Q (ω₁ - ω₂) = 0 := by
      have e := hQ_add (ω₁ - ω₂) ω₂
      rw [sub_add_cancel, hQ12] at e
      simpa using e.symm
    exact sub_eq_zero.mp (hQ_inj _ h0)
  have hone : ∀ f : ↥(CuspForm.intLattice N 2), ∃ ω, θ ω = (1 : ↥(GaloisRep.ratLocalizedAt p)) ⊗ₜ[ℤ] f := by
    intro f
    obtain ⟨ω, hω⟩ := ModularCurve.exists_kaehlerH0_coeffMap_diffQExpBar_eq_qExpansion_of_mem_intLattice_of_ratCurveModel_of_cuspSection_compat_of_neZero N p hpN ι₀ c 𝒱 M₀ e₀ he₀ hgen0 ι' hιdef hιR res hres εinf x₀ y hx₀ hy hyε hyx₀ Mη eη heη hgal hcompat ρ hρ Ms es hes_iso hes hsp f
    refine ⟨ω, huniq _ _ ?_⟩
    rw [hθ, hE_one]
    exact hω
  have hsurj : Function.Surjective Θₗ := by
    intro g
    induction g using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul r f =>
      obtain ⟨ω, hω⟩ := hone f
      exact ⟨r • ω, by rw [map_smul, hΘₗ, hω, TensorProduct.smul_tmul', smul_eq_mul, mul_one]⟩
    | add x y hx hy =>
      obtain ⟨ω₁, rfl⟩ := hx; obtain ⟨ω₂, rfl⟩ := hy
      exact ⟨ω₁ + ω₂, map_add _ _ _⟩
  let Θ := LinearEquiv.ofBijective Θₗ ⟨hinj, hsurj⟩
  have hΘ : ∀ ω, Θ ω = θ ω := fun _ => rfl
  refine ⟨hres_inj, Θ, ?_, ?_⟩
  ·
    intro ω f hΘf
    rw [hΘ] at hΘf
    show Q ω = _
    rw [← hθ ω, hΘf, hE_one]
  ·
    intro ℓ ω
    have hsymm_tmul : ∀ (r : ↥(GaloisRep.ratLocalizedAt p)) (f : ↥(CuspForm.intLattice N 2)),
        Θ.symm (r ⊗ₜ[ℤ] f) = r • Θ.symm ((1 : ↥(GaloisRep.ratLocalizedAt p)) ⊗ₜ[ℤ] f) := by
      intro r f
      apply Θ.injective
      rw [map_smul, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, TensorProduct.smul_tmul', smul_eq_mul,
        mul_one]
    have key : ∀ g : ↥(GaloisRep.ratLocalizedAt p) ⊗[ℤ] ↥(CuspForm.intLattice N 2),
        coeffMap ι₀ (diffQExpBar N (heckeDiffBar N ℓ (res (Θ.symm g)))) =
          HahnSeries.ofPowerSeries ℤ ℂ (E ((((((CuspForm.latticeRestrictHom N ∅).toRingHom.comp (heckeProj N)) (heckeGen ℓ)).val)).baseChange ↥(GaloisRep.ratLocalizedAt p) g)) := by
      intro g
      induction g using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul r f =>
        have h1 : coeffMap ι₀ (diffQExpBar N (res (Θ.symm ((1 : ↥(GaloisRep.ratLocalizedAt p)) ⊗ₜ[ℤ] f)))) =
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2)) := by
          show Q _ = _
          rw [← hθ, ← hΘ, LinearEquiv.apply_symm_apply, hE_one]
        have h36 := ModularCurve.coeffMap_diffQExpBar_heckeDiffBar_eq_qExpansion_latticeRestrictHom_heckeProj_heckeGen
          N ι₀ ℓ (res (Θ.symm ((1 : ↥(GaloisRep.ratLocalizedAt p)) ⊗ₜ[ℤ] f))) f h1
        rw [hsymm_tmul, hres_smul, map_smul, LinearMap.baseChange_tmul, hE, map_mul, HahnSeries.ofPowerSeries_C, ← h36]
        ext k
        rw [hdQ_smul, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
      | add x y hx hy => simp only [map_add, hx, hy]
    refine ⟨Θ.symm ((((((CuspForm.latticeRestrictHom N ∅).toRingHom.comp (heckeProj N)) (heckeGen ℓ)).val)).baseChange ↥(GaloisRep.ratLocalizedAt p) (Θ ω)), ?_, by rw [LinearEquiv.apply_symm_apply]⟩
    have hcinj : Function.Injective (coeffMap ι₀ : LaurentSeries (AlgebraicClosure ℚ) → LaurentSeries ℂ) := by
      intro x₁ x₂ h
      ext k
      apply ι₀.injective
      rw [← coeffMap_coeff, ← coeffMap_coeff, h]
    apply ModularCurve.diffQExpBar_injective_of_neZero N
    apply hcinj
    have lhs : coeffMap ι₀ (diffQExpBar N (res (Θ.symm ((((((CuspForm.latticeRestrictHom N ∅).toRingHom.comp (heckeProj N)) (heckeGen ℓ)).val)).baseChange ↥(GaloisRep.ratLocalizedAt p) (Θ ω))))) =
        HahnSeries.ofPowerSeries ℤ ℂ (E ((((((CuspForm.latticeRestrictHom N ∅).toRingHom.comp (heckeProj N)) (heckeGen ℓ)).val)).baseChange ↥(GaloisRep.ratLocalizedAt p) (Θ ω))) := by
      show Q _ = _
      rw [← hθ, ← hΘ, LinearEquiv.apply_symm_apply]
    rw [lhs, ← key (Θ ω), LinearEquiv.symm_apply_apply]

end S_ModularCurve_exists_linearEquiv_kaehlerH0_baseChange_intLattice_of_ratCurveModel_of_cuspSection_compat_of_neZero
end P2MW
export P2MW.S_ModularCurve_exists_linearEquiv_kaehlerH0_baseChange_intLattice_of_ratCurveModel_of_cuspSection_compat_of_neZero (solution)
