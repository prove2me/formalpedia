-- Prove2me | solution 1 for ModularCurve.reductionModL_smul_of_isFrobeniusAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/5879ee95-3000-5760-9aa2-a8eb1acb1fe6

import Mathlib
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_FrobeniusModL
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_JZero_divisible
import Theorems.Thm_ModularCurve_frobeniusInputsModL
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_reductionModL_smul_of_isFrobeniusAt
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree WeierstrassCurve.Affine.Point.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "instance" "ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply"
p2m_attr_erase "simp" "AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk"
p2m_attr_erase "simp" "ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap"

set_option autoImplicit false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "IsPlaceReductionAlong integralPrincipalDivisors PrincipalGeneratedByIntegral ReductionInputsAlong coe_reductionDegZeroAlong reductionAlong reductionAlong_mk ReductionInputsModL reductionModL IsPlaceReductionAlong.eq_of_agree arithmeticGalois coe_arithmeticGalois_smul galois_smul_pic0_def modularFunctionFieldBar JZero qExpand_one_apply jq modularFunctionFieldFull jqd_mem_full coeffMap coeffMap_coeffMap coeffMap_id coeffMap_congr algebraMap_laurentSeries_eq_single coeffMap_algebraMap laurentBaseChange coeffEmb_mem_laurentBaseChange coeffMap_mem_laurentBaseChange coeffMap_jqModC jqModC_ne_zero_of_nontrivial modularFunctionFieldFullC jqModCd_mem_full jqModC_mem_full jqModC jqModC_rat coeffMap_qExpand coeff_jqModC_neg_one pow_char_eq_coeffMap_frobenius_qExpand frobeniusModL coe_frobeniusModL frobeniusModL_isIntegral frobeniusPlaceModL mem_frobeniusPlaceModL_iff frobeniusDivPushforwardModL frobeniusDivPushforwardModL_single FrobeniusInputsModL coe_frobeniusDegZeroPushforwardModL frobeniusPushforwardModL frobeniusPushforwardModL_mk isCurveOver_modularFunctionFieldBar exists_transcendental_finiteDimensional_modularFunctionFieldBar JZero.divisible frobeniusInputsModL"
namespace W4Frobenius
p2m_open "ModularCurve"

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_reductionModL_smul_of_isFrobeniusAt.ModularCurve HahnSeries IntermediateField WithZero"
open scoped Pointwise

section QAdic

variable (K : Type*) [Field K] (N : ℕ)

def qadicValuation : Valuation (modularFunctionFieldFullC K N) ℤᵐ⁰ :=
  Valued.v.comap (algebraMap (modularFunctionFieldFullC K N) (LaurentSeries K))

theorem qadicValuation_apply (x : modularFunctionFieldFullC K N) :
    qadicValuation K N x = Valued.v (x : LaurentSeries K) := rfl

omit N in
theorem valuation_C_le_one (a : K) : Valued.v (HahnSeries.C a : LaurentSeries K) ≤ 1 := by
  have h := (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero K (D := 0) (f := HahnSeries.C a)).mpr
    (fun n hn => by rw [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne hn.ne])
  simpa using h

omit N in
theorem not_valuation_jqModC_le_one : ¬ Valued.v (jqModC K : LaurentSeries K) ≤ 1 := by
  intro h
  have h' : Valued.v (jqModC K : LaurentSeries K) ≤ exp (-(0:ℤ)) := by simpa using h
  rw [LaurentSeries.valuation_le_iff_coeff_lt_eq_zero] at h'
  have := h' (-1) (by norm_num)
  rw [coeff_jqModC_neg_one] at this
  exact one_ne_zero this

scoped instance : Nontrivial (MonoidWithZeroHom.valueGroup (MonoidWithZeroHom.ofClass (qadicValuation K N))) := by
  have hj : (qadicValuation K N) ⟨jqModC K, jqModC_mem_full K N⟩ ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact fun h => jqModC_ne_zero_of_nontrivial K (congrArg Subtype.val h)
  refine ⟨⟨⟨Units.mk0 _ hj, MonoidWithZeroHom.mem_valueGroup _ ⟨_, rfl⟩⟩, 1, ?_⟩⟩
  intro h
  have h2 := congrArg (fun u : (MonoidWithZeroHom.valueGroup (MonoidWithZeroHom.ofClass (qadicValuation K N))) =>
    ((u : (ℤᵐ⁰)ˣ) : ℤᵐ⁰)) h
  simp only [Units.val_mk0, OneMemClass.coe_one, Units.val_one] at h2
  exact not_valuation_jqModC_le_one K (le_of_eq h2)

def qadicPlace : Place K (modularFunctionFieldFullC K N) where
  toValuationSubring := (qadicValuation K N).valuationSubring
  algebraMap_mem' a := by
    rw [Valuation.mem_valuationSubring_iff, qadicValuation_apply]
    show Valued.v ((algebraMap K (LaurentSeries K)) a) ≤ 1
    rw [algebraMap_laurentSeries_eq_single, ← HahnSeries.C_apply]
    exact valuation_C_le_one K a
  ne_top' h := by
    have : (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) ∈
        (qadicValuation K N).valuationSubring := h ▸ ValuationSubring.mem_top _
    rw [Valuation.mem_valuationSubring_iff] at this
    exact not_valuation_jqModC_le_one K this
  isPrincipalIdealRing' := Valuation.valuationSubring_isPrincipalIdealRing _

theorem jqModC_not_mem_qadicPlace :
    (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) ∉ (qadicPlace K N).toValuationSubring := by
  intro h
  change _ ∈ (qadicValuation K N).valuationSubring at h
  rw [Valuation.mem_valuationSubring_iff] at h
  exact not_valuation_jqModC_le_one K h

theorem ord_ne_zero_of_not_mem {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F}
    (hf : f ∉ v.toValuationSubring) : v.ord f ≠ 0 := by
  intro h0
  have hf0 : f ≠ 0 := fun h => hf (h ▸ v.toValuationSubring.zero_mem)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf0 hϖ
  rw [h0, zpow_zero, mul_one] at hu
  exact hf (hu ▸ (u : v.toValuationSubring).2)

theorem ord_qadicPlace_jqModC_ne_zero_of_nontrivial :
    (qadicPlace K N).ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) ≠ 0 :=
  ord_ne_zero_of_not_mem _ (jqModC_not_mem_qadicPlace K N)

end QAdic

section Coeff

variable (K : Type*) [Field K] (N : ℕ)

theorem coeffMap_mem_fullC (φ : K →+* K) {x : LaurentSeries K} (hx : x ∈ modularFunctionFieldFullC K N) :
    coeffMap φ x ∈ modularFunctionFieldFullC K N := by
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy =>
    obtain ⟨d, hne, hdvd, rfl⟩ := hy
    haveI := hne
    rw [coeffMap_qExpand, coeffMap_jqModC]
    exact jqModCd_mem_full K N hdvd
  | algebraMap c =>
    rw [coeffMap_algebraMap]; exact (modularFunctionFieldFullC K N).algebraMap_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | inv y _ hy => rw [map_inv₀]; exact inv_mem hy
  | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz

def coeffRingAut (e : K ≃+* K) : (modularFunctionFieldFullC K N) ≃+* (modularFunctionFieldFullC K N) where
  toFun x := ⟨coeffMap (e : K →+* K) x, coeffMap_mem_fullC K N _ x.2⟩
  invFun x := ⟨coeffMap (e.symm : K →+* K) x, coeffMap_mem_fullC K N _ x.2⟩
  left_inv x := Subtype.ext <| by
    show coeffMap (e.symm : K →+* K) (coeffMap (e : K →+* K) (x : LaurentSeries K)) = x
    rw [coeffMap_coeffMap, coeffMap_congr (g := RingHom.id K) (RingHom.ext fun a => e.symm_apply_apply a),
      coeffMap_id]
  right_inv x := Subtype.ext <| by
    show coeffMap (e : K →+* K) (coeffMap (e.symm : K →+* K) (x : LaurentSeries K)) = x
    rw [coeffMap_coeffMap, coeffMap_congr (g := RingHom.id K) (RingHom.ext fun a => e.apply_symm_apply a),
      coeffMap_id]
  map_mul' x y := Subtype.ext (map_mul _ _ _)
  map_add' x y := Subtype.ext (map_add _ _ _)

def coeffSemilinearAut (e : K ≃+* K) : SemilinearAut K (modularFunctionFieldFullC K N) :=
  ⟨(coeffRingAut K N e, e), fun a => Subtype.ext <| by
    show coeffMap (e : K →+* K) (algebraMap K (LaurentSeries K) a) = algebraMap K (LaurentSeries K) (e a)
    exact coeffMap_algebraMap _ a⟩

@[scoped simp] theorem coe_coeffSemilinearAut_smul (e : K ≃+* K) (x : modularFunctionFieldFullC K N) :
    ((coeffSemilinearAut K N e • x : modularFunctionFieldFullC K N) : LaurentSeries K) =
      coeffMap (e : K →+* K) x :=
  rfl

theorem coe_toRingAut_coeffSemilinearAut_symm (e : K ≃+* K) (x : modularFunctionFieldFullC K N) :
    (((SemilinearAut.toRingAut (coeffSemilinearAut K N e)).symm x : modularFunctionFieldFullC K N) :
      LaurentSeries K) = coeffMap (e.symm : K →+* K) x :=
  rfl

end Coeff

section Frobenius

variable (K : Type*) [Field K] (N : ℕ) (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ] [PerfectRing K ℓ]

def arithFrobModL : SemilinearAut K (modularFunctionFieldFullC K N) :=
  coeffSemilinearAut K N (frobeniusEquiv K ℓ)

theorem frobeniusModL_eq_inv_smul_pow (x : modularFunctionFieldFullC K N) :
    frobeniusModL K N ℓ x = ((arithFrobModL K N ℓ)⁻¹ • x) ^ ℓ := by
  apply Subtype.ext
  rw [coe_frobeniusModL, SubmonoidClass.coe_pow, arithFrobModL, SemilinearAut.inv_smul_def,
    coe_toRingAut_coeffSemilinearAut_symm, pow_char_eq_coeffMap_frobenius_qExpand ℓ,
    ← coeffMap_qExpand, coeffMap_coeffMap,
    coeffMap_congr (g := RingHom.id K) (RingHom.ext fun a => ?_), coeffMap_id]
  show frobenius K ℓ ((frobeniusEquiv K ℓ).symm a) = a
  exact frobeniusEquiv_symm_apply_frobenius K ℓ a |>.symm ▸ (frobeniusEquiv K ℓ).apply_symm_apply a

theorem frobeniusPlaceModL_eq_smul (Q : Place K (modularFunctionFieldFullC K N)) :
    frobeniusPlaceModL K N ℓ Q = arithFrobModL K N ℓ • Q := by
  apply Place.ext
  ext x
  rw [mem_frobeniusPlaceModL_iff, SemilinearAut.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, frobeniusModL_eq_inv_smul_pow,
    ← ValuationSubring.valuation_le_one_iff, ← ValuationSubring.valuation_le_one_iff, Valuation.map_pow,
    pow_le_one_iff (Fact.out : ℓ.Prime).ne_zero]

theorem deg_restrictAlong_mul_inertiaDegAlong {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') :
    (w.restrictAlong φ hφ).deg * w.inertiaDegAlong φ hφ = w.deg := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact w.deg_restrict_mul_inertiaDeg (F := F)

theorem frobeniusDivPushforwardModL_single_of_deg_eq_one (Q : Place K (modularFunctionFieldFullC K N))
    (hQ : Q.deg = 1) (n : ℤ) :
    frobeniusDivPushforwardModL K N ℓ (Finsupp.single Q n) = Finsupp.single (arithFrobModL K N ℓ • Q) n := by
  rw [frobeniusDivPushforwardModL_single, ← frobeniusPlaceModL_eq_smul]
  have h := deg_restrictAlong_mul_inertiaDegAlong (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ) Q
  rw [hQ] at h
  have h1 : Q.inertiaDegAlong (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ) = 1 :=
    Nat.eq_one_of_mul_eq_one_left h
  rw [h1, Nat.cast_one, mul_one]

theorem frobeniusDivPushforwardModL_eq_mapDomain_of_deg
    (E : Divisor K (modularFunctionFieldFullC K N)) (hE : ∀ Q ∈ E.support, Q.deg = 1) :
    frobeniusDivPushforwardModL K N ℓ E = Finsupp.mapDomain (fun Q => arithFrobModL K N ℓ • Q) E := by
  classical
  induction E using Finsupp.induction with
  | zero => simp
  | single_add Q n E hQE hn ih =>
    have hQ : Q.deg = 1 := hE Q (by
      rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_same,
        Finsupp.notMem_support_iff.mp hQE, add_zero]; exact hn)
    have hE' : ∀ Q' ∈ E.support, Q'.deg = 1 := fun Q' hQ' => hE Q' (by
      rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply]
      have hne : Q ≠ Q' := fun h => hQE (h ▸ hQ')
      rw [if_neg hne, zero_add]; exact Finsupp.mem_support_iff.mp hQ')
    rw [map_add, Finsupp.mapDomain_add, ih hE', frobeniusDivPushforwardModL_single_of_deg_eq_one K N ℓ Q hQ,
      Finsupp.mapDomain_single]

end Frobenius

section Generic

variable {L : Type*} [Field L] [Algebra ℚ L] {A : ValuationSubring L}
variable {k : Type*} [Field k] {π : A →+* k} {N : ℕ}
variable (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] [PerfectRing k ℓ]

omit [Fact ℓ.Prime] [CharP k ℓ] [PerfectRing k ℓ] in

theorem coeffMap_subtype_coeffMap (σ : L ≃ₐ[ℚ] L) (σA : A →+* A) (hσA : ∀ a : A, (σA a : L) = σ a)
    (y : LaurentSeries A) :
    coeffMap A.subtype (coeffMap σA y) = coeffMap (σ : L →+* L) (coeffMap A.subtype y) := by
  rw [coeffMap_coeffMap, coeffMap_coeffMap]
  exact coeffMap_congr (RingHom.ext fun a => hσA a) y

theorem mapDomain_frob_agree
    {r : Place L (laurentBaseChange L (modularFunctionFieldFull N)) → Place k (modularFunctionFieldFullC k N)}
    (hr : IsPlaceReductionAlong A π N r)
    (σ : L ≃ₐ[ℚ] L) (σA : A →+* A) (hσA : ∀ a : A, (σA a : L) = σ a)
    (hπ : ∀ a, π (σA a) = frobenius k ℓ (π a))
    {D : Divisor L (laurentBaseChange L (modularFunctionFieldFull N))}
    (hD : D ∈ integralPrincipalDivisors A π N) :
    Finsupp.mapDomain ((fun Q => arithFrobModL k N ℓ • Q) ∘ r) D =
      Finsupp.mapDomain (r ∘ fun P => arithmeticGalois (modularFunctionFieldFull N) σ • P) D := by
  obtain ⟨y, hy, hyk, hne, hDy⟩ := hD
  set g := arithmeticGalois (modularFunctionFieldFull N) σ with hg
  set φ := arithFrobModL k N ℓ with hφ
  set y' : LaurentSeries A := coeffMap σA y with hy'def
  have himg : coeffMap A.subtype y' = coeffMap (σ : L →+* L) (coeffMap A.subtype y) :=
    coeffMap_subtype_coeffMap σ σA hσA y
  have hy' : coeffMap A.subtype y' ∈ laurentBaseChange L (modularFunctionFieldFull N) := by
    rw [himg]; exact coeffMap_mem_laurentBaseChange σ hy
  have hred : coeffMap π y' = coeffMap (frobenius k ℓ) (coeffMap π y) := by
    rw [hy'def, coeffMap_coeffMap, coeffMap_coeffMap]
    exact coeffMap_congr (RingHom.ext fun a => hπ a) y

  have hredφ : coeffMap π y' =
      ((φ • (⟨coeffMap π y, hyk⟩ : modularFunctionFieldFullC k N) : modularFunctionFieldFullC k N) :
        LaurentSeries k) := by
    rw [hred, hφ, arithFrobModL, coe_coeffSemilinearAut_smul]
    exact coeffMap_congr (RingHom.ext fun a => rfl) _
  have hyk' : coeffMap π y' ∈ modularFunctionFieldFullC k N :=
    hredφ ▸ (φ • (⟨coeffMap π y, hyk⟩ : modularFunctionFieldFullC k N)).2
  have hne' : coeffMap π y' ≠ 0 := by
    rw [hred]; intro h0; apply hne
    have := congrArg (coeffMap ((frobeniusEquiv k ℓ).symm : k →+* k)) h0
    rw [map_zero, coeffMap_coeffMap, coeffMap_congr (g := RingHom.id k) (RingHom.ext fun a => ?_),
      coeffMap_id] at this
    · exact this
    · exact frobeniusEquiv_symm_apply_frobenius k ℓ a
  have hyeq : (⟨coeffMap π y', hyk'⟩ : modularFunctionFieldFullC k N) = φ • ⟨coeffMap π y, hyk⟩ :=
    Subtype.ext hredφ

  have hgx : g • (⟨coeffMap A.subtype y, hy⟩ : laurentBaseChange L (modularFunctionFieldFull N)) =
      ⟨coeffMap A.subtype y', hy'⟩ :=
    Subtype.ext (by rw [coe_arithmeticGalois_smul]; exact himg.symm)

  have hD' : ∀ P, (g • D) P =
      P.ord (⟨coeffMap A.subtype y', hy'⟩ : laurentBaseChange L (modularFunctionFieldFull N)) := by
    intro P
    rw [SemilinearAut.divisor_smul_apply, hDy, ← hgx, ← SemilinearAut.ord_smul g (g⁻¹ • P), smul_inv_smul]

  rw [Finsupp.mapDomain_comp, Finsupp.mapDomain_comp, ← SemilinearAut.divisor_smul_def,
    ← SemilinearAut.divisor_smul_def]
  ext Q
  rw [SemilinearAut.divisor_smul_apply, hr.2 y hy hyk hne D hDy (φ⁻¹ • Q),
    hr.2 y' hy' hyk' hne' (g • D) hD' Q, hyeq, ← SemilinearAut.ord_smul φ (φ⁻¹ • Q), smul_inv_smul]

theorem degree_eq_zero_of_mem_principal {K F : Type*} [Field K] [Field F] [Algebra K F]
    [HasPrincipalDivisors K F] {D : Divisor K F}
    (hD : D ∈ Divisor.principal (K := K) (F := F)) : Divisor.degree D = 0 := by
  obtain ⟨f, hf, hDf⟩ := hD
  obtain ⟨D', hD', hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
  have : D = D' := Finsupp.ext fun v => by rw [hDf v, hD' v]
  rw [this, hdeg]

omit [Fact ℓ.Prime] [CharP k ℓ] [PerfectRing k ℓ] in

theorem jqModC_mem_laurentBaseChange [NeZero N] :
    coeffMap A.subtype (jqModC A) ∈ laurentBaseChange L (modularFunctionFieldFull N) := by
  rw [coeffMap_jqModC, ← coeffMap_jqModC (algebraMap ℚ L), jqModC_rat]
  have h : jq ∈ modularFunctionFieldFull N := by
    simpa [qExpand_one_apply] using jqd_mem_full (N := N) (one_dvd N)
  exact coeffEmb_mem_laurentBaseChange L h

theorem exists_principal_mapDomain_ne_zero [NeZero N]
    [hPL : HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull N))]
    {r : Place L (laurentBaseChange L (modularFunctionFieldFull N)) → Place k (modularFunctionFieldFullC k N)}
    (hr : IsPlaceReductionAlong A π N r) :
    ∃ D ∈ Divisor.principal (K := L) (F := laurentBaseChange L (modularFunctionFieldFull N)),
      Finsupp.mapDomain ((fun Q => arithFrobModL k N ℓ • Q) ∘ r) D ≠ 0 := by
  set xj : laurentBaseChange L (modularFunctionFieldFull N) := ⟨coeffMap A.subtype (jqModC A), jqModC_mem_laurentBaseChange⟩
  have hxj0 : xj ≠ 0 := fun h => by
    have := congrArg Subtype.val h
    rw [show ((0 : laurentBaseChange L (modularFunctionFieldFull N)) : LaurentSeries L) = 0 from rfl] at this
    rw [show (xj : LaurentSeries L) = coeffMap A.subtype (jqModC A) from rfl, coeffMap_jqModC] at this
    exact jqModC_ne_zero_of_nontrivial L this
  obtain ⟨D, hD, -⟩ := hPL.exists_divisor xj hxj0
  refine ⟨D, ⟨xj, hxj0, hD⟩, ?_⟩
  have hyk : coeffMap π (jqModC A) ∈ modularFunctionFieldFullC k N := by
    rw [coeffMap_jqModC]; exact jqModC_mem_full k N
  have hne : coeffMap π (jqModC A) ≠ 0 := by rw [coeffMap_jqModC]; exact jqModC_ne_zero_of_nontrivial k
  rw [Finsupp.mapDomain_comp, ← SemilinearAut.divisor_smul_def]
  intro h0
  rw [smul_eq_zero_iff_eq] at h0
  have h1 := congrArg (fun E => E (qadicPlace k N)) h0
  simp only [Finsupp.zero_apply] at h1
  rw [hr.2 (jqModC A) jqModC_mem_laurentBaseChange hyk hne D hD (qadicPlace k N)] at h1
  apply ord_qadicPlace_jqModC_ne_zero_of_nontrivial k N
  convert h1 using 2
  exact Subtype.ext (coeffMap_jqModC π).symm

theorem reductionAlong_smul_eq_frobeniusPushforward [NeZero N]
    [HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull N))]
    [HasPrincipalDivisors k (modularFunctionFieldFullC k N)]
    (hfin : FiniteAlong k (frobeniusModL k N ℓ))
    (hFI : FundamentalIdentityAlong k (frobeniusModL k N ℓ) (frobeniusModL_isIntegral k N ℓ))
    (hN : NormFormulaAlong k (frobeniusModL k N ℓ) hfin)
    (h : ReductionInputsAlong A π N)
    (hdeg : ∀ P : Place L (laurentBaseChange L (modularFunctionFieldFull N)), P.deg = 1)
    (hdiv : ∀ n : ℕ, n ≠ 0 → ∀ x : Pic0 L (laurentBaseChange L (modularFunctionFieldFull N)),
      ∃ y : Pic0 L (laurentBaseChange L (modularFunctionFieldFull N)), n • y = x)
    (σ : L ≃ₐ[ℚ] L) (σA : A →+* A) (hσA : ∀ a : A, (σA a : L) = σ a)
    (hπ : ∀ a, π (σA a) = frobenius k ℓ (π a))
    (x : Pic0 L (laurentBaseChange L (modularFunctionFieldFull N))) :
    reductionAlong A π N (σ • x) = frobeniusPushforwardModL k N ℓ (reductionAlong A π N x) := by
  set r := h.choose with hrdef
  have hr : IsPlaceReductionAlong A π N r := h.choose_spec.1
  have hgen : PrincipalGeneratedByIntegral A π N := h.choose_spec.2
  set g := arithmeticGalois (modularFunctionFieldFull N) σ with hg
  set φ := arithFrobModL k N ℓ with hφ

  have key : ((fun Q => φ • Q) ∘ r) = (r ∘ fun P => g • P) :=
    IsPlaceReductionAlong.eq_of_agree hgen (fun D hD => mapDomain_frob_agree ℓ hr σ σA hσA hπ hD) hdeg
      (fun D hD => degree_eq_zero_of_mem_principal hD) hdiv (exists_principal_mapDomain_ne_zero ℓ hr)
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [galois_smul_pic0_def, SemilinearAut.pic0_smul_mk, reductionAlong_mk h, reductionAlong_mk h,
    frobeniusPushforwardModL_mk hfin hFI hN]
  congr 1
  apply Subtype.ext
  rw [coe_reductionDegZeroAlong, coe_frobeniusDegZeroPushforwardModL, coe_reductionDegZeroAlong,
    SemilinearAut.coe_degZeroSMulHom, SemilinearAut.divisor_smul_def, ← Finsupp.mapDomain_comp, ← hg,
    show h.choose = r from rfl, ← key, Finsupp.mapDomain_comp]
  refine (frobeniusDivPushforwardModL_eq_mapDomain_of_deg k N ℓ _ fun Q hQ => ?_).symm
  classical
  obtain ⟨P, -, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hQ)
  rw [hr.1 P, hdeg P]

end Generic

section Modular

p2m_open "ValuationSubring~isAlgClosed_residueField"

theorem isAlgClosed_residueField {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L) :
    IsAlgClosed (IsLocalRing.ResidueField A) := by
  refine IsAlgClosed.of_exists_root _ fun p hp hirr => ?_
  have hsurj : Function.Surjective (IsLocalRing.residue A) := IsLocalRing.residue_surjective
  have hlifts : p ∈ Polynomial.lifts (IsLocalRing.residue A) := by
    obtain ⟨q, hq⟩ := Polynomial.map_surjective (IsLocalRing.residue A) hsurj p
    exact ⟨q, hq⟩
  obtain ⟨q, hqp, hdeg, hqmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hp
  have hdegL : (q.map (algebraMap A L)).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective (IsFractionRing.injective A L),
      Polynomial.degree_eq_natDegree hqmonic.ne_zero, hdeg]
    exact_mod_cast (Polynomial.natDegree_pos_iff_degree_pos.mpr
      (Polynomial.degree_pos_of_irreducible hirr)).ne'
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root (q.map (algebraMap A L)) hdegL
  have hyint : IsIntegral A y :=
    ⟨q, hqmonic, by rwa [Polynomial.IsRoot.def, Polynomial.eval_map] at hy⟩
  obtain ⟨a, rfl⟩ : ∃ a : A, algebraMap A L a = y := IsIntegrallyClosed.isIntegral_iff.mp hyint
  refine ⟨IsLocalRing.residue A a, ?_⟩
  have hqa : q.eval a = 0 := by
    have h := hy
    rw [Polynomial.IsRoot.def, Polynomial.eval_map, Polynomial.eval₂_hom] at h
    exact (IsFractionRing.injective A L) (h.trans (map_zero _).symm)
  rw [← hqp, Polynomial.eval_map, Polynomial.eval₂_hom, hqa, map_zero]

theorem main (N : ℕ) [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) [CharP (IsLocalRing.ResidueField A) ℓ]
    (h : ModularCurve.ReductionInputsModL A N)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A.IsFrobeniusAt σ ℓ)
    (z : ModularCurve.JZero N) :
    ModularCurve.reductionModL A N (σ • z) =
      ModularCurve.frobeniusPushforwardModL (IsLocalRing.ResidueField A) N ℓ
        (ModularCurve.reductionModL A N z) := by

  haveI : IsAlgClosed (IsLocalRing.ResidueField A) := isAlgClosed_residueField A
  haveI : ExpChar (IsLocalRing.ResidueField A) ℓ := ExpChar.prime (Fact.out : ℓ.Prime)
  haveI : PerfectRing (IsLocalRing.ResidueField A) ℓ := PerfectField.toPerfectRing ℓ

  obtain ⟨hP, hfin, hFI, hN⟩ :=
    (ModularCurve.frobeniusInputsModL (IsLocalRing.ResidueField A) N :
      FrobeniusInputsModL (IsLocalRing.ResidueField A) N ℓ)
  haveI := hP

  haveI : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := isCurveOver_modularFunctionFieldBar N
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := IsCurveOver.hasPrincipalDivisors
  have hdeg : ∀ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), P.deg = 1 :=
    IsCurveOver.deg_eq_one_of_isAlgClosed
  have hdiv : ∀ n : ℕ, n ≠ 0 → ∀ x : Pic0 (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      ∃ y : Pic0 (AlgebraicClosure ℚ) (modularFunctionFieldBar N), n • y = x :=
    fun n hn x => ModularCurve.JZero.divisible N n hn x

  obtain ⟨hσmem, hσfrob⟩ := hσ
  let d : A.decompositionSubgroup ℚ := ⟨σ, hσmem⟩
  let σA : A →+* A := MulSemiringAction.toRingHom (A.decompositionSubgroup ℚ) A d
  have hσA : ∀ a : A, (σA a : AlgebraicClosure ℚ) = σ a := fun a => rfl
  have hπ : ∀ a : A, IsLocalRing.residue A (σA a) = frobenius _ ℓ (IsLocalRing.residue A a) := by
    intro a
    show IsLocalRing.residue A (d • a) = _
    rw [IsLocalRing.ResidueField.residue_smul, frobenius_def]
    exact hσfrob _
  exact reductionAlong_smul_eq_frobeniusPushforward ℓ hfin hFI hN h hdeg hdiv σ σA hσA hπ z

end Modular

end ModularCurve.W4Frobenius
p2m_reactivate "P2MW.S_ModularCurve_reductionModL_smul_of_isFrobeniusAt.ModularCurve P2MW.S_ModularCurve_reductionModL_smul_of_isFrobeniusAt.ModularCurve.W4Frobenius"
p2m_reactivate "P2MW.S_ModularCurve_reductionModL_smul_of_isFrobeniusAt.ModularCurve"

theorem solution (N : ℕ) [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) [CharP (IsLocalRing.ResidueField A) ℓ]
    (h : ModularCurve.ReductionInputsModL A N)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A.IsFrobeniusAt σ ℓ)
    (z : ModularCurve.JZero N) :
    ModularCurve.reductionModL A N (σ • z) =
      ModularCurve.frobeniusPushforwardModL (IsLocalRing.ResidueField A) N ℓ
        (ModularCurve.reductionModL A N z) :=
  ModularCurve.W4Frobenius.main N A h σ hσ z

end
p2m_reactivate "P2MW.S_ModularCurve_reductionModL_smul_of_isFrobeniusAt.ModularCurve P2MW.S_ModularCurve_reductionModL_smul_of_isFrobeniusAt.ModularCurve.W4Frobenius"

end S_ModularCurve_reductionModL_smul_of_isFrobeniusAt
end P2MW
export P2MW.S_ModularCurve_reductionModL_smul_of_isFrobeniusAt (solution)
