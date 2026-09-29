-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.eq_of_isModel_of_orderLawFixed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/fcb6ab6c-a6f6-5300-bf3f-35149fb6b4ee

import Definitions.Def_ModularCurve_ProlongationTuple
import Theorems.Thm_ModularCurve_JZero_divisible
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_PlaceSpecialization_spPic0_eq_of_sp_eq
import Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteAlong_heckeAlphaBar_of_prime
import Theorems.Thm_AlgebraicCurve_Place_restrictAlong_surjective
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_divisorLawSnd_oneSided
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_oneSided
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawZero_oneSided
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isCuspidal_of_not_isAffineGeomPlace_reduceFst
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isInftySide_or_isZeroSide_of_isCuspidal
import Theorems.Thm_ModularCurve_modularFunctionFieldBar_eq_modularFunctionFieldC
import Theorems.Thm_ModularCurve_geomAut_atkinLehner_comp_legs
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_eq_of_isModel_of_orderLawFixed
p2m_attr_erase "instance" "CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent"
p2m_attr_erase "instance" "ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper ModularCurve.instIsElliptic_tateBase ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ValuationSubring.instIsAlgClosedResidueField"
p2m_attr_erase "simp" "ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe"
p2m_attr_erase "simp" "AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero"
p2m_attr_erase "simp" "Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero"
p2m_attr_erase "simp" "HeckeEis.heckeConjMat_apply_zero_zero AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero"
open AlgebraicCurve

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

namespace ReductionRigidity

namespace UniqRed

section Coefficients

open ModularCurve

private def Bounded (g : LaurentSeries (AlgebraicClosure ℚ)) : Prop :=
  ∃ M : Submodule ℤ (AlgebraicClosure ℚ), M.FG ∧ ∀ t : ℤ, g.coeff t ∈ M

private theorem bounded_algebraMap (c : AlgebraicClosure ℚ) :
    Bounded (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c) := by
  refine ⟨Submodule.span ℤ {c}, Submodule.fg_span_singleton c, fun t => ?_⟩
  rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single]
  split_ifs
  · exact Submodule.subset_span (Set.mem_singleton c)
  · exact Submodule.zero_mem _

private theorem intCast_mem_span_one (n : ℤ) :
    (n : AlgebraicClosure ℚ) ∈ Submodule.span ℤ ({1} : Set (AlgebraicClosure ℚ)) :=
  Submodule.mem_span_singleton.mpr ⟨n, by simp⟩

private theorem bounded_jqModC : Bounded (jqModC (AlgebraicClosure ℚ)) := by
  refine ⟨Submodule.span ℤ {1}, Submodule.fg_span_singleton 1, fun t => ?_⟩
  rw [jqModC_eq_map_intCast]
  exact intCast_mem_span_one _

private theorem bounded_jqNModC (N : ℕ) [NeZero N] : Bounded (jqNModC (AlgebraicClosure ℚ) N) := by
  refine ⟨Submodule.span ℤ {1}, Submodule.fg_span_singleton 1, fun t => ?_⟩
  unfold jqNModC
  by_cases ht : (N : ℤ) ∣ t
  · obtain ⟨m, rfl⟩ := ht
    rw [qExpand_coeff_mul, jqModC_eq_map_intCast]
    exact intCast_mem_span_one _
  · rw [qExpand_coeff_of_not_dvd _ _ ht]
    exact Submodule.zero_mem _

private theorem bounded_zero : Bounded (0 : LaurentSeries (AlgebraicClosure ℚ)) :=
  ⟨⊥, Submodule.fg_bot, fun t => by simp⟩

private theorem bounded_one : Bounded (1 : LaurentSeries (AlgebraicClosure ℚ)) := by
  refine ⟨Submodule.span ℤ {1}, Submodule.fg_span_singleton 1, fun t => ?_⟩
  rw [HahnSeries.coeff_one]
  split_ifs
  · exact Submodule.subset_span (Set.mem_singleton _)
  · exact Submodule.zero_mem _

private theorem bounded_add {x y : LaurentSeries (AlgebraicClosure ℚ)} (hx : Bounded x)
    (hy : Bounded y) : Bounded (x + y) := by
  obtain ⟨M, hM, hxM⟩ := hx
  obtain ⟨M', hM', hyM'⟩ := hy
  refine ⟨M ⊔ M', hM.sup hM', fun t => ?_⟩
  rw [HahnSeries.coeff_add]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (hxM t)) (Submodule.mem_sup_right (hyM' t))

private theorem bounded_neg {x : LaurentSeries (AlgebraicClosure ℚ)} (hx : Bounded x) :
    Bounded (-x) := by
  obtain ⟨M, hM, hxM⟩ := hx
  exact ⟨M, hM, fun t => by rw [HahnSeries.coeff_neg]; exact Submodule.neg_mem _ (hxM t)⟩

private theorem bounded_mul {x y : LaurentSeries (AlgebraicClosure ℚ)} (hx : Bounded x)
    (hy : Bounded y) : Bounded (x * y) := by
  obtain ⟨M, hM, hxM⟩ := hx
  obtain ⟨M', hM', hyM'⟩ := hy
  refine ⟨M * M', hM.mul hM', fun t => ?_⟩
  rw [HahnSeries.coeff_mul]
  exact Submodule.sum_mem _ fun ij _ => Submodule.mul_mem_mul (hxM ij.1) (hyM' ij.2)

private theorem qExpand_algebraMap (n : ℕ) [NeZero n] (c : AlgebraicClosure ℚ) :
    qExpand (AlgebraicClosure ℚ) n
        (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c)
      = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c := by
  rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero]

private theorem bounded_of_mem_closure (N : ℕ) [NeZero N] {g : LaurentSeries (AlgebraicClosure ℚ)}
    (hg : g ∈ Subring.closure
      (Set.range (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))) ∪
        {jqModC (AlgebraicClosure ℚ), jqNModC (AlgebraicClosure ℚ) N})) : Bounded g := by
  induction hg using Subring.closure_induction with
  | mem x hx =>
    simp only [Set.mem_union, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with ⟨c, rfl⟩ | rfl | rfl
    · exact bounded_algebraMap c
    · exact bounded_jqModC
    · exact bounded_jqNModC N
  | zero => exact bounded_zero
  | one => exact bounded_one
  | add x y _ _ hx hy => exact bounded_add hx hy
  | neg x _ hx => exact bounded_neg hx
  | mul x y _ _ hx hy => exact bounded_mul hx hy

variable {A : ValuationSubring (AlgebraicClosure ℚ)}

private theorem exists_coeff_valuation_max (A : ValuationSubring (AlgebraicClosure ℚ))
    {g : LaurentSeries (AlgebraicClosure ℚ)} (hg : g ≠ 0) (hb : Bounded g) :
    ∃ t₀ : ℤ, g.coeff t₀ ≠ 0 ∧ ∀ t : ℤ, A.valuation (g.coeff t) ≤ A.valuation (g.coeff t₀) := by
  obtain ⟨M, hM, hgM⟩ := hb
  haveI : IsNoetherian ℤ M := isNoetherian_of_fg_of_noetherian M hM
  let φ : A.ValueGroup → Submodule ℤ M := fun γ =>
    { carrier := {m | A.valuation (m : AlgebraicClosure ℚ) ≤ γ}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb => le_trans (A.valuation.map_add _ _) (max_le ha hb)
      smul_mem' := fun n {m} hm => by
        show A.valuation ((n • m : M) : AlgebraicClosure ℚ) ≤ γ
        rw [Submodule.coe_smul, zsmul_eq_mul, A.valuation.map_mul]
        have hn : A.valuation (n : AlgebraicClosure ℚ) ≤ 1 :=
          (A.valuation_le_one_iff _).mpr (intCast_mem A n)
        exact le_trans (mul_le_of_le_one_left' hn) hm }
  have hφ : ∀ (γ : A.ValueGroup) (m : M), m ∈ φ γ ↔ A.valuation (m : AlgebraicClosure ℚ) ≤ γ :=
    fun _ _ => Iff.rfl
  have hwf : WellFounded (fun γ γ' : A.ValueGroup => φ γ > φ γ') := InvImage.wf φ wellFounded_gt
  let V : Set A.ValueGroup := {γ | ∃ t : ℤ, g.coeff t ≠ 0 ∧ A.valuation (g.coeff t) = γ}
  have hV : V.Nonempty := by
    obtain ⟨t, ht⟩ : ∃ t : ℤ, g.coeff t ≠ 0 := by
      by_contra hcon
      exact hg (HahnSeries.coeff_fun_eq_zero_iff.mp
        (funext fun t => by_contra fun h => hcon ⟨t, h⟩))
    exact ⟨_, t, ht, rfl⟩
  obtain ⟨γ₀, ⟨t₀, ht₀, hγ₀⟩, hmin⟩ := hwf.has_min V hV
  refine ⟨t₀, ht₀, fun t => ?_⟩
  by_cases h0 : g.coeff t = 0
  · rw [h0, A.valuation.map_zero]
    exact zero_le'
  · rw [hγ₀]
    rcases le_or_gt (A.valuation (g.coeff t)) γ₀ with hle | hlt
    · exact hle
    exfalso
    apply hmin (A.valuation (g.coeff t)) ⟨t, h0, rfl⟩
    show φ γ₀ < φ (A.valuation (g.coeff t))
    refine lt_of_le_of_ne (fun m hm => (hφ _ m).2 (le_trans ((hφ _ m).1 hm) hlt.le)) fun heq => ?_
    have hmem : (⟨g.coeff t, hgM t⟩ : M) ∈ φ (A.valuation (g.coeff t)) := (hφ _ _).2 (le_refl _)
    rw [← heq] at hmem
    exact absurd ((hφ _ _).1 hmem) (not_le.mpr hlt)

private theorem exists_smul_eq_coeffMap (A : ValuationSubring (AlgebraicClosure ℚ))
    {g : LaurentSeries (AlgebraicClosure ℚ)} (hg : g ≠ 0) (hb : Bounded g) :
    ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧ ∃ y : LaurentSeries A,
      coeffMap A.subtype y
          = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c * g ∧
        coeffMap (IsLocalRing.residue A) y ≠ 0 := by
  obtain ⟨t₀, ht₀, hmax⟩ := exists_coeff_valuation_max A hg hb
  set c : AlgebraicClosure ℚ := (g.coeff t₀)⁻¹ with hc
  have hc0 : c ≠ 0 := inv_ne_zero ht₀
  have hv0 : A.valuation (g.coeff t₀) ≠ 0 := (Valuation.ne_zero_iff _).mpr ht₀
  have hint : ∀ t : ℤ, c * g.coeff t ∈ A := fun t => by
    apply A.mem_of_valuation_le_one
    rw [A.valuation.map_mul, hc, map_inv₀]
    calc (A.valuation (g.coeff t₀))⁻¹ * A.valuation (g.coeff t)
        ≤ (A.valuation (g.coeff t₀))⁻¹ * A.valuation (g.coeff t₀) := mul_le_mul' le_rfl (hmax t)
      _ = 1 := inv_mul_cancel₀ hv0
  let yc : ℤ → A := fun t => ⟨c * g.coeff t, hint t⟩
  let y : LaurentSeries A :=
    { coeff := yc
      isPWO_support' := g.isPWO_support.mono fun t ht hgt =>
        ht (Subtype.ext (by simp [yc, hgt])) }
  refine ⟨c, hc0, y, ?_, ?_⟩
  · ext t
    rw [coeffMap_coeff, algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul]
    rfl
  · intro h0
    have h1 : (coeffMap (IsLocalRing.residue A) y).coeff t₀ = 0 := by rw [h0]; simp
    rw [coeffMap_coeff] at h1
    have hy : y.coeff t₀ = 1 := Subtype.ext (by simp [y, yc, hc, inv_mul_cancel₀ ht₀])
    rw [hy, map_one] at h1
    exact one_ne_zero h1

end Coefficients

section CommonUnits

p2m_open "AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization~IsInftySide~jFun~IsCuspidal~IsZeroSide"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

private def IsCommonUnit (R : ProlongationTuple P) (f : modularFunctionFieldBar (N * q)) : Prop :=
  ∃ (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 ∧ R.R₂.residue ⟨f, h₂⟩ ≠ 0

private theorem atkinLehnerBar_heckeAlphaBar (hqN : ¬ q ∣ N) (G : modularFunctionFieldBar N) :
    ProlongationTuple.atkinLehnerBar N q (heckeAlphaBar (AlgebraicClosure ℚ) N q G)
      = heckeBetaBar (AlgebraicClosure ℚ) N q G := by
  have hex := exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q (Fact.out) hqN
  have hσ := isAtkinLehnerAutFull_atkinLehnerInvolutionFull (N := N) (ℓ := q) hex
  have hleg := (geomAut_atkinLehner_comp_legs (AlgebraicClosure ℚ) N q _ hσ).1
  have := DFunLike.congr_fun hleg G
  simpa [ProlongationTuple.atkinLehnerBar] using this

set_option maxHeartbeats 3200000 in

private theorem exists_smul_isCommonUnit_of_bounded (hqN : ¬ q ∣ N) (R : ProlongationTuple P)
    (G : modularFunctionFieldBar N) (hG : G ≠ 0)
    (hb : Bounded (G : LaurentSeries (AlgebraicClosure ℚ))) :
    ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧
      IsCommonUnit R (c • heckeAlphaBar (AlgebraicClosure ℚ) N q G) := by
  have hg : (G : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := fun h => hG (Subtype.ext h)
  obtain ⟨c, hc0, y, hy, hres⟩ := exists_smul_eq_coeffMap A hg hb
  refine ⟨c, hc0, ?_⟩

  set F₁ : modularFunctionFieldBar (N * q) := c • heckeAlphaBar (AlgebraicClosure ℚ) N q G with hF₁
  set F₂ : modularFunctionFieldBar (N * q) := c • heckeBetaBar (AlgebraicClosure ℚ) N q G with hF₂
  have hF₁s : (F₁ : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype y := by
    rw [hy, hF₁, IntermediateField.coe_smul, coe_heckeAlphaBar, Algebra.smul_def]
  have hF₂s : (F₂ : LaurentSeries (AlgebraicClosure ℚ))
      = coeffMap A.subtype (qExpand A q y) := by
    rw [coeffSemilinearAut.coeffMap_qExpand, hy, hF₂, IntermediateField.coe_smul, coe_heckeBetaBar,
      Algebra.smul_def, map_mul, qExpand_algebraMap]

  obtain ⟨m₁, hm₁⟩ := R.residue₁_coeffMap y (hF₁s ▸ F₁.2)
  have hE₁ : (⟨coeffMap A.subtype y, hF₁s ▸ F₁.2⟩ : modularFunctionFieldBar (N * q)) = F₁ :=
    Subtype.ext hF₁s.symm
  have h₁ : F₁ ∈ R.R₁.integers := hE₁ ▸ m₁
  have hr₁ : R.R₁.residue ⟨F₁, h₁⟩ ≠ 0 := by
    intro h0
    apply hres
    have hE : (⟨F₁, h₁⟩ : R.R₁.integers) = ⟨_, m₁⟩ := Subtype.ext hE₁.symm
    rw [hE] at h0
    rw [← hm₁, h0]
    simp

  have hres₂ : coeffMap (IsLocalRing.residue A) (qExpand A q y) ≠ 0 := by
    rw [coeffSemilinearAut.coeffMap_qExpand]
    intro h0
    exact hres (qExpand_injective (R := ResidueField A) (N := q) (by rw [h0, map_zero]))
  obtain ⟨m₂, hm₂⟩ := R.residue₁_coeffMap (qExpand A q y) (hF₂s ▸ F₂.2)
  have hE₂ : (⟨coeffMap A.subtype (qExpand A q y), hF₂s ▸ F₂.2⟩ : modularFunctionFieldBar (N * q))
      = F₂ := Subtype.ext hF₂s.symm
  have h₂' : F₂ ∈ R.R₁.integers := hE₂ ▸ m₂
  have hr₂' : R.R₁.residue ⟨F₂, h₂'⟩ ≠ 0 := by
    intro h0
    apply hres₂
    have hE : (⟨F₂, h₂'⟩ : R.R₁.integers) = ⟨_, m₂⟩ := Subtype.ext hE₂.symm
    rw [hE] at h0
    rw [← hm₂, h0]
    simp

  have hAL : ProlongationTuple.atkinLehnerBar N q F₁ = F₂ := by
    rw [hF₁, hF₂]
    simp only [Algebra.smul_def, map_mul, AlgEquiv.commutes, atkinLehnerBar_heckeAlphaBar hqN]
  have h₂ : F₁ ∈ R.R₂.integers := by
    rw [R.mem_integers₂_iff, hAL]
    exact h₂'
  refine ⟨h₁, h₂, hr₁, ?_⟩
  rw [R.residue₂_eq F₁ h₂]
  have hr : ∀ x : R.R₁.integers,
      (x : modularFunctionFieldBar (N * q)) = F₂ → R.R₁.residue x ≠ 0 := by
    intro x hx
    have hx' : x = ⟨F₂, h₂'⟩ := Subtype.ext hx
    rw [hx']
    exact hr₂'
  exact hr _ hAL

set_option maxHeartbeats 3200000 in

private theorem isCommonUnit_div (R : ProlongationTuple P) {f g : modularFunctionFieldBar (N * q)}
    (hf : IsCommonUnit R f) (hg : IsCommonUnit R g) : IsCommonUnit R (f / g) := by
  obtain ⟨hf₁, hf₂, hrf₁, hrf₂⟩ := hf
  obtain ⟨hg₁, hg₂, hrg₁, hrg₂⟩ := hg

  have key : ∀ (S : RegularProlongation A (modularFunctionFieldBar (N * q))
      (modularFunctionFieldFullC (ResidueField A) N))
      (hf' : f ∈ S.integers) (hg' : g ∈ S.integers),
      S.residue ⟨f, hf'⟩ ≠ 0 → S.residue ⟨g, hg'⟩ ≠ 0 →
      ∃ h : f / g ∈ S.integers, S.residue ⟨f / g, h⟩ ≠ 0 := by
    intro S hf' hg' hrf hrg
    obtain ⟨u, hu⟩ := S.isUnit_of_residue_ne_zero hrg
    have hu' : ((u⁻¹ : S.integersˣ) : S.integers) * ⟨g, hg'⟩ = 1 := by rw [← hu]; exact u.inv_mul
    have hinv : (((u⁻¹ : S.integersˣ) : S.integers) : modularFunctionFieldBar (N * q)) = g⁻¹ := by
      have h1 := congrArg Subtype.val hu'
      push_cast at h1
      exact eq_inv_of_mul_eq_one_left h1
    have hmem : f / g ∈ S.integers := by
      rw [div_eq_mul_inv, ← hinv]
      exact mul_mem hf' ((u⁻¹ : S.integersˣ) : S.integers).2
    refine ⟨hmem, ?_⟩
    have hE : (⟨f / g, hmem⟩ : S.integers) = ⟨f, hf'⟩ * ((u⁻¹ : S.integersˣ) : S.integers) := by
      apply Subtype.ext
      simp [hinv, div_eq_mul_inv]
    rw [hE, map_mul]
    exact mul_ne_zero hrf (S.residue_ne_zero_of_isUnit (Units.isUnit _))
  obtain ⟨m₁, r₁⟩ := key R.R₁ hf₁ hg₁ hrf₁ hrg₁
  obtain ⟨m₂, r₂⟩ := key R.R₂ hf₂ hg₂ hrf₂ hrg₂
  exact ⟨m₁, m₂, r₁, r₂⟩

private theorem exists_closure_div (h : modularFunctionFieldBar N) (hh : h ≠ 0) :
    ∃ (Y Z : modularFunctionFieldBar N), Y ≠ 0 ∧ Z ≠ 0 ∧ h = Y / Z ∧
      Bounded (Y : LaurentSeries (AlgebraicClosure ℚ)) ∧
      Bounded (Z : LaurentSeries (AlgebraicClosure ℚ)) := by
  set S : Set (LaurentSeries (AlgebraicClosure ℚ)) :=
    Set.range (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))) ∪
      {jqModC (AlgebraicClosure ℚ), jqNModC (AlgebraicClosure ℚ) N} with hS
  have hmemC : ∀ x : LaurentSeries (AlgebraicClosure ℚ),
      x ∈ modularFunctionFieldBar N ↔ x ∈ Subfield.closure S := by
    intro x
    rw [modularFunctionFieldBar_eq_modularFunctionFieldC]
    rfl
  obtain ⟨y, hy, z, hz, hyz⟩ := Subfield.mem_closure_iff.mp ((hmemC _).mp h.2)
  have hle : Subring.closure S ≤ (Subfield.closure S).toSubring :=
    Subring.closure_le.mpr fun x hx => Subfield.subset_closure hx
  have hsub : ∀ x ∈ Subring.closure S, x ∈ modularFunctionFieldBar N := fun x hx =>
    (hmemC x).mpr (hle hx)
  refine ⟨⟨y, hsub y hy⟩, ⟨z, hsub z hz⟩, ?_, ?_, ?_, bounded_of_mem_closure N hy,
    bounded_of_mem_closure N hz⟩
  · intro h0
    have hy0 : y = 0 := congrArg Subtype.val h0
    apply hh
    apply Subtype.ext
    show (h : LaurentSeries (AlgebraicClosure ℚ)) = 0
    rw [← hyz, hy0, zero_div]
  · intro h0
    have hz0 : z = 0 := congrArg Subtype.val h0
    apply hh
    apply Subtype.ext
    show (h : LaurentSeries (AlgebraicClosure ℚ)) = 0
    rw [← hyz, hz0, div_zero]
  · apply Subtype.ext
    simp only [IntermediateField.coe_div]
    exact hyz.symm

private theorem exists_smul_commonUnit (hqN : ¬ q ∣ N) (R : ProlongationTuple P)
    (h : modularFunctionFieldBar N) (hh : h ≠ 0) :
    ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧
      ∃ (h₁ : c • heckeAlphaBar (AlgebraicClosure ℚ) N q h ∈ R.R₁.integers)
        (h₂ : c • heckeAlphaBar (AlgebraicClosure ℚ) N q h ∈ R.R₂.integers),
        R.R₁.residue ⟨_, h₁⟩ ≠ 0 ∧ R.R₂.residue ⟨_, h₂⟩ ≠ 0 := by
  obtain ⟨Y, Z, hY, hZ, rfl, hbY, hbZ⟩ := exists_closure_div h hh
  obtain ⟨c₁, hc₁, hu₁⟩ := exists_smul_isCommonUnit_of_bounded hqN R Y hY hbY
  obtain ⟨c₂, hc₂, hu₂⟩ := exists_smul_isCommonUnit_of_bounded hqN R Z hZ hbZ
  refine ⟨c₁ / c₂, div_ne_zero hc₁ hc₂, ?_⟩
  have hq : (c₁ / c₂) • heckeAlphaBar (AlgebraicClosure ℚ) N q (Y / Z)
      = (c₁ • heckeAlphaBar (AlgebraicClosure ℚ) N q Y) /
          (c₂ • heckeAlphaBar (AlgebraicClosure ℚ) N q Z) := by
    rw [map_div₀, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_div₀, div_mul_div_comm]
  rw [hq]
  exact isCommonUnit_div R hu₁ hu₂

end CommonUnits

end UniqRed

section Generic

private theorem int_eq_zero_of_forall_dvd (z : ℤ) (h : ∀ m : ℕ, m ≠ 0 → (m : ℤ) ∣ z) : z = 0 := by
  have hd := h (z.natAbs + 1) (Nat.succ_ne_zero _)
  refine Int.eq_zero_of_abs_lt_dvd hd ?_
  rw [Int.abs_eq_natAbs]
  push_cast
  omega

private theorem map_single_eq_of_forall_nsmul {ι X : Type*} (δ : (ι →₀ ℤ) →+ (X →₀ ℤ))
    (Pr : AddSubgroup (ι →₀ ℤ)) (hPr : ∀ D ∈ Pr, δ D = 0)
    (hdiv : ∀ (b b₀ : ι) (m : ℕ), m ≠ 0 → ∃ E : ι →₀ ℤ, ∃ D₀ ∈ Pr,
      Finsupp.single b (1 : ℤ) - Finsupp.single b₀ (1 : ℤ) = m • E + D₀)
    (b b₀ : ι) : δ (Finsupp.single b 1) = δ (Finsupp.single b₀ 1) := by
  rw [← sub_eq_zero, ← map_sub]
  ext x
  show δ (Finsupp.single b 1 - Finsupp.single b₀ 1) x = 0
  refine int_eq_zero_of_forall_dvd _ fun m hm => ?_
  obtain ⟨E, D₀, hD₀, hE⟩ := hdiv b b₀ m hm
  refine ⟨δ E x, ?_⟩
  rw [hE, map_add, hPr D₀ hD₀, add_zero, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]

private theorem eq_of_ite_single_eq {X : Type*} (T : X → Prop) {x x' : X} {n n' : ℤ}
    {d : Decidable (T x)} {d' : Decidable (T x')}
    (h : @ite _ (T x) d (Finsupp.single x n) 0 = @ite _ (T x') d' (Finsupp.single x' n') 0)
    (hx : T x) (hn : n ≠ 0) : T x' ∧ x' = x := by
  rw [if_pos hx] at h
  by_cases hx' : T x'
  · rw [if_pos hx'] at h
    rcases (Finsupp.single_eq_single_iff _ _ _ _).mp h with ⟨hxx, -⟩ | ⟨h0, -⟩
    · exact ⟨hx', hxx.symm⟩
    · exact absurd h0 hn
  · rw [if_neg hx'] at h
    exact absurd (Finsupp.single_eq_zero.mp h) hn

private theorem filterAddHom_apply' {α M : Type*} [AddZeroClass M] (p : α → Prop) [DecidablePred p]
    (v : α →₀ M) : Finsupp.filterAddHom p v = v.filter p := rfl

private theorem ord_algebraMap_eq_zero {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {a : K} (ha : a ≠ 0) : v.ord (algebraMap K F a) = 0 := by
  have hne : algebraMap K F a ≠ 0 := (map_ne_zero _).mpr ha
  have h1 := v.adicValuation_le_one_iff.mp (v.adicValuation_algebraMap_le_one a)
  have h2 := v.adicValuation_le_one_iff.mp (v.adicValuation_algebraMap_le_one a⁻¹)
  rw [or_iff_right hne] at h1
  rw [map_inv₀, or_iff_right (inv_ne_zero hne), v.ord_inv] at h2
  omega

private theorem ord_smul_eq {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {c : K} (hc : c ≠ 0) {f : F} (hf : f ≠ 0) : v.ord (c • f) = v.ord f := by
  rw [Algebra.smul_def, v.ord_mul ((map_ne_zero _).mpr hc) hf, ord_algebraMap_eq_zero v hc, zero_add]

end Generic

section Regroup

variable {K F₁ Z : Type*} [Field K] [Field F₁] [Field Z] [Algebra K F₁] [Algebra K Z]
  [HasPrincipalDivisors K Z]

omit [HasPrincipalDivisors K Z] in

private theorem ramificationIndexAlong_pos (u : F₁ →ₐ[K] Z) (hu : u.toRingHom.IsIntegral) (W : Place K Z) : 0 < W.ramificationIndexAlong u := by
  letI := algebraAlong u
  haveI := isScalarTower_along u
  haveI := isIntegral_along u hu
  exact Place.ramificationIndex_pos (F := F₁) (w := W)

open Classical in

private noncomputable def fw (u : F₁ →ₐ[K] Z) (hu : u.toRingHom.IsIntegral) (S : Place K Z → Prop) (b : Place K F₁) : ℤ :=
  ∑ W ∈ (Place.fiberAlong u hu b).filter S, (W.ramificationIndexAlong u : ℤ)

open Classical in
private theorem fw_nonneg (u : F₁ →ₐ[K] Z) (hu : u.toRingHom.IsIntegral) (S : Place K Z → Prop) (b : Place K F₁) : 0 ≤ fw u hu S b :=
  Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _

open Classical in
private theorem fw_pos_of_mem (u : F₁ →ₐ[K] Z) (hu : u.toRingHom.IsIntegral) (S : Place K Z → Prop) (b : Place K F₁) (W : Place K Z)
    (hW : W.restrictAlong u hu = b) (hS : S W) : 0 < fw u hu S b := by
  have hmem : W ∈ (Place.fiberAlong u hu b).filter S :=
    Finset.mem_filter.mpr ⟨Place.mem_fiberAlong.mpr hW, hS⟩
  have hle : (W.ramificationIndexAlong u : ℤ) ≤ fw u hu S b :=
    Finset.single_le_sum (f := fun W : Place K Z => (W.ramificationIndexAlong u : ℤ))
      (fun i _ => Int.natCast_nonneg _) hmem
  have hpos : 0 < (W.ramificationIndexAlong u : ℤ) := by
    exact_mod_cast ramificationIndexAlong_pos u hu W
  omega

open Classical in
private theorem not_of_fw_eq_zero (u : F₁ →ₐ[K] Z) (hu : u.toRingHom.IsIntegral) (S : Place K Z → Prop) (b : Place K F₁) (h0 : fw u hu S b = 0)
    (W : Place K Z) (hW : W.restrictAlong u hu = b) : ¬ S W := fun hS =>
  (fw_pos_of_mem u hu S b W hW hS).ne' h0

private noncomputable def fΘ (u : F₁ →ₐ[K] Z) (hu : u.toRingHom.IsIntegral) {X : Type*} (S : Place K Z → Prop) (g' : Place K F₁ → X) :
    Divisor K F₁ →+ (X →₀ ℤ) :=
  Finsupp.liftAddHom fun b =>
    (Finsupp.singleAddHom (g' b)).comp (AddMonoidHom.mulRight (fw u hu S b))

private theorem fΘ_single (u : F₁ →ₐ[K] Z) (hu : u.toRingHom.IsIntegral) {X : Type*} (S : Place K Z → Prop) (g' : Place K F₁ → X)
    (b : Place K F₁) (n : ℤ) :
    fΘ u hu S g' (Finsupp.single b n) = Finsupp.single (g' b) (n * fw u hu S b) := by
  rw [fΘ, Finsupp.liftAddHom_apply_single, AddMonoidHom.comp_apply, AddMonoidHom.mulRight_apply,
    Finsupp.singleAddHom_apply]

open Classical in

private theorem mapDomain_filter_pullbackAlong (u : F₁ →ₐ[K] Z) (hu : u.toRingHom.IsIntegral) {X : Type*} (S : Place K Z → Prop)
    (g' : Place K F₁ → X) (g : Place K Z → X) (hg : ∀ W, g W = g' (W.restrictAlong u hu))
    (D : Divisor K F₁) :
    Finsupp.mapDomain g ((Divisor.pullbackAlong u hu D).filter S) = fΘ u hu S g' D := by
  set L : Divisor K F₁ →+ (X →₀ ℤ) :=
    (Finsupp.mapDomain.addMonoidHom g).comp
      ((Finsupp.filterAddHom S).comp (Divisor.pullbackAlong u hu)) with hL
  have hLD : Finsupp.mapDomain g ((Divisor.pullbackAlong u hu D).filter S) = L D := rfl
  rw [hLD]
  refine DFunLike.congr_fun (Finsupp.addHom_ext fun b n => ?_) D
  rw [fΘ_single]
  show Finsupp.mapDomain g ((Divisor.pullbackAlong u hu (Finsupp.single b n)).filter S) = _
  rw [Divisor.pullbackAlong_single, ← filterAddHom_apply', map_sum]
  simp only [filterAddHom_apply']
  have hfs : ∀ W ∈ Place.fiberAlong u hu b,
      (Finsupp.single W (n * (W.ramificationIndexAlong u : ℤ))).filter S
        = if S W then Finsupp.single W (n * (W.ramificationIndexAlong u : ℤ)) else 0 := by
    intro W _
    split_ifs with h
    · exact Finsupp.filter_single_of_pos _ h
    · exact Finsupp.filter_single_of_neg _ h
  rw [Finset.sum_congr rfl hfs, ← Finset.sum_filter, Finsupp.mapDomain_finsetSum]
  simp only [Finsupp.mapDomain_single]
  have hsum : ∑ W ∈ (Place.fiberAlong u hu b).filter S,
        Finsupp.single (g W) (n * (W.ramificationIndexAlong u : ℤ))
      = ∑ W ∈ (Place.fiberAlong u hu b).filter S,
        Finsupp.single (g' b) (n * (W.ramificationIndexAlong u : ℤ)) :=
    Finset.sum_congr rfl fun W hW => by
      rw [hg W, Place.mem_fiberAlong.mp (Finset.mem_filter.mp hW).1]
  rw [hsum, ← Finsupp.single_finsetSum, ← Finset.mul_sum]
  rfl

open Classical in

private noncomputable def tΦ (u : F₁ →ₐ[K] Z) (hu : u.toRingHom.IsIntegral) {X : Type*} (S : Place K Z → Prop) (g' : Place K F₁ → X)
    (T : X → Prop) : Divisor K F₁ →+ (X →₀ ℤ) :=
  (Finsupp.filterAddHom T).comp (fΘ u hu S g')

open Classical in
private theorem tΦ_single (u : F₁ →ₐ[K] Z) (hu : u.toRingHom.IsIntegral) {X : Type*} (S : Place K Z → Prop) (g' : Place K F₁ → X)
    (T : X → Prop) (b : Place K F₁) (n : ℤ) :
    tΦ u hu S g' T (Finsupp.single b n)
      = if T (g' b) then Finsupp.single (g' b) (n * fw u hu S b) else 0 := by
  rw [tΦ, AddMonoidHom.comp_apply, fΘ_single, filterAddHom_apply']
  split_ifs with h
  · exact Finsupp.filter_single_of_pos _ h
  · exact Finsupp.filter_single_of_neg _ h

open Classical in

private theorem tΦ_apply_of_law (u : F₁ →ₐ[K] Z) (hu : u.toRingHom.IsIntegral) {X : Type*} (S : Place K Z → Prop) (g' : Place K F₁ → X)
    (T : X → Prop) (g : Place K Z → X) (hg : ∀ W, g W = g' (W.restrictAlong u hu))
    (D : Divisor K F₁) (E : X → ℤ)
    (hlaw : ∀ v, T v → Finsupp.mapDomain g ((Divisor.pullbackAlong u hu D).filter S) v = E v)
    (v : X) : tΦ u hu S g' T D v = if T v then E v else 0 := by
  rw [tΦ, AddMonoidHom.comp_apply, filterAddHom_apply', Finsupp.filter_apply,
    ← mapDomain_filter_pullbackAlong u hu S g' g hg D]
  split_ifs with h
  · exact hlaw v h
  · rfl

end Regroup

section Modular

p2m_open "ModularCurve ModularCurve.PlaceSpecialization~IsInftySide~jFun~IsCuspidal~IsZeroSide ModularCurve.PlaceSpecialization.ProlongationTuple"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
  {hKr : KroneckerCongruence q data} {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

private scoped instance instHasPrincipalDivisorsBar (M : ℕ) [NeZero M] :
    HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar M) :=
  hasPrincipalDivisors_modularFunctionFieldBar_unconditional M

private theorem mem_integersFst_iff_of_tuples {P P' : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (R' : ProlongationTuple P') (f : modularFunctionFieldBar (N * q)) :
    f ∈ R.R₁.integers ↔ f ∈ R'.R₁.integers :=
  (R.mem_integersFst_iff f).trans (R'.mem_integersFst_iff f).symm

private theorem mem_integersSnd_iff_of_tuples {P P' : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (R' : ProlongationTuple P') (f : modularFunctionFieldBar (N * q)) :
    f ∈ R.R₂.integers ↔ f ∈ R'.R₂.integers :=
  (R.mem_integersSnd_iff f).trans (R'.mem_integersSnd_iff f).symm

private theorem residue₁_eq_of_tuples {P P' : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (R' : ProlongationTuple P') (f : modularFunctionFieldBar (N * q))
    (h : f ∈ R.R₁.integers) (h' : f ∈ R'.R₁.integers) :
    R.residue₁ ⟨f, h⟩ = R'.residue₁ ⟨f, h'⟩ := by
  have hf : (f : LaurentSeries (AlgebraicClosure ℚ))
      ∈ CharPReduction.modularLocalized (N * q) A.toSubring red := (R.mem_integersFst_iff f).mp h
  obtain ⟨h₀, e₀⟩ := R.residue₁_eq_modularRedLocHom f hf
  obtain ⟨h₀', e₀'⟩ := R'.residue₁_eq_modularRedLocHom f hf
  apply Subtype.ext
  rw [residue₁_apply, residue₁_apply]
  exact e₀.trans e₀'.symm

private theorem residue₂_eq_of_tuples {P P' : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (R' : ProlongationTuple P') (f : modularFunctionFieldBar (N * q))
    (h : f ∈ R.R₂.integers) (h' : f ∈ R'.R₂.integers) :
    R.residue₂ ⟨f, h⟩ = R'.residue₂ ⟨f, h'⟩ := by
  rw [residue₂_apply, residue₂_apply, R.residue₂_eq f h, R'.residue₂_eq f h']
  exact residue₁_eq_of_tuples R R' (atkinLehnerBar N q f) _ _

private theorem residueFst_ne_zero_of_tuples {P P' : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (R' : ProlongationTuple P') (f : modularFunctionFieldBar (N * q))
    (h : f ∈ R.R₁.integers) (h' : f ∈ R'.R₁.integers) (hne : R.R₁.residue ⟨f, h⟩ ≠ 0) :
    R'.R₁.residue ⟨f, h'⟩ ≠ 0 := by
  intro h0
  apply hne
  have e := residue₁_eq_of_tuples R R' f h h'
  rw [residue₁_apply, residue₁_apply, h0, map_zero] at e
  exact (map_eq_zero_iff R.ι R.ι.injective).mp e

private theorem residueSnd_ne_zero_of_tuples {P P' : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (R' : ProlongationTuple P') (f : modularFunctionFieldBar (N * q))
    (h : f ∈ R.R₂.integers) (h' : f ∈ R'.R₂.integers) (hne : R.R₂.residue ⟨f, h⟩ ≠ 0) :
    R'.R₂.residue ⟨f, h'⟩ ≠ 0 := by
  intro h0
  apply hne
  have e := residue₂_eq_of_tuples R R' f h h'
  rw [residue₂_apply, residue₂_apply, h0, map_zero] at e
  exact (map_eq_zero_iff R.ι R.ι.injective).mp e

private theorem pullbackAlong_eq_ord (u : modularFunctionFieldBar N →ₐ[AlgebraicClosure ℚ]
      modularFunctionFieldBar (N * q)) (hu : u.toRingHom.IsIntegral)
    (h : modularFunctionFieldBar N) (hh : h ≠ 0)
    (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hD₀ : ∀ b, D₀ b = b.ord h) {c : AlgebraicClosure ℚ} (hc : c ≠ 0)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    Divisor.pullbackAlong u hu D₀ W = W.ord (c • u h) := by
  rw [Divisor.pullbackAlong_apply, hD₀, ← Place.ord_restrictAlong u hu W h,
    ord_smul_eq W hc ((map_ne_zero u).mpr hh)]

omit [Fact q.Prime] [NeZero N] in

private theorem smul_scalar_ne_zero {B : ValuationSubring (modularFunctionFieldBar (N * q))}
    {Fbar : Type*} [Field Fbar] (res : B →+* Fbar) {c : AlgebraicClosure ℚ}
    {g : modularFunctionFieldBar (N * q)} (hc : c • g ∈ B) (hres : res ⟨c • g, hc⟩ ≠ 0) :
    c ≠ 0 := by
  rintro rfl
  apply hres
  have h0 : (⟨(0 : AlgebraicClosure ℚ) • g, hc⟩ : B) = 0 := Subtype.ext (zero_smul _ _)
  rw [h0, map_zero]

private abbrev TA (_P : PlaceSpecialization A q N data hKr k red hα hβ) (v : Place k (modularFunctionFieldC k N)) : Prop :=
  frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) ≠ v ∧ IsAffineGeomPlace k N v

private abbrev TN (_P : PlaceSpecialization A q N data hKr k red hα hβ) (v : Place k (modularFunctionFieldC k N)) : Prop :=
  frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) ≠ v ∧ ¬ IsAffineGeomPlace k N v

private abbrev TF (_P : PlaceSpecialization A q N data hKr k red hα hβ) (v : Place k (modularFunctionFieldC k N)) : Prop :=
  frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v ∧ IsAffineGeomPlace k N v

private abbrev TC (_P : PlaceSpecialization A q N data hKr k red hα hβ) (v : Place k (modularFunctionFieldC k N)) : Prop :=
  frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v ∧ ¬ IsAffineGeomPlace k N v

private def AllPlaces (_W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) : Prop := True

omit [Fact q.Prime] [NeZero N] in
open Classical in
private theorem filter_allPlaces (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    (D.filter AllPlaces) = D := by
  ext W
  rw [Finsupp.filter_apply, if_pos (show AllPlaces W from trivial)]

open Classical in

private theorem snd_functional_eq (hqN : ¬ q ∣ N) (P P' : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P) (hmodel : R.IsModel)
    (R' : ProlongationTuple P') (hmodel' : R'.IsModel)
    (T : Place k (modularFunctionFieldC k N) → Prop)
    (hT : ∀ v, T v → frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) ≠ v)
    (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hD₀ : D₀ ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N)) :
    tΦ (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ P.IsStrictSnd P.sp T D₀
      = tΦ (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ P'.IsStrictSnd P'.sp T D₀ := by
  obtain ⟨h, hh, hD⟩ := Divisor.mem_principal.mp hD₀
  have hg0 : heckeBetaBar (AlgebraicClosure ℚ) N q h ≠ 0 := (map_ne_zero _).mpr hh
  obtain ⟨c, hc2, hres⟩ := R.R₂.exists_smul_mem _ hg0
  have hc0 : c ≠ 0 := smul_scalar_ne_zero R.R₂.residue hc2 hres
  have hDf : ∀ W, Divisor.pullbackAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ D₀ W
      = W.ord (c • heckeBetaBar (AlgebraicClosure ℚ) N q h) :=
    fun W => pullbackAlong_eq_ord (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ h hh D₀ hD hc0 W
  have hc2' : c • heckeBetaBar (AlgebraicClosure ℚ) N q h ∈ R'.R₂.integers :=
    (mem_integersSnd_iff_of_tuples R R' _).mp hc2
  have hres' : R'.R₂.residue ⟨_, hc2'⟩ ≠ 0 := residueSnd_ne_zero_of_tuples R R' _ hc2 hc2' hres
  have law := divisorLawSnd_oneSided hqN P R hmodel _ hc2 hres _ hDf
  have law' := divisorLawSnd_oneSided hqN P' R' hmodel' _ hc2' hres' _ hDf
  ext v
  rw [tΦ_apply_of_law (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ P.IsStrictSnd P.sp T P.reduceSnd (fun W => rfl) D₀
      (fun v => v.ord (R.residue₂ ⟨_, hc2⟩)) (fun v hv => law v (hT v hv)) v,
    tΦ_apply_of_law (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ P'.IsStrictSnd P'.sp T P'.reduceSnd (fun W => rfl) D₀
      (fun v => v.ord (R'.residue₂ ⟨_, hc2'⟩)) (fun v hv => law' v (hT v hv)) v,
    residue₂_eq_of_tuples R R' _ hc2 hc2']

open Classical in

private theorem fix_functional_eq (hqN : ¬ q ∣ N) (P P' : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P) (hO : R.OrderLawFixed)
    (R' : ProlongationTuple P') (hO' : R'.OrderLawFixed)
    (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hD₀ : D₀ ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N)) :
    tΦ (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα AllPlaces P.sp (TF P) D₀
      = tΦ (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα AllPlaces P'.sp (TF P) D₀ := by
  obtain ⟨h, hh, hD⟩ := Divisor.mem_principal.mp hD₀
  obtain ⟨c, hc0, h₁, h₂, hr₁, hr₂⟩ := UniqRed.exists_smul_commonUnit hqN R h hh
  have hDf : ∀ W, Divisor.pullbackAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα D₀ W
      = W.ord (c • heckeAlphaBar (AlgebraicClosure ℚ) N q h) :=
    fun W => pullbackAlong_eq_ord (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα h hh D₀ hD hc0 W
  have h₁' : c • heckeAlphaBar (AlgebraicClosure ℚ) N q h ∈ R'.R₁.integers :=
    (mem_integersFst_iff_of_tuples R R' _).mp h₁
  have h₂' : c • heckeAlphaBar (AlgebraicClosure ℚ) N q h ∈ R'.R₂.integers :=
    (mem_integersSnd_iff_of_tuples R R' _).mp h₂
  have hr₁' : R'.R₁.residue ⟨_, h₁'⟩ ≠ 0 := residueFst_ne_zero_of_tuples R R' _ h₁ h₁' hr₁
  have hr₂' : R'.R₂.residue ⟨_, h₂'⟩ ≠ 0 := residueSnd_ne_zero_of_tuples R R' _ h₂ h₂' hr₂
  have law := hO _ h₁ h₂ hr₁ hr₂ _ hDf
  have law' := hO' _ h₁' h₂' hr₁' hr₂' _ hDf
  ext v
  rw [tΦ_apply_of_law (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα AllPlaces P.sp (TF P) P.reduceFst (fun W => rfl) D₀
      (fun v => v.ord (R.residue₁ ⟨_, h₁⟩) + (frobOnPlacesGeomLevel k N data hKr v).ord (R.residue₂ ⟨_, h₂⟩))
      (fun v hv => by rw [filter_allPlaces]; exact law v hv.1 hv.2) v,
    tΦ_apply_of_law (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα AllPlaces P'.sp (TF P) P'.reduceFst (fun W => rfl) D₀
      (fun v => v.ord (R'.residue₁ ⟨_, h₁'⟩) + (frobOnPlacesGeomLevel k N data hKr v).ord (R'.residue₂ ⟨_, h₂'⟩))
      (fun v hv => by rw [filter_allPlaces]; exact law' v hv.1 hv.2) v,
    residue₁_eq_of_tuples R R' _ h₁ h₁', residue₂_eq_of_tuples R R' _ h₂ h₂']

open Classical in

private theorem inf_functional_eq (hqN : ¬ q ∣ N) (P P' : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P) (hmodel : R.IsModel)
    (R' : ProlongationTuple P') (hmodel' : R'.IsModel)
    (T : Place k (modularFunctionFieldC k N) → Prop)
    (hT : ∀ v, T v → ¬ IsAffineGeomPlace k N v)
    (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hD₀ : D₀ ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N)) :
    tΦ (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα (IsInftySide P) P.sp T D₀
      = tΦ (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα (IsInftySide P) P'.sp T D₀ := by
  obtain ⟨h, hh, hD⟩ := Divisor.mem_principal.mp hD₀
  have hg0 : heckeAlphaBar (AlgebraicClosure ℚ) N q h ≠ 0 := (map_ne_zero _).mpr hh
  obtain ⟨c, hc1, hres⟩ := R.R₁.exists_smul_mem _ hg0
  have hc0 : c ≠ 0 := smul_scalar_ne_zero R.R₁.residue hc1 hres
  have hDf : ∀ W, Divisor.pullbackAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα D₀ W
      = W.ord (c • heckeAlphaBar (AlgebraicClosure ℚ) N q h) :=
    fun W => pullbackAlong_eq_ord (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα h hh D₀ hD hc0 W
  have hc1' : c • heckeAlphaBar (AlgebraicClosure ℚ) N q h ∈ R'.R₁.integers :=
    (mem_integersFst_iff_of_tuples R R' _).mp hc1
  have hres' : R'.R₁.residue ⟨_, hc1'⟩ ≠ 0 := residueFst_ne_zero_of_tuples R R' _ hc1 hc1' hres
  have law := cuspLawInfty_oneSided hqN P R hmodel _ hc1 hres _ hDf
  have law' := cuspLawInfty_oneSided hqN P' R' hmodel' _ hc1' hres' _ hDf
  have hlaw : ∀ v, T v → Finsupp.mapDomain P.reduceFst ((Divisor.pullbackAlong
      (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα D₀).filter (IsInftySide P)) v
        = v.ord (R.residue₁ ⟨_, hc1⟩) := by
    intro v hv
    obtain ⟨⟨C, hC, hCv⟩, -⟩ :=
      exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace
        hqN P v (hT v hv)
    have e := law C hC
    rw [hCv] at e
    exact e
  have hlaw' : ∀ v, T v → Finsupp.mapDomain P'.reduceFst ((Divisor.pullbackAlong
      (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα D₀).filter (IsInftySide P)) v
        = v.ord (R'.residue₁ ⟨_, hc1'⟩) := by
    intro v hv
    obtain ⟨⟨C, hC, hCv⟩, -⟩ :=
      exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace
        hqN P' v (hT v hv)
    have e := law' C hC
    rw [hCv] at e
    exact e
  ext v
  rw [tΦ_apply_of_law (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα (IsInftySide P) P.sp T P.reduceFst (fun W => rfl) D₀
      (fun v => v.ord (R.residue₁ ⟨_, hc1⟩)) hlaw v,
    tΦ_apply_of_law (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα (IsInftySide P) P'.sp T P'.reduceFst (fun W => rfl) D₀
      (fun v => v.ord (R'.residue₁ ⟨_, hc1'⟩)) hlaw' v,
    residue₁_eq_of_tuples R R' _ hc1 hc1']

open Classical in

private theorem zero_functional_eq (hqN : ¬ q ∣ N) (P P' : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P) (hmodel : R.IsModel)
    (R' : ProlongationTuple P') (hmodel' : R'.IsModel)
    (T : Place k (modularFunctionFieldC k N) → Prop)
    (hT : ∀ v, T v → ¬ IsAffineGeomPlace k N v)
    (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hD₀ : D₀ ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N)) :
    tΦ (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ (IsZeroSide P) P.sp T D₀
      = tΦ (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ (IsZeroSide P) P'.sp T D₀ := by
  obtain ⟨h, hh, hD⟩ := Divisor.mem_principal.mp hD₀
  have hg0 : heckeBetaBar (AlgebraicClosure ℚ) N q h ≠ 0 := (map_ne_zero _).mpr hh
  obtain ⟨c, hc2, hres⟩ := R.R₂.exists_smul_mem _ hg0
  have hc0 : c ≠ 0 := smul_scalar_ne_zero R.R₂.residue hc2 hres
  have hDf : ∀ W, Divisor.pullbackAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ D₀ W
      = W.ord (c • heckeBetaBar (AlgebraicClosure ℚ) N q h) :=
    fun W => pullbackAlong_eq_ord (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ h hh D₀ hD hc0 W
  have hc2' : c • heckeBetaBar (AlgebraicClosure ℚ) N q h ∈ R'.R₂.integers :=
    (mem_integersSnd_iff_of_tuples R R' _).mp hc2
  have hres' : R'.R₂.residue ⟨_, hc2'⟩ ≠ 0 := residueSnd_ne_zero_of_tuples R R' _ hc2 hc2' hres
  have law := cuspLawZero_oneSided hqN P R hmodel _ hc2 hres _ hDf
  have law' := cuspLawZero_oneSided hqN P' R' hmodel' _ hc2' hres' _ hDf
  have hlaw : ∀ v, T v → Finsupp.mapDomain P.reduceSnd ((Divisor.pullbackAlong
      (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ D₀).filter (IsZeroSide P)) v
        = v.ord (R.residue₂ ⟨_, hc2⟩) := by
    intro v hv
    obtain ⟨-, ⟨C, hC, hCv⟩⟩ :=
      exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace
        hqN P v (hT v hv)
    have e := law C hC
    rw [hCv] at e
    exact e
  have hlaw' : ∀ v, T v → Finsupp.mapDomain P'.reduceSnd ((Divisor.pullbackAlong
      (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ D₀).filter (IsZeroSide P)) v
        = v.ord (R'.residue₂ ⟨_, hc2'⟩) := by
    intro v hv
    obtain ⟨-, ⟨C, hC, hCv⟩⟩ :=
      exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace
        hqN P' v (hT v hv)
    have e := law' C hC
    rw [hCv] at e
    exact e
  ext v
  rw [tΦ_apply_of_law (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ (IsZeroSide P) P.sp T P.reduceSnd (fun W => rfl) D₀
      (fun v => v.ord (R.residue₂ ⟨_, hc2⟩)) hlaw v,
    tΦ_apply_of_law (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ (IsZeroSide P) P'.sp T P'.reduceSnd (fun W => rfl) D₀
      (fun v => v.ord (R'.residue₂ ⟨_, hc2'⟩)) hlaw' v,
    residue₂_eq_of_tuples R R' _ hc2 hc2']

private theorem exists_nsmul_add_principal
    (w w₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (m : ℕ) (hm : m ≠ 0) :
    ∃ E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      ∃ D₀ ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N),
        Finsupp.single w (1 : ℤ) - Finsupp.single w₀ (1 : ℤ) = m • E + D₀ := by
  have hdeg : Finsupp.single w (1 : ℤ) - Finsupp.single w₀ (1 : ℤ)
      ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N) := by
    rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single,
      deg_eq_one_modularFunctionFieldBar N w, deg_eq_one_modularFunctionFieldBar N w₀, sub_self]
  set x : JZero N := Pic0.mk ⟨_, hdeg⟩ with hxdef
  obtain ⟨y, hy⟩ := JZero.divisible N m hm x
  obtain ⟨E', rfl⟩ := Pic0.mk_surjective y
  have hmk : (m • Pic0.mk E' : JZero N) = Pic0.mk (m • E') := rfl
  rw [hmk, hxdef] at hy
  have hmem : m • E' - (⟨_, hdeg⟩ : Divisor.degZero) ∈ (Divisor.principal (K := AlgebraicClosure ℚ)
      (F := modularFunctionFieldBar N)).addSubgroupOf Divisor.degZero :=
    QuotientAddGroup.eq_iff_sub_mem.mp hy
  have hmem' : ((m • E' - (⟨_, hdeg⟩ : Divisor.degZero) : Divisor.degZero)
      : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) ∈ Divisor.principal :=
    AddSubgroup.mem_addSubgroupOf.mp hmem
  have hval : ((m • E' - (⟨_, hdeg⟩ : Divisor.degZero) : Divisor.degZero)
      : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
      = m • (E' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
        - (Finsupp.single w (1 : ℤ) - Finsupp.single w₀ (1 : ℤ)) := rfl
  rw [hval] at hmem'
  refine ⟨(E' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)), _,
    Divisor.principal.neg_mem hmem', ?_⟩
  abel

private theorem apply_single_eq_of_anchor
    (Φ Φ' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →+
      Divisor k (modularFunctionFieldC k N))
    (hPr : ∀ D₀ ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N),
      Φ D₀ = Φ' D₀)
    (b₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (h₀ : Φ (Finsupp.single b₀ 1) = Φ' (Finsupp.single b₀ 1))
    (b : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    Φ (Finsupp.single b 1) = Φ' (Finsupp.single b 1) := by
  have key := map_single_eq_of_forall_nsmul (Φ - Φ') Divisor.principal
    (fun D hD => by rw [AddMonoidHom.sub_apply, hPr D hD, sub_self])
    (fun b b₀ m hm => exists_nsmul_add_principal b b₀ m hm) b b₀
  rw [AddMonoidHom.sub_apply, AddMonoidHom.sub_apply, h₀, sub_self, sub_eq_zero] at key
  exact key

private theorem not_isAffineGeomPlace_sp_cuspInftyBar (P : PlaceSpecialization A q N data hKr k red hα hβ) :
    ¬ IsAffineGeomPlace k N (P.sp (cuspInftyBar N)) := by
  intro hA
  have hpole : (P.sp (cuspInftyBar N)).ord
      (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) < 0 := by
    refine P.d0_j_pole (cuspInftyBar N) fun a => ?_
    have hJ : (cuspInftyBar N).ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N) = -1 :=
      ord_cuspInftyBar_coeffEmb_jq N
    have hvJ := (cuspInftyBar N).not_adicValuation_le_one_iff.mpr (by rw [hJ]; norm_num)
    refine le_of_lt ((cuspInftyBar N).not_adicValuation_le_one_iff.mp fun hle => hvJ ?_)
    have hc := (cuspInftyBar N).adicValuation_algebraMap_le_one
      (K := AlgebraicClosure ℚ) (a : AlgebraicClosure ℚ)
    refine le_trans ?_ (max_le hle hc)
    exact le_trans (by rw [sub_add_cancel]) (Valuation.map_add _ _ _)
  exact (P.sp (cuspInftyBar N)).not_adicValuation_le_one_iff.mpr hpole
    ((P.sp (cuspInftyBar N)).adicValuation_le_one_of_mem hA.1)

private theorem exists_ord_jFun_pos :
    ∃ W₁ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)), 0 < W₁.ord (jFun N q) := by
  have hc : (cuspInftyBar (N * q)).ord (jFun N q) = -1 := ord_cuspInftyBar_coeffEmb_jq (N * q)
  have hne : jFun N q ≠ 0 := by
    intro h
    rw [h, Place.ord_zero] at hc
    omega
  obtain ⟨D, hD, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) (jFun N q) hne
  classical
  by_contra hno
  simp only [not_exists, not_lt] at hno

  have key : ∀ E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      (∀ W, E W ≤ 0) → Divisor.degree E ≤ 0 := by
    intro E
    induction E using Finsupp.induction with
    | zero => intro _; simp
    | single_add a m f haf hm ih =>
      intro hle
      have hfa : f a = 0 := Finsupp.notMem_support_iff.mp haf
      have hm' : m ≤ 0 := by
        have h1 := hle a
        rwa [Finsupp.add_apply, Finsupp.single_eq_same, hfa, add_zero] at h1
      have hf' : ∀ W, f W ≤ 0 := by
        intro W
        by_cases hW : a = W
        · rw [← hW, hfa]
        · have h1 := hle W
          rwa [Finsupp.add_apply, Finsupp.single_apply, if_neg hW, zero_add] at h1
      rw [map_add, Divisor.degree_single, deg_eq_one_modularFunctionFieldBar (N * q) a, Nat.cast_one,
        mul_one]
      have h2 := ih hf'
      omega
  have hsplit := Finsupp.single_add_erase (cuspInftyBar (N * q)) D
  have hE : ∀ W, (D.erase (cuspInftyBar (N * q))) W ≤ 0 := by
    intro W
    by_cases hW : W = cuspInftyBar (N * q)
    · rw [hW, Finsupp.erase_same]
    · rw [Finsupp.erase_ne hW, hD]
      exact hno W
  have h1 := key _ hE
  have h2 : Divisor.degree D = D (cuspInftyBar (N * q)) + Divisor.degree (D.erase (cuspInftyBar (N * q))) := by
    conv_lhs => rw [← hsplit]
    rw [map_add, Divisor.degree_single, deg_eq_one_modularFunctionFieldBar (N * q) (cuspInftyBar (N * q)),
      Nat.cast_one, mul_one]
  rw [hD, hc] at h2
  omega

private theorem exists_isAffineGeomPlace_sp (P P' : PlaceSpecialization A q N data hKr k red hα hβ) :
    ∃ b₁ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      IsAffineGeomPlace k N (P.sp b₁) ∧ IsAffineGeomPlace k N (P'.sp b₁) := by
  obtain ⟨W₁, hW₁⟩ := exists_ord_jFun_pos (N := N) (q := q)
  have key : ∀ Q : PlaceSpecialization A q N data hKr k red hα hβ,
      IsAffineGeomPlace k N (Q.sp (W₁.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα)) := by
    intro Q
    by_contra hA
    have hc := isCuspidal_of_not_isAffineGeomPlace_reduceFst Q W₁ hA 0
    rw [ZeroMemClass.coe_zero, map_zero, sub_zero] at hc
    omega
  exact ⟨_, key P, key P'⟩

private theorem separableAlong_alpha :
    SeparableAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) := by
  letI := algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q)
  haveI := isScalarTower_along (heckeAlphaBar (AlgebraicClosure ℚ) N q)
  haveI : Module.Finite (modularFunctionFieldBar N) (modularFunctionFieldBar (N * q)) :=
    finiteAlong_heckeAlphaBar_of_prime (AlgebraicClosure ℚ) N q
  haveI : CharZero (modularFunctionFieldBar N) :=
    charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure ℚ) _).injective
  haveI : PerfectField (modularFunctionFieldBar N) := PerfectField.ofCharZero
  haveI : Algebra.IsAlgebraic (modularFunctionFieldBar N) (modularFunctionFieldBar (N * q)) :=
    Algebra.IsAlgebraic.of_finite _ _
  show Algebra.IsSeparable (modularFunctionFieldBar N) (modularFunctionFieldBar (N * q))
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

private theorem exists_restrictAlong_alpha_eq (b : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    ∃ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα = b :=
  Place.restrictAlong_surjective (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα
    (finiteAlong_heckeAlphaBar_of_prime (AlgebraicClosure ℚ) N q) separableAlong_alpha b

open Classical in

private theorem sp_eq_of_not_fixed (hqN : ¬ q ∣ N) (P P' : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P) (hmodel : R.IsModel)
    (R' : ProlongationTuple P') (hmodel' : R'.IsModel)
    (b : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hnf : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.sp b)) ≠ P.sp b) :
    P'.sp b = P.sp b := by
  obtain ⟨W₀, hW₀b, hW₀a, hW₀e, -⟩ := P.d2 b hnf
  have hS : P.IsStrictSnd W₀ := by
    constructor
    · show P.sp (W₀.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα)
        = frobOnPlacesGeomLevel k N data hKr (P.sp (W₀.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ))
      rw [hW₀b]
      exact hW₀a
    · show frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.sp (W₀.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ)))
        ≠ P.sp (W₀.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ)
      rw [hW₀b]
      exact hnf
  have hw : 0 < fw (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ P.IsStrictSnd b :=
    fw_pos_of_mem (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ P.IsStrictSnd b W₀ hW₀b hS
  by_cases hA : IsAffineGeomPlace k N (P.sp b)
  · have h₀ : tΦ (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ P.IsStrictSnd P.sp (TA P)
          (Finsupp.single (cuspInftyBar N) 1)
        = tΦ (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ P'.IsStrictSnd P'.sp (TA P)
          (Finsupp.single (cuspInftyBar N) 1) := by
      rw [tΦ_single, tΦ_single, if_neg (fun h => not_isAffineGeomPlace_sp_cuspInftyBar P h.2),
        if_neg (fun h => not_isAffineGeomPlace_sp_cuspInftyBar P' h.2)]
    have hrig := apply_single_eq_of_anchor _ _
      (fun D₀ hD₀ => snd_functional_eq hqN P P' R hmodel R' hmodel' (TA P) (fun v hv => hv.1) D₀ hD₀)
      (cuspInftyBar N) h₀ b
    rw [tΦ_single, tΦ_single] at hrig
    simp only [one_mul] at hrig
    exact (eq_of_ite_single_eq (TA P) hrig ⟨hnf, hA⟩ hw.ne').2
  · obtain ⟨b₁, hb₁, hb₁'⟩ := exists_isAffineGeomPlace_sp P P'
    have h₀ : tΦ (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ P.IsStrictSnd P.sp (TN P)
          (Finsupp.single b₁ 1)
        = tΦ (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ P'.IsStrictSnd P'.sp (TN P)
          (Finsupp.single b₁ 1) := by
      rw [tΦ_single, tΦ_single, if_neg (fun h => h.2 hb₁), if_neg (fun h => h.2 hb₁')]
    have hrig := apply_single_eq_of_anchor _ _
      (fun D₀ hD₀ => snd_functional_eq hqN P P' R hmodel R' hmodel' (TN P) (fun v hv => hv.1) D₀ hD₀)
      b₁ h₀ b
    rw [tΦ_single, tΦ_single] at hrig
    simp only [one_mul] at hrig
    exact (eq_of_ite_single_eq (TN P) hrig ⟨hnf, hA⟩ hw.ne').2

open Classical in

private theorem sp_eq_of_fixed_affine (hqN : ¬ q ∣ N) (P P' : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P) (hO : R.OrderLawFixed)
    (R' : ProlongationTuple P') (hO' : R'.OrderLawFixed)
    (b : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hfix : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.sp b)) = P.sp b) (hA : IsAffineGeomPlace k N (P.sp b)) :
    P'.sp b = P.sp b := by
  obtain ⟨W, hW⟩ := exists_restrictAlong_alpha_eq (N := N) (q := q) (hα := hα) b
  have hw : 0 < fw (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα AllPlaces b :=
    fw_pos_of_mem (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα AllPlaces b W hW trivial
  have h₀ : tΦ (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα AllPlaces P.sp (TF P)
        (Finsupp.single (cuspInftyBar N) 1)
      = tΦ (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα AllPlaces P'.sp (TF P)
        (Finsupp.single (cuspInftyBar N) 1) := by
    rw [tΦ_single, tΦ_single, if_neg (fun h => not_isAffineGeomPlace_sp_cuspInftyBar P h.2),
      if_neg (fun h => not_isAffineGeomPlace_sp_cuspInftyBar P' h.2)]
  have hrig := apply_single_eq_of_anchor _ _
    (fun D₀ hD₀ => fix_functional_eq hqN P P' R hO R' hO' D₀ hD₀) (cuspInftyBar N) h₀ b
  rw [tΦ_single, tΦ_single] at hrig
  simp only [one_mul] at hrig
  exact (eq_of_ite_single_eq (TF P) hrig ⟨hfix, hA⟩ hw.ne').2

open Classical in

private theorem sp_eq_of_fixed_not_affine (hqN : ¬ q ∣ N) (P P' : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P) (hmodel : R.IsModel) (hO : R.OrderLawFixed)
    (R' : ProlongationTuple P') (hmodel' : R'.IsModel) (hO' : R'.OrderLawFixed)
    (b : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hfix : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.sp b)) = P.sp b) (hnA : ¬ IsAffineGeomPlace k N (P.sp b)) :
    P'.sp b = P.sp b := by
  by_cases hnf' : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P'.sp b)) ≠ P'.sp b
  · exact (sp_eq_of_not_fixed hqN P' P R' hmodel' R hmodel b hnf').symm
  have hfix' : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P'.sp b)) = P'.sp b := not_not.mp hnf'
  by_cases hA' : IsAffineGeomPlace k N (P'.sp b)
  · exact (sp_eq_of_fixed_affine hqN P' P R' hO' R hO b hfix' hA').symm

  obtain ⟨b₁, hb₁, hb₁'⟩ := exists_isAffineGeomPlace_sp P P'
  have h₀ : tΦ (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα (IsInftySide P) P.sp (TC P)
        (Finsupp.single b₁ 1)
      = tΦ (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα (IsInftySide P) P'.sp (TC P)
        (Finsupp.single b₁ 1) := by
    rw [tΦ_single, tΦ_single, if_neg (fun h => h.2 hb₁), if_neg (fun h => h.2 hb₁')]
  have hrig := apply_single_eq_of_anchor _ _
    (fun D₀ hD₀ => inf_functional_eq hqN P P' R hmodel R' hmodel' (TC P) (fun v hv => hv.2) D₀ hD₀)
    b₁ h₀ b
  rw [tΦ_single, tΦ_single] at hrig
  simp only [one_mul] at hrig
  rcases (fw_nonneg (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα (IsInftySide P) b).lt_or_eq with
    hpos | hzero
  · exact (eq_of_ite_single_eq (TC P) hrig ⟨hfix, hnA⟩ hpos.ne').2

  obtain ⟨W, hWb⟩ := exists_restrictAlong_alpha_eq (N := N) (q := q) (hα := hα) b
  have hcusp : IsCuspidal P W := by
    refine isCuspidal_of_not_isAffineGeomPlace_reduceFst P W ?_
    show ¬ IsAffineGeomPlace k N (P.sp (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα))
    rw [hWb]
    exact hnA
  have hninf : ¬ IsInftySide P W := not_of_fw_eq_zero (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα (IsInftySide P) b hzero.symm W hWb
  have hzs : IsZeroSide P W := (isInftySide_or_isZeroSide_of_isCuspidal P hqN W hcusp).resolve_left hninf

  have hx : P'.sp (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ)
      = P.sp (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ) := by
    by_cases hnf₂ : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.sp (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ)))
        ≠ P.sp (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ)
    · exact sp_eq_of_not_fixed hqN P P' R hmodel R' hmodel' _ hnf₂
    by_cases hA₂ : IsAffineGeomPlace k N (P.sp (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ))
    · exact sp_eq_of_fixed_affine hqN P P' R hO R' hO' _ (not_not.mp hnf₂) hA₂
    have h₀' : tΦ (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ (IsZeroSide P) P.sp (TC P)
          (Finsupp.single b₁ 1)
        = tΦ (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ (IsZeroSide P) P'.sp (TC P)
          (Finsupp.single b₁ 1) := by
      rw [tΦ_single, tΦ_single, if_neg (fun h => h.2 hb₁), if_neg (fun h => h.2 hb₁')]
    have hrigZ := apply_single_eq_of_anchor _ _
      (fun D₀ hD₀ => zero_functional_eq hqN P P' R hmodel R' hmodel' (TC P) (fun v hv => hv.2) D₀ hD₀)
      b₁ h₀' (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ)
    rw [tΦ_single, tΦ_single] at hrigZ
    simp only [one_mul] at hrigZ
    have hwz : 0 < fw (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ (IsZeroSide P)
        (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ) :=
      fw_pos_of_mem (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ (IsZeroSide P) _ W rfl hzs
    exact (eq_of_ite_single_eq (TC P) hrigZ ⟨not_not.mp hnf₂, hA₂⟩ hwz.ne').2

  have h1 := P.d1 W
  have h1' := P'.d1 W
  rw [hWb] at h1 h1'
  rw [hx] at h1'
  rcases h1 with h1 | h1 <;> rcases h1' with h1' | h1'
  · rw [h1, h1']
  · rw [h1, ← h1', hfix']
  · rw [h1', ← h1, hfix]
  · exact frobOnPlacesGeomLevel_injective (K := k) (N := N) (data := data) (hKr := hKr) (h1'.trans h1.symm)

private theorem sp_apply_eq (hqN : ¬ q ∣ N) (P P' : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P) (hmodel : R.IsModel) (hO : R.OrderLawFixed)
    (R' : ProlongationTuple P') (hmodel' : R'.IsModel) (hO' : R'.OrderLawFixed)
    (b : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : P'.sp b = P.sp b := by
  by_cases hnf : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.sp b)) ≠ P.sp b
  · exact sp_eq_of_not_fixed hqN P P' R hmodel R' hmodel' b hnf
  by_cases hA : IsAffineGeomPlace k N (P.sp b)
  · exact sp_eq_of_fixed_affine hqN P P' R hO R' hO' b (not_not.mp hnf) hA
  · exact sp_eq_of_fixed_not_affine hqN P P' R hmodel hO R' hmodel' hO' b (not_not.mp hnf) hA

private theorem sp_eq (hqN : ¬ q ∣ N) (P P' : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P) (hmodel : R.IsModel) (hO : R.OrderLawFixed)
    (R' : ProlongationTuple P') (hmodel' : R'.IsModel) (hO' : R'.OrderLawFixed) : P.sp = P'.sp :=
  funext fun b => (sp_apply_eq hqN P P' R hmodel hO R' hmodel' hO' b).symm

end Modular

end ReductionRigidity
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_eq_of_isModel_of_orderLawFixed.ReductionRigidity"

p2m_open "ModularCurve.PlaceSpecialization~IsInftySide~jFun~IsCuspidal~IsZeroSide" in open ModularCurve  in

theorem solution
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q} (hqN : ¬ q ∣ N)
    (P P' : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : PlaceSpecialization.ProlongationTuple P) (hmodel : R.IsModel) (hO : R.OrderLawFixed)
    (R' : PlaceSpecialization.ProlongationTuple P') (hmodel' : R'.IsModel) (hO' : R'.OrderLawFixed) :
    P = P' := by
  have hsp : P.sp = P'.sp := ReductionRigidity.sp_eq hqN P P' R hmodel hO R' hmodel' hO'
  have hpic : P.spPic0 = P'.spPic0 := PlaceSpecialization.spPic0_eq_of_sp_eq P P' hsp
  clear hmodel hO hmodel' hO'
  clear R R'
  obtain ⟨sp, pic, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := P
  obtain ⟨sp', pic', _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := P'
  change sp = sp' at hsp
  change pic = pic' at hpic
  subst hsp hpic
  rfl

#print axioms solution

end S_ModularCurve_PlaceSpecialization_eq_of_isModel_of_orderLawFixed
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_eq_of_isModel_of_orderLawFixed (solution)
