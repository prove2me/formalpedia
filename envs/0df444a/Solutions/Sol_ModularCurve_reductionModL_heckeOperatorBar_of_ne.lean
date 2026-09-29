-- Prove2me | solution 1 for ModularCurve.reductionModL_heckeOperatorBar_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/710e70bb-0ee0-5845-b7c0-4eda8444ad72

import Mathlib
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_AlgebraicCurve_Pic0Congr
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_Divisor_mapDomain_pullbackAlong_eq_and_restrictAlong_eq_of_degZero
import Theorems.Thm_ModularCurve_relfinrank_modularFunctionFieldFullC_mul_dedekindPsi
import Theorems.Thm_ModularCurve_separableAlong_heckeAlphaC_heckeBetaC
import Theorems.Thm_ModularCurve_reductionInputsModL_of_not_dvd
import Theorems.Thm_ModularCurve_heckeInputsAlong_of_prime
import Theorems.Thm_ModularCurve_JZero_divisible
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_place_deg_eq_one_charLDegeneracyRoof
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul
import Theorems.Thm_ModularCurve_laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldFullC
import Theorems.Thm_AlgebraicCurve_finrankAlong_eq_relfinrank_fieldRange
import Theorems.Thm_AlgebraicCurve_fundamentalIdentityAlong
import Theorems.Thm_ModularCurve_finiteAlong_heckeAlphaBar_of_prime
import Theorems.Thm_ModularCurve_finiteAlong_heckeBetaBar_of_prime
import Theorems.Thm_ModularCurve_finiteAlong_heckeAlphaC
import Theorems.Thm_ModularCurve_finiteAlong_heckeBetaC
import Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
import Theorems.Thm_ModularCurve_dedekindPsi_pos
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Theorems.Thm_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_jqModC
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_reductionModL_heckeOperatorBar_of_ne
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree WeierstrassCurve.Affine.Point.instFinite ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe"
p2m_attr_erase "simp" "ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.dualHeckeRep_apply_apply"
p2m_attr_erase "simp" "ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply"
p2m_attr_erase "simp" "HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open AlgebraicCurve ModularCurve IntermediateField

namespace P2mSolRedHeckeNe

section ResidueAlgClosed

open IsLocalRing Polynomial

variable {L : Type*} [Field L] (A : ValuationSubring L)

theorem isAlgClosed_residueField [IsAlgClosed L] : IsAlgClosed (ResidueField A) := by
  refine IsAlgClosed.of_exists_root _ (fun f hf_monic hf_irr => ?_)
  have hf_lifts : f ∈ lifts (residue A) := by
    rw [lifts_iff_coeff_lifts]
    exact fun n => residue_surjective (f.coeff n)
  obtain ⟨g, hg_map, -, hg_monic⟩ := lifts_and_degree_eq_and_monic hf_lifts hf_monic
  have hgL_deg : (g.map (algebraMap A L)).degree ≠ 0 := by
    rw [hg_monic.degree_map]
    intro h0
    have hg_nat : g.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h0)
    have hf_deg : f.natDegree = 0 := by
      rw [← hg_map, hg_monic.natDegree_map]
      exact hg_nat
    have hf1 : f = 1 := (hf_monic.natDegree_eq_zero).mp hf_deg
    exact hf_irr.not_isUnit (by rw [hf1]; exact isUnit_one)
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root _ hgL_deg
  have hα_int : IsIntegral A α := by
    refine ⟨g, hg_monic, ?_⟩
    rwa [IsRoot.def, eval_map] at hα
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hα_int
  refine ⟨residue A a, ?_⟩
  have hga : g.eval a = 0 := by
    have : algebraMap A L (g.eval a) = 0 := by
      have hcomm : algebraMap A L (g.eval a) = (g.map (algebraMap A L)).eval α := by
        rw [← ha, eval_map, eval₂_hom]
      rw [hcomm]
      exact hα
    exact (map_eq_zero_iff _ Subtype.coe_injective).mp this
  have : f.eval (residue A a) = residue A (g.eval a) := by
    rw [← hg_map, eval_map, eval₂_hom]
  rw [this, hga, map_zero]

end ResidueAlgClosed

section Generic

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem pullbackAlong_apply_eq_ord [HasPrincipalDivisors K F'] (φ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) {f : F} {D : Divisor K F} (hD : ∀ v, D v = v.ord f)
    (w : Place K F') : Divisor.pullbackAlong φ hφ D w = w.ord (φ f) := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact Divisor.pullback_apply_eq_ord hD w

theorem coe_equivOfEq_toRingEquiv_symm_apply {L E : Type*} [Field L] [Field E] [Algebra L E]
    {S T : IntermediateField L E} (h : S = T) (x : T) :
    (((IntermediateField.equivOfEq h).toRingEquiv.symm x : S) : E) = (x : E) := by
  subst h; rfl

variable (e : F ≃+* F') (he : ∀ a : K, e (algebraMap K F a) = algebraMap K F' a)

theorem congr_symm_eq_mapDomain (D : Divisor K F') :
    (Divisor.congr e he).symm D = Finsupp.mapDomain (fun w => (Place.congrEquiv e he).symm w) D := by
  show (Finsupp.domCongr (Place.congrEquiv e he)).symm D = _
  rw [Finsupp.domCongr_symm, Finsupp.domCongr_apply, Finsupp.equivMapDomain_eq_mapDomain]

theorem congr_symm_apply_eq_ord {f' : F'} {D : Divisor K F'} (hD : ∀ w, D w = w.ord f')
    (v : Place K F) : (Divisor.congr e he).symm D v = v.ord (e.symm f') := by
  rw [Divisor.congr_symm_apply_place, hD]
  have h := Place.ord_congrRingEquiv e he v (e.symm f')
  rwa [e.apply_symm_apply] at h

theorem int_eq_zero_of_forall_dvd {a : ℤ} (h : ∀ n : ℕ, n ≠ 0 → (n : ℤ) ∣ a) : a = 0 :=
  Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (h (a.natAbs + 1) (Nat.succ_ne_zero _))
    (by rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _)

theorem agree_of_agree_on_generators {X : Type*} (S : Set (Divisor K F))
    (hgen : Divisor.principal (K := K) (F := F) ≤ AddSubgroup.closure S)
    (Φ₁ Φ₂ : Divisor K F →+ (X →₀ ℤ)) (hagree : ∀ D ∈ S, Φ₁ D = Φ₂ D)
    (hdiv : ∀ n : ℕ, n ≠ 0 → ∀ x : Pic0 K F, ∃ y : Pic0 K F, n • y = x)
    {D : Divisor K F} (hD : D ∈ Divisor.degZero (K := K) (F := F)) : Φ₁ D = Φ₂ D := by
  classical
  set δ : Divisor K F →+ (X →₀ ℤ) := Φ₁ - Φ₂ with hδ
  have hδapp : ∀ E, δ E = Φ₁ E - Φ₂ E := fun E => rfl
  have hδprin : ∀ E ∈ Divisor.principal (K := K) (F := F), δ E = 0 := by
    intro E hE
    have hE' := hgen hE
    clear hE
    induction hE' using AddSubgroup.closure_induction with
    | mem E hE => rw [hδapp, hagree E hE, sub_self]
    | zero => exact map_zero δ
    | add E E' _ _ hE hE' => rw [map_add, hE, hE', add_zero]
    | neg E _ hE => rw [map_neg, hE, neg_zero]
  suffices h0 : δ D = 0 by rwa [hδapp, sub_eq_zero] at h0
  ext Q
  rw [Finsupp.zero_apply]
  refine int_eq_zero_of_forall_dvd fun n hn => ?_
  obtain ⟨y, hy⟩ := hdiv n hn (Pic0.mk ⟨D, hD⟩)
  obtain ⟨E, rfl⟩ := Pic0.mk_surjective y
  have hmem : ((⟨D, hD⟩ : Divisor.degZero (K := K) (F := F)) - n • E :
      Divisor.degZero (K := K) (F := F)) ∈
        (Divisor.principal (K := K) (F := F)).addSubgroupOf (Divisor.degZero (K := K) (F := F)) := by
    rw [← QuotientAddGroup.eq_iff_sub_mem, QuotientAddGroup.mk_nsmul]
    exact hy.symm
  rw [AddSubgroup.mem_addSubgroupOf, AddSubgroupClass.coe_sub, AddSubgroupClass.coe_nsmul] at hmem
  have h0 := hδprin _ hmem
  rw [map_sub, map_nsmul, sub_eq_zero] at h0
  refine ⟨δ (E : Divisor K F) Q, ?_⟩
  rw [h0, Finsupp.smul_apply, nsmul_eq_mul]

end Generic

section Modular

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

variable (N : ℕ) [NeZero N] {ℓ : ℕ} [hℓ : Fact ℓ.Prime]
variable (A : ValuationSubring (AlgebraicClosure ℚ))
variable {k : Type*} [Field k] [IsAlgClosed k] [CharP k ℓ] (π : A →+* k)
variable (q : ℕ) [NeZero q] [hqF : Fact q.Prime]

local notation "ℚ̄" => AlgebraicClosure ℚ

theorem commutes_toRingEquiv {E : Type*} [Field E] [Algebra k E] {S T : IntermediateField k E}
    (e : S ≃ₐ[k] T) : ∀ a : k, e.toRingEquiv (algebraMap k S a) = algebraMap k T a :=
  fun a => e.commutes a

variable {N q}

theorem spec_apply {M : ℕ} [NeZero M]
    {r : Place ℚ̄ (modularFunctionFieldBar M) → Place k (modularFunctionFieldFullC k M)}
    (hr : IsPlaceReductionAlong A π M r) (y : LaurentSeries A)
    (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M)
    (hyk : coeffMap π y ∈ modularFunctionFieldFullC k M) (hne : coeffMap π y ≠ 0)
    (D : Divisor ℚ̄ (modularFunctionFieldBar M))
    (hD : ∀ P, D P = P.ord (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar M))
    (Q : Place k (modularFunctionFieldFullC k M)) :
    Finsupp.mapDomain r D Q = Q.ord (⟨coeffMap π y, hyk⟩ : modularFunctionFieldFullC k M) :=
  hr.2 y hy hyk hne D hD Q

variable (hE : modularFunctionFieldC k N = modularFunctionFieldFullC k N)
variable (hR : charLDegeneracyRoof k N q = modularFunctionFieldFullC k (N * q))

def πC (Q : Place k (modularFunctionFieldFullC k N)) : Place k (modularFunctionFieldC k N) :=
  (Place.congrEquiv (equivOfEq hE).toRingEquiv (commutes_toRingEquiv (equivOfEq hE))).symm Q

def πR (Q : Place k (modularFunctionFieldFullC k (N * q))) : Place k (charLDegeneracyRoof k N q) :=
  (Place.congrEquiv (equivOfEq hR).toRingEquiv (commutes_toRingEquiv (equivOfEq hR))).symm Q

theorem mapDomain_πC (D : Divisor k (modularFunctionFieldFullC k N)) :
    Finsupp.mapDomain (πC hE) D =
      (Divisor.congr (equivOfEq hE).toRingEquiv (commutes_toRingEquiv (equivOfEq hE))).symm D :=
  (congr_symm_eq_mapDomain _ _ D).symm

theorem mapDomain_πR (D : Divisor k (modularFunctionFieldFullC k (N * q))) :
    Finsupp.mapDomain (πR hR) D =
      (Divisor.congr (equivOfEq hR).toRingEquiv (commutes_toRingEquiv (equivOfEq hR))).symm D :=
  (congr_symm_eq_mapDomain _ _ D).symm

theorem πC_injective : Function.Injective (πC hE) :=
  (Place.congrEquiv _ _).symm.injective

theorem gen_alpha
    {ρ : Place ℚ̄ (modularFunctionFieldBar N) → Place k (modularFunctionFieldFullC k N)}
    (hρ : IsPlaceReductionAlong A π N ρ)
    {ρ' : Place ℚ̄ (modularFunctionFieldBar (N * q)) → Place k (modularFunctionFieldFullC k (N * q))}
    (hρ' : IsPlaceReductionAlong A π (N * q) ρ')
    (hαq : HeckeAlphaBarIntegral ℚ̄ N q)
    [HasPrincipalDivisors ℚ̄ (modularFunctionFieldBar (N * q))]
    [HasPrincipalDivisors k (charLDegeneracyRoof k N q)]
    (hαc : HeckeAlphaCIntegral k N q)
    (D : Divisor ℚ̄ (modularFunctionFieldBar N)) (hDS : D ∈ integralPrincipalDivisors A π N) :
    Finsupp.mapDomain (πR hR ∘ ρ') (Divisor.pullbackAlong (heckeAlphaBar ℚ̄ N q) hαq D) =
      Divisor.pullbackAlong (heckeAlphaC k N q) hαc (Finsupp.mapDomain (πC hE ∘ ρ) D) := by
  obtain ⟨y, hy, hyk, hne, hD⟩ := hDS

  have hy' : coeffMap A.subtype y ∈ modularFunctionFieldBar (N * q) := by
    have := (heckeAlphaBar ℚ̄ N q ⟨coeffMap A.subtype y, hy⟩).2
    rwa [coe_heckeAlphaBar] at this
  have hαy : heckeAlphaBar ℚ̄ N q ⟨coeffMap A.subtype y, hy⟩ = ⟨coeffMap A.subtype y, hy'⟩ :=
    Subtype.ext (coe_heckeAlphaBar N q _)
  have hD' : ∀ W, Divisor.pullbackAlong (heckeAlphaBar ℚ̄ N q) hαq D W =
      W.ord (⟨coeffMap A.subtype y, hy'⟩ : modularFunctionFieldBar (N * q)) := fun W => by
    rw [pullbackAlong_apply_eq_ord _ hαq hD W, hαy]
  have hyk' : coeffMap π y ∈ modularFunctionFieldFullC k (N * q) :=
    full_degeneracyC_le k (dvd_mul_right N q) hyk
  have E1 : ∀ Q, Finsupp.mapDomain ρ' (Divisor.pullbackAlong (heckeAlphaBar ℚ̄ N q) hαq D) Q =
      Q.ord (⟨coeffMap π y, hyk'⟩ : modularFunctionFieldFullC k (N * q)) :=
    spec_apply A π hρ' y hy' hyk' hne _ hD'
  have E2 : ∀ Q, Finsupp.mapDomain ρ D Q =
      Q.ord (⟨coeffMap π y, hyk⟩ : modularFunctionFieldFullC k N) :=
    spec_apply A π hρ y hy hyk hne D hD
  have L : ∀ Y, Finsupp.mapDomain (πR hR ∘ ρ') (Divisor.pullbackAlong (heckeAlphaBar ℚ̄ N q) hαq D) Y =
      Y.ord ((equivOfEq hR).toRingEquiv.symm ⟨coeffMap π y, hyk'⟩) := fun Y => by
    rw [Finsupp.mapDomain_comp, mapDomain_πR]
    exact congr_symm_apply_eq_ord (equivOfEq hR).toRingEquiv (commutes_toRingEquiv (equivOfEq hR)) E1 Y
  have E3 : ∀ v, Finsupp.mapDomain (πC hE ∘ ρ) D v =
      v.ord ((equivOfEq hE).toRingEquiv.symm ⟨coeffMap π y, hyk⟩) := fun v => by
    rw [Finsupp.mapDomain_comp, mapDomain_πC]
    exact congr_symm_apply_eq_ord (equivOfEq hE).toRingEquiv (commutes_toRingEquiv (equivOfEq hE)) E2 v
  have Rt : ∀ Y, Divisor.pullbackAlong (heckeAlphaC k N q) hαc (Finsupp.mapDomain (πC hE ∘ ρ) D) Y =
      Y.ord (heckeAlphaC k N q ((equivOfEq hE).toRingEquiv.symm ⟨coeffMap π y, hyk⟩)) :=
    pullbackAlong_apply_eq_ord _ hαc E3
  have hel : (equivOfEq hR).toRingEquiv.symm ⟨coeffMap π y, hyk'⟩ =
      heckeAlphaC k N q ((equivOfEq hE).toRingEquiv.symm ⟨coeffMap π y, hyk⟩) := by
    apply Subtype.ext
    rw [coe_equivOfEq_toRingEquiv_symm_apply, coe_heckeAlphaC, coe_equivOfEq_toRingEquiv_symm_apply]
  ext Y
  rw [L, Rt, hel]

theorem gen_beta
    {ρ : Place ℚ̄ (modularFunctionFieldBar N) → Place k (modularFunctionFieldFullC k N)}
    (hρ : IsPlaceReductionAlong A π N ρ)
    {ρ' : Place ℚ̄ (modularFunctionFieldBar (N * q)) → Place k (modularFunctionFieldFullC k (N * q))}
    (hρ' : IsPlaceReductionAlong A π (N * q) ρ')
    (hβq : HeckeBetaBarIntegral ℚ̄ N q)
    [HasPrincipalDivisors ℚ̄ (modularFunctionFieldBar (N * q))]
    [HasPrincipalDivisors k (charLDegeneracyRoof k N q)]
    (hβc : HeckeBetaCIntegral k N q)
    (D : Divisor ℚ̄ (modularFunctionFieldBar N)) (hDS : D ∈ integralPrincipalDivisors A π N) :
    Finsupp.mapDomain (πR hR ∘ ρ') (Divisor.pullbackAlong (heckeBetaBar ℚ̄ N q) hβq D) =
      Divisor.pullbackAlong (heckeBetaC k N q) hβc (Finsupp.mapDomain (πC hE ∘ ρ) D) := by
  obtain ⟨y, hy, hyk, hne, hD⟩ := hDS

  set y₂ : LaurentSeries A := qExpand A q y with hy₂def
  have hcoe : coeffMap A.subtype y₂ = qExpand ℚ̄ q (coeffMap A.subtype y) := coeffMap_qExpand _ q y
  have hy' : coeffMap A.subtype y₂ ∈ modularFunctionFieldBar (N * q) := by
    have := (heckeBetaBar ℚ̄ N q ⟨coeffMap A.subtype y, hy⟩).2
    rwa [coe_heckeBetaBar, ← hcoe] at this
  have hβy : heckeBetaBar ℚ̄ N q ⟨coeffMap A.subtype y, hy⟩ = ⟨coeffMap A.subtype y₂, hy'⟩ :=
    Subtype.ext (by rw [coe_heckeBetaBar]; exact hcoe.symm)
  have hD' : ∀ W, Divisor.pullbackAlong (heckeBetaBar ℚ̄ N q) hβq D W =
      W.ord (⟨coeffMap A.subtype y₂, hy'⟩ : modularFunctionFieldBar (N * q)) := fun W => by
    rw [pullbackAlong_apply_eq_ord _ hβq hD W, hβy]
  have hcoek : coeffMap π y₂ = qExpand k q (coeffMap π y) := coeffMap_qExpand _ q y
  have hyk' : coeffMap π y₂ ∈ modularFunctionFieldFullC k (N * q) := by
    rw [hcoek]
    exact full_degeneracyC_map_le k N q ⟨coeffMap π y, hyk, rfl⟩
  have hne' : coeffMap π y₂ ≠ 0 := by
    rw [hcoek]
    intro h0
    exact hne (qExpand_injective q (by rw [h0, map_zero]))
  have E1 : ∀ Q, Finsupp.mapDomain ρ' (Divisor.pullbackAlong (heckeBetaBar ℚ̄ N q) hβq D) Q =
      Q.ord (⟨coeffMap π y₂, hyk'⟩ : modularFunctionFieldFullC k (N * q)) :=
    spec_apply A π hρ' y₂ hy' hyk' hne' _ hD'
  have E2 : ∀ Q, Finsupp.mapDomain ρ D Q =
      Q.ord (⟨coeffMap π y, hyk⟩ : modularFunctionFieldFullC k N) :=
    spec_apply A π hρ y hy hyk hne D hD
  have L : ∀ Y, Finsupp.mapDomain (πR hR ∘ ρ') (Divisor.pullbackAlong (heckeBetaBar ℚ̄ N q) hβq D) Y =
      Y.ord ((equivOfEq hR).toRingEquiv.symm ⟨coeffMap π y₂, hyk'⟩) := fun Y => by
    rw [Finsupp.mapDomain_comp, mapDomain_πR]
    exact congr_symm_apply_eq_ord (equivOfEq hR).toRingEquiv (commutes_toRingEquiv (equivOfEq hR)) E1 Y
  have E3 : ∀ v, Finsupp.mapDomain (πC hE ∘ ρ) D v =
      v.ord ((equivOfEq hE).toRingEquiv.symm ⟨coeffMap π y, hyk⟩) := fun v => by
    rw [Finsupp.mapDomain_comp, mapDomain_πC]
    exact congr_symm_apply_eq_ord (equivOfEq hE).toRingEquiv (commutes_toRingEquiv (equivOfEq hE)) E2 v
  have Rt : ∀ Y, Divisor.pullbackAlong (heckeBetaC k N q) hβc (Finsupp.mapDomain (πC hE ∘ ρ) D) Y =
      Y.ord (heckeBetaC k N q ((equivOfEq hE).toRingEquiv.symm ⟨coeffMap π y, hyk⟩)) :=
    pullbackAlong_apply_eq_ord _ hβc E3
  have hel : (equivOfEq hR).toRingEquiv.symm ⟨coeffMap π y₂, hyk'⟩ =
      heckeBetaC k N q ((equivOfEq hE).toRingEquiv.symm ⟨coeffMap π y, hyk⟩) := by
    apply Subtype.ext
    rw [coe_equivOfEq_toRingEquiv_symm_apply, coe_heckeBetaC, coe_equivOfEq_toRingEquiv_symm_apply]
    exact hcoek
  ext Y
  rw [L, Rt, hel]

theorem val_comp_alphaBar_apply (f : modularFunctionFieldBar N) :
    ((modularFunctionFieldBar (N * q)).val.comp (heckeAlphaBar ℚ̄ N q)) f = (f : LaurentSeries ℚ̄) := by
  rw [AlgHom.comp_apply, IntermediateField.coe_val]
  exact coe_heckeAlphaBar N q f

theorem val_comp_betaBar_apply (f : modularFunctionFieldBar N) :
    ((modularFunctionFieldBar (N * q)).val.comp (heckeBetaBar ℚ̄ N q)) f =
      qExpand ℚ̄ q (f : LaurentSeries ℚ̄) := by
  rw [AlgHom.comp_apply, IntermediateField.coe_val]
  exact coe_heckeBetaBar N q f

theorem val_comp_alphaC_apply (f : modularFunctionFieldC k N) :
    ((charLDegeneracyRoof k N q).val.comp (heckeAlphaC k N q)) f = (f : LaurentSeries k) := by
  rw [AlgHom.comp_apply, IntermediateField.coe_val]
  exact coe_heckeAlphaC k N q f

theorem val_comp_betaC_apply (f : modularFunctionFieldC k N) :
    ((charLDegeneracyRoof k N q).val.comp (heckeBetaC k N q)) f = qExpand k q (f : LaurentSeries k) := by
  rw [AlgHom.comp_apply, IntermediateField.coe_val]
  exact coe_heckeBetaC k N q f

theorem fieldRange_alphaBar :
    ((modularFunctionFieldBar (N * q)).val.comp (heckeAlphaBar ℚ̄ N q)).fieldRange =
      modularFunctionFieldBar N := by
  ext x
  rw [AlgHom.mem_fieldRange]
  constructor
  · rintro ⟨f, hf⟩
    rw [val_comp_alphaBar_apply] at hf
    rw [← hf]
    exact f.2
  · intro hx
    exact ⟨⟨x, hx⟩, val_comp_alphaBar_apply ⟨x, hx⟩⟩

theorem fieldRange_betaBar :
    ((modularFunctionFieldBar (N * q)).val.comp (heckeBetaBar ℚ̄ N q)).fieldRange =
      (modularFunctionFieldBar N).map (qExpandAlgHomC ℚ̄ q) := by
  ext x
  rw [AlgHom.mem_fieldRange, IntermediateField.mem_map]
  constructor
  · rintro ⟨f, hf⟩
    rw [val_comp_betaBar_apply] at hf
    exact ⟨f, f.2, hf⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨⟨f, hf⟩, val_comp_betaBar_apply ⟨f, hf⟩⟩

theorem fieldRange_alphaC :
    ((charLDegeneracyRoof k N q).val.comp (heckeAlphaC k N q)).fieldRange = modularFunctionFieldC k N := by
  ext x
  rw [AlgHom.mem_fieldRange]
  constructor
  · rintro ⟨f, hf⟩
    rw [val_comp_alphaC_apply] at hf
    rw [← hf]
    exact f.2
  · intro hx
    exact ⟨⟨x, hx⟩, val_comp_alphaC_apply ⟨x, hx⟩⟩

theorem fieldRange_betaC :
    ((charLDegeneracyRoof k N q).val.comp (heckeBetaC k N q)).fieldRange =
      (modularFunctionFieldC k N).map (qExpandAlgHomC k q) := by
  ext x
  rw [AlgHom.mem_fieldRange, IntermediateField.mem_map]
  constructor
  · rintro ⟨f, hf⟩
    rw [val_comp_betaC_apply] at hf
    exact ⟨f, f.2, hf⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨⟨f, hf⟩, val_comp_betaC_apply ⟨f, hf⟩⟩

variable (N q) in
include hE hR in

theorem finrankAlong_legs_eq (hℓNq : ¬ ℓ ∣ N * q) :
    finrankAlong ℚ̄ (heckeAlphaBar ℚ̄ N q) = finrankAlong k (heckeAlphaC k N q) ∧
    finrankAlong ℚ̄ (heckeBetaBar ℚ̄ N q) = finrankAlong k (heckeBetaC k N q) := by
  have hψ : 0 < dedekindPsi N := dedekindPsi_pos N (NeZero.ne N)
  have hNq0 : ((N * q : ℕ) : ℚ̄) ≠ 0 := by exact_mod_cast (NeZero.ne (N * q))
  have hNqk : ((N * q : ℕ) : k) ≠ 0 := by
    intro h0
    exact hℓNq ((CharP.cast_eq_zero_iff k ℓ (N * q)).mp h0)
  obtain ⟨hA0, hB0⟩ := relfinrank_modularFunctionFieldFullC_mul_dedekindPsi ℚ̄ N q hNq0
  obtain ⟨hAk, hBk⟩ := relfinrank_modularFunctionFieldFullC_mul_dedekindPsi k N q hNqk
  have hFN := laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldFullC ℚ̄ N
  have hFNq := laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldFullC ℚ̄ (N * q)
  constructor
  · have h0 : finrankAlong ℚ̄ (heckeAlphaBar ℚ̄ N q) =
        relfinrank (modularFunctionFieldFullC ℚ̄ N) (modularFunctionFieldFullC ℚ̄ (N * q)) := by
      have h := finrankAlong_eq_relfinrank_fieldRange (modularFunctionFieldBar N)
        (modularFunctionFieldBar (N * q)) (heckeAlphaBar ℚ̄ N q)
      have h1 : relfinrank ((modularFunctionFieldBar (N * q)).val.comp (heckeAlphaBar ℚ̄ N q)).fieldRange
            (modularFunctionFieldBar (N * q)) =
          relfinrank (modularFunctionFieldBar N) (modularFunctionFieldBar (N * q)) := by
        congr 1
        exact fieldRange_alphaBar
      have h2 : relfinrank (modularFunctionFieldBar N) (modularFunctionFieldBar (N * q)) =
          relfinrank (modularFunctionFieldFullC ℚ̄ N) (modularFunctionFieldFullC ℚ̄ (N * q)) := by
        show relfinrank (laurentBaseChange ℚ̄ (modularFunctionFieldFull N))
          (laurentBaseChange ℚ̄ (modularFunctionFieldFull (N * q))) = _
        rw [hFN, hFNq]
      exact (h.trans h1).trans h2
    have hk : finrankAlong k (heckeAlphaC k N q) =
        relfinrank (modularFunctionFieldFullC k N) (modularFunctionFieldFullC k (N * q)) := by
      have h := finrankAlong_eq_relfinrank_fieldRange (modularFunctionFieldC k N)
        (charLDegeneracyRoof k N q) (heckeAlphaC k N q)
      have h1 : relfinrank ((charLDegeneracyRoof k N q).val.comp (heckeAlphaC k N q)).fieldRange
            (charLDegeneracyRoof k N q) =
          relfinrank (modularFunctionFieldC k N) (charLDegeneracyRoof k N q) := by
        congr 1
        exact fieldRange_alphaC
      have h2 : relfinrank (modularFunctionFieldC k N) (charLDegeneracyRoof k N q) =
          relfinrank (modularFunctionFieldFullC k N) (modularFunctionFieldFullC k (N * q)) := by
        rw [hE, hR]
      exact (h.trans h1).trans h2
    rw [h0, hk]
    exact Nat.eq_of_mul_eq_mul_right hψ (hA0.trans hAk.symm)
  · have h0 : finrankAlong ℚ̄ (heckeBetaBar ℚ̄ N q) =
        relfinrank ((modularFunctionFieldFullC ℚ̄ N).map (qExpandAlgHomC ℚ̄ q))
          (modularFunctionFieldFullC ℚ̄ (N * q)) := by
      have h := finrankAlong_eq_relfinrank_fieldRange (modularFunctionFieldBar N)
        (modularFunctionFieldBar (N * q)) (heckeBetaBar ℚ̄ N q)
      have h1 : relfinrank ((modularFunctionFieldBar (N * q)).val.comp (heckeBetaBar ℚ̄ N q)).fieldRange
            (modularFunctionFieldBar (N * q)) =
          relfinrank ((modularFunctionFieldBar N).map (qExpandAlgHomC ℚ̄ q))
            (modularFunctionFieldBar (N * q)) := by
        congr 1
        exact fieldRange_betaBar
      have h2 : relfinrank ((modularFunctionFieldBar N).map (qExpandAlgHomC ℚ̄ q))
            (modularFunctionFieldBar (N * q)) =
          relfinrank ((modularFunctionFieldFullC ℚ̄ N).map (qExpandAlgHomC ℚ̄ q))
            (modularFunctionFieldFullC ℚ̄ (N * q)) := by
        show relfinrank ((laurentBaseChange ℚ̄ (modularFunctionFieldFull N)).map (qExpandAlgHomC ℚ̄ q))
          (laurentBaseChange ℚ̄ (modularFunctionFieldFull (N * q))) = _
        rw [hFN, hFNq]
      exact (h.trans h1).trans h2
    have hk : finrankAlong k (heckeBetaC k N q) =
        relfinrank ((modularFunctionFieldFullC k N).map (qExpandAlgHomC k q))
          (modularFunctionFieldFullC k (N * q)) := by
      have h := finrankAlong_eq_relfinrank_fieldRange (modularFunctionFieldC k N)
        (charLDegeneracyRoof k N q) (heckeBetaC k N q)
      have h1 : relfinrank ((charLDegeneracyRoof k N q).val.comp (heckeBetaC k N q)).fieldRange
            (charLDegeneracyRoof k N q) =
          relfinrank ((modularFunctionFieldC k N).map (qExpandAlgHomC k q)) (charLDegeneracyRoof k N q) := by
        congr 1
        exact fieldRange_betaC
      have h2 : relfinrank ((modularFunctionFieldC k N).map (qExpandAlgHomC k q)) (charLDegeneracyRoof k N q) =
          relfinrank ((modularFunctionFieldFullC k N).map (qExpandAlgHomC k q))
            (modularFunctionFieldFullC k (N * q)) := by
        rw [hE, hR]
      exact (h.trans h1).trans h2
    rw [h0, hk]
    exact Nat.eq_of_mul_eq_mul_right hψ (hB0.trans hBk.symm)

theorem exists_ord_jbar_ne_zero
    [FiniteDimensional
      (IntermediateField.adjoin k
        ({(⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)} :
          Set (modularFunctionFieldC k N)))
      (modularFunctionFieldC k N)] :
    ∃ Q : Place k (modularFunctionFieldC k N),
      Q.ord (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ≠ 0 := by
  by_contra hall
  push Not at hall
  have hj : Transcendental k (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) := by
    intro halg
    apply transcendental_jqModC k
    exact halg.algHom (modularFunctionFieldC k N).val
  have hmem := Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
    (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) hj hall
  obtain ⟨c, hc⟩ := hmem
  exact hj (hc ▸ isAlgebraic_algebraMap c)

variable (N q) in

theorem main (hℓN : ¬ ℓ ∣ N) (h : ReductionInputsAlong A π N) (hq : q.Prime) (hqℓ : q ≠ ℓ)
    (h' : ReductionInputsAlong A π (N * q)) (hf : HeckeInputsFibre k N q)
    (hfd : FiniteDimensional
      (IntermediateField.adjoin k
        ({(⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)} :
          Set (modularFunctionFieldC k N)))
      (modularFunctionFieldC k N))
    (z : Pic0 ℚ̄ (modularFunctionFieldBar N)) :
    reductionAlong A π N (heckeOperatorBar N ⟨q, hq⟩ z) =
      Pic0.congr (equivOfEq hE).toRingEquiv (fun a => (equivOfEq hE).commutes a)
        (heckePic0Fibre k N q
          ((Pic0.congr (equivOfEq hE).toRingEquiv (fun a => (equivOfEq hE).commutes a)).symm
            (reductionAlong A π N z))) := by
  classical
  have hℓNq : ¬ ℓ ∣ N * q := by
    intro hdvd
    rcases (Nat.Prime.dvd_mul hℓ.out).mp hdvd with h1 | h2
    · exact hℓN h1
    · exact hqℓ ((Nat.prime_dvd_prime_iff_eq hℓ.out hq).mp h2).symm
  have hR : charLDegeneracyRoof k N q = modularFunctionFieldFullC k (N * q) :=
    charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul k ℓ N q hℓNq

  obtain ⟨hαq, hβq, hPq, hfin, hFIβ, hNα⟩ := heckeInputsAlong_of_prime ℚ̄ N q
  obtain ⟨hP, hβc, hαc, hdesc⟩ := hf

  set ρ := h.choose with hρdef
  have hρ : IsPlaceReductionAlong A π N ρ := h.choose_spec.1
  have hgen : PrincipalGeneratedByIntegral A π N := h.choose_spec.2
  set ρ' := h'.choose with hρ'def
  have hρ' : IsPlaceReductionAlong A π (N * q) ρ' := h'.choose_spec.1
  set r₁ : Place ℚ̄ (modularFunctionFieldBar N) → Place k (modularFunctionFieldC k N) :=
    πC hE ∘ ρ with hr₁def
  set r : Place ℚ̄ (modularFunctionFieldBar (N * q)) → Place k (charLDegeneracyRoof k N q) :=
    πR hR ∘ ρ' with hrdef

  haveI := isCurveOver_modularFunctionFieldC_of_perfectField k N
  have h1F₁ : ∀ v : Place ℚ̄ (modularFunctionFieldBar N), v.deg = 1 := deg_eq_one_modularFunctionFieldBar N
  have h1F₂ : ∀ W : Place ℚ̄ (modularFunctionFieldBar (N * q)), W.deg = 1 :=
    deg_eq_one_modularFunctionFieldBar (N * q)
  have h1C₁ : ∀ Q : Place k (modularFunctionFieldC k N), Q.deg = 1 := fun Q =>
    IsCurveOver.deg_eq_one_of_isAlgClosed (K := k) Q
  have h1C₂ : ∀ Y : Place k (charLDegeneracyRoof k N q), Y.deg = 1 :=
    place_deg_eq_one_charLDegeneracyRoof k N q

  have hdiv : ∀ n : ℕ, n ≠ 0 → ∀ x : Pic0 ℚ̄ (modularFunctionFieldBar N),
      ∃ y : Pic0 ℚ̄ (modularFunctionFieldBar N), n • y = x := JZero.divisible N

  have hcompatα : ∀ D : Divisor ℚ̄ (modularFunctionFieldBar N),
      D ∈ Divisor.degZero (K := ℚ̄) (F := modularFunctionFieldBar N) →
      Finsupp.mapDomain r (Divisor.pullbackAlong (heckeAlphaBar ℚ̄ N q) hαq D) =
        Divisor.pullbackAlong (heckeAlphaC k N q) hαc (Finsupp.mapDomain r₁ D) := by
    intro D hD
    have := agree_of_agree_on_generators (integralPrincipalDivisors A π N) hgen
      ((Finsupp.mapDomain.addMonoidHom r).comp (Divisor.pullbackAlong (heckeAlphaBar ℚ̄ N q) hαq))
      ((Divisor.pullbackAlong (heckeAlphaC k N q) hαc).comp (Finsupp.mapDomain.addMonoidHom r₁))
      (fun D hDS => by
        simpa only [AddMonoidHom.coe_comp, Function.comp_apply, Finsupp.mapDomain.addMonoidHom_apply]
          using gen_alpha A π hE hR hρ hρ' hαq hαc D hDS)
      hdiv hD
    simpa only [AddMonoidHom.coe_comp, Function.comp_apply, Finsupp.mapDomain.addMonoidHom_apply]
      using this
  have hcompatβ : ∀ D : Divisor ℚ̄ (modularFunctionFieldBar N),
      D ∈ Divisor.degZero (K := ℚ̄) (F := modularFunctionFieldBar N) →
      Finsupp.mapDomain r (Divisor.pullbackAlong (heckeBetaBar ℚ̄ N q) hβq D) =
        Divisor.pullbackAlong (heckeBetaC k N q) hβc (Finsupp.mapDomain r₁ D) := by
    intro D hD
    have := agree_of_agree_on_generators (integralPrincipalDivisors A π N) hgen
      ((Finsupp.mapDomain.addMonoidHom r).comp (Divisor.pullbackAlong (heckeBetaBar ℚ̄ N q) hβq))
      ((Divisor.pullbackAlong (heckeBetaC k N q) hβc).comp (Finsupp.mapDomain.addMonoidHom r₁))
      (fun D hDS => by
        simpa only [AddMonoidHom.coe_comp, Function.comp_apply, Finsupp.mapDomain.addMonoidHom_apply]
          using gen_beta A π hE hR hρ hρ' hβq hβc D hDS)
      hdiv hD
    simpa only [AddMonoidHom.coe_comp, Function.comp_apply, Finsupp.mapDomain.addMonoidHom_apply]
      using this

  haveI : CharZero (modularFunctionFieldBar N) :=
    charZero_of_injective_algebraMap (algebraMap ℚ̄ (modularFunctionFieldBar N)).injective
  have hFIα : FundamentalIdentityAlong ℚ̄ (heckeAlphaBar ℚ̄ N q) hαq :=
    fundamentalIdentityAlong _ hαq (finiteAlong_heckeAlphaBar_of_prime ℚ̄ N q)
      (separableAlong_of_charZero _ hαq)
  have hFIβ' : FundamentalIdentityAlong ℚ̄ (heckeBetaBar ℚ̄ N q) hβq :=
    fundamentalIdentityAlong _ hβq (finiteAlong_heckeBetaBar_of_prime ℚ̄ N q)
      (separableAlong_of_charZero _ hβq)
  obtain ⟨hsepα, hsepβ⟩ := separableAlong_heckeAlphaC_heckeBetaC k N q hℓNq
  have hFIαc : FundamentalIdentityAlong k (heckeAlphaC k N q) hαc :=
    fundamentalIdentityAlong _ hαc (finiteAlong_heckeAlphaC k N q) hsepα
  have hFIβc : FundamentalIdentityAlong k (heckeBetaC k N q) hβc :=
    fundamentalIdentityAlong _ hβc (finiteAlong_heckeBetaC k N q) hsepβ
  obtain ⟨hdegα, hdegβ⟩ := finrankAlong_legs_eq N q hE hR hℓNq
  have hdegα' : ∀ v : Place ℚ̄ (modularFunctionFieldBar N),
      Divisor.degree (Divisor.pullbackAlong (heckeAlphaBar ℚ̄ N q) hαq (Finsupp.single v 1)) ≤
        Divisor.degree (Divisor.pullbackAlong (heckeAlphaC k N q) hαc (Finsupp.single (r₁ v) 1)) := by
    intro v
    rw [Divisor.degree_pullbackAlong _ hαq hFIα, Divisor.degree_pullbackAlong _ hαc hFIαc,
      Divisor.degree_single, Divisor.degree_single, h1F₁, h1C₁, hdegα]
  have hdegβ' : ∀ v : Place ℚ̄ (modularFunctionFieldBar N),
      Divisor.degree (Divisor.pullbackAlong (heckeBetaBar ℚ̄ N q) hβq (Finsupp.single v 1)) ≤
        Divisor.degree (Divisor.pullbackAlong (heckeBetaC k N q) hβc (Finsupp.single (r₁ v) 1)) := by
    intro v
    rw [Divisor.degree_pullbackAlong _ hβq hFIβ', Divisor.degree_pullbackAlong _ hβc hFIβc,
      Divisor.degree_single, Divisor.degree_single, h1F₁, h1C₁, hdegβ]

  have hnc : ∀ v : Place ℚ̄ (modularFunctionFieldBar N), ∃ v', r₁ v' ≠ r₁ v := by
    intro v
    by_contra hall
    push Not at hall
    obtain ⟨Q, hQ⟩ := exists_ord_jbar_ne_zero (k := k) (N := N)

    haveI := hPq
    have hjmem : coeffMap A.subtype (jqModC A) ∈ modularFunctionFieldBar N := by
      rw [coeffMap_jqModC]
      show jqModC ℚ̄ ∈ laurentBaseChange ℚ̄ (modularFunctionFieldFull N)
      rw [laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldFullC]
      exact jqModC_mem_full ℚ̄ N
    have hjk : coeffMap π (jqModC A) ∈ modularFunctionFieldFullC k N := by
      rw [coeffMap_jqModC]; exact jqModC_mem_full k N
    have hjne : coeffMap π (jqModC A) ≠ 0 := by
      rw [coeffMap_jqModC]; exact jqModC_ne_zero_of_nontrivial k
    haveI := isCurveOver_modularFunctionFieldBar N
    haveI : HasPrincipalDivisors ℚ̄ (modularFunctionFieldBar N) := IsCurveOver.hasPrincipalDivisors
    have hj0 : (⟨coeffMap A.subtype (jqModC A), hjmem⟩ : modularFunctionFieldBar N) ≠ 0 := by
      intro h0
      have hval : coeffMap A.subtype (jqModC A) = 0 := by
        simpa using congrArg Subtype.val h0
      rw [coeffMap_jqModC] at hval
      exact jqModC_ne_zero_of_nontrivial ℚ̄ hval
    obtain ⟨Dj, hDj, hDj0⟩ := HasPrincipalDivisors.exists_divisor (K := ℚ̄) _ hj0
    have E2 : ∀ Q', Finsupp.mapDomain ρ Dj Q' =
        Q'.ord (⟨coeffMap π (jqModC A), hjk⟩ : modularFunctionFieldFullC k N) :=
      spec_apply A π hρ (jqModC A) hjmem hjk hjne Dj hDj
    have E3 : ∀ v', Finsupp.mapDomain r₁ Dj v' =
        v'.ord ((equivOfEq hE).toRingEquiv.symm ⟨coeffMap π (jqModC A), hjk⟩) := fun v' => by
      rw [hr₁def, Finsupp.mapDomain_comp, mapDomain_πC]
      exact congr_symm_apply_eq_ord (equivOfEq hE).toRingEquiv (commutes_toRingEquiv (equivOfEq hE)) E2 v'
    have hjC : (equivOfEq hE).toRingEquiv.symm ⟨coeffMap π (jqModC A), hjk⟩ =
        (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) := by
      apply Subtype.ext
      rw [coe_equivOfEq_toRingEquiv_symm_apply]
      exact coeffMap_jqModC π

    have hconst : ∀ D : Divisor ℚ̄ (modularFunctionFieldBar N),
        Finsupp.mapDomain r₁ D = Finsupp.single (r₁ v) (Divisor.degree D) := by
      intro D
      induction D using Finsupp.induction with
      | zero => simp
      | single_add P n D _ _ ih =>
        rw [Finsupp.mapDomain_add, ih, Finsupp.mapDomain_single, hall P, map_add,
          Divisor.degree_single, h1F₁, Nat.cast_one, mul_one, ← Finsupp.single_add, add_comm]
    have := E3 Q
    rw [hconst Dj, hDj0, Finsupp.single_zero, Finsupp.zero_apply, hjC] at this
    exact hQ this.symm

  obtain ⟨_, _, hpushα⟩ :=
    Divisor.mapDomain_pullbackAlong_eq_and_restrictAlong_eq_of_degZero
      (heckeAlphaBar ℚ̄ N q) hαq (heckeAlphaC k N q) hαc r₁ r h1F₁ h1F₂ h1C₁ h1C₂ hcompatα hdegα' hnc
  obtain ⟨hpullβ, _, _⟩ :=
    Divisor.mapDomain_pullbackAlong_eq_and_restrictAlong_eq_of_degZero
      (heckeBetaBar ℚ̄ N q) hβq (heckeBetaC k N q) hβc r₁ r h1F₁ h1F₂ h1C₁ h1C₂ hcompatβ hdegβ' hnc
  have hdiv_id : ∀ D : Divisor ℚ̄ (modularFunctionFieldBar N),
      Finsupp.mapDomain r₁ (Divisor.correspondence (heckeBetaBar ℚ̄ N q) (heckeAlphaBar ℚ̄ N q) hβq hαq D)
        = heckeDivFibre k N q hβc hαc (Finsupp.mapDomain r₁ D) := by
    intro D
    rw [Divisor.correspondence_apply, hpushα, hpullβ]
    rfl

  obtain ⟨D₀, rfl⟩ := Pic0.mk_surjective z

  show reductionAlong A π N (heckeOperatorBar N ⟨q, hq⟩ (Pic0.mk D₀)) =
    Pic0.congr (equivOfEq hE).toRingEquiv (commutes_toRingEquiv (equivOfEq hE)) (heckePic0Fibre k N q ((Pic0.congr (equivOfEq hE).toRingEquiv (commutes_toRingEquiv (equivOfEq hE))).symm (reductionAlong A π N (Pic0.mk D₀))))

  have hLHS : reductionAlong A π N (heckeOperatorBar N ⟨q, hq⟩ (Pic0.mk D₀)) =
      Pic0.mk (reductionDegZeroAlong ρ hρ.1
        (Pic0.degZeroCorrespondence (heckeBetaBar ℚ̄ N q) (heckeAlphaBar ℚ̄ N q) hβq hαq hFIβ D₀)) := by
    rw [heckeOperatorBar_apply]
    show reductionAlong A π N (heckeOperatorAlong ℚ̄ N q (Pic0.mk D₀)) = _
    rw [heckeOperatorAlong_eq hαq hβq hFIβ hfin hNα, heckePic0Bar, Pic0.correspondence_mk,
      reductionAlong_mk h]

  set Dz : Divisor.degZero (K := k) (F := modularFunctionFieldC k N) :=
    (Pic0.degZeroCongr (equivOfEq hE).toRingEquiv (commutes_toRingEquiv (equivOfEq hE))).symm (reductionDegZeroAlong ρ hρ.1 D₀) with hDzdef
  have hz : (Pic0.congr (equivOfEq hE).toRingEquiv (commutes_toRingEquiv (equivOfEq hE))).symm (reductionAlong A π N (Pic0.mk D₀)) = Pic0.mk Dz := by
    rw [AddEquiv.symm_apply_eq, reductionAlong_mk h]
    show _ = Pic0.mk (Pic0.degZeroCongr (equivOfEq hE).toRingEquiv (commutes_toRingEquiv (equivOfEq hE)) Dz)
    rw [hDzdef, AddEquiv.apply_symm_apply]
  have hcoeDz : (Dz : Divisor k (modularFunctionFieldC k N)) = Finsupp.mapDomain r₁ (D₀ : Divisor ℚ̄ _) := by
    rw [hDzdef, Pic0.coe_degZeroCongr_symm, coe_reductionDegZeroAlong, hr₁def, Finsupp.mapDomain_comp,
      mapDomain_πC]

  have hRHS : heckePic0Fibre k N q (Pic0.mk Dz) =
      Pic0.mk (Divisor.degZeroEnd (heckeDivFibre k N q hβc hαc) hdesc Dz) := by
    rw [heckePic0Fibre_eq k N q hβc hαc hdesc, AddMonoidHom.coe_toIntLinearMap,
      Divisor.toPic0End_mk _ hdesc]
  rw [hLHS, hz, hRHS]
  show _ = Pic0.mk (Pic0.degZeroCongr (equivOfEq hE).toRingEquiv (commutes_toRingEquiv (equivOfEq hE)) (Divisor.degZeroEnd (heckeDivFibre k N q hβc hαc) hdesc Dz))
  congr 1
  apply Subtype.ext
  rw [coe_reductionDegZeroAlong, Pic0.coe_degZeroCorrespondence, Pic0.coe_degZeroCongr,
    Divisor.coe_degZeroEnd, hcoeDz, ← hdiv_id, hr₁def, Finsupp.mapDomain_comp, mapDomain_πC,
    AddEquiv.apply_symm_apply]

end Modular

end P2mSolRedHeckeNe

end

open P2mSolRedHeckeNe in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution (N : ℕ) [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓN : ¬ ℓ ∣ N) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    [CharP (IsLocalRing.ResidueField A) ℓ] (h : ModularCurve.ReductionInputsModL A N)
    (q : ℕ) [NeZero q] (hq : q.Prime) (hqℓ : q ≠ ℓ)
    (hE : ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField A) N =
      ModularCurve.modularFunctionFieldFullC (IsLocalRing.ResidueField A) N)
    (hf : ModularCurve.HeckeInputsFibre (IsLocalRing.ResidueField A) N q) (z : ModularCurve.JZero N) :
    ModularCurve.reductionModL A N (ModularCurve.heckeOperatorBar N ⟨q, hq⟩ z) =
      AlgebraicCurve.Pic0.congr
        (IntermediateField.equivOfEq hE).toRingEquiv
        (fun a => (IntermediateField.equivOfEq hE).commutes a)
        (ModularCurve.heckePic0Fibre (IsLocalRing.ResidueField A) N q
          ((AlgebraicCurve.Pic0.congr
            (IntermediateField.equivOfEq hE).toRingEquiv
            (fun a => (IntermediateField.equivOfEq hE).commutes a)).symm
            (ModularCurve.reductionModL A N z))) := by
  haveI : IsAlgClosed (IsLocalRing.ResidueField A) := isAlgClosed_residueField A
  haveI : Fact q.Prime := ⟨hq⟩
  have hℓNq : ¬ ℓ ∣ N * q := by
    intro hdvd
    rcases (Nat.Prime.dvd_mul (Fact.out : ℓ.Prime)).mp hdvd with h1 | h2
    · exact hℓN h1
    · exact hqℓ ((Nat.prime_dvd_prime_iff_eq (Fact.out : ℓ.Prime) hq).mp h2).symm
  have h' : ModularCurve.ReductionInputsModL A (N * q) :=
    ModularCurve.reductionInputsModL_of_not_dvd (N * q) hℓNq A hA
  exact main N A (IsLocalRing.residue A) q hE hℓN h hq hqℓ h' hf
    (ModularCurve.finiteDimensional_adjoin_jqModC A) z

end S_ModularCurve_reductionModL_heckeOperatorBar_of_ne
end P2MW
export P2MW.S_ModularCurve_reductionModL_heckeOperatorBar_of_ne (solution)
