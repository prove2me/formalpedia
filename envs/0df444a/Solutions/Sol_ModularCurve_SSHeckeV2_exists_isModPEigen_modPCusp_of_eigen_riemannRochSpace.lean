-- Prove2me | solution 1 for ModularCurve.SSHeckeV2.exists_isModPEigen_modPCusp_of_eigen_riemannRochSpace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/acc9bf8f-5ac1-5234-9258-a12bcf574cf8

import Mathlib
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_ModularCurve_ModPFormFn
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_SwdAlgebra
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_WeightDivisor
import Definitions.Def_ModularCurve_SSCarrier
import Definitions.Def_ModularCurve_SSHeckeV2
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModPForms_exists_isModPFormFn_qexpOfWeight_eq_of_mem_modPMod
import Theorems.Thm_ModularCurve_stackOrd_nonneg_and_le_ord_of_isModPFormFn
import Theorems.Thm_ModularCurve_ord_unif
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidth_of_ord_pos
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg

import Theorems.Thm_ModularCurve_SSHeckeV2_heckeMultiplier_spec
import Theorems.Thm_ModularCurve_qexpOfWeight_trace_heckeBetaC_mul_pow_eq_heckePS_of_eq_smul_map
import Theorems.Thm_ModularCurve_isModPFormFn_of_mem_riemannRochSpace
import Theorems.Thm_ModularCurve_finiteDimensional_and_isSeparable_adjoin_jGeomGen_of_isSeparable_jqNModC
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero
import Theorems.Thm_ModPForms_exists_mem_modPMod_ofPowerSeries_eq_qexpOfWeight_of_isModPFormFn
import Theorems.Thm_ModPForms_exists_mem_modPCusp_ofPowerSeries_eq_qexpOfWeight_of_isModPCuspFormFn
import Theorems.Thm_ModularCurve_exists_divisor_forall_eq_weightFloor_fieldC
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charP_pos
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_SSHeckeV2_exists_isModPEigen_modPCusp_of_eigen_riemannRochSpace
p2m_attr_erase "instance" "ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup ModularCurve.instIsElliptic_tateLaurent ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree HeckeEis.instFiniteProjLineCusps HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.numberField_of_finiteDimensional ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent"
p2m_attr_erase "instance" "ModularCurve.instModuleKaehlerIntermediateFieldLaurent"
p2m_attr_erase "simp" "ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"
p2m_attr_erase "simp" "ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.cuspCount_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply"
p2m_attr_erase "simp" "WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply HeckeEis.binaryFormEval_mk HeckeEis.binaryFormAlphaAdj_apply_coe HeckeEis.binaryFormRepSL_apply_coe ModularCurve.ProjectiveLine.vecMulRow_snd HeckeEis.projLineRepSL_apply HeckeEis.projLineAct_one HeckeEis.projLineRep_apply HeckeEis.projLineAlphaAdj_apply ModularCurve.ProjectiveLine.vecMulRow_fst ModularCurve.ProjectiveLine.vecMul_mk HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero HeckeEis.coe_linePow ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe"
p2m_attr_erase "simp" "ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.symPoly_zero ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve ModularCurve

namespace ResQ

theorem thetaL_jqModC_ne_zero (K : Type*) [Field K] : thetaL K (jqModC K) ≠ 0 := by
  intro h
  have hc := congrArg (fun f : LaurentSeries K => f.coeff (-2 + 1)) h
  simp only [HahnSeries.coeff_zero, thetaL_apply, HahnSeries.coeff_single_mul_add, one_mul,
    LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff] at hc
  norm_num [Ring.choose_one_right, coeff_jqModC_neg_one] at hc

section Places

variable (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N]

theorem isRational (x : Place K ↥(modularFunctionFieldC K N)) : x.IsRational := by
  haveI := isCurveOver_modularFunctionFieldC_of_perfectField K N
  exact (Place.isRational_iff_deg_eq_one x).2 (IsCurveOver.deg_eq_one_of_isAlgClosed x)

variable {K N}

theorem natCast_placeRamificationJ {x : Place K ↥(modularFunctionFieldC K N)} (haff : IsAffineGeomPlace K N x) :
    (placeRamificationJ N x : ℤ) = x.ord (jGeomGen K N -
      algebraMap K ↥(modularFunctionFieldC K N) (x.evalAt (jGeomGen K N))) := by
  unfold placeRamificationJ
  exact Int.toNat_of_nonneg (ord_sub_evalAt_pos_of_isRational (isRational K N x) haff.1
    (jGeomGen_sub_algebraMap_ne_zero K N _)).le

theorem placeRamificationJ_pos {x : Place K ↥(modularFunctionFieldC K N)} (haff : IsAffineGeomPlace K N x) :
    0 < placeRamificationJ N x := by
  have h := ord_sub_evalAt_pos_of_isRational (isRational K N x) haff.1
    (jGeomGen_sub_algebraMap_ne_zero K N (x.evalAt (jGeomGen K N)))
  have h2 := natCast_placeRamificationJ haff
  omega

theorem placeWidth_pos {q : ℕ} [Fact q.Prime] [CharP K q] (hq5 : 5 ≤ q) (hqN : ¬ q ∣ N)
    {x : Place K ↥(modularFunctionFieldC K N)} (haff : IsAffineGeomPlace K N x) : 0 < placeWidth N x := by
  have he := placeRamificationJ_pos haff
  have hdvd := placeRamificationJ_dvd_jWidth_of_ord_pos (q := q) (N := N) (K := K) hq5 hqN he
  unfold placeWidth
  exact Nat.div_pos (Nat.le_of_dvd (jWidth_pos _) hdvd) he

theorem evalAt_add_of_mem (x : Place K ↥(modularFunctionFieldC K N)) {f g : ↥(modularFunctionFieldC K N)}
    (hf : f ∈ x.toValuationSubring) (hg : g ∈ x.toValuationSubring) :
    x.evalAt (f + g) = x.evalAt f + x.evalAt g := by
  have hrat := isRational K N x
  apply x.algebraMap_residueField_injective
  rw [map_add, x.algebraMap_evalAt hrat (add_mem hf hg), x.algebraMap_evalAt hrat hf, x.algebraMap_evalAt hrat hg,
    ← map_add]
  rfl

theorem evalAt_smul_of_mem (x : Place K ↥(modularFunctionFieldC K N)) (c : K) {f : ↥(modularFunctionFieldC K N)}
    (hf : f ∈ x.toValuationSubring) :
    x.evalAt (c • f) = c * x.evalAt f := by
  have hrat := isRational K N x
  have hcf : c • f ∈ x.toValuationSubring := by
    rw [Algebra.smul_def]; exact mul_mem (x.algebraMap_mem' c) hf
  apply x.algebraMap_residueField_injective
  rw [map_mul, x.algebraMap_evalAt hrat hcf, x.algebraMap_evalAt hrat hf]
  have : (⟨c • f, hcf⟩ : x.toValuationSubring) = algebraMap K x.toValuationSubring c * ⟨f, hf⟩ := by
    apply Subtype.ext
    simp [Algebra.smul_def]
  rw [this, map_mul]
  congr 1

end Places

section Bridge

variable (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
  (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)

include hN in
omit [IsAlgClosed K] [DecidableEq K] in
theorem not_dvd : ¬ p ∣ N := fun h => hN ((CharP.cast_eq_zero_iff K p N).2 h)

def P (k : ℤ) (φ : PowerSeries K) (G : ↥(modularFunctionFieldC K N)) : Prop :=
  (G : LaurentSeries K) = HahnSeries.ofPowerSeries ℤ K φ * thetaL K (jqModC K) ^ (-(k / 2))

theorem resQFun_apply (k : ℤ) (φ : PowerSeries K) (x : SSIndex p N K hp5 k) :
    resQFun p N K hp5 k φ x = lead N K x.1 (poleOrder p N K hp5 k x) (Classical.epsilon (P K N k φ)) := rfl

include p hN in
omit [IsAlgClosed K] [DecidableEq K] in

theorem exists_P (m : ℕ) (φ : PowerSeries K) (hφ : φ ∈ ModPForms.modPMod N (2 * (m : ℤ)) K) :
    ∃ G : ↥(modularFunctionFieldC K N), IsModPFormFn K m (G : LaurentSeries K) ∧ P K N (2 * (m : ℤ)) φ G := by
  obtain ⟨G, hGf, hGq⟩ :=
    ModPForms.exists_isModPFormFn_qexpOfWeight_eq_of_mem_modPMod p N (not_dvd p K N hN) K m φ hφ
  refine ⟨G, hGf, ?_⟩
  have hθ := thetaL_jqModC_ne_zero K
  unfold P
  rw [show (2 * (m : ℤ)) / 2 = (m : ℤ) by omega]
  rw [qexpOfWeight, thetaJ] at hGq
  rw [← hGq, mul_assoc, ← zpow_add₀ hθ, add_neg_cancel, zpow_zero, mul_one]

omit [Fact p.Prime] [CharP K p] [IsAlgClosed K] [DecidableEq K] in
theorem P_unique {k : ℤ} {φ : PowerSeries K} {G G' : ↥(modularFunctionFieldC K N)}
    (h : P K N k φ G) (h' : P K N k φ G') : G = G' :=
  Subtype.ext (h.trans h'.symm)

include p hN in
omit [IsAlgClosed K] [DecidableEq K] in
theorem eps_spec (m : ℕ) (φ : PowerSeries K) (hφ : φ ∈ ModPForms.modPMod N (2 * (m : ℤ)) K) :
    P K N (2 * (m : ℤ)) φ (Classical.epsilon (P K N (2 * (m : ℤ)) φ)) ∧
      IsModPFormFn K m ((Classical.epsilon (P K N (2 * (m : ℤ)) φ) : ↥(modularFunctionFieldC K N)) : LaurentSeries K) := by
  obtain ⟨G, hGf, hGP⟩ := exists_P p K N hN m φ hφ
  have hε : P K N (2 * (m : ℤ)) φ (Classical.epsilon (P K N (2 * (m : ℤ)) φ)) :=
    Classical.epsilon_spec ⟨G, hGP⟩
  refine ⟨hε, ?_⟩
  rw [P_unique K N hε hGP]; exact hGf

include p hN in
omit [IsAlgClosed K] [DecidableEq K] in
theorem eps_add (m : ℕ) (φ ψ : PowerSeries K) (hφ : φ ∈ ModPForms.modPMod N (2 * (m : ℤ)) K)
    (hψ : ψ ∈ ModPForms.modPMod N (2 * (m : ℤ)) K) :
    Classical.epsilon (P K N (2 * (m : ℤ)) (φ + ψ))
      = Classical.epsilon (P K N (2 * (m : ℤ)) φ) + Classical.epsilon (P K N (2 * (m : ℤ)) ψ) := by
  have h1 := (eps_spec p K N hN m φ hφ).1
  have h2 := (eps_spec p K N hN m ψ hψ).1
  have h12 := (eps_spec p K N hN m (φ + ψ) (add_mem hφ hψ)).1
  refine P_unique K N h12 ?_
  unfold P at h1 h2 ⊢
  rw [IntermediateField.coe_add, h1, h2, map_add, add_mul]

include p hN in
omit [IsAlgClosed K] [DecidableEq K] in
theorem eps_smul (m : ℕ) (c : K) (φ : PowerSeries K) (hφ : φ ∈ ModPForms.modPMod N (2 * (m : ℤ)) K) :
    Classical.epsilon (P K N (2 * (m : ℤ)) (c • φ)) = c • Classical.epsilon (P K N (2 * (m : ℤ)) φ) := by
  have h1 := (eps_spec p K N hN m φ hφ).1
  have h12 := (eps_spec p K N hN m (c • φ) (Submodule.smul_mem _ c hφ)).1
  refine P_unique K N h12 ?_
  unfold P at h1 ⊢
  rw [IntermediateField.coe_smul, h1, show c • φ = PowerSeries.C c * φ by rw [PowerSeries.smul_eq_C_mul], map_mul,
    HahnSeries.ofPowerSeries_C, Algebra.smul_def, HahnSeries.algebraMap_apply',
    show algebraMap K (PowerSeries K) c = PowerSeries.C c by simp, HahnSeries.ofPowerSeries_C, mul_assoc]

end Bridge

section Floor

variable (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
  (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)

include hN in
theorem mul_unif_zpow_mem (m : ℕ) (x : SSIndex p N K hp5 (2 * (m : ℤ))) (G : ↥(modularFunctionFieldC K N))
    (hG : IsModPFormFn K m (G : LaurentSeries K)) :
    unif N K x.1 ^ (poleOrder p N K hp5 (2 * (m : ℤ)) x) * G ∈ x.1.toValuationSubring := by
  rcases eq_or_ne G 0 with rfl | hG0
  · rw [mul_zero]; exact zero_mem _
  obtain ⟨hss, -, -, hdvd, -⟩ := x.2
  have haff : IsAffineGeomPlace K N x.1 := hss.2.1
  have hpN := not_dvd p K N hN
  have hst := (stackOrd_nonneg_and_le_ord_of_isModPFormFn p hp5 N hpN K m G hG0 hG).1 x.1 haff
  have hu : 0 < placeWidth N x.1 := placeWidth_pos (q := p) hp5 hpN haff
  unfold stackOrd at hst
  obtain ⟨t, ht⟩ := hdvd

  set W : ℤ := (jWidth (x.1.evalAt (jGeomGen K N)) : ℤ) with hW
  set u : ℤ := (placeWidth N x.1 : ℤ) with hu'
  have hu0 : (0 : ℤ) < u := by rw [hu']; exact_mod_cast hu
  have hm2 : (2 * (m : ℤ)) / 2 = (m : ℤ) := by omega
  have ht' : (m : ℤ) = u * t := by linarith
  have ha0 : (2 * (m : ℤ)) / 2 * (W - 1) / u = t * (W - 1) := by
    rw [show (2 * (m : ℤ)) / 2 * (W - 1) = u * (t * (W - 1)) by rw [hm2, ht']; ring]
    exact Int.mul_ediv_cancel_left _ hu0.ne'
  have ha : poleOrder p N K hp5 (2 * (m : ℤ)) x = t * (W - 1) := by
    unfold poleOrder; exact ha0

  have h3 : (m : ℤ) * (W - 1) = u * (t * (W - 1)) := by rw [ht']; ring
  have hord : -(t * (W - 1)) ≤ x.1.ord G := by
    have : u * (-(t * (W - 1))) ≤ u * x.1.ord G := by linarith
    exact le_of_mul_le_mul_left this hu0

  have hπ0 : unif N K x.1 ≠ 0 := fun h => by
    have := ord_unif K N x.1; rw [h, Place.ord_zero] at this; exact zero_ne_one this
  apply (x.1.mem_iff_ord_nonneg (mul_ne_zero (zpow_ne_zero _ hπ0) hG0)).2
  rw [x.1.ord_mul (zpow_ne_zero _ hπ0) hG0, x.1.ord_zpow, ord_unif, mul_one, ha]
  omega

end Floor

end ResQ

namespace ExitL

open ResQ

theorem isModPFormFn_of_mem_L_of_eq (K : Type) [Field K] (N : ℕ) [NeZero N] (m : ℕ)
    (E : IntermediateField K (LaurentSeries K)) (hE : modularFunctionFieldFullC K N = E) (hj : jqModC K ∈ E)
    [FiniteDimensional ↥(IntermediateField.adjoin K ({(⟨jqModC K, hj⟩ : ↥E)} : Set ↥E)) ↥E]
    [Algebra.IsSeparable ↥(IntermediateField.adjoin K ({(⟨jqModC K, hj⟩ : ↥E)} : Set ↥E)) ↥E]
    (D : Divisor K ↥E)
    (hD : ∀ w : Place K ↥E,
      D w = (if 0 < w.ord (⟨jqModC K, hj⟩ : ↥E)
               then (2 * (m : ℤ) * w.ord (⟨jqModC K, hj⟩ : ↥E)) / 3 else 0)
          + (if 0 < w.ord ((⟨jqModC K, hj⟩ : ↥E) - algebraMap K _ 1728)
               then ((m : ℤ) * w.ord ((⟨jqModC K, hj⟩ : ↥E) - algebraMap K _ 1728)) / 2 else 0)
          + (if w.ord (⟨jqModC K, hj⟩ : ↥E) < 0
               then (m : ℤ) * w.ord (⟨jqModC K, hj⟩ : ↥E) else 0))
    (G : ↥E) (hG : G ∈ riemannRochSpace D) : IsModPFormFn K m (G : LaurentSeries K) := by
  subst hE
  exact isModPFormFn_of_mem_riemannRochSpace K N m D hD G hG

theorem isModPFormFn_of_mem_L (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] [PerfectField K]
    (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) (m : ℕ) (G : ↥(modularFunctionFieldC K N))
    (hG : G ∈ riemannRochSpace (weightDivisor K N m)) : IsModPFormFn K m (G : LaurentSeries K) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hpN : ¬ p ∣ N := fun h => hN ((CharP.cast_eq_zero_iff K p N).2 h)
  obtain ⟨data⟩ := nonempty_modularPolynomialData N
  have hfs := finiteDimensional_and_isSeparable_adjoin_jGeomGen_of_isSeparable_jqNModC K N data
    (isSeparable_jqNModC_of_natCast_ne_zero K N hN)
  haveI := hfs.1
  haveI := hfs.2
  exact isModPFormFn_of_mem_L_of_eq K N m _
    (modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charP_pos K p N hpN).symm (jqModC_mem K N)
    (weightDivisor K N m)
    (fun w => by rw [weightDivisor_apply K N m (exists_divisor_forall_eq_weightFloor_fieldC K N m) w]; rfl) G hG

theorem exitL (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N]
    (hN : (N : K) ≠ 0) (S₀ : Set ℕ) (hS₀p : p ∈ S₀)
    (m : ℕ) (hm : 1 ≤ m) (G : ↥(modularFunctionFieldC K N)) (hG0 : G ≠ 0)
    (hG : G ∈ AlgebraicCurve.riemannRochSpace (ModularCurve.weightDivisor K N m)) (lam : ℕ → K)
    (heig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ℓ ∉ S₀ →
      haveI : Fact ℓ.Prime := ⟨hℓ⟩
      letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ)
      algebraMap K ↥(modularFunctionFieldC K N) ((ℓ : K) ^ (m - 1)) *
          Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ)
            (heckeBetaC K N ℓ G * ModularCurve.heckeMultiplier N K ℓ ^ m)
        = algebraMap K ↥(modularFunctionFieldC K N) (lam ℓ) * G) :
    ∃ ψ : PowerSeries K,
      HahnSeries.ofPowerSeries ℤ K ψ = (G : LaurentSeries K) * thetaL K (jqModC K) ^ m ∧
      ψ ∈ ModPForms.modPMod N (2 * (m : ℤ)) K ∧ ModPForms.IsModPEigen N S₀ (2 * (m : ℤ)) ψ lam := by
  classical
  have hpN : ¬ p ∣ N := fun h => hN ((CharP.cast_eq_zero_iff K p N).2 h)
  have hθ := thetaL_jqModC_ne_zero K

  have hGf : IsModPFormFn K m (G : LaurentSeries K) := isModPFormFn_of_mem_L p K N hN m G hG
  obtain ⟨ψ, hψmem, hψq⟩ := ModPForms.exists_mem_modPMod_ofPowerSeries_eq_qexpOfWeight_of_isModPFormFn p hp5 N hpN K m G hGf
  have hψq' : HahnSeries.ofPowerSeries ℤ K ψ = (G : LaurentSeries K) * thetaL K (jqModC K) ^ m := by
    rw [hψq, qexpOfWeight, thetaJ, zpow_natCast]
  refine ⟨ψ, hψq', hψmem, ?_, ?_⟩
  ·
    intro h0
    rw [h0, map_zero] at hψq'
    have : (G : LaurentSeries K) = 0 := by
      rcases mul_eq_zero.mp hψq'.symm with h1 | h2
      · exact h1
      · exact absurd h2 (pow_ne_zero _ hθ)
    exact hG0 (by exact_mod_cast this)
  · intro ℓ hℓ hℓN hℓS
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    have hℓp : ℓ ≠ p := fun h => hℓS (h ▸ hS₀p)
    have hℓK : (ℓ : K) ≠ 0 := by
      intro h
      have := (CharP.cast_eq_zero_iff K p ℓ).1 h
      exact hℓp ((Nat.prime_dvd_prime_iff_eq (Fact.out) hℓ).1 this).symm
    haveI : NeZero (ℓ : K) := ⟨hℓK⟩
    obtain ⟨ζ0, hζ0⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K ℓ
    have hζne : ζ0 ≠ 0 := hζ0.ne_zero hℓ.ne_zero
    set ζ : Kˣ := Units.mk0 ζ0 hζne with hζdef
    have hζ : IsPrimitiveRoot (ζ : K) ℓ := hζ0
    have hspec := ModularCurve.SSHeckeV2.heckeMultiplier_spec p hp5 K N hN ℓ hℓN hℓK
    have hq := qexpOfWeight_trace_heckeBetaC_mul_pow_eq_heckePS_of_eq_smul_map K N ℓ hN hℓN ζ hζ m hm G ψ hψq
      (heckeMultiplier N K ℓ) hspec

    have he := heig ℓ hℓ hℓN hℓS
    letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ)
    have he' := congrArg (fun z : ↥(modularFunctionFieldC K N) => qexpOfWeight K (m : ℤ) ((z : ↥(modularFunctionFieldC K N)) : LaurentSeries K)) he
    beta_reduce at he'
    have hC : ∀ c : K, ((algebraMap K ↥(modularFunctionFieldC K N) c : ↥(modularFunctionFieldC K N)) : LaurentSeries K)
        = HahnSeries.C c := fun c => by
      rw [show ((algebraMap K ↥(modularFunctionFieldC K N) c : ↥(modularFunctionFieldC K N)) : LaurentSeries K)
          = algebraMap K (LaurentSeries K) c from rfl, HahnSeries.algebraMap_apply',
        show algebraMap K (PowerSeries K) c = PowerSeries.C c by simp, HahnSeries.ofPowerSeries_C]
    have hcoe1 : ((algebraMap K ↥(modularFunctionFieldC K N) ((ℓ : K) ^ (m - 1)) *
        Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ)
          (heckeBetaC K N ℓ G * ModularCurve.heckeMultiplier N K ℓ ^ m) : ↥(modularFunctionFieldC K N)) : LaurentSeries K)
        = HahnSeries.C ((ℓ : K) ^ (m - 1)) *
          ((Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ)
            (heckeBetaC K N ℓ G * ModularCurve.heckeMultiplier N K ℓ ^ m) : ↥(modularFunctionFieldC K N)) : LaurentSeries K) := by
      rw [IntermediateField.coe_mul, hC]
    have hcoe2 : ((algebraMap K ↥(modularFunctionFieldC K N) (lam ℓ) * G : ↥(modularFunctionFieldC K N)) : LaurentSeries K)
        = HahnSeries.C (lam ℓ) * (G : LaurentSeries K) := by
      rw [IntermediateField.coe_mul, hC]
    rw [hcoe1, hcoe2] at he'
    rw [he'] at hq

    have : HahnSeries.ofPowerSeries ℤ K (ModPForms.heckePS (2 * (m : ℤ)) ℓ ψ)
        = HahnSeries.ofPowerSeries ℤ K (lam ℓ • ψ) := by
      have hψq2 := hψq
      rw [qexpOfWeight] at hψq2
      rw [hq, qexpOfWeight, mul_assoc, ← hψq2,
        show lam ℓ • ψ = PowerSeries.C (lam ℓ) * ψ by rw [PowerSeries.smul_eq_C_mul], map_mul, HahnSeries.ofPowerSeries_C]
    exact HahnSeries.ofPowerSeries_injective this

theorem exitR (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N]
    (hN : (N : K) ≠ 0) (S₀ : Set ℕ) (hS₀p : p ∈ S₀)
    (m : ℕ) (hm : 1 ≤ m) (G : ↥(modularFunctionFieldC K N)) (hG0 : G ≠ 0)
    (hG : G ∈ AlgebraicCurve.riemannRochSpace (ModularCurve.weightDivisor K N m))
    (hcusp : ModularCurve.IsModPCuspFormFn K m (G : LaurentSeries K)) (lam : ℕ → K)
    (heig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ℓ ∉ S₀ →
      haveI : Fact ℓ.Prime := ⟨hℓ⟩
      letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ)
      algebraMap K ↥(modularFunctionFieldC K N) ((ℓ : K) ^ (m - 1)) *
          Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ)
            (heckeBetaC K N ℓ G * ModularCurve.heckeMultiplier N K ℓ ^ m)
        = algebraMap K ↥(modularFunctionFieldC K N) (lam ℓ) * G) :
    ∃ ψ : PowerSeries K,
      HahnSeries.ofPowerSeries ℤ K ψ = (G : LaurentSeries K) * thetaL K (jqModC K) ^ m ∧
      ψ ∈ ModPForms.modPCusp N (2 * (m : ℤ)) K ∧ ModPForms.IsModPEigen N S₀ (2 * (m : ℤ)) ψ lam := by
  classical
  have hpN : ¬ p ∣ N := fun h => hN ((CharP.cast_eq_zero_iff K p N).2 h)
  have hθ := thetaL_jqModC_ne_zero K

  obtain ⟨ψ, hψmem, hψq⟩ := ModPForms.exists_mem_modPCusp_ofPowerSeries_eq_qexpOfWeight_of_isModPCuspFormFn p hp5 N hpN K m G hcusp
  have hψq' : HahnSeries.ofPowerSeries ℤ K ψ = (G : LaurentSeries K) * thetaL K (jqModC K) ^ m := by
    rw [hψq, qexpOfWeight, thetaJ, zpow_natCast]
  refine ⟨ψ, hψq', hψmem, ?_, ?_⟩
  ·
    intro h0
    rw [h0, map_zero] at hψq'
    have : (G : LaurentSeries K) = 0 := by
      rcases mul_eq_zero.mp hψq'.symm with h1 | h2
      · exact h1
      · exact absurd h2 (pow_ne_zero _ hθ)
    exact hG0 (by exact_mod_cast this)
  · intro ℓ hℓ hℓN hℓS
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    have hℓp : ℓ ≠ p := fun h => hℓS (h ▸ hS₀p)
    have hℓK : (ℓ : K) ≠ 0 := by
      intro h
      have := (CharP.cast_eq_zero_iff K p ℓ).1 h
      exact hℓp ((Nat.prime_dvd_prime_iff_eq (Fact.out) hℓ).1 this).symm
    haveI : NeZero (ℓ : K) := ⟨hℓK⟩
    obtain ⟨ζ0, hζ0⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K ℓ
    have hζne : ζ0 ≠ 0 := hζ0.ne_zero hℓ.ne_zero
    set ζ : Kˣ := Units.mk0 ζ0 hζne with hζdef
    have hζ : IsPrimitiveRoot (ζ : K) ℓ := hζ0
    have hspec := ModularCurve.SSHeckeV2.heckeMultiplier_spec p hp5 K N hN ℓ hℓN hℓK
    have hq := qexpOfWeight_trace_heckeBetaC_mul_pow_eq_heckePS_of_eq_smul_map K N ℓ hN hℓN ζ hζ m hm G ψ hψq
      (heckeMultiplier N K ℓ) hspec

    have he := heig ℓ hℓ hℓN hℓS
    letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ)
    have he' := congrArg (fun z : ↥(modularFunctionFieldC K N) => qexpOfWeight K (m : ℤ) ((z : ↥(modularFunctionFieldC K N)) : LaurentSeries K)) he
    beta_reduce at he'
    have hC : ∀ c : K, ((algebraMap K ↥(modularFunctionFieldC K N) c : ↥(modularFunctionFieldC K N)) : LaurentSeries K)
        = HahnSeries.C c := fun c => by
      rw [show ((algebraMap K ↥(modularFunctionFieldC K N) c : ↥(modularFunctionFieldC K N)) : LaurentSeries K)
          = algebraMap K (LaurentSeries K) c from rfl, HahnSeries.algebraMap_apply',
        show algebraMap K (PowerSeries K) c = PowerSeries.C c by simp, HahnSeries.ofPowerSeries_C]
    have hcoe1 : ((algebraMap K ↥(modularFunctionFieldC K N) ((ℓ : K) ^ (m - 1)) *
        Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ)
          (heckeBetaC K N ℓ G * ModularCurve.heckeMultiplier N K ℓ ^ m) : ↥(modularFunctionFieldC K N)) : LaurentSeries K)
        = HahnSeries.C ((ℓ : K) ^ (m - 1)) *
          ((Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ)
            (heckeBetaC K N ℓ G * ModularCurve.heckeMultiplier N K ℓ ^ m) : ↥(modularFunctionFieldC K N)) : LaurentSeries K) := by
      rw [IntermediateField.coe_mul, hC]
    have hcoe2 : ((algebraMap K ↥(modularFunctionFieldC K N) (lam ℓ) * G : ↥(modularFunctionFieldC K N)) : LaurentSeries K)
        = HahnSeries.C (lam ℓ) * (G : LaurentSeries K) := by
      rw [IntermediateField.coe_mul, hC]
    rw [hcoe1, hcoe2] at he'
    rw [he'] at hq

    have : HahnSeries.ofPowerSeries ℤ K (ModPForms.heckePS (2 * (m : ℤ)) ℓ ψ)
        = HahnSeries.ofPowerSeries ℤ K (lam ℓ • ψ) := by
      have hψq2 := hψq
      rw [qexpOfWeight] at hψq2
      rw [hq, qexpOfWeight, mul_assoc, ← hψq2,
        show lam ℓ • ψ = PowerSeries.C (lam ℓ) * ψ by rw [PowerSeries.smul_eq_C_mul], map_mul, HahnSeries.ofPowerSeries_C]
    exact HahnSeries.ofPowerSeries_injective this

end ExitL

theorem solution (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N]
    (hN : (N : K) ≠ 0) (S₀ : Set ℕ) (hS₀p : p ∈ S₀)
    (m' : ℕ) (hm' : 1 ≤ m') (G : ↥(modularFunctionFieldC K N)) (hG0 : G ≠ 0)
    (hG : G ∈ AlgebraicCurve.riemannRochSpace (ModularCurve.weightDivisor K N m'))
    (hcusp : ModularCurve.IsModPCuspFormFn K m' (G : LaurentSeries K)) (lam : ℕ → K)
    (heig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ℓ ∉ S₀ →
      haveI : Fact ℓ.Prime := ⟨hℓ⟩
      letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ)
      algebraMap K ↥(modularFunctionFieldC K N) ((ℓ : K) ^ (m' - 1)) *
          Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ)
            (heckeBetaC K N ℓ G * ModularCurve.heckeMultiplier N K ℓ ^ m')
        = algebraMap K ↥(modularFunctionFieldC K N) (lam ℓ) * G) :
    ∃ ψ : PowerSeries K,
      HahnSeries.ofPowerSeries ℤ K ψ = (G : LaurentSeries K) * thetaL K (jqModC K) ^ m' ∧
      ψ ∈ ModPForms.modPCusp N (2 * (m' : ℤ)) K ∧ ModPForms.IsModPEigen N S₀ (2 * (m' : ℤ)) ψ lam :=
  ExitL.exitR p hp5 K N hN S₀ hS₀p m' hm' G hG0 hG hcusp lam heig

end S_ModularCurve_SSHeckeV2_exists_isModPEigen_modPCusp_of_eigen_riemannRochSpace
end P2MW
export P2MW.S_ModularCurve_SSHeckeV2_exists_isModPEigen_modPCusp_of_eigen_riemannRochSpace (solution)
