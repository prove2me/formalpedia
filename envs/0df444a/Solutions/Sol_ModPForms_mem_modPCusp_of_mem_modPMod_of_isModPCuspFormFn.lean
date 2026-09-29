-- Prove2me | solution 1 for ModPForms.mem_modPCusp_of_mem_modPMod_of_isModPCuspFormFn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/27261ac5-ee95-5311-aea0-0b68e3c4c995

import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_ModularCurve_ModPFormFn
import Definitions.Def_ModularCurve_WeightDivisor
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_ModularCurve_GenusNumerics
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModPForms_exists_isModPFormFn_qexpOfWeight_eq_of_mem_modPMod
import Theorems.Thm_ModPForms_exists_isModPCuspFormFn_qexpOfWeight_eq_of_mem_modPCusp
import Theorems.Thm_ModularCurve_mem_riemannRochSpace_iff_isModPCuspFormFn_of_forall_eq_weightFloor_sub
import Theorems.Thm_ModPForms_dimFormulaCusp_le_finrank_modPCusp
import Theorems.Thm_ModularCurve_ell_le_dimFormulaCusp_of_forall_eq_weightFloor_sub
import Theorems.Thm_ModPForms_modPCusp_le_modPMod
import Theorems.Thm_ModPForms_finiteDimensional_modPMod
import Theorems.Thm_ModularCurve_exists_divisor_forall_eq_weightFloor_fieldC
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModPForms_exists_mem_modPMod_ofPowerSeries_eq_qexpOfWeight_of_isModPFormFn
import Theorems.Thm_ModularCurve_isModPFormFn_of_mem_riemannRochSpace
import Theorems.Thm_ModularCurve_finiteDimensional_and_isSeparable_adjoin_jGeomGen_of_isSeparable_jqNModC
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charP_pos
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Theorems.Thm_ModularCurve_eq_zero_of_isModPCuspFormFn_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModPForms_mem_modPCusp_of_mem_modPMod_of_isModPCuspFormFn
p2m_attr_erase "instance" "ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup ModularCurve.instIsElliptic_tateLaurent ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree HeckeEis.instFiniteProjLineCusps HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.numberField_of_finiteDimensional ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent"
p2m_attr_erase "instance" "ModularCurve.instModuleKaehlerIntermediateFieldLaurent"
p2m_attr_erase "simp" "ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"
p2m_attr_erase "simp" "ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆"
p2m_attr_erase "simp" "Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero"
p2m_attr_erase "simp" "ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one"
p2m_attr_erase "simp" "TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply"
p2m_attr_erase "simp" "CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply HeckeEis.binaryFormEval_mk HeckeEis.binaryFormAlphaAdj_apply_coe HeckeEis.binaryFormRepSL_apply_coe ModularCurve.ProjectiveLine.vecMulRow_snd HeckeEis.projLineRepSL_apply HeckeEis.projLineAct_one HeckeEis.projLineRep_apply HeckeEis.projLineAlphaAdj_apply ModularCurve.ProjectiveLine.vecMulRow_fst ModularCurve.ProjectiveLine.vecMul_mk HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero HeckeEis.coe_linePow ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.symPoly_zero"
p2m_attr_erase "simp" "ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

p2m_open "AlgebraicCurve ModularCurve~coeffMap_mem_modularFunctionFieldC"

noncomputable section

p2m_open "ModularCurve~coeffMap_mem_modularFunctionFieldC"

namespace SpanCuspBC

section Supply

variable {K L : Type*} [Field K] [Field L] (ι : K →+* L)

theorem coeffMap_jqModC : coeffMap ι (jqModC K) = jqModC L := map_jqModC ι

theorem coeffMap_jqNModC (N : ℕ) [NeZero N] : coeffMap ι (jqNModC K N) = jqNModC L N := by
  rw [jqNModC, coeffMap_qExpand, coeffMap_jqModC, jqNModC]

theorem coeffMap_algebraMap' (c : K) :
    coeffMap ι (algebraMap K (LaurentSeries K) c) = algebraMap L (LaurentSeries L) (ι c) := by
  rw [algebraMap_laurentSeries_eq_single, coeffMap_single, algebraMap_laurentSeries_eq_single]

theorem coeffMap_ofPowerSeries (φ : PowerSeries K) :
    coeffMap ι (HahnSeries.ofPowerSeries ℤ K φ) = HahnSeries.ofPowerSeries ℤ L (PowerSeries.map ι φ) := by
  ext k
  rw [coeffMap_coeff, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with hk
  · rw [map_zero]
  · rw [PowerSeries.coeff_map]

theorem thetaL_coeff' (x : LaurentSeries K) (n : ℤ) :
    (thetaL K x).coeff n = (n : K) * x.coeff n := by
  rw [thetaL_apply, HahnSeries.coeff_single_mul, one_mul, LaurentSeries.derivative_apply,
    LaurentSeries.hasseDeriv_coeff]
  simp only [Nat.cast_one, sub_add_cancel, Ring.choose_one_right, zsmul_eq_mul]

theorem coeffMap_thetaL (x : LaurentSeries K) :
    coeffMap ι (thetaL K x) = thetaL L (coeffMap ι x) := by
  ext n
  simp only [coeffMap_coeff, thetaL_coeff', map_mul, map_intCast]

theorem coeffMap_thetaJ : coeffMap ι (thetaJ K) = thetaJ L := by
  unfold thetaJ
  rw [coeffMap_thetaL, coeffMap_jqModC]

theorem coeffMap_qexpOfWeight (m : ℤ) (G : LaurentSeries K) :
    coeffMap ι (qexpOfWeight K m G) = qexpOfWeight L m (coeffMap ι G) := by
  unfold qexpOfWeight
  rw [map_mul, map_zpow₀, coeffMap_thetaJ]

theorem map_mk_intCast (a : ℕ → ℤ) :
    PowerSeries.map ι (PowerSeries.mk fun n => ((a n : ℤ) : K)) = PowerSeries.mk fun n => ((a n : ℤ) : L) := by
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_mk, map_intCast]

theorem map_smul' (c : K) (φ : PowerSeries K) : PowerSeries.map ι (c • φ) = ι c • PowerSeries.map ι φ := by
  rw [PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C, ← PowerSeries.smul_eq_C_mul]

end Supply

section Up

variable {K L : Type*} [Field K] [Field L] (ι : K →+* L)

theorem coeffMap_mem_adjoin (y : LaurentSeries K) {b : LaurentSeries K}
    (hb : b ∈ Algebra.adjoin K ({y} : Set (LaurentSeries K))) :
    coeffMap ι b ∈ Algebra.adjoin L ({coeffMap ι y} : Set (LaurentSeries L)) := by
  induction hb using Algebra.adjoin_induction with
  | mem z hz =>
    rw [Set.mem_singleton_iff] at hz; subst hz
    exact Algebra.subset_adjoin rfl
  | algebraMap c => rw [coeffMap_algebraMap']; exact Subalgebra.algebraMap_mem _ _
  | add b c _ _ hb hc => rw [map_add]; exact add_mem hb hc
  | mul b c _ _ hb hc => rw [map_mul]; exact mul_mem hb hc

theorem isIntegral_coeffMap_gen (y x : LaurentSeries K)
    (hx : IsIntegral (Algebra.adjoin K ({y} : Set (LaurentSeries K))) x) :
    IsIntegral (Algebra.adjoin L ({coeffMap ι y} : Set (LaurentSeries L))) (coeffMap ι x) := by
  set A₀ := Algebra.adjoin K ({y} : Set (LaurentSeries K))
  set B := Algebra.adjoin L ({coeffMap ι y} : Set (LaurentSeries L))
  let φ : A₀ →+* B :=
    { toFun := fun b => ⟨coeffMap ι b, coeffMap_mem_adjoin ι y b.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun _ _ => Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _) }
  have hcomp : (algebraMap B (LaurentSeries L)).comp φ = (coeffMap ι).comp (algebraMap A₀ (LaurentSeries K)) :=
    RingHom.ext fun _ => rfl
  obtain ⟨P, hPm, hPx⟩ := hx
  refine ⟨P.map φ, hPm.map φ, ?_⟩
  rw [Polynomial.eval₂_map, hcomp, ← Polynomial.hom_eval₂, hPx, map_zero]

theorem isModPCuspFormFn_coeffMap (m : ℕ) (G : LaurentSeries K) (hG : IsModPCuspFormFn K m G) :
    IsModPCuspFormFn L m (coeffMap ι G) := by
  obtain ⟨h1, M, h2⟩ := hG
  have hc : coeffMap ι (algebraMap K (LaurentSeries K) 1728) = algebraMap L (LaurentSeries L) 1728 := by
    rw [coeffMap_algebraMap', map_ofNat]
  refine ⟨?_, M, ?_⟩
  · have h := isIntegral_coeffMap_gen ι (jqModC K) _ h1
    rw [map_mul, map_mul, map_pow, map_pow, map_pow, map_sub, hc, coeffMap_jqModC] at h
    exact h
  · have h := isIntegral_coeffMap_gen ι (jqModC K)⁻¹ _ h2
    rw [map_mul, map_mul, map_pow, map_pow, map_pow, map_sub, hc, map_inv₀, coeffMap_jqModC] at h
    exact h

theorem isModPFormFn_coeffMap (m : ℕ) (G : LaurentSeries K) (hG : IsModPFormFn K m G) :
    IsModPFormFn L m (coeffMap ι G) := by
  obtain ⟨h1, h2⟩ := hG
  have hc : coeffMap ι (algebraMap K (LaurentSeries K) 1728) = algebraMap L (LaurentSeries L) 1728 := by
    rw [coeffMap_algebraMap', map_ofNat]
  refine ⟨?_, ?_⟩
  · have h := isIntegral_coeffMap_gen ι (jqModC K) _ h1
    rw [map_mul, map_mul, map_pow, map_pow, map_pow, map_sub, hc, coeffMap_jqModC] at h
    exact h
  · have h := isIntegral_coeffMap_gen ι (jqModC K)⁻¹ _ h2
    rw [map_mul, map_mul, map_pow, map_pow, map_pow, map_sub, hc, map_inv₀, coeffMap_jqModC] at h
    exact h

theorem coeffMap_mem_modularFunctionFieldC (N : ℕ) [NeZero N] {G : LaurentSeries K}
    (hG : G ∈ modularFunctionFieldC K N) : coeffMap ι G ∈ modularFunctionFieldC L N := by
  let T : Subfield (LaurentSeries K) := (modularFunctionFieldC L N).toSubfield.comap (coeffMap ι)
  have hle : (modularFunctionFieldC K N).toSubfield ≤ T := by
    change (IntermediateField.adjoin K ({jqModC K, jqNModC K N} : Set (LaurentSeries K))).toSubfield ≤ T
    refine IntermediateField.adjoin_le_subfield K _ ?_ ?_
    · rintro _ ⟨c, rfl⟩
      change coeffMap ι (algebraMap K (LaurentSeries K) c) ∈ modularFunctionFieldC L N
      rw [coeffMap_algebraMap']
      exact (modularFunctionFieldC L N).algebraMap_mem (ι c)
    · intro x hx
      change coeffMap ι x ∈ modularFunctionFieldC L N
      rcases hx with rfl | hx
      · rw [coeffMap_jqModC]; exact jqModC_mem L N
      · rw [Set.mem_singleton_iff] at hx; subst hx
        rw [coeffMap_jqNModC]; exact jqNModC_mem L N
  have hG' : G ∈ (modularFunctionFieldC K N).toSubfield := (IntermediateField.mem_toSubfield _ _).mpr hG
  exact (Subfield.mem_comap.mp (hle hG') : _)

theorem map_mem_modPMod {K L : Type} [Field K] [Field L] (ι : K →+* L) (N : ℕ) (k : ℤ)
    {φ : PowerSeries K} (h : φ ∈ ModPForms.modPMod N k K) :
    PowerSeries.map ι φ ∈ ModPForms.modPMod N k L := by
  unfold ModPForms.modPMod at h ⊢
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, a, ha, rfl⟩ := hx
    exact Submodule.subset_span ⟨f, a, ha, map_mk_intCast ι a⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul']; exact Submodule.smul_mem _ _ hx

theorem map_mem_modPCusp {K L : Type} [Field K] [Field L] (ι : K →+* L) (N : ℕ) (k : ℤ)
    {φ : PowerSeries K} (h : φ ∈ ModPForms.modPCusp N k K) :
    PowerSeries.map ι φ ∈ ModPForms.modPCusp N k L := by
  unfold ModPForms.modPCusp at h ⊢
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, a, ha, rfl⟩ := hx
    exact Submodule.subset_span ⟨f, a, ha, map_mk_intCast ι a⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul']; exact Submodule.smul_mem _ _ hx

end Up

section Down

variable {K L : Type} [Field K] [Field L] (ι : K →+* L)

theorem exists_retraction : ∃ r : L →+ K, (∀ x, r (ι x) = x) ∧ ∀ (x : K) (c : L), r (ι x * c) = x * r c := by
  letI : Algebra K L := ι.toAlgebra
  have hker : LinearMap.ker (Algebra.linearMap K L) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (algebraMap K L).injective
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K L) hker
  refine ⟨g.toAddMonoidHom, fun x => ?_, fun x c => ?_⟩
  · have := LinearMap.congr_fun hg x
    rw [LinearMap.comp_apply, Algebra.linearMap_apply, LinearMap.id_apply] at this
    exact this
  · have e : ι x * c = x • c := (Algebra.smul_def x c).symm
    rw [e, LinearMap.toAddMonoidHom_coe, map_smul, smul_eq_mul]

def cmap (r : L →+ K) : PowerSeries L →+ PowerSeries K where
  toFun ψ := PowerSeries.mk fun n => r (PowerSeries.coeff n ψ)
  map_zero' := by ext n; rw [PowerSeries.coeff_mk, map_zero, map_zero, map_zero]
  map_add' ψ χ := by ext n; rw [PowerSeries.coeff_mk, map_add, map_add, map_add, PowerSeries.coeff_mk, PowerSeries.coeff_mk]

theorem coeff_cmap (r : L →+ K) (ψ : PowerSeries L) (n : ℕ) :
    PowerSeries.coeff n (cmap r ψ) = r (PowerSeries.coeff n ψ) := by
  change PowerSeries.coeff n (PowerSeries.mk fun n => r (PowerSeries.coeff n ψ)) = _
  rw [PowerSeries.coeff_mk]

theorem cmap_map (r : L →+ K) (hr : ∀ x, r (ι x) = x) (φ : PowerSeries K) :
    cmap r (PowerSeries.map ι φ) = φ := by
  ext n; rw [coeff_cmap, PowerSeries.coeff_map, hr]

theorem cmap_smul_map (r : L →+ K) (hr : ∀ (x : K) (c : L), r (ι x * c) = x * r c) (c : L) (φ : PowerSeries K) :
    cmap r (c • PowerSeries.map ι φ) = r c • φ := by
  ext n
  rw [coeff_cmap, PowerSeries.coeff_smul, PowerSeries.coeff_map, PowerSeries.coeff_smul, smul_eq_mul,
    smul_eq_mul, mul_comm c, hr, mul_comm]

theorem mem_modPCusp_of_map_mem (N : ℕ) (k : ℤ) (φ : PowerSeries K)
    (h : PowerSeries.map ι φ ∈ ModPForms.modPCusp N k L) : φ ∈ ModPForms.modPCusp N k K := by
  obtain ⟨r, hr1, hr2⟩ := exists_retraction ι
  suffices H : ∀ ψ ∈ ModPForms.modPCusp N k L, ∀ c : L, cmap r (c • ψ) ∈ ModPForms.modPCusp N k K by
    have := H _ h 1
    rwa [one_smul, cmap_map ι r hr1] at this
  intro ψ hψ
  unfold ModPForms.modPCusp at hψ
  induction hψ using Submodule.span_induction with
  | mem x hx =>
    intro c
    obtain ⟨f, a, ha, rfl⟩ := hx
    rw [← map_mk_intCast ι a, cmap_smul_map ι r hr2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨f, a, ha, rfl⟩)
  | zero => intro c; rw [smul_zero, map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => intro c; rw [smul_add, map_add]; exact Submodule.add_mem _ (hx c) (hy c)
  | smul d x _ hx => intro c; rw [smul_smul]; exact hx (c * d)

theorem mem_modPMod_of_map_mem (N : ℕ) (k : ℤ) (φ : PowerSeries K)
    (h : PowerSeries.map ι φ ∈ ModPForms.modPMod N k L) : φ ∈ ModPForms.modPMod N k K := by
  obtain ⟨r, hr1, hr2⟩ := exists_retraction ι
  suffices H : ∀ ψ ∈ ModPForms.modPMod N k L, ∀ c : L, cmap r (c • ψ) ∈ ModPForms.modPMod N k K by
    have := H _ h 1
    rwa [one_smul, cmap_map ι r hr1] at this
  intro ψ hψ
  unfold ModPForms.modPMod at hψ
  induction hψ using Submodule.span_induction with
  | mem x hx =>
    intro c
    obtain ⟨f, a, ha, rfl⟩ := hx
    rw [← map_mk_intCast ι a, cmap_smul_map ι r hr2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨f, a, ha, rfl⟩)
  | zero => intro c; rw [smul_zero, map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => intro c; rw [smul_add, map_add]; exact Submodule.add_mem _ (hx c) (hy c)
  | smul d x _ hx => intro c; rw [smul_smul]; exact hx (c * d)

theorem map_mem_modPCusp_iff (N : ℕ) (k : ℤ) (φ : PowerSeries K) :
    PowerSeries.map ι φ ∈ ModPForms.modPCusp N k L ↔ φ ∈ ModPForms.modPCusp N k K :=
  ⟨mem_modPCusp_of_map_mem ι N k φ, map_mem_modPCusp ι N k⟩

end Down

end SpanCuspBC

end

namespace SpanCusp

theorem thetaL_jqModC_ne_zero (K : Type*) [Field K] : thetaL K (jqModC K) ≠ 0 := by
  intro h
  have hc := congrArg (fun f : LaurentSeries K => f.coeff (-2 + 1)) h
  simp only [HahnSeries.coeff_zero, thetaL_apply, HahnSeries.coeff_single_mul_add, one_mul,
    LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff] at hc
  norm_num [Ring.choose_one_right, coeff_jqModC_neg_one] at hc

theorem qexpOfWeight_eq (K : Type*) [Field K] (m : ℕ) (G : LaurentSeries K) :
    qexpOfWeight K (m : ℤ) G = G * thetaL K (jqModC K) ^ m := by
  rw [qexpOfWeight, thetaJ, zpow_natCast]

theorem eq_of_qexpOfWeight_eq (K : Type*) [Field K] (N : ℕ) [NeZero N] (m : ℕ) {G H : ↥(modularFunctionFieldC K N)}
    (h : qexpOfWeight K (m : ℤ) (G : LaurentSeries K) = qexpOfWeight K (m : ℤ) (H : LaurentSeries K)) : G = H := by
  rw [qexpOfWeight_eq, qexpOfWeight_eq] at h
  exact Subtype.ext (mul_right_cancel₀ (pow_ne_zero _ (thetaL_jqModC_ne_zero K)) h)

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

section Closed

variable (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
  (L : Type) [Field L] [CharP L p] [IsAlgClosed L] (m : ℕ) (hm : 1 ≤ m)

include p hpN in
set_option maxHeartbeats 3200000 in

theorem exists_bridge :
    ∃ β : ↥(ModPForms.modPMod N (2 * (m : ℤ)) L) →ₗ[L] ↥(modularFunctionFieldC L N),
      ∀ ψ, qexpOfWeight L (m : ℤ) ((β ψ : ↥(modularFunctionFieldC L N)) : LaurentSeries L) = HahnSeries.ofPowerSeries ℤ L (ψ : PowerSeries L) := by
  classical
  have hex : ∀ ψ : ↥(ModPForms.modPMod N (2 * (m : ℤ)) L), ∃ G : ↥(modularFunctionFieldC L N),
      qexpOfWeight L (m : ℤ) (G : LaurentSeries L) = HahnSeries.ofPowerSeries ℤ L (ψ : PowerSeries L) := fun ψ => by
    obtain ⟨G, -, hG⟩ := ModPForms.exists_isModPFormFn_qexpOfWeight_eq_of_mem_modPMod p N hpN L m ψ.1 ψ.2
    exact ⟨G, hG⟩
  choose b hb using hex
  refine ⟨{ toFun := b, map_add' := ?_, map_smul' := ?_ }, hb⟩
  · intro ψ ψ'
    apply eq_of_qexpOfWeight_eq L N m
    rw [hb, Submodule.coe_add, map_add, qexpOfWeight_eq, IntermediateField.coe_add, add_mul, ← qexpOfWeight_eq,
      ← qexpOfWeight_eq, hb, hb]
  · intro c ψ
    simp only [RingHom.id_apply]
    apply eq_of_qexpOfWeight_eq L N m
    rw [hb, Submodule.coe_smul, show c • (ψ : PowerSeries L) = PowerSeries.C c * (ψ : PowerSeries L) by
        rw [PowerSeries.smul_eq_C_mul], map_mul, HahnSeries.ofPowerSeries_C,
      qexpOfWeight_eq, IntermediateField.coe_smul, Algebra.smul_def,
      HahnSeries.algebraMap_apply', show algebraMap L (PowerSeries L) c = PowerSeries.C c by simp,
      HahnSeries.ofPowerSeries_C, mul_assoc, ← qexpOfWeight_eq, hb]

include hp5 hpN hm in
set_option maxHeartbeats 6400000 in

theorem main_closed (φ : PowerSeries L) (hφ : φ ∈ ModPForms.modPMod N (2 * (m : ℤ)) L)
    (G : ↥(modularFunctionFieldC L N)) (hG : IsModPCuspFormFn L m (G : LaurentSeries L))
    (hGφ : qexpOfWeight L (m : ℤ) (G : LaurentSeries L) = HahnSeries.ofPowerSeries ℤ L φ) :
    φ ∈ ModPForms.modPCusp N (2 * (m : ℤ)) L := by
  classical
  haveI : PerfectField L := IsAlgClosed.perfectField L
  haveI hco := isCurveOver_modularFunctionFieldC_of_perfectField L N
  have hN : (N : L) ≠ 0 := fun h => hpN ((CharP.cast_eq_zero_iff L p N).1 h)
  set V := ModPForms.modPMod N (2 * (m : ℤ)) L with hV
  haveI : FiniteDimensional L ↥V := ModPForms.finiteDimensional_modPMod N (2 * (m : ℤ)) L
  obtain ⟨β, hβ⟩ := exists_bridge p N hpN L m
  have hβinj : Function.Injective β := by
    intro ψ ψ' h
    have := hβ ψ; rw [h, hβ ψ'] at this
    exact Subtype.ext (HahnSeries.ofPowerSeries_injective this.symm)

  obtain ⟨D, hD⟩ := exists_divisor_forall_eq_weightFloor_fieldC L N m
  obtain ⟨Dj, hDj, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) (F := ↥(modularFunctionFieldC L N)) (jGeomGen L N)
    (by
      intro h
      have : (jqModC L : LaurentSeries L) = 0 := congrArg (fun z : ↥(modularFunctionFieldC L N) => (z : LaurentSeries L)) h
      exact (thetaL_jqModC_ne_zero L) (by rw [this, map_zero]))
  set T := Dj.support.filter (fun w => Dj w < 0) with hTdef
  have hT : ∀ w, w ∈ T ↔ w.ord (jGeomGen L N) < 0 := by
    intro w; rw [hTdef, Finset.mem_filter, Finsupp.mem_support_iff, hDj w]; omega
  set E : Divisor L ↥(modularFunctionFieldC L N) := D - ∑ w ∈ T, Finsupp.single w 1 with hEdef
  have hind : ∀ v, (∑ w ∈ T, Finsupp.single w (1 : ℤ)) v = if v ∈ T then 1 else 0 := by
    intro v
    rw [Finset.sum_apply']
    simp only [Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
  have hE : ∀ w, E w = weightFloor L N m w - (if w.ord (jGeomGen L N) < 0 then 1 else 0) := by
    intro w
    rw [hEdef, Finsupp.sub_apply, hD w, hind, show (if w ∈ T then (1 : ℤ) else 0) = if w.ord (jGeomGen L N) < 0 then 1 else 0 from by
      simp only [hT w]]
  have hEle : ∀ w, E w ≤ D w := by
    intro w
    rw [hEdef, Finsupp.sub_apply, hind]
    split_ifs <;> omega

  have hLDfin : FiniteDimensional L ↥(riemannRochSpace D) := by
    have key : ∀ H : ↥(riemannRochSpace D), ∃ ψ : ↥V,
        HahnSeries.ofPowerSeries ℤ L (ψ : PowerSeries L) = qexpOfWeight L (m : ℤ) ((H : ↥(modularFunctionFieldC L N)) : LaurentSeries L) := by
      intro H
      have hDw : (H : ↥(modularFunctionFieldC L N)) ∈ riemannRochSpace (weightDivisor L N m) := by
        have : weightDivisor L N m = D := by
          ext w; rw [weightDivisor_apply L N m ⟨D, hD⟩ w, hD w]
        rw [this]; exact H.2
      have hH := isModPFormFn_of_mem_L p L N hN m H hDw
      obtain ⟨ψ, hψ, hq⟩ := ModPForms.exists_mem_modPMod_ofPowerSeries_eq_qexpOfWeight_of_isModPFormFn p hp5 N hpN L m _ hH
      exact ⟨⟨ψ, hψ⟩, hq⟩
    choose lift hlift using key
    have hinj : Function.Injective lift := by
      intro H H' h
      have h1 := hlift H; have h2 := hlift H'
      rw [h] at h1; rw [h1] at h2
      exact Subtype.ext (eq_of_qexpOfWeight_eq L N m h2)

    let liftₗ : ↥(riemannRochSpace D) →ₗ[L] ↥V :=
      { toFun := lift
        map_add' := fun H H' => by
          apply Subtype.ext
          apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := L)
          rw [Submodule.coe_add, map_add, hlift, hlift, hlift, Submodule.coe_add, IntermediateField.coe_add, qexpOfWeight_eq,
            qexpOfWeight_eq, qexpOfWeight_eq, add_mul]
        map_smul' := fun c H => by
          apply Subtype.ext
          apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := L)
          simp only [RingHom.id_apply]
          rw [hlift, Submodule.coe_smul, IntermediateField.coe_smul, qexpOfWeight_eq, Algebra.smul_def, mul_assoc,
            HahnSeries.algebraMap_apply', show algebraMap L (PowerSeries L) c = PowerSeries.C c by simp,
            HahnSeries.ofPowerSeries_C, ← qexpOfWeight_eq, ← hlift, Submodule.coe_smul,
            show c • ((lift H : ↥V) : PowerSeries L) = PowerSeries.C c * ((lift H : ↥V) : PowerSeries L) by rw [PowerSeries.smul_eq_C_mul],
            map_mul, HahnSeries.ofPowerSeries_C] }
    exact Module.Finite.of_injective liftₗ hinj
  have hLEle : riemannRochSpace E ≤ riemannRochSpace D := by
    intro f hf
    rw [mem_riemannRochSpace_iff] at hf ⊢
    intro v
    rcases hf v with h0 | h
    · exact Or.inl h0
    · exact Or.inr (le_trans (neg_le_neg (hEle v)) h)
  haveI hLEfin : FiniteDimensional L ↥(riemannRochSpace E) :=
    Module.Finite.of_injective (Submodule.inclusion hLEle) (Submodule.inclusion_injective hLEle)

  set Tsub : Submodule L ↥V := (riemannRochSpace E).comap β with hTsub
  set T' : Submodule L (PowerSeries L) := Tsub.map V.subtype with hT'
  have hcusp_le : ModPForms.modPCusp N (2 * (m : ℤ)) L ≤ T' := by
    intro ψ hψ
    have hψV : ψ ∈ V := ModPForms.modPCusp_le_modPMod N (2 * (m : ℤ)) L hψ
    obtain ⟨H, hHc, hHq⟩ := ModPForms.exists_isModPCuspFormFn_qexpOfWeight_eq_of_mem_modPCusp p N hpN L m ψ hψ
    have hHβ : β ⟨ψ, hψV⟩ = H := eq_of_qexpOfWeight_eq L N m (by rw [hβ, hHq])
    refine ⟨⟨ψ, hψV⟩, ?_, rfl⟩
    show β ⟨ψ, hψV⟩ ∈ riemannRochSpace E
    rw [hHβ]
    exact (mem_riemannRochSpace_iff_isModPCuspFormFn_of_forall_eq_weightFloor_sub p hp5 N hpN L m hm E hE H).2 hHc
  have hdim : Module.finrank L ↥T' ≤ Module.finrank L ↥(ModPForms.modPCusp N (2 * (m : ℤ)) L) := by

    have h1 : Module.finrank L ↥T' = Module.finrank L ↥Tsub := by
      rw [hT']; exact (Submodule.finrank_map_subtype_eq V Tsub)
    let r : ↥Tsub →ₗ[L] ↥(riemannRochSpace E) := (β.domRestrict Tsub).codRestrict _ (fun x => x.2)
    have hr : Function.Injective r := by
      intro x y h
      have : β x = β y := congrArg (fun z : ↥(riemannRochSpace E) => (z : ↥(modularFunctionFieldC L N))) h
      exact Subtype.ext (hβinj this)
    have h2 : Module.finrank L ↥Tsub ≤ ell E := LinearMap.finrank_le_finrank_of_injective hr
    have h3 := ell_le_dimFormulaCusp_of_forall_eq_weightFloor_sub p hp5 N hpN L m hm E hE
    have h4 := ModPForms.dimFormulaCusp_le_finrank_modPCusp N m hm L
    have h5 : (Module.finrank L ↥Tsub : ℚ) ≤ Module.finrank L ↥(ModPForms.modPCusp N (2 * (m : ℤ)) L) :=
      le_trans (le_trans (by exact_mod_cast h2) h3) h4
    rw [h1]; exact_mod_cast h5
  haveI : FiniteDimensional L ↥T' := by
    rw [hT']; infer_instance
  have heq : ModPForms.modPCusp N (2 * (m : ℤ)) L = T' := Submodule.eq_of_le_of_finrank_le hcusp_le hdim

  have hGβ : β ⟨φ, hφ⟩ = G := eq_of_qexpOfWeight_eq L N m (by rw [hβ, hGφ])
  rw [heq]
  refine ⟨⟨φ, hφ⟩, ?_, rfl⟩
  show β ⟨φ, hφ⟩ ∈ riemannRochSpace E
  rw [hGβ]
  exact (mem_riemannRochSpace_iff_isModPCuspFormFn_of_forall_eq_weightFloor_sub p hp5 N hpN L m hm E hE G).2 hG

end Closed

end SpanCusp

theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type) [Field K] [CharP K p] (m : ℕ)
    (φ : PowerSeries K) (hφ : φ ∈ ModPForms.modPMod N (2 * (m : ℤ)) K)
    (G : ↥(modularFunctionFieldC K N)) (hG : IsModPCuspFormFn K m (G : LaurentSeries K))
    (hGφ : qexpOfWeight K (m : ℤ) (G : LaurentSeries K) = HahnSeries.ofPowerSeries ℤ K φ) :
    φ ∈ ModPForms.modPCusp N (2 * (m : ℤ)) K := by
  classical
  let L := AlgebraicClosure K
  let ι : K →+* L := algebraMap K L
  haveI : CharP L p := charP_of_injective_algebraMap ι.injective p

  have hφ' := SpanCuspBC.map_mem_modPMod ι N (2 * (m : ℤ)) hφ
  have hG' := SpanCuspBC.isModPCuspFormFn_coeffMap ι m (G : LaurentSeries K) hG
  have hGmem := SpanCuspBC.coeffMap_mem_modularFunctionFieldC ι N G.2
  have hq : qexpOfWeight L (m : ℤ) (ModularCurve.coeffMap ι (G : LaurentSeries K)) = HahnSeries.ofPowerSeries ℤ L (PowerSeries.map ι φ) := by
    rw [← SpanCuspBC.coeffMap_qexpOfWeight, hGφ, SpanCuspBC.coeffMap_ofPowerSeries]

  rcases Nat.eq_zero_or_pos m with hm0 | hm
  · subst hm0
    have hN : (N : L) ≠ 0 := fun h => hpN ((CharP.cast_eq_zero_iff L p N).1 h)
    have h0 := eq_zero_of_isModPCuspFormFn_zero p L N hN ⟨_, hGmem⟩ hG'
    have : HahnSeries.ofPowerSeries ℤ L (PowerSeries.map ι φ) = 0 := by
      rw [← hq, show ModularCurve.coeffMap ι (G : LaurentSeries K) = ((⟨_, hGmem⟩ : ↥(modularFunctionFieldC L N)) : LaurentSeries L) from rfl,
        h0, ZeroMemClass.coe_zero, SpanCusp.qexpOfWeight_eq, zero_mul]
    have hφ0 : PowerSeries.map ι φ = 0 := HahnSeries.ofPowerSeries_injective (by rw [this, map_zero])
    have : φ = 0 := PowerSeries.map_injective ι ι.injective (by rw [hφ0, map_zero])
    rw [this]; exact zero_mem _
  · have hL := SpanCusp.main_closed p hp5 N hpN L m hm (PowerSeries.map ι φ) hφ' ⟨_, hGmem⟩ hG' hq
    exact SpanCuspBC.mem_modPCusp_of_map_mem ι N (2 * (m : ℤ)) φ hL

end S_ModPForms_mem_modPCusp_of_mem_modPMod_of_isModPCuspFormFn
end P2MW
export P2MW.S_ModPForms_mem_modPCusp_of_mem_modPMod_of_isModPCuspFormFn (solution)
