-- Prove2me | solution 1 for ModularCurve.SSHeckeV2.exists_omegaHecke_dualMap_theta_and_exit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/88296572-bc90-5d05-91ce-08f7da29c504

import Mathlib
import Definitions.Def_ModularCurve_SSCarrier
import Definitions.Def_ModularCurve_SSHeckeV2
import Definitions.Def_AlgebraicCurve_WeilOfKaehler
import Definitions.Def_ModularCurve_ModPFormFn
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_SerrePairing
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Theorems.Thm_ModularCurve_hasse_smul_traceAlong_smul_pullbackAlong_smul_D_jGeomGen_eq
import Definitions.Def_AlgebraicCurve_RiemannRochRows
import Theorems.Thm_AlgebraicCurve_exists_weilSmul_eq_of_riemannIndexFormula
import Theorems.Thm_AlgebraicCurve_eq_zero_or_exists_eq_weilOfKaehler_smul_of_mem_omegaSpace
import Theorems.Thm_ModularCurve_theta_ssHeckeFun_eq_inv_smul_dualMap_of_forall_weilOfKaehler
import Theorems.Thm_AlgebraicCurve_riemannIndexFormula_of_genusReached
import Theorems.Thm_AlgebraicCurve_riemannGenusReached_of_stichtenothGenusExists
import Theorems.Thm_ModularCurve_stichtenothGenusExists_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_constantsAreBase_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_weilOfKaehler_smul_D_jGeomGen_mem_omegaSpace_iff_isModPCuspFormFn
import Theorems.Thm_ModularCurve_exists_coe_eq_thetaL_jqModC_zpow_and_stackOrd_eq
import Theorems.Thm_ModularCurve_isQExpansionDiffAlong_qExpansionDiffAlong
import Theorems.Thm_ModularCurve_theta_coeff
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Theorems.Thm_ModularCurve_SSHeckeV2_trace_heckeBetaC_mul_pow_comm_of_mem
import Theorems.Thm_ModularCurve_isAffineGeomPlace_or_ord_jGeomGen_lt_zero
import Theorems.Thm_ModularCurve_exists_divisor_forall_eq_weightFloor_fieldC
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_WeightDivisor
import Theorems.Thm_ModPForms_exists_mem_modPCusp_ofPowerSeries_eq_qexpOfWeight_of_isModPCuspFormFn
import Theorems.Thm_ModPForms_heckePS_mem_modPCusp
import Theorems.Thm_ModPForms_exists_isModPCuspFormFn_qexpOfWeight_eq_of_mem_modPCusp
import Theorems.Thm_ModularCurve_qexpOfWeight_trace_heckeBetaC_mul_pow_eq_heckePS_of_eq_smul_map
import Theorems.Thm_ModularCurve_SSHeckeV2_heckeMultiplier_spec
import Theorems.Thm_ModPForms_modPCusp_le_modPMod
import Theorems.Thm_ModPForms_exists_isModPFormFn_qexpOfWeight_eq_of_mem_modPMod
import Theorems.Thm_ModularCurve_mem_riemannRochSpace_weightDivisor_iff_isModPFormFn
import Definitions.Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Theorems.Thm_ModularCurve_omegaSpace_eq_bot_of_two_mul_eq_add_one
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_ModularCurve_isCurveOver_charLDegeneracyRoof
import Theorems.Thm_ModularCurve_ssPlaces_nonempty
import Theorems.Thm_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul
import Theorems.Thm_ModularCurve_essFiniteType_modularFunctionFieldFullC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit
p2m_attr_erase "instance" "ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup ModularCurve.instIsElliptic_tateLaurent ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin"
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateBase CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree HeckeEis.instFiniteProjLineCusps HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.numberField_of_finiteDimensional ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.cechH1.traceAlong_mk AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply AlgebraicCurve.cechH1.pullbackAlong_mk compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero"
p2m_attr_erase "simp" "TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul"
p2m_attr_erase "simp" "ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm ModularCurve.cuspCount_one HahnSeries.ramScale_apply PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU LaurentSeries.coeff_heckeV LaurentSeries.coeff_heckeU FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₃ AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T"
p2m_attr_erase "simp" "ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply HeckeEis.binaryFormEval_mk HeckeEis.binaryFormAlphaAdj_apply_coe HeckeEis.binaryFormRepSL_apply_coe ModularCurve.ProjectiveLine.vecMulRow_snd HeckeEis.projLineRepSL_apply HeckeEis.projLineAct_one HeckeEis.projLineRep_apply HeckeEis.projLineAlphaAdj_apply ModularCurve.ProjectiveLine.vecMulRow_fst ModularCurve.ProjectiveLine.vecMul_mk HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero HeckeEis.coe_linePow ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one"
p2m_attr_erase "simp" "ModularCurve.symPoly_zero ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "SSCarrier placeWidth ssPlaces jGeomGen jqModC modularFunctionFieldC coeff_jqModC_neg_one heckeMultiplier liftFun ssHeckeFun charLDegeneracyRoof heckeAlphaC heckeBetaC thetaL thetaL_apply qExpansionDiffAlong weightFloor weightDivisor weightDivisor_apply thetaJ qexpOfWeight IsModPCuspFormFn hasse_smul_traceAlong_smul_pullbackAlong_smul_D_jGeomGen_eq theta_ssHeckeFun_eq_inv_smul_dualMap_of_forall_weilOfKaehler stichtenothGenusExists_modularFunctionFieldC_of_perfectField constantsAreBase_modularFunctionFieldC_of_perfectField weilOfKaehler_smul_D_jGeomGen_mem_omegaSpace_iff_isModPCuspFormFn exists_coe_eq_thetaL_jqModC_zpow_and_stackOrd_eq isQExpansionDiffAlong_qExpansionDiffAlong theta_coeff SSHeckeV2.trace_heckeBetaC_mul_pow_comm_of_mem isAffineGeomPlace_or_ord_jGeomGen_lt_zero exists_divisor_forall_eq_weightFloor_fieldC qexpOfWeight_trace_heckeBetaC_mul_pow_eq_heckePS_of_eq_smul_map SSHeckeV2.heckeMultiplier_spec mem_riemannRochSpace_weightDivisor_iff_isModPFormFn omegaSpace_eq_bot_of_two_mul_eq_add_one isCurveOver_charLDegeneracyRoof ssPlaces_nonempty charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul essFiniteType_modularFunctionFieldFullC"
namespace OmegaSide
namespace A
p2m_open "ModularCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem kaehlerResidueTerm_smulF_left [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    [HasCanonicalLocalResidueKStar K F]
    (f : F) (ω : Ω[F⁄K]) (α : Place K F → F) (v : Place K F) :
    kaehlerResidueTerm (f • ω) α v = kaehlerResidueTerm ω (mulAdele K f α) v := by
  unfold kaehlerResidueTerm
  rw [v.differentialCoeff_smul, mulAdele_apply]
  ring_nf

theorem weilOfKaehler_smulF [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    [HasCanonicalLocalResidueKStar K F] [HasPrincipalDivisors K F] [HasCanonicalDivisor (K := K) (F := F)]
    {f : F} {ω : Ω[F⁄K]} (hω : ω ≠ 0) (hf : f ≠ 0) :
    weilOfKaehler K F (ω := f • ω) (smul_ne_zero hf hω) = weilSmul K F f (weilOfKaehler K F hω) := by
  apply LinearMap.ext
  intro α
  rw [weilSmul_apply, weilOfKaehler_apply, weilOfKaehler_apply]
  refine finsum_congr fun v => ?_
  rw [kaehlerResidueTerm_smulF_left, adeleSpaceMul_coe]

end ModularCurve.OmegaSide.A

namespace ModularCurve
p2m_export "ModularCurve" "SSCarrier placeWidth ssPlaces jGeomGen jqModC modularFunctionFieldC coeff_jqModC_neg_one heckeMultiplier liftFun ssHeckeFun charLDegeneracyRoof heckeAlphaC heckeBetaC thetaL thetaL_apply qExpansionDiffAlong weightFloor weightDivisor weightDivisor_apply thetaJ qexpOfWeight IsModPCuspFormFn hasse_smul_traceAlong_smul_pullbackAlong_smul_D_jGeomGen_eq theta_ssHeckeFun_eq_inv_smul_dualMap_of_forall_weilOfKaehler stichtenothGenusExists_modularFunctionFieldC_of_perfectField constantsAreBase_modularFunctionFieldC_of_perfectField weilOfKaehler_smul_D_jGeomGen_mem_omegaSpace_iff_isModPCuspFormFn exists_coe_eq_thetaL_jqModC_zpow_and_stackOrd_eq isQExpansionDiffAlong_qExpansionDiffAlong theta_coeff SSHeckeV2.trace_heckeBetaC_mul_pow_comm_of_mem isAffineGeomPlace_or_ord_jGeomGen_lt_zero exists_divisor_forall_eq_weightFloor_fieldC qexpOfWeight_trace_heckeBetaC_mul_pow_eq_heckePS_of_eq_smul_map SSHeckeV2.heckeMultiplier_spec mem_riemannRochSpace_weightDivisor_iff_isModPFormFn omegaSpace_eq_bot_of_two_mul_eq_add_one isCurveOver_charLDegeneracyRoof ssPlaces_nonempty charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul essFiniteType_modularFunctionFieldFullC"
namespace OmegaSide
namespace B
p2m_open "ModularCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

section
variable [HasPrincipalDivisors K F]

def smulMap (φ : Module.Dual K (adeleSpace K F)) : F →ₗ[K] Module.Dual K (adeleSpace K F) where
  toFun G := weilSmul K F G φ
  map_add' G H := by
    apply LinearMap.ext; intro α
    rw [LinearMap.add_apply, weilSmul_apply, weilSmul_apply, weilSmul_apply, ← map_add]
    congr 1
    apply Subtype.ext
    rw [Submodule.coe_add, adeleSpaceMul_coe, adeleSpaceMul_coe, adeleSpaceMul_coe]
    funext v; simp [mulAdele_apply, add_mul]
  map_smul' c G := by
    apply LinearMap.ext; intro α
    rw [RingHom.id_apply, LinearMap.smul_apply, weilSmul_apply, weilSmul_apply, ← map_smul]
    congr 1
    apply Subtype.ext
    rw [Submodule.coe_smul, adeleSpaceMul_coe, adeleSpaceMul_coe]
    funext v; simp [mulAdele_apply, Algebra.smul_def, mul_assoc]

@[scoped simp] theorem smulMap_apply (φ : Module.Dual K (adeleSpace K F)) (G : F) : smulMap φ G = weilSmul K F G φ := rfl

end

variable [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] [Nonempty (Place K F)]
  [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]] [HasCanonicalLocalResidueKStar K F]

def lam (ω₁ : Ω[F⁄K]) (hω₁ : ω₁ ≠ 0) : F →ₗ[K] Module.Dual K (adeleSpace K F) :=
  haveI : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
  smulMap (weilOfKaehler K F hω₁)

variable {ω₁ : Ω[F⁄K]} (hω₁ : ω₁ ≠ 0)

theorem lam_apply_of_ne_zero {G : F} (hG : G ≠ 0) :
    lam ω₁ hω₁ G = weilOfKaehler K F (ω := G • ω₁) (smul_ne_zero hG hω₁) := by
  haveI : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
  show weilSmul K F G (weilOfKaehler K F hω₁) = _
  rw [ModularCurve.OmegaSide.A.weilOfKaehler_smulF hω₁ hG]

theorem lam_injective (hagree : WeilKaehlerAgree K F) : Function.Injective (lam ω₁ hω₁) := by
  haveI : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro G hG
  by_contra hG0
  rw [LinearMap.mem_ker, lam_apply_of_ne_zero hω₁ hG0] at hG
  exact (hagree (smul_ne_zero hG0 hω₁)).1 hG

def W (D : Divisor K F) : Submodule K F := (omegaSpace (K := K) (F := F) D).comap (lam ω₁ hω₁)

theorem mem_W {D : Divisor K F} {G : F} : G ∈ W hω₁ D ↔ lam ω₁ hω₁ G ∈ omegaSpace (K := K) (F := F) D := Iff.rfl

def lamW (D : Divisor K F) : ↥(W hω₁ D) →ₗ[K] ↥(omegaSpace (K := K) (F := F) D) :=
  (lam ω₁ hω₁).restrict fun G hG => hG

theorem lamW_bijective (hRI : RiemannIndexFormula K F) (hagree : WeilKaehlerAgree K F) (D : Divisor K F) :
    Function.Bijective (lamW hω₁ D) := by
  haveI : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
  constructor
  · intro a b h
    apply Subtype.ext
    apply lam_injective hω₁ hagree
    exact congrArg Subtype.val h
  · intro μ
    rcases AlgebraicCurve.eq_zero_or_exists_eq_weilOfKaehler_smul_of_mem_omegaSpace hRI hagree hω₁ D μ.1 μ.2 with h0 | ⟨f, hf, hμ⟩
    · exact ⟨0, Subtype.ext (by rw [map_zero]; exact h0.symm)⟩
    · have hfW : f ∈ W hω₁ D := by
        rw [mem_W, lam_apply_of_ne_zero hω₁ hf, ← hμ]; exact μ.2
      exact ⟨⟨f, hfW⟩, Subtype.ext (by show lam ω₁ hω₁ f = μ.1; rw [lam_apply_of_ne_zero hω₁ hf, hμ])⟩

def E (hRI : RiemannIndexFormula K F) (hagree : WeilKaehlerAgree K F) (D : Divisor K F) :
    ↥(omegaSpace (K := K) (F := F) D) ≃ₗ[K] ↥(W hω₁ D) :=
  (LinearEquiv.ofBijective (lamW hω₁ D) (lamW_bijective hω₁ hRI hagree D)).symm

theorem lam_E (hRI : RiemannIndexFormula K F) (hagree : WeilKaehlerAgree K F) (D : Divisor K F)
    (μ : ↥(omegaSpace (K := K) (F := F) D)) :
    lam ω₁ hω₁ (E hω₁ hRI hagree D μ : F) = μ := by
  have := (LinearEquiv.ofBijective (lamW hω₁ D) (lamW_bijective hω₁ hRI hagree D)).apply_symm_apply μ
  exact congrArg Subtype.val this

theorem E_symm_apply (hRI : RiemannIndexFormula K F) (hagree : WeilKaehlerAgree K F) (D : Divisor K F) (G : ↥(W hω₁ D)) :
    ((E hω₁ hRI hagree D).symm G : Module.Dual K (adeleSpace K F)) = lam ω₁ hω₁ G := rfl

end ModularCurve.OmegaSide.B
p2m_reactivate "P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide.B"
p2m_reactivate "P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide"
p2m_reactivate "P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "SSCarrier placeWidth ssPlaces jGeomGen jqModC modularFunctionFieldC coeff_jqModC_neg_one heckeMultiplier liftFun ssHeckeFun charLDegeneracyRoof heckeAlphaC heckeBetaC thetaL thetaL_apply qExpansionDiffAlong weightFloor weightDivisor weightDivisor_apply thetaJ qexpOfWeight IsModPCuspFormFn hasse_smul_traceAlong_smul_pullbackAlong_smul_D_jGeomGen_eq theta_ssHeckeFun_eq_inv_smul_dualMap_of_forall_weilOfKaehler stichtenothGenusExists_modularFunctionFieldC_of_perfectField constantsAreBase_modularFunctionFieldC_of_perfectField weilOfKaehler_smul_D_jGeomGen_mem_omegaSpace_iff_isModPCuspFormFn exists_coe_eq_thetaL_jqModC_zpow_and_stackOrd_eq isQExpansionDiffAlong_qExpansionDiffAlong theta_coeff SSHeckeV2.trace_heckeBetaC_mul_pow_comm_of_mem isAffineGeomPlace_or_ord_jGeomGen_lt_zero exists_divisor_forall_eq_weightFloor_fieldC qexpOfWeight_trace_heckeBetaC_mul_pow_eq_heckePS_of_eq_smul_map SSHeckeV2.heckeMultiplier_spec mem_riemannRochSpace_weightDivisor_iff_isModPFormFn omegaSpace_eq_bot_of_two_mul_eq_add_one isCurveOver_charLDegeneracyRoof ssPlaces_nonempty charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul essFiniteType_modularFunctionFieldFullC"
namespace OmegaSide
namespace B3a
p2m_open "ModularCurve"

theorem thetaJ_ne_zero (K : Type) [Field K] : ModularCurve.thetaJ K ≠ 0 := by
  intro h0
  have h1 := congrArg (fun s : LaurentSeries K => s.coeff (-1)) h0
  simp only [HahnSeries.coeff_zero] at h1
  rw [ModularCurve.thetaJ, thetaL_apply, theta_coeff, ModularCurve.coeff_jqModC_neg_one, zsmul_eq_mul, mul_one] at h1
  norm_num at h1

theorem qexpOfWeight_injective (K : Type) [Field K] (m : ℕ) :
    Function.Injective (ModularCurve.qexpOfWeight K (m : ℤ)) := by
  intro x y hxy
  unfold ModularCurve.qexpOfWeight at hxy
  exact mul_left_injective₀ (zpow_ne_zero _ (thetaJ_ne_zero K)) hxy

theorem coe_algebraMap_mul (K : Type) [Field K] (N : ℕ) [NeZero N] (c : K) (t : ↥(modularFunctionFieldC K N)) :
    (((algebraMap K ↥(modularFunctionFieldC K N) c * t : ↥(modularFunctionFieldC K N))) : LaurentSeries K) = HahnSeries.C c * (t : LaurentSeries K) := by
  rw [IntermediateField.coe_mul]
  congr 1
  have e1 : ((algebraMap K ↥(modularFunctionFieldC K N) c : ↥(modularFunctionFieldC K N)) : LaurentSeries K)
      = algebraMap K (LaurentSeries K) c := by
    rfl
  rw [e1]
  simp [HahnSeries.algebraMap_apply', HahnSeries.ofPowerSeries_C]

theorem isModPCuspFormFn_Tfun
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N]
    (hN : (N : K) ≠ 0) (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (hℓp : ℓ ≠ p)
    (m' : ℕ) (hm' : 1 ≤ m') (G : ↥(modularFunctionFieldC K N)) (hG : ModularCurve.IsModPCuspFormFn K m' (G : LaurentSeries K)) :
    letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ)
    ModularCurve.IsModPCuspFormFn K m'
      ((algebraMap K ↥(modularFunctionFieldC K N) ((ℓ : K) ^ (m' - 1)) *
          Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ) (heckeBetaC K N ℓ G * ModularCurve.heckeMultiplier N K ℓ ^ m') : ↥(modularFunctionFieldC K N)) : LaurentSeries K) := by
  letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ)
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have hpN : ¬ p ∣ N := fun h => hN ((CharP.cast_eq_zero_iff K p N).mpr h)
  have hpℓ : ¬ p ∣ ℓ := fun h => hℓp ((Nat.prime_dvd_prime_iff_eq (Fact.out) (Fact.out)).mp h).symm
  have hℓK : (ℓ : K) ≠ 0 := fun h => hpℓ ((CharP.cast_eq_zero_iff K p ℓ).mp h)

  haveI : NeZero ((ℓ : ℕ) : K) := ⟨hℓK⟩
  haveI := IsSepClosed.hasEnoughRootsOfUnity K ℓ
  obtain ⟨ζ0, hζ0⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K ℓ

  obtain ⟨φ, hφc, hφq⟩ :=
    ModPForms.exists_mem_modPCusp_ofPowerSeries_eq_qexpOfWeight_of_isModPCuspFormFn p hp5 N hpN K m' G hG
  have hT := ModularCurve.qexpOfWeight_trace_heckeBetaC_mul_pow_eq_heckePS_of_eq_smul_map K N ℓ hN hℓN
    (Units.mk0 ζ0 (hζ0.ne_zero (NeZero.ne ℓ))) (by simpa using hζ0) m' hm' G φ hφq
    (ModularCurve.heckeMultiplier N K ℓ) (ModularCurve.SSHeckeV2.heckeMultiplier_spec p hp5 K N hN ℓ hℓN hℓK)
  have hc := ModPForms.heckePS_mem_modPCusp N K (2 * (m' : ℤ)) ℓ (Fact.out) hℓN φ hφc
  obtain ⟨G', hG'c, hG'q⟩ :=
    ModPForms.exists_isModPCuspFormFn_qexpOfWeight_eq_of_mem_modPCusp p N hpN K m' _ hc
  have hGG : ((G' : ↥(modularFunctionFieldC K N)) : LaurentSeries K)
      = HahnSeries.C ((ℓ : K) ^ (m' - 1)) *
          ((Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ) (heckeBetaC K N ℓ G * ModularCurve.heckeMultiplier N K ℓ ^ m') : ↥(modularFunctionFieldC K N)) : LaurentSeries K) :=
    qexpOfWeight_injective K m' (hG'q.trans hT)
  rw [coe_algebraMap_mul, ← hGG]
  exact hG'c

theorem mem_riemannRochSpace_weightDivisor_of_isModPCuspFormFn
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N]
    (hN : (N : K) ≠ 0) (m' : ℕ) (hm' : 1 ≤ m') (G : ↥(modularFunctionFieldC K N)) (hG : ModularCurve.IsModPCuspFormFn K m' (G : LaurentSeries K)) :
    G ∈ AlgebraicCurve.riemannRochSpace (ModularCurve.weightDivisor K N m') := by
  have hpN : ¬ p ∣ N := fun h => hN ((CharP.cast_eq_zero_iff K p N).mpr h)
  obtain ⟨φ, hφc, hφq⟩ :=
    ModPForms.exists_mem_modPCusp_ofPowerSeries_eq_qexpOfWeight_of_isModPCuspFormFn p hp5 N hpN K m' G hG
  have hφm := ModPForms.modPCusp_le_modPMod N (2 * (m' : ℤ)) K hφc
  obtain ⟨G₁, hG₁f, hG₁q⟩ := ModPForms.exists_isModPFormFn_qexpOfWeight_eq_of_mem_modPMod p N hpN K m' φ hφm
  have h1 : G₁ = G := Subtype.ext (qexpOfWeight_injective K m' (hG₁q.trans hφq))
  subst h1
  exact (ModularCurve.mem_riemannRochSpace_weightDivisor_iff_isModPFormFn p hp5 N hpN K m' G₁).mpr hG₁f

end ModularCurve.OmegaSide.B3a
p2m_reactivate "P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide.B"
p2m_reactivate "P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide.B"
p2m_reactivate "P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide.B"

namespace ModularCurve
p2m_export "ModularCurve" "SSCarrier placeWidth ssPlaces jGeomGen jqModC modularFunctionFieldC coeff_jqModC_neg_one heckeMultiplier liftFun ssHeckeFun charLDegeneracyRoof heckeAlphaC heckeBetaC thetaL thetaL_apply qExpansionDiffAlong weightFloor weightDivisor weightDivisor_apply thetaJ qexpOfWeight IsModPCuspFormFn hasse_smul_traceAlong_smul_pullbackAlong_smul_D_jGeomGen_eq theta_ssHeckeFun_eq_inv_smul_dualMap_of_forall_weilOfKaehler stichtenothGenusExists_modularFunctionFieldC_of_perfectField constantsAreBase_modularFunctionFieldC_of_perfectField weilOfKaehler_smul_D_jGeomGen_mem_omegaSpace_iff_isModPCuspFormFn exists_coe_eq_thetaL_jqModC_zpow_and_stackOrd_eq isQExpansionDiffAlong_qExpansionDiffAlong theta_coeff SSHeckeV2.trace_heckeBetaC_mul_pow_comm_of_mem isAffineGeomPlace_or_ord_jGeomGen_lt_zero exists_divisor_forall_eq_weightFloor_fieldC qexpOfWeight_trace_heckeBetaC_mul_pow_eq_heckePS_of_eq_smul_map SSHeckeV2.heckeMultiplier_spec mem_riemannRochSpace_weightDivisor_iff_isModPFormFn omegaSpace_eq_bot_of_two_mul_eq_add_one isCurveOver_charLDegeneracyRoof ssPlaces_nonempty charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul essFiniteType_modularFunctionFieldFullC"
namespace OmegaSide
namespace B3
p2m_open "ModularCurve"

variable (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N]

theorem thetaL_coeff' (f : LaurentSeries K) (n : ℤ) : (thetaL K f).coeff n = (n : K) * f.coeff n := by
  rw [thetaL_apply, theta_coeff, zsmul_eq_mul]

theorem thetaL_jqModC_ne_zero : thetaL K (jqModC K) ≠ 0 := by
  intro h
  have h1 := congrArg (fun s : LaurentSeries K => s.coeff (-1)) h
  beta_reduce at h1
  rw [thetaL_coeff', coeff_jqModC_neg_one, HahnSeries.coeff_zero, mul_one] at h1
  norm_num at h1

theorem D_jGeomGen_ne_zero : KaehlerDifferential.D K ↥(modularFunctionFieldC K N) (jGeomGen K N) ≠ 0 := by
  intro h0
  set σ := IntermediateField.val (modularFunctionFieldC K N) with hσ
  have h1 := (ModularCurve.isQExpansionDiffAlong_qExpansionDiffAlong σ).1 (jGeomGen K N)
  have h2 : (qExpansionDiffAlong σ) ((KaehlerDifferential.D K ↥(modularFunctionFieldC K N)) (jGeomGen K N)) = 0 := by
    rw [h0]; exact LinearMap.map_zero _
  have h3 : thetaL K (σ (jGeomGen K N)) = 0 := by
    rw [← h1]
    convert h2 using 2
  exact thetaL_jqModC_ne_zero K h3

theorem riemannIndexFormula_F
    [AlgebraicCurve.IsCurveOver K ↥(modularFunctionFieldC K N)] [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := ↥(modularFunctionFieldC K N))]
    [∀ w : AlgebraicCurve.Place K ↥(modularFunctionFieldC K N), w.DCoordGenerates] [AlgebraicCurve.HasCanonicalLocalResidueKStar K ↥(modularFunctionFieldC K N)]
    (hagree : AlgebraicCurve.WeilKaehlerAgree K ↥(modularFunctionFieldC K N)) : RiemannIndexFormula K ↥(modularFunctionFieldC K N) :=
  AlgebraicCurve.riemannIndexFormula_of_genusReached (fun {_} {_} =>
    AlgebraicCurve.riemannGenusReached_of_stichtenothGenusExists
      (ModularCurve.stichtenothGenusExists_modularFunctionFieldC_of_perfectField K N) hagree
      (ModularCurve.constantsAreBase_modularFunctionFieldC_of_perfectField K N))

def hasseFn (hpN : ¬ p ∣ N) : ↥(modularFunctionFieldC K N) :=
  (ModularCurve.exists_coe_eq_thetaL_jqModC_zpow_and_stackOrd_eq p hp5 N hpN K).choose

theorem coe_hasseFn (hpN : ¬ p ∣ N) :
    ((hasseFn p hp5 K N hpN : ↥(modularFunctionFieldC K N)) : LaurentSeries K) = thetaL K (jqModC K) ^ (-(((p : ℤ) - 1) / 2)) :=
  (ModularCurve.exists_coe_eq_thetaL_jqModC_zpow_and_stackOrd_eq p hp5 N hpN K).choose_spec.1

theorem hasseFn_ne_zero (hpN : ¬ p ∣ N) : hasseFn p hp5 K N hpN ≠ 0 := by
  intro h0
  have := coe_hasseFn p hp5 K N hpN
  rw [h0] at this
  exact zpow_ne_zero _ (thetaL_jqModC_ne_zero K) (by simpa using this.symm)

def omega1 (hpN : ¬ p ∣ N) : Ω[↥(modularFunctionFieldC K N)⁄K] := (hasseFn p hp5 K N hpN)⁻¹ • KaehlerDifferential.D K ↥(modularFunctionFieldC K N) (jGeomGen K N)

theorem omega1_ne_zero (hpN : ¬ p ∣ N) : omega1 p hp5 K N hpN ≠ 0 :=
  smul_ne_zero (inv_ne_zero (hasseFn_ne_zero p hp5 K N hpN)) (D_jGeomGen_ne_zero K N)

end ModularCurve.OmegaSide.B3
p2m_reactivate "P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide.B"
p2m_reactivate "P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide.B"
p2m_reactivate "P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide.B"

namespace ModularCurve
p2m_export "ModularCurve" "SSCarrier placeWidth ssPlaces jGeomGen jqModC modularFunctionFieldC coeff_jqModC_neg_one heckeMultiplier liftFun ssHeckeFun charLDegeneracyRoof heckeAlphaC heckeBetaC thetaL thetaL_apply qExpansionDiffAlong weightFloor weightDivisor weightDivisor_apply thetaJ qexpOfWeight IsModPCuspFormFn hasse_smul_traceAlong_smul_pullbackAlong_smul_D_jGeomGen_eq theta_ssHeckeFun_eq_inv_smul_dualMap_of_forall_weilOfKaehler stichtenothGenusExists_modularFunctionFieldC_of_perfectField constantsAreBase_modularFunctionFieldC_of_perfectField weilOfKaehler_smul_D_jGeomGen_mem_omegaSpace_iff_isModPCuspFormFn exists_coe_eq_thetaL_jqModC_zpow_and_stackOrd_eq isQExpansionDiffAlong_qExpansionDiffAlong theta_coeff SSHeckeV2.trace_heckeBetaC_mul_pow_comm_of_mem isAffineGeomPlace_or_ord_jGeomGen_lt_zero exists_divisor_forall_eq_weightFloor_fieldC qexpOfWeight_trace_heckeBetaC_mul_pow_eq_heckePS_of_eq_smul_map SSHeckeV2.heckeMultiplier_spec mem_riemannRochSpace_weightDivisor_iff_isModPFormFn omegaSpace_eq_bot_of_two_mul_eq_add_one isCurveOver_charLDegeneracyRoof ssPlaces_nonempty charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul essFiniteType_modularFunctionFieldFullC"
namespace OmegaSide
namespace B3
p2m_open "ModularCurve"

variable (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N]

theorem weilOfKaehler_congr {F : Type*} [Field F] [Algebra K F]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K F] [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : AlgebraicCurve.Place K F, v.DCoordGenerates] [Nontrivial (Ω[F⁄K])] [AlgebraicCurve.HasPrincipalDivisors K F]
    {ω ω' : Ω[F⁄K]} (h : ω = ω') (hω : ω ≠ 0) (hω' : ω' ≠ 0) :
    AlgebraicCurve.weilOfKaehler K F hω = AlgebraicCurve.weilOfKaehler K F hω' := by
  subst h; rfl

variable [AlgebraicCurve.IsCurveOver K ↥(modularFunctionFieldC K N)] [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := ↥(modularFunctionFieldC K N))]
  [∀ w : AlgebraicCurve.Place K ↥(modularFunctionFieldC K N), w.DCoordGenerates] [Nontrivial (Ω[↥(modularFunctionFieldC K N)⁄K])]
  [AlgebraicCurve.HasPrincipalDivisors K ↥(modularFunctionFieldC K N)] [AlgebraicCurve.HasCanonicalLocalResidueKStar K ↥(modularFunctionFieldC K N)]
  [Nonempty (AlgebraicCurve.Place K ↥(modularFunctionFieldC K N))]

theorem mem_W_iff_isModPCuspFormFn
    (hagree : AlgebraicCurve.WeilKaehlerAgree K ↥(modularFunctionFieldC K N))
    (htame : ∀ w : AlgebraicCurve.Place K ↥(modularFunctionFieldC K N), w.ord (jGeomGen K N) < 0 → (((w.ord (jGeomGen K N)).natAbs : ℕ) : K) ≠ 0)
    (hN : (N : K) ≠ 0) (hpN : ¬ p ∣ N) (m m' : ℕ) (hm : 1 ≤ m) (hm' : 1 ≤ m') (hmm' : m + m' = (p + 1) / 2)
    (D' : AlgebraicCurve.Divisor K ↥(modularFunctionFieldC K N))
    (hD'1 : ∀ w, w ∈ ssPlaces p N K → ((placeWidth N w : ℤ) ∣ (m : ℤ)) → D' w = ModularCurve.weightDivisor K N m w - 1)
    (hD'0 : ∀ w, ¬ (w ∈ ssPlaces p N K ∧ ((placeWidth N w : ℤ) ∣ (m : ℤ))) → D' w = ModularCurve.weightDivisor K N m w)
    (G : ↥(modularFunctionFieldC K N)) (hG : G ≠ 0) :
    G ∈ ModularCurve.OmegaSide.B.W (omega1_ne_zero p hp5 K N hpN) D' ↔ ModularCurve.IsModPCuspFormFn K m' (G : LaurentSeries K) := by
  classical
  have hex := ModularCurve.exists_divisor_forall_eq_weightFloor_fieldC K N m
  have hD1 : ∀ w : AlgebraicCurve.Place K ↥(modularFunctionFieldC K N), w ∈ ssPlaces p N K → ((placeWidth N w : ℤ) ∣ (m : ℤ)) → D' w = weightFloor K N m w - 1 := by
    intro w hw hd; rw [hD'1 w hw hd, ModularCurve.weightDivisor_apply K N m hex w]
  have hD0 : ∀ w : AlgebraicCurve.Place K ↥(modularFunctionFieldC K N), ¬ (w ∈ ssPlaces p N K ∧ ((placeWidth N w : ℤ) ∣ (m : ℤ))) → D' w = weightFloor K N m w := by
    intro w hw; rw [hD'0 w hw, ModularCurve.weightDivisor_apply K N m hex w]
  set hp_ := hasseFn p hp5 K N hpN with hhp
  have hhp0 := hasseFn_ne_zero p hp5 K N hpN
  have hf : G * hp_⁻¹ ≠ 0 := mul_ne_zero hG (inv_ne_zero hhp0)
  have key := ModularCurve.weilOfKaehler_smul_D_jGeomGen_mem_omegaSpace_iff_isModPCuspFormFn p hp5 N hpN K hagree
    (D_jGeomGen_ne_zero K N) m m' hm hm' hmm' hp_ (coe_hasseFn p hp5 K N hpN)
    (ModularCurve.isAffineGeomPlace_or_ord_jGeomGen_lt_zero K N) htame D' hD1 hD0 (G * hp_⁻¹) hf
  rw [inv_mul_cancel_right₀ hhp0] at key
  rw [ModularCurve.OmegaSide.B.mem_W, ModularCurve.OmegaSide.B.lam_apply_of_ne_zero _ hG, ← key]
  have hω : G • omega1 p hp5 K N hpN = (G * hp_⁻¹) • KaehlerDifferential.D K ↥(modularFunctionFieldC K N) (jGeomGen K N) := by
    rw [omega1, smul_smul]
  rw [weilOfKaehler_congr K hω]

def TfunL (m' : ℕ) (ℓ : ℕ) [NeZero ℓ] : ↥(modularFunctionFieldC K N) →ₗ[K] ↥(modularFunctionFieldC K N) :=
  letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ)
  haveI := AlgebraicCurve.isScalarTower_along (heckeAlphaC K N ℓ)
  (LinearMap.mulLeft K (algebraMap K ↥(modularFunctionFieldC K N) ((ℓ : K) ^ (m' - 1)))) ∘ₗ
    ((Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ)).restrictScalars K) ∘ₗ
    (LinearMap.mulRight K (ModularCurve.heckeMultiplier N K ℓ ^ m')) ∘ₗ
    (heckeBetaC K N ℓ).toLinearMap

theorem TfunL_apply (m' : ℕ) (ℓ : ℕ) [NeZero ℓ] (G : ↥(modularFunctionFieldC K N)) :
    TfunL K N m' ℓ G = (letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ)
      algebraMap K ↥(modularFunctionFieldC K N) ((ℓ : K) ^ (m' - 1)) *
        Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ) (heckeBetaC K N ℓ G * ModularCurve.heckeMultiplier N K ℓ ^ m')) := rfl

end ModularCurve.OmegaSide.B3
p2m_reactivate "P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide.B"
p2m_reactivate "P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide.B"
p2m_reactivate "P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide.B"

namespace ModularCurve
p2m_export "ModularCurve" "SSCarrier placeWidth ssPlaces jGeomGen jqModC modularFunctionFieldC coeff_jqModC_neg_one heckeMultiplier liftFun ssHeckeFun charLDegeneracyRoof heckeAlphaC heckeBetaC thetaL thetaL_apply qExpansionDiffAlong weightFloor weightDivisor weightDivisor_apply thetaJ qexpOfWeight IsModPCuspFormFn hasse_smul_traceAlong_smul_pullbackAlong_smul_D_jGeomGen_eq theta_ssHeckeFun_eq_inv_smul_dualMap_of_forall_weilOfKaehler stichtenothGenusExists_modularFunctionFieldC_of_perfectField constantsAreBase_modularFunctionFieldC_of_perfectField weilOfKaehler_smul_D_jGeomGen_mem_omegaSpace_iff_isModPCuspFormFn exists_coe_eq_thetaL_jqModC_zpow_and_stackOrd_eq isQExpansionDiffAlong_qExpansionDiffAlong theta_coeff SSHeckeV2.trace_heckeBetaC_mul_pow_comm_of_mem isAffineGeomPlace_or_ord_jGeomGen_lt_zero exists_divisor_forall_eq_weightFloor_fieldC qexpOfWeight_trace_heckeBetaC_mul_pow_eq_heckePS_of_eq_smul_map SSHeckeV2.heckeMultiplier_spec mem_riemannRochSpace_weightDivisor_iff_isModPFormFn omegaSpace_eq_bot_of_two_mul_eq_add_one isCurveOver_charLDegeneracyRoof ssPlaces_nonempty charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul essFiniteType_modularFunctionFieldFullC"
namespace OmegaSide
namespace B3
p2m_open "ModularCurve"

variable (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N]
  [AlgebraicCurve.IsCurveOver K ↥(modularFunctionFieldC K N)] [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := ↥(modularFunctionFieldC K N))]
  [∀ w : AlgebraicCurve.Place K ↥(modularFunctionFieldC K N), w.DCoordGenerates] [Nontrivial (Ω[↥(modularFunctionFieldC K N)⁄K])]
  [AlgebraicCurve.HasPrincipalDivisors K ↥(modularFunctionFieldC K N)] [AlgebraicCurve.HasCanonicalLocalResidueKStar K ↥(modularFunctionFieldC K N)]
  [Nonempty (AlgebraicCurve.Place K ↥(modularFunctionFieldC K N))]

structure Ctx where
  hagree : AlgebraicCurve.WeilKaehlerAgree K ↥(modularFunctionFieldC K N)
  htame : ∀ w : AlgebraicCurve.Place K ↥(modularFunctionFieldC K N), w.ord (jGeomGen K N) < 0 → (((w.ord (jGeomGen K N)).natAbs : ℕ) : K) ≠ 0
  hN : (N : K) ≠ 0
  hpN : ¬ p ∣ N
  m : ℕ
  m' : ℕ
  hm : 1 ≤ m
  hm' : 1 ≤ m'
  hmm' : m + m' = (p + 1) / 2
  D' : AlgebraicCurve.Divisor K ↥(modularFunctionFieldC K N)
  hD'1 : ∀ w, w ∈ ssPlaces p N K → ((placeWidth N w : ℤ) ∣ (m : ℤ)) → D' w = ModularCurve.weightDivisor K N m w - 1
  hD'0 : ∀ w, ¬ (w ∈ ssPlaces p N K ∧ ((placeWidth N w : ℤ) ∣ (m : ℤ))) → D' w = ModularCurve.weightDivisor K N m w

variable {p K N}
variable (c : Ctx p K N)

def Ctx.hω₁ : omega1 p hp5 K N c.hpN ≠ 0 := omega1_ne_zero p hp5 K N c.hpN
def Ctx.hRI : RiemannIndexFormula K ↥(modularFunctionFieldC K N) := riemannIndexFormula_F K N c.hagree

abbrev Ctx.WW : Submodule K ↥(modularFunctionFieldC K N) := ModularCurve.OmegaSide.B.W (c.hω₁ hp5) c.D'
abbrev Ctx.EE : ↥(AlgebraicCurve.omegaSpace (K := K) (F := ↥(modularFunctionFieldC K N)) c.D') ≃ₗ[K] ↥(c.WW hp5) :=
  ModularCurve.OmegaSide.B.E (c.hω₁ hp5) (c.hRI) c.hagree c.D'

theorem Ctx.mem_WW_iff {G : ↥(modularFunctionFieldC K N)} (hG : G ≠ 0) : G ∈ c.WW hp5 ↔ ModularCurve.IsModPCuspFormFn K c.m' (G : LaurentSeries K) :=
  mem_W_iff_isModPCuspFormFn p hp5 K N c.hagree c.htame c.hN c.hpN c.m c.m' c.hm c.hm' c.hmm' c.D' c.hD'1 c.hD'0 G hG

theorem Ctx.TfunL_mem_WW (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (hℓp : ℓ ≠ p) {G : ↥(modularFunctionFieldC K N)} (hG : G ∈ c.WW hp5) :
    TfunL K N c.m' ℓ G ∈ c.WW hp5 := by
  by_cases hG0 : G = 0
  · rw [hG0, map_zero]; exact zero_mem _
  have hcusp := (c.mem_WW_iff hp5 hG0).mp hG
  have hT := ModularCurve.OmegaSide.B3a.isModPCuspFormFn_Tfun p hp5 K N c.hN ℓ hℓN hℓp c.m' c.hm' G hcusp
  by_cases hT0 : TfunL K N c.m' ℓ G = 0
  · rw [hT0]; exact zero_mem _
  exact (c.mem_WW_iff hp5 hT0).mpr hT

def Ctx.TfunW (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (hℓp : ℓ ≠ p) : ↥(c.WW hp5) →ₗ[K] ↥(c.WW hp5) :=
  (TfunL K N c.m' ℓ).restrict fun G hG => c.TfunL_mem_WW hp5 ℓ hℓN hℓp hG

def Ctx.TOmega (ℓ : ℕ) : Module.End K ↥(AlgebraicCurve.omegaSpace (K := K) (F := ↥(modularFunctionFieldC K N)) c.D') :=
  if h : ℓ.Prime ∧ ¬ ℓ ∣ N ∧ ℓ ≠ p then
    haveI : Fact ℓ.Prime := ⟨h.1⟩
    (c.EE hp5).symm.toLinearMap ∘ₗ c.TfunW hp5 ℓ h.2.1 h.2.2 ∘ₗ (c.EE hp5).toLinearMap
  else 0

theorem Ctx.TOmega_eq (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (hℓp : ℓ ≠ p) :
    c.TOmega hp5 ℓ = (c.EE hp5).symm.toLinearMap ∘ₗ c.TfunW hp5 ℓ hℓN hℓp ∘ₗ (c.EE hp5).toLinearMap := by
  unfold Ctx.TOmega
  rw [dif_pos ⟨hℓ.out, hℓN, hℓp⟩]

theorem Ctx.TOmega_apply (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (hℓp : ℓ ≠ p)
    (μ : ↥(AlgebraicCurve.omegaSpace (K := K) (F := ↥(modularFunctionFieldC K N)) c.D')) :
    c.TOmega hp5 ℓ μ = (c.EE hp5).symm (c.TfunW hp5 ℓ hℓN hℓp (c.EE hp5 μ)) := by
  rw [c.TOmega_eq hp5 ℓ hℓN hℓp]; rfl

theorem Ctx.coe_TfunW (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (hℓp : ℓ ≠ p) (G : ↥(c.WW hp5)) :
    ((c.TfunW hp5 ℓ hℓN hℓp G : ↥(c.WW hp5)) : ↥(modularFunctionFieldC K N)) = TfunL K N c.m' ℓ G := rfl

theorem Ctx.commute_TOmega (ℓ ℓ' : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓp : ℓ ≠ p) (hℓ' : ℓ'.Prime) (hℓ'N : ¬ ℓ' ∣ N) (hℓ'p : ℓ' ≠ p) :
    Commute (c.TOmega hp5 ℓ) (c.TOmega hp5 ℓ') := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : Fact ℓ'.Prime := ⟨hℓ'⟩
  have key : ∀ G : ↥(c.WW hp5), c.TfunW hp5 ℓ hℓN hℓp (c.TfunW hp5 ℓ' hℓ'N hℓ'p G) = c.TfunW hp5 ℓ' hℓ'N hℓ'p (c.TfunW hp5 ℓ hℓN hℓp G) := by
    intro G
    apply Subtype.ext
    rw [coe_TfunW, coe_TfunW, coe_TfunW, coe_TfunW, TfunL_apply, TfunL_apply, TfunL_apply, TfunL_apply]
    by_cases hG0 : (G : ↥(modularFunctionFieldC K N)) = 0
    · simp [hG0]
    have hGL : (G : ↥(modularFunctionFieldC K N)) ∈ AlgebraicCurve.riemannRochSpace (ModularCurve.weightDivisor K N c.m') :=
      ModularCurve.OmegaSide.B3a.mem_riemannRochSpace_weightDivisor_of_isModPCuspFormFn p hp5 K N c.hN c.m' c.hm' G
        ((c.mem_WW_iff hp5 hG0).mp G.2)
    exact ModularCurve.SSHeckeV2.trace_heckeBetaC_mul_pow_comm_of_mem p hp5 K N c.hN ℓ hℓN hℓp ℓ' hℓ'N hℓ'p c.m' c.hm' G hGL
  show c.TOmega hp5 ℓ * c.TOmega hp5 ℓ' = c.TOmega hp5 ℓ' * c.TOmega hp5 ℓ
  apply LinearMap.ext; intro μ
  rw [Module.End.mul_apply, Module.End.mul_apply, c.TOmega_apply hp5 ℓ hℓN hℓp, c.TOmega_apply hp5 ℓ' hℓ'N hℓ'p,
    c.TOmega_apply hp5 ℓ hℓN hℓp, c.TOmega_apply hp5 ℓ' hℓ'N hℓ'p, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, key]

end ModularCurve.OmegaSide.B3
p2m_reactivate "P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide.B"
p2m_reactivate "P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide.B"
p2m_reactivate "P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide.B"

namespace ModularCurve
p2m_export "ModularCurve" "SSCarrier placeWidth ssPlaces jGeomGen jqModC modularFunctionFieldC coeff_jqModC_neg_one heckeMultiplier liftFun ssHeckeFun charLDegeneracyRoof heckeAlphaC heckeBetaC thetaL thetaL_apply qExpansionDiffAlong weightFloor weightDivisor weightDivisor_apply thetaJ qexpOfWeight IsModPCuspFormFn hasse_smul_traceAlong_smul_pullbackAlong_smul_D_jGeomGen_eq theta_ssHeckeFun_eq_inv_smul_dualMap_of_forall_weilOfKaehler stichtenothGenusExists_modularFunctionFieldC_of_perfectField constantsAreBase_modularFunctionFieldC_of_perfectField weilOfKaehler_smul_D_jGeomGen_mem_omegaSpace_iff_isModPCuspFormFn exists_coe_eq_thetaL_jqModC_zpow_and_stackOrd_eq isQExpansionDiffAlong_qExpansionDiffAlong theta_coeff SSHeckeV2.trace_heckeBetaC_mul_pow_comm_of_mem isAffineGeomPlace_or_ord_jGeomGen_lt_zero exists_divisor_forall_eq_weightFloor_fieldC qexpOfWeight_trace_heckeBetaC_mul_pow_eq_heckePS_of_eq_smul_map SSHeckeV2.heckeMultiplier_spec mem_riemannRochSpace_weightDivisor_iff_isModPFormFn omegaSpace_eq_bot_of_two_mul_eq_add_one isCurveOver_charLDegeneracyRoof ssPlaces_nonempty charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul essFiniteType_modularFunctionFieldFullC"
namespace OmegaSide
p2m_open "ModularCurve"

def T42 (K : Type) [Field K] (N : ℕ) [NeZero N] (m : ℕ) (ℓ : ℕ) [NeZero ℓ] (ω : Ω[↥(modularFunctionFieldC K N)⁄K]) : Ω[↥(modularFunctionFieldC K N)⁄K] :=
  Differential.traceAlong (heckeBetaC K N ℓ)
    ((algebraMap K ↥(charLDegeneracyRoof K N ℓ) ((ℓ : K) ^ (m - 1)) * ModularCurve.heckeMultiplier N K ℓ ^ m) •
      Differential.pullbackAlong (heckeAlphaC K N ℓ) ω)

end ModularCurve.OmegaSide
p2m_reactivate "P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide.B"
p2m_reactivate "P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide.B"

namespace ModularCurve
p2m_export "ModularCurve" "SSCarrier placeWidth ssPlaces jGeomGen jqModC modularFunctionFieldC coeff_jqModC_neg_one heckeMultiplier liftFun ssHeckeFun charLDegeneracyRoof heckeAlphaC heckeBetaC thetaL thetaL_apply qExpansionDiffAlong weightFloor weightDivisor weightDivisor_apply thetaJ qexpOfWeight IsModPCuspFormFn hasse_smul_traceAlong_smul_pullbackAlong_smul_D_jGeomGen_eq theta_ssHeckeFun_eq_inv_smul_dualMap_of_forall_weilOfKaehler stichtenothGenusExists_modularFunctionFieldC_of_perfectField constantsAreBase_modularFunctionFieldC_of_perfectField weilOfKaehler_smul_D_jGeomGen_mem_omegaSpace_iff_isModPCuspFormFn exists_coe_eq_thetaL_jqModC_zpow_and_stackOrd_eq isQExpansionDiffAlong_qExpansionDiffAlong theta_coeff SSHeckeV2.trace_heckeBetaC_mul_pow_comm_of_mem isAffineGeomPlace_or_ord_jGeomGen_lt_zero exists_divisor_forall_eq_weightFloor_fieldC qexpOfWeight_trace_heckeBetaC_mul_pow_eq_heckePS_of_eq_smul_map SSHeckeV2.heckeMultiplier_spec mem_riemannRochSpace_weightDivisor_iff_isModPFormFn omegaSpace_eq_bot_of_two_mul_eq_add_one isCurveOver_charLDegeneracyRoof ssPlaces_nonempty charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul essFiniteType_modularFunctionFieldFullC"
namespace OmegaSide
namespace B3
p2m_open "ModularCurve"

variable {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {K : Type} [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] {N : ℕ} [NeZero N]
  [AlgebraicCurve.IsCurveOver K ↥(modularFunctionFieldC K N)] [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := ↥(modularFunctionFieldC K N))]
  [∀ w : AlgebraicCurve.Place K ↥(modularFunctionFieldC K N), w.DCoordGenerates] [Nontrivial (Ω[↥(modularFunctionFieldC K N)⁄K])]
  [AlgebraicCurve.HasPrincipalDivisors K ↥(modularFunctionFieldC K N)] [AlgebraicCurve.HasCanonicalLocalResidueKStar K ↥(modularFunctionFieldC K N)]
  [Nonempty (AlgebraicCurve.Place K ↥(modularFunctionFieldC K N))]
  (c : Ctx p K N)

include hp5

theorem Ctx.exists_eq_smul_omega1 (ω : Ω[↥(modularFunctionFieldC K N)⁄K]) : ∃ f : ↥(modularFunctionFieldC K N), ω = f • omega1 p hp5 K N c.hpN := by
  have h1 : Module.finrank ↥(modularFunctionFieldC K N) (Ω[↥(modularFunctionFieldC K N)⁄K]) = 1 := AlgebraicCurve.IsCurveOver.kaehler_free_rank_one.2
  obtain ⟨f, hf⟩ := (finrank_eq_one_iff_of_nonzero' _ (c.hω₁ hp5)).mp h1 ω
  exact ⟨f, hf.symm⟩

theorem Ctx.H1 (μ : ↥(AlgebraicCurve.omegaSpace (K := K) (F := ↥(modularFunctionFieldC K N)) c.D')) :
    μ = 0 ∨ ∃ (ω : Ω[↥(modularFunctionFieldC K N)⁄K]) (hω : ω ≠ 0) (hmem : AlgebraicCurve.weilOfKaehler K ↥(modularFunctionFieldC K N) hω ∈ AlgebraicCurve.omegaSpace (K := K) (F := ↥(modularFunctionFieldC K N)) c.D'),
      μ = ⟨AlgebraicCurve.weilOfKaehler K ↥(modularFunctionFieldC K N) hω, hmem⟩ := by
  rcases AlgebraicCurve.eq_zero_or_exists_eq_weilOfKaehler_smul_of_mem_omegaSpace (c.hRI) c.hagree (c.hω₁ hp5) c.D' μ.1 μ.2 with h0 | ⟨f, hf, hμ⟩
  · left; exact Subtype.ext h0
  · right
    refine ⟨f • omega1 p hp5 K N c.hpN, smul_ne_zero hf (c.hω₁ hp5), ?_, ?_⟩
    · rw [← hμ]; exact μ.2
    · exact Subtype.ext hμ

theorem Ctx.eq_smul_of_weilOfKaehler_mem {ω : Ω[↥(modularFunctionFieldC K N)⁄K]} (hω : ω ≠ 0)
    (hmem : AlgebraicCurve.weilOfKaehler K ↥(modularFunctionFieldC K N) hω ∈ AlgebraicCurve.omegaSpace (K := K) (F := ↥(modularFunctionFieldC K N)) c.D') :
    ((c.EE hp5 ⟨_, hmem⟩ : ↥(c.WW hp5)) : ↥(modularFunctionFieldC K N)) ≠ 0 ∧
      ω = ((c.EE hp5 ⟨_, hmem⟩ : ↥(c.WW hp5)) : ↥(modularFunctionFieldC K N)) • omega1 p hp5 K N c.hpN := by
  set G : ↥(modularFunctionFieldC K N) := ((c.EE hp5 ⟨_, hmem⟩ : ↥(c.WW hp5)) : ↥(modularFunctionFieldC K N)) with hGdef
  have hlamG : ModularCurve.OmegaSide.B.lam _ (c.hω₁ hp5) G = AlgebraicCurve.weilOfKaehler K ↥(modularFunctionFieldC K N) hω :=
    ModularCurve.OmegaSide.B.lam_E (c.hω₁ hp5) (c.hRI) c.hagree c.D' ⟨_, hmem⟩
  obtain ⟨f, hf⟩ := c.exists_eq_smul_omega1 hp5 ω
  have hf0 : f ≠ 0 := by rintro rfl; exact hω (by rw [hf, zero_smul])
  have hlamf : ModularCurve.OmegaSide.B.lam _ (c.hω₁ hp5) f = AlgebraicCurve.weilOfKaehler K ↥(modularFunctionFieldC K N) hω := by
    rw [ModularCurve.OmegaSide.B.lam_apply_of_ne_zero _ hf0]
    exact weilOfKaehler_congr K hf.symm _ _
  have hfg : f = G := ModularCurve.OmegaSide.B.lam_injective (c.hω₁ hp5) c.hagree (hlamf.trans hlamG.symm)
  refine ⟨?_, ?_⟩
  · rw [← hfg]; exact hf0
  · rw [← hfg]; exact hf

variable (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (hℓp : ℓ ≠ p)
  [AlgebraicCurve.IsCurveOver K ↥(charLDegeneracyRoof K N ℓ)]

include hℓN hℓp

theorem Ctx.T42_smul_omega1 (G : ↥(modularFunctionFieldC K N)) :
    ModularCurve.OmegaSide.T42 K N c.m ℓ (G • omega1 p hp5 K N c.hpN)
      = (algebraMap K ↥(modularFunctionFieldC K N) (((ℓ : K) ^ (p - 2 * c.m))⁻¹) * TfunL K N c.m' ℓ G) • omega1 p hp5 K N c.hpN := by
  have hℓK : (ℓ : K) ≠ 0 := by
    intro h0
    exact hℓp ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp ((CharP.cast_eq_zero_iff K p ℓ).mp h0)).symm
  set hp_ := hasseFn p hp5 K N c.hpN with hhp
  have hhp0 := hasseFn_ne_zero p hp5 K N c.hpN
  have key := ModularCurve.hasse_smul_traceAlong_smul_pullbackAlong_smul_D_jGeomGen_eq p hp5 K N ℓ c.hN c.hpN hℓN hℓp
    c.m c.m' c.hm c.hm' c.hmm' hp_ (coe_hasseFn p hp5 K N c.hpN) (G * hp_⁻¹)
  rw [inv_mul_cancel_right₀ hhp0] at key

  have hω : G • omega1 p hp5 K N c.hpN = (G * hp_⁻¹) • KaehlerDifferential.D K ↥(modularFunctionFieldC K N) (jGeomGen K N) := by
    rw [omega1, smul_smul]
  have hu : (algebraMap K ↥(modularFunctionFieldC K N) ((ℓ : K) ^ (p - 2 * c.m)) * hp_) ≠ 0 :=
    mul_ne_zero ((map_ne_zero_iff _ (algebraMap K _).injective).mpr (pow_ne_zero _ hℓK)) hhp0

  have key' : ModularCurve.OmegaSide.T42 K N c.m ℓ (G • omega1 p hp5 K N c.hpN)
      = (algebraMap K ↥(modularFunctionFieldC K N) ((ℓ : K) ^ (p - 2 * c.m)) * hp_)⁻¹ • ((TfunL K N c.m' ℓ G) • KaehlerDifferential.D K ↥(modularFunctionFieldC K N) (jGeomGen K N)) := by
    rw [hω, eq_inv_smul_iff₀ hu]
    exact key
  rw [key', omega1, smul_smul, smul_smul, map_inv₀, mul_inv]
  congr 1
  ring

theorem Ctx.H2z (ω : Ω[↥(modularFunctionFieldC K N)⁄K]) (hω : ω ≠ 0)
    (hmem : AlgebraicCurve.weilOfKaehler K ↥(modularFunctionFieldC K N) hω ∈ AlgebraicCurve.omegaSpace (K := K) (F := ↥(modularFunctionFieldC K N)) c.D')
    (hT : ModularCurve.OmegaSide.T42 K N c.m ℓ ω = 0) :
    c.TOmega hp5 ℓ ⟨AlgebraicCurve.weilOfKaehler K ↥(modularFunctionFieldC K N) hω, hmem⟩ = 0 := by
  obtain ⟨hG0, hωG⟩ := c.eq_smul_of_weilOfKaehler_mem hp5 hω hmem
  set μ : ↥(AlgebraicCurve.omegaSpace (K := K) (F := ↥(modularFunctionFieldC K N)) c.D') := ⟨AlgebraicCurve.weilOfKaehler K ↥(modularFunctionFieldC K N) hω, hmem⟩
  set G := c.EE hp5 μ with hGdef
  have hT' : TfunL K N c.m' ℓ (G : ↥(modularFunctionFieldC K N)) = 0 := by
    have h := c.T42_smul_omega1 hp5 ℓ hℓN hℓp (G : ↥(modularFunctionFieldC K N))
    rw [← hωG, hT] at h
    have h2 := (smul_eq_zero.mp h.symm).resolve_right (c.hω₁ hp5)
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exfalso
      have hℓK : (ℓ : K) ≠ 0 := by
        intro h0; exact hℓp ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp ((CharP.cast_eq_zero_iff K p ℓ).mp h0)).symm
      exact (inv_ne_zero (pow_ne_zero _ hℓK)) ((map_eq_zero_iff _ (algebraMap K ↥(modularFunctionFieldC K N)).injective).mp h3)
    · exact h3
  rw [c.TOmega_apply hp5 ℓ hℓN hℓp]
  have : c.TfunW hp5 ℓ hℓN hℓp G = 0 := Subtype.ext (by rw [coe_TfunW]; exact hT')
  rw [this, map_zero]

theorem Ctx.H2n (ω : Ω[↥(modularFunctionFieldC K N)⁄K]) (hω : ω ≠ 0)
    (hmem : AlgebraicCurve.weilOfKaehler K ↥(modularFunctionFieldC K N) hω ∈ AlgebraicCurve.omegaSpace (K := K) (F := ↥(modularFunctionFieldC K N)) c.D')
    (hT : ModularCurve.OmegaSide.T42 K N c.m ℓ ω ≠ 0) :
    ∃ hmem' : AlgebraicCurve.weilOfKaehler K ↥(modularFunctionFieldC K N) hT ∈ AlgebraicCurve.omegaSpace (K := K) (F := ↥(modularFunctionFieldC K N)) c.D',
      c.TOmega hp5 ℓ ⟨AlgebraicCurve.weilOfKaehler K ↥(modularFunctionFieldC K N) hω, hmem⟩
        = ((ℓ : K) ^ (p - 2 * c.m)) • ⟨AlgebraicCurve.weilOfKaehler K ↥(modularFunctionFieldC K N) hT, hmem'⟩ := by
  have hℓK : (ℓ : K) ≠ 0 := by
    intro h0; exact hℓp ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp ((CharP.cast_eq_zero_iff K p ℓ).mp h0)).symm
  obtain ⟨hG0, hωG⟩ := c.eq_smul_of_weilOfKaehler_mem hp5 hω hmem
  set μ : ↥(AlgebraicCurve.omegaSpace (K := K) (F := ↥(modularFunctionFieldC K N)) c.D') := ⟨AlgebraicCurve.weilOfKaehler K ↥(modularFunctionFieldC K N) hω, hmem⟩
  set G := c.EE hp5 μ with hGdef
  set c0 : K := ((ℓ : K) ^ (p - 2 * c.m))⁻¹ with hc0
  have hc00 : c0 ≠ 0 := inv_ne_zero (pow_ne_zero _ hℓK)
  set T : ↥(modularFunctionFieldC K N) := TfunL K N c.m' ℓ (G : ↥(modularFunctionFieldC K N)) with hTdef
  have hT42 : ModularCurve.OmegaSide.T42 K N c.m ℓ ω = (algebraMap K ↥(modularFunctionFieldC K N) c0 * T) • omega1 p hp5 K N c.hpN := by
    rw [hωG]; exact c.T42_smul_omega1 hp5 ℓ hℓN hℓp (G : ↥(modularFunctionFieldC K N))
  have hT0 : T ≠ 0 := by
    intro h0; apply hT; rw [hT42, h0, mul_zero, zero_smul]
  have hcT0 : algebraMap K ↥(modularFunctionFieldC K N) c0 * T ≠ 0 := mul_ne_zero ((map_ne_zero_iff _ (algebraMap K _).injective).mpr hc00) hT0

  have hlamT : ModularCurve.OmegaSide.B.lam _ (c.hω₁ hp5) T = AlgebraicCurve.weilOfKaehler K ↥(modularFunctionFieldC K N)
      (ω := T • omega1 p hp5 K N c.hpN) (smul_ne_zero hT0 (c.hω₁ hp5)) :=
    ModularCurve.OmegaSide.B.lam_apply_of_ne_zero _ hT0
  have hW : AlgebraicCurve.weilOfKaehler K ↥(modularFunctionFieldC K N) hT = c0 • ModularCurve.OmegaSide.B.lam _ (c.hω₁ hp5) T := by
    rw [← LinearMap.map_smul, Algebra.smul_def, ModularCurve.OmegaSide.B.lam_apply_of_ne_zero _ hcT0]
    exact weilOfKaehler_congr K hT42 _ _

  have hTW : T ∈ c.WW hp5 := c.TfunL_mem_WW hp5 ℓ hℓN hℓp G.2
  have hmem' : AlgebraicCurve.weilOfKaehler K ↥(modularFunctionFieldC K N) hT ∈ AlgebraicCurve.omegaSpace (K := K) (F := ↥(modularFunctionFieldC K N)) c.D' := by
    rw [hW]; exact Submodule.smul_mem _ c0 ((ModularCurve.OmegaSide.B.mem_W _).mp hTW)
  refine ⟨hmem', ?_⟩
  apply Subtype.ext
  rw [c.TOmega_apply hp5 ℓ hℓN hℓp, ModularCurve.OmegaSide.B.E_symm_apply, Submodule.coe_smul]
  show ModularCurve.OmegaSide.B.lam _ (c.hω₁ hp5) (TfunL K N c.m' ℓ (G : ↥(modularFunctionFieldC K N))) = (ℓ : K) ^ (p - 2 * c.m) • AlgebraicCurve.weilOfKaehler K ↥(modularFunctionFieldC K N) hT
  rw [hW, smul_smul, hc0, mul_inv_cancel₀ (pow_ne_zero _ hℓK), one_smul]

end ModularCurve.OmegaSide.B3
p2m_reactivate "P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide.B"
p2m_reactivate "P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide.B"
p2m_reactivate "P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide.B"

namespace ModularCurve
p2m_export "ModularCurve" "SSCarrier placeWidth ssPlaces jGeomGen jqModC modularFunctionFieldC coeff_jqModC_neg_one heckeMultiplier liftFun ssHeckeFun charLDegeneracyRoof heckeAlphaC heckeBetaC thetaL thetaL_apply qExpansionDiffAlong weightFloor weightDivisor weightDivisor_apply thetaJ qexpOfWeight IsModPCuspFormFn hasse_smul_traceAlong_smul_pullbackAlong_smul_D_jGeomGen_eq theta_ssHeckeFun_eq_inv_smul_dualMap_of_forall_weilOfKaehler stichtenothGenusExists_modularFunctionFieldC_of_perfectField constantsAreBase_modularFunctionFieldC_of_perfectField weilOfKaehler_smul_D_jGeomGen_mem_omegaSpace_iff_isModPCuspFormFn exists_coe_eq_thetaL_jqModC_zpow_and_stackOrd_eq isQExpansionDiffAlong_qExpansionDiffAlong theta_coeff SSHeckeV2.trace_heckeBetaC_mul_pow_comm_of_mem isAffineGeomPlace_or_ord_jGeomGen_lt_zero exists_divisor_forall_eq_weightFloor_fieldC qexpOfWeight_trace_heckeBetaC_mul_pow_eq_heckePS_of_eq_smul_map SSHeckeV2.heckeMultiplier_spec mem_riemannRochSpace_weightDivisor_iff_isModPFormFn omegaSpace_eq_bot_of_two_mul_eq_add_one isCurveOver_charLDegeneracyRoof ssPlaces_nonempty charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul essFiniteType_modularFunctionFieldFullC"
namespace OmegaSide
namespace B3
p2m_open "ModularCurve"

variable {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {K : Type} [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] {N : ℕ} [NeZero N]
  [AlgebraicCurve.IsCurveOver K ↥(modularFunctionFieldC K N)] [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := ↥(modularFunctionFieldC K N))]
  [∀ w : AlgebraicCurve.Place K ↥(modularFunctionFieldC K N), w.DCoordGenerates] [Nontrivial (Ω[↥(modularFunctionFieldC K N)⁄K])]
  [AlgebraicCurve.HasPrincipalDivisors K ↥(modularFunctionFieldC K N)] [AlgebraicCurve.HasCanonicalLocalResidueKStar K ↥(modularFunctionFieldC K N)]
  [Nonempty (AlgebraicCurve.Place K ↥(modularFunctionFieldC K N))]
  (c : Ctx p K N)

theorem Ctx.exit (S₀ : Set ℕ) (hS₀ : p ∈ S₀)
    (ω : ↥(AlgebraicCurve.omegaSpace (K := K) (F := ↥(modularFunctionFieldC K N)) c.D')) (κ : ℕ → K) (hω : ω ≠ 0)
    (heig : ∀ ℓ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → c.TOmega hp5 ℓ ω = κ ℓ • ω) :
    ∃ (m' : ℕ) (hm' : 1 ≤ m') (_ : c.m + m' = (p + 1) / 2) (G' : ↥(modularFunctionFieldC K N)),
      G' ≠ 0 ∧ G' ∈ AlgebraicCurve.riemannRochSpace (ModularCurve.weightDivisor K N m') ∧
      ModularCurve.IsModPCuspFormFn K m' (G' : LaurentSeries K) ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ℓ ∉ S₀ →
        haveI : Fact ℓ.Prime := ⟨hℓ⟩
        letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ)
        algebraMap K ↥(modularFunctionFieldC K N) ((ℓ : K) ^ (m' - 1)) *
            Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ)
              (heckeBetaC K N ℓ G' * ModularCurve.heckeMultiplier N K ℓ ^ m')
          = algebraMap K ↥(modularFunctionFieldC K N) ((ℓ : K) ^ (p - 2 * c.m) * ((((ℓ : K) ^ (p - 2 * c.m))⁻¹) * κ ℓ)) * G' := by
  classical
  set G : ↥(c.WW hp5) := c.EE hp5 ω with hGdef
  have hG0 : (G : ↥(modularFunctionFieldC K N)) ≠ 0 := by
    intro h0
    apply hω
    have : G = 0 := Subtype.ext h0
    rw [hGdef] at this
    exact (c.EE hp5).injective (this.trans (map_zero _).symm)
  have hcusp : ModularCurve.IsModPCuspFormFn K c.m' ((G : ↥(modularFunctionFieldC K N)) : LaurentSeries K) := (c.mem_WW_iff hp5 hG0).mp G.2
  refine ⟨c.m', c.hm', c.hmm', (G : ↥(modularFunctionFieldC K N)), hG0,
    ModularCurve.OmegaSide.B3a.mem_riemannRochSpace_weightDivisor_of_isModPCuspFormFn p hp5 K N c.hN c.m' c.hm' _ hcusp, hcusp, ?_⟩
  intro ℓ hℓ hℓN hℓS
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓp : ℓ ≠ p := fun h => hℓS (h ▸ hS₀)
  have hℓK : (ℓ : K) ≠ 0 := by
    intro h0; exact hℓp ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp ((CharP.cast_eq_zero_iff K p ℓ).mp h0)).symm

  have h1 := heig ℓ hℓ hℓN hℓS
  rw [c.TOmega_apply hp5 ℓ hℓN hℓp] at h1
  have h2 : c.TfunW hp5 ℓ hℓN hℓp G = κ ℓ • G := by
    apply (c.EE hp5).symm.injective
    rw [h1, map_smul, hGdef, LinearEquiv.symm_apply_apply]
  have h3 : TfunL K N c.m' ℓ (G : ↥(modularFunctionFieldC K N)) = κ ℓ • (G : ↥(modularFunctionFieldC K N)) := by
    have := congrArg Subtype.val h2
    rwa [coe_TfunW, Submodule.coe_smul] at this
  rw [TfunL_apply] at h3
  rw [mul_inv_cancel_left₀ (pow_ne_zero _ hℓK), ← Algebra.smul_def]
  exact h3

end ModularCurve.OmegaSide.B3
p2m_reactivate "P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide.B"
p2m_reactivate "P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide.B"
p2m_reactivate "P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide.B"

set_option maxHeartbeats 6400000

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide"

theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N]
    [AlgebraicCurve.IsCurveOver K ↥(modularFunctionFieldC K N)]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := ↥(modularFunctionFieldC K N))]
    [∀ w : AlgebraicCurve.Place K ↥(modularFunctionFieldC K N), w.DCoordGenerates]
    [Nontrivial (Ω[↥(modularFunctionFieldC K N)⁄K])]
    [AlgebraicCurve.HasPrincipalDivisors K ↥(modularFunctionFieldC K N)]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K ↥(modularFunctionFieldC K N)]
    (hagree : AlgebraicCurve.WeilKaehlerAgree K ↥(modularFunctionFieldC K N))
    (htame : ∀ w : AlgebraicCurve.Place K ↥(modularFunctionFieldC K N),
      w.ord (jGeomGen K N) < 0 → (((w.ord (jGeomGen K N)).natAbs : ℕ) : K) ≠ 0)
    (hN : (N : K) ≠ 0) (m : ℕ) (hm : 1 ≤ m) (hmp : 2 * m ≤ p + 1)
    (SS : Finset (AlgebraicCurve.Place K ↥(modularFunctionFieldC K N))) (hSS : ∀ x, x ∈ SS ↔ x ∈ ssPlaces p N K)
    (D' : AlgebraicCurve.Divisor K ↥(modularFunctionFieldC K N))
    (hD'1 : ∀ w, w ∈ ssPlaces p N K → ((placeWidth N w : ℤ) ∣ (m : ℤ)) → D' w = ModularCurve.weightDivisor K N m w - 1)
    (hD'0 : ∀ w, ¬ (w ∈ ssPlaces p N K ∧ ((placeWidth N w : ℤ) ∣ (m : ℤ))) → D' w = ModularCurve.weightDivisor K N m w)
    (Θ : ModularCurve.SSCarrier p N K hp5 (2 * (m : ℤ)) →ₗ[K]
        Module.Dual K ↥(AlgebraicCurve.omegaSpace (K := K) (F := ↥(modularFunctionFieldC K N)) D'))
    (hΘres : ∀ v (ω : Ω[↥(modularFunctionFieldC K N)⁄K]) (hω : ω ≠ 0)
          (hmem : AlgebraicCurve.weilOfKaehler K ↥(modularFunctionFieldC K N) hω ∈
            AlgebraicCurve.omegaSpace (K := K) (F := ↥(modularFunctionFieldC K N)) D'),
          Θ v ⟨AlgebraicCurve.weilOfKaehler K ↥(modularFunctionFieldC K N) hω, hmem⟩
            = ∑ x ∈ SS, kaehlerResidueTerm ω
                (diagonalHom K ↥(modularFunctionFieldC K N) (ModularCurve.liftFun p N K hp5 (2 * (m : ℤ)) v)) x) :
    ∃ (TΩ : ℕ → Module.End K ↥(AlgebraicCurve.omegaSpace (K := K) (F := ↥(modularFunctionFieldC K N)) D')) (c : ℕ → K) (j : ℕ),
      (∀ ℓ ℓ', ℓ.Prime → ¬ ℓ ∣ N → ℓ ≠ p → ℓ'.Prime → ¬ ℓ' ∣ N → ℓ' ≠ p → Commute (TΩ ℓ) (TΩ ℓ')) ∧
      (∀ ℓ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ≠ p → c ℓ ≠ 0) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ℓ ≠ p → ∀ v,
          haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
          Θ (ModularCurve.ssHeckeFun p N K hp5 (2 * (m : ℤ)) ℓ v) = c ℓ • (TΩ ℓ).dualMap (Θ v)) ∧
      (∀ (S₀ : Set ℕ) (_ : p ∈ S₀) (ω : ↥(AlgebraicCurve.omegaSpace (K := K) (F := ↥(modularFunctionFieldC K N)) D')) (κ : ℕ → K), ω ≠ 0 →
          (∀ ℓ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → TΩ ℓ ω = κ ℓ • ω) →
          ∃ (m' : ℕ) (hm' : 1 ≤ m') (_ : m + m' = (p + 1) / 2) (G' : ↥(modularFunctionFieldC K N)),
            G' ≠ 0 ∧ G' ∈ AlgebraicCurve.riemannRochSpace (ModularCurve.weightDivisor K N m') ∧
            ModularCurve.IsModPCuspFormFn K m' (G' : LaurentSeries K) ∧
            ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ℓ ∉ S₀ →
              haveI : Fact ℓ.Prime := ⟨hℓ⟩
              letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ)
              algebraMap K ↥(modularFunctionFieldC K N) ((ℓ : K) ^ (m' - 1)) *
                  Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ)
                    (heckeBetaC K N ℓ G' * ModularCurve.heckeMultiplier N K ℓ ^ m')
                = algebraMap K ↥(modularFunctionFieldC K N) ((ℓ : K) ^ j * (c ℓ * κ ℓ)) * G') := by
  classical
  have hpN : ¬ p ∣ N := fun h => hN ((CharP.cast_eq_zero_iff K p N).mpr h)
  by_cases hedge : 2 * m = p + 1
  ·
    have hbot := ModularCurve.omegaSpace_eq_bot_of_two_mul_eq_add_one p hp5 K N hN m hm hedge SS hSS D' hD'1 hD'0
    have hsub : ∀ μ : ↥(AlgebraicCurve.omegaSpace (K := K) (F := ↥(modularFunctionFieldC K N)) D'), μ = 0 := fun μ => by
      apply Subtype.ext
      have h2 : (μ : Module.Dual K (AlgebraicCurve.adeleSpace K ↥(modularFunctionFieldC K N))) ∈
          (⊥ : Submodule K (Module.Dual K (AlgebraicCurve.adeleSpace K ↥(modularFunctionFieldC K N)))) := by
        rw [← hbot]; exact μ.2
      exact (Submodule.mem_bot K).mp h2
    refine ⟨fun _ => 0, fun _ => 1, 0, ?_, ?_, ?_, ?_⟩
    · intro ℓ ℓ' _ _ _ _ _ _; exact Commute.refl 0
    · intro ℓ _ _ _; exact one_ne_zero
    · intro ℓ hℓ hℓN hℓp v
      apply LinearMap.ext
      intro μ
      rw [hsub μ, map_zero, map_zero]
    · intro S₀ _ ω κ hω _
      exact absurd (hsub ω) hω
  ·
    have hp2 : p % 2 = 1 := by
      rcases Nat.Prime.eq_two_or_odd (Fact.out : p.Prime) with h2 | h2
      · omega
      · exact h2
    obtain ⟨m', hm', hmm'⟩ : ∃ m' : ℕ, 1 ≤ m' ∧ m + m' = (p + 1) / 2 := ⟨(p + 1) / 2 - m, by omega, by omega⟩

    haveI : Nonempty (AlgebraicCurve.Place K ↥(modularFunctionFieldC K N)) := by
      obtain ⟨x, _⟩ := ModularCurve.ssPlaces_nonempty p N hpN K
      exact ⟨x⟩
    let c : ModularCurve.OmegaSide.B3.Ctx p K N :=
      { hagree := hagree, htame := htame, hN := hN, hpN := hpN, m := m, m' := m', hm := hm, hm' := hm', hmm' := hmm',
        D' := D', hD'1 := hD'1, hD'0 := hD'0 }
    refine ⟨fun ℓ => c.TOmega hp5 ℓ, fun ℓ => ((ℓ : K) ^ (p - 2 * m))⁻¹, p - 2 * m, ?_, ?_, ?_, ?_⟩
    · intro ℓ ℓ' hℓ hℓN hℓp hℓ' hℓ'N hℓ'p
      exact c.commute_TOmega hp5 ℓ ℓ' hℓ hℓN hℓp hℓ' hℓ'N hℓ'p
    · intro ℓ hℓ hℓN hℓp
      have hℓK : (ℓ : K) ≠ 0 := fun h0 =>
        hℓp ((Nat.prime_dvd_prime_iff_eq (Fact.out) hℓ).mp ((CharP.cast_eq_zero_iff K p ℓ).mp h0)).symm
      exact inv_ne_zero (pow_ne_zero _ hℓK)
    · intro ℓ hℓ hℓN hℓp v
      haveI : Fact ℓ.Prime := ⟨hℓ⟩
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      have hpℓ : ¬ p ∣ ℓ := fun h => hℓp ((Nat.prime_dvd_prime_iff_eq (Fact.out) hℓ).mp h).symm
      have hpNℓ : ¬ p ∣ N * ℓ := fun h => ((Nat.Prime.dvd_mul (Fact.out)).mp h).elim hpN hpℓ
      have hℓK : (ℓ : K) ≠ 0 := fun h0 => hpℓ ((CharP.cast_eq_zero_iff K p ℓ).mp h0)

      haveI hR : AlgebraicCurve.IsCurveOver K ↥(charLDegeneracyRoof K N ℓ) := ModularCurve.isCurveOver_charLDegeneracyRoof K p N ℓ hpNℓ

      haveI : NeZero (N * ℓ) := ⟨Nat.mul_ne_zero (NeZero.ne N) (NeZero.ne ℓ)⟩
      haveI : Algebra.EssFiniteType K ↥(charLDegeneracyRoof K N ℓ) := by
        rw [ModularCurve.charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul K p N ℓ hpNℓ]
        exact ModularCurve.essFiniteType_modularFunctionFieldFullC K (N * ℓ)
      haveI : ∀ w : AlgebraicCurve.Place K ↥(charLDegeneracyRoof K N ℓ), w.DCoordGenerates :=
        AlgebraicCurve.dCoordGenerates_of_isCurveOver
      haveI : Nontrivial (Ω[↥(charLDegeneracyRoof K N ℓ)⁄K]) :=
        Module.nontrivial_of_finrank_eq_succ (AlgebraicCurve.IsCurveOver.kaehler_free_rank_one (K := K) (F := ↥(charLDegeneracyRoof K N ℓ))).2
      exact ModularCurve.theta_ssHeckeFun_eq_inv_smul_dualMap_of_forall_weilOfKaehler p hp5 K N hagree hN m hm SS hSS D' hD'1 hD'0 Θ hΘres
        ℓ hℓN hℓp (c.TOmega hp5 ℓ) ((ℓ : K) ^ (p - 2 * m)) (pow_ne_zero _ hℓK)
        (c.H1 hp5) (c.H2z hp5 ℓ hℓN hℓp) (c.H2n hp5 ℓ hℓN hℓp) v
    ·
      intro S₀ hS₀ ω κ hω heig
      exact c.exit hp5 S₀ hS₀ ω κ hω heig

end
p2m_reactivate "P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit.ModularCurve.OmegaSide.B"

end S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit
end P2MW
export P2MW.S_ModularCurve_SSHeckeV2_exists_omegaHecke_dualMap_theta_and_exit (solution)
