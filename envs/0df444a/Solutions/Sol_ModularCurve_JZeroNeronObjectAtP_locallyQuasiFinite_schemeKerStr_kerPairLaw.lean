-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.locallyQuasiFinite_schemeKerStr_kerPairLaw
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/2db25794-8d5e-5c1d-a576-e57116121d06

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKerPair
import Definitions.Def_ModularCurve_ToricDescentData
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_ValuationSubring_krullDimLE_one_of_isAlgebraic_rat
import Definitions.Def_ModularCurve_JZeroTorsionFinite
import Theorems.Thm_ModularCurve_jZeroTorsionFinite
import Theorems.Thm_AlgebraicGeometry_isFinite_of_finite_setOf_exists_section_of_isAlgClosed
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isPullback_schemeKer_kerPairLaw_baseChange
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_finite_fixedPoints_frobSp_comp_self
import Theorems.Thm_AlgebraicGeometry_ext_of_forall_geometricPoint_comp_eq_of_flat
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw
p2m_attr_erase "instance" "CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent"
p2m_attr_erase "instance" "ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply"
p2m_attr_erase "simp" "AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero"
p2m_attr_erase "simp" "TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian IsLocalRing ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.ModularCurve ModularCurve.JZeroNeronObjectAtP P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.ModularCurve.JZeroNeronObjectAtP"

universe u

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable
open AlgebraicCurve NeronSpecialFibreInfra

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.nsmul_zero RelativeGroupLaw.nsmul_succ RelativeGroupLaw.schemeNsmul_over RelativeGroupLaw.baseChangeStr RelativeGroupLaw.baseChangePointToBase RelativeGroupLaw.baseChangePointOfBase RelativeGroupLaw.baseChangePointToBase_ofBase RelativeGroupLaw.baseChangePointOfBase_toBase RelativeGroupLaw.baseChangePointEquiv RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong RelativeGroupLaw.baseChangePointToBase_one RelativeGroupLaw.IsHom RelativeGroupLaw.IsHom.fibreRestrictAlong RelativeGroupLaw.kerPair RelativeGroupLaw.kerPairStr RelativeGroupLaw.one_coe_eq RelativeGroupLaw.kerPairLaw RelativeGroupLaw.exists_isPullback_schemeKer_kerPairLaw_baseChange"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "pointGroup mul_inv_cancel one_natural mul_assoc one inv one_mul inv_mul_cancel mul nsmul nsmul_zero nsmul_succ nsmul_natural idPoint schemeNsmul schemeNsmul_over schemeKer schemeKerStr baseChangeStr baseChangePointToBase baseChangePointOfBase baseChangePointToBase_coe baseChangePointToBase_ofBase baseChangePointOfBase_toBase baseChangePointEquiv baseChangePointToBase_comp_fibreRestrictAlong baseChange baseChangePointToBase_mul baseChangePointToBase_one fibre IsHom IsHom.fibreRestrictAlong kerPair kerPairι kerPairStr kerLeg_snd_eq kerPair_snd_fst one_coe_eq kerPairPointEquiv kerPairPointEquiv_apply_coe_coe kerPairPointEquiv_symm_apply_coe kerPairLaw kerPairPointEquiv_one kerPairPointEquiv_nsmul kerPair_snd_fst_assoc exists_isPullback_schemeKer_kerPairLaw_baseChange"
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}

theorem coe_comp_schemeNsmul (G : RelativeGroupLaw R f) (n : ℕ) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver t f) : x.1 ≫ G.schemeNsmul n = (G.nsmul t n x).1 := by
  have h := G.nsmul_natural f t x.1 x.2 n idPoint
  have hx : GoodReductionJacobian.schemeHomOverComp x.1 x.2 (idPoint (f := f)) = x :=
    Subtype.ext (Category.comp_id _)
  rw [hx] at h
  rw [← h]
  rfl

private noncomputable def _root_.GoodReductionJacobian.RelativeGroupLaw.schemeKerLift (G : RelativeGroupLaw R f) (n : ℕ) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver t f) (hx : G.nsmul t n x = G.one t) : SchemeHomOver t (G.schemeKerStr n) :=
  ⟨pullback.lift x.1 t (by
      rw [coe_comp_schemeNsmul, hx]
      have h := G.one_natural (𝟙 _) t t (Category.comp_id t)
      exact (congrArg Subtype.val h).symm),
    pullback.lift_snd _ _ _⟩

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "schemeKerLift"
@[scoped simp]
theorem schemeKerLift_fst (G : RelativeGroupLaw R f) (n : ℕ) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver t f) (hx : G.nsmul t n x = G.one t) :
    (G.schemeKerLift n x hx).1 ≫ pullback.fst _ _ = x.1 :=
  pullback.lift_fst _ _ _

end GoodReductionJacobian.RelativeGroupLaw
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian.RelativeGroupLaw"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian"

namespace ModularCurve
p2m_export "ModularCurve" "JZeroNeronObjectAtP.LevelData JZeroNeronObjectAtP jZeroTorsion JZero JZeroC instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable jZeroTorsionFinite JZeroNeronObjectAtP.isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le JZeroNeronObjectAtP.finite_fixedPoints_frobSp_comp_self"
namespace JZeroNeronObjectAtP
p2m_export "ModularCurve.JZeroNeronObjectAtP" "base genPt barPt resPt overId toFibrePt ofFibrePt fibreMap torusCoord torusStr torusPt LevelData abqFibre_eq_one_iff L G pts_add abqFibre_mul degeneracyHom torusFibre abqFibre degeneracyHom_mul g frobSp separated toricRank degeneracyHom_special pts locallyOfFiniteType isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le finite_fixedPoints_frobSp_comp_self"
p2m_open "ModularCurve.JZeroNeronObjectAtP ModularCurve"

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  {Λ : LevelData N₀ p A}

noncomputable abbrev degA (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (i : Fin 2) :
    SchemeHomOver (RelativeGroupLaw.baseChangeStr Λ.σA O.g) (RelativeGroupLaw.baseChangeStr Λ.σA Λ.f) :=
  fibreRestrictAlong Λ.σA Λ.f O.g (O.degeneracyHom i)

theorem degA_isHom (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (i : Fin 2) :
    RelativeGroupLaw.IsHom (O.L.baseChange Λ.σA) (Λ.L.baseChange Λ.σA) (degA O i) :=
  RelativeGroupLaw.IsHom.fibreRestrictAlong Λ.σA (fun t x y => O.degeneracyHom_mul i t x y)

noncomputable abbrev kerA (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) : Scheme.{0} :=
  RelativeGroupLaw.kerPair (Λ.L.baseChange Λ.σA) (degA O)

noncomputable abbrev kerALaw (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) :
    RelativeGroupLaw ↥A (RelativeGroupLaw.kerPairStr (Λ.L.baseChange Λ.σA) (degA O)) :=
  RelativeGroupLaw.kerPairLaw (O.L.baseChange Λ.σA) (Λ.L.baseChange Λ.σA) (degA O) (degA_isHom O)

noncomputable abbrev kerATorsStr (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) :
    (kerALaw O).schemeKer m ⟶ Spec (CommRingCat.of ↥A) :=
  (kerALaw O).schemeKerStr m

end ModularCurve.JZeroNeronObjectAtP
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian.RelativeGroupLaw"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian.RelativeGroupLaw"

namespace ModularCurve
p2m_export "ModularCurve" "JZeroNeronObjectAtP.LevelData JZeroNeronObjectAtP jZeroTorsion JZero JZeroC instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable jZeroTorsionFinite JZeroNeronObjectAtP.isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le JZeroNeronObjectAtP.finite_fixedPoints_frobSp_comp_self"
namespace JZeroNeronObjectAtP
p2m_export "ModularCurve.JZeroNeronObjectAtP" "base genPt barPt resPt overId toFibrePt ofFibrePt fibreMap torusCoord torusStr torusPt LevelData abqFibre_eq_one_iff L G pts_add abqFibre_mul degeneracyHom torusFibre abqFibre degeneracyHom_mul g frobSp separated toricRank degeneracyHom_special pts locallyOfFiniteType isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le finite_fixedPoints_frobSp_comp_self"
p2m_open "ModularCurve.JZeroNeronObjectAtP ModularCurve"

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  {Λ : LevelData N₀ p A}

namespace LevelData p2m_export "ModularCurve.JZeroNeronObjectAtP.LevelData" "IsJacobian σA X L hσA f ptsSp pts" end LevelData
p2m_open_scoped "ModularCurve.JZeroNeronObjectAtP.LevelData" in

theorem LevelData.ptsSp_zero (hΛ : Λ.IsJacobian) : Λ.ptsSp 0 = Λ.L.one (resPt A ≫ Λ.σA) := by
  letI := Λ.L.pointGroup (resPt A ≫ Λ.σA)
  have hadd := hΛ.2.2.2.2.1
  have h : Λ.ptsSp 0 * Λ.ptsSp 0 = Λ.ptsSp 0 := by
    change Λ.L.mul _ (Λ.ptsSp 0) (Λ.ptsSp 0) = Λ.ptsSp 0
    rw [← hadd, add_zero]
  exact mul_eq_left.mp h

theorem ribet_coords (hΛ : Λ.IsJacobian) (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
    (x : SchemeHomOver (resPt A ≫ Λ.σA) O.g)
    (h0 : NeronModelInfra.schemeHomOverComp x (O.degeneracyHom 0) = Λ.L.one (resPt A ≫ Λ.σA))
    (h1 : NeronModelInfra.schemeHomOverComp x (O.degeneracyHom 1) = Λ.L.one (resPt A ≫ Λ.σA)) :
    Λ.ptsSp.symm (fibreMap (O.abqFibre 0) x) + O.frobSp (Λ.ptsSp.symm (fibreMap (O.abqFibre 1) x)) = 0 ∧
    O.frobSp (Λ.ptsSp.symm (fibreMap (O.abqFibre 0) x)) + Λ.ptsSp.symm (fibreMap (O.abqFibre 1) x) = 0 := by
  have hz : Λ.ptsSp.symm (Λ.L.one (resPt A ≫ Λ.σA)) = 0 := by
    rw [Equiv.symm_apply_eq, LevelData.ptsSp_zero hΛ]
  obtain ⟨e0, e1⟩ := O.degeneracyHom_special x
  rw [h0, hz] at e0
  rw [h1, hz] at e1
  exact ⟨e0.symm, e1.symm⟩

theorem ribet_coords' (hΛ : Λ.IsJacobian) (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
    (x : SchemeHomOver (resPt A ≫ Λ.σA) O.g)
    (h0 : NeronModelInfra.schemeHomOverComp x (O.degeneracyHom 0) = Λ.L.one (resPt A ≫ Λ.σA))
    (h1 : NeronModelInfra.schemeHomOverComp x (O.degeneracyHom 1) = Λ.L.one (resPt A ≫ Λ.σA)) :
    Λ.ptsSp.symm (fibreMap (O.abqFibre 1) x) ∈ Function.fixedPoints (O.frobSp ∘ O.frobSp) ∧
    Λ.ptsSp.symm (fibreMap (O.abqFibre 0) x) = - O.frobSp (Λ.ptsSp.symm (fibreMap (O.abqFibre 1) x)) := by
  obtain ⟨e0, e1⟩ := ribet_coords hΛ O x h0 h1
  have ha₀ := eq_neg_of_add_eq_zero_left e0
  refine ⟨?_, ha₀⟩
  change O.frobSp (O.frobSp _) = _
  rw [ha₀, map_neg, neg_add_eq_zero] at e1
  exact e1

theorem ofFibrePt_injective {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
    {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} {f : X ⟶ Spec (CommRingCat.of R)} :
    Function.Injective (ofFibrePt (ι := ι) (f := f)) := by
  intro y y' h
  have h1 : (RelativeGroupLaw.baseChangePointToBase ι y).1 = (RelativeGroupLaw.baseChangePointToBase ι y').1 :=
    congrArg Subtype.val h
  exact (RelativeGroupLaw.baseChangePointEquiv ι (𝟙 _)).injective (Subtype.ext h1)

theorem exists_torus_mul_of_abqFibre_eq (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
    {x y : SchemeHomOver (resPt A ≫ Λ.σA) O.g}
    (h : ∀ i, fibreMap (O.abqFibre i) x = fibreMap (O.abqFibre i) y) :
    ∃ τ : SchemeHomOver (𝟙 _) (torusStr (ResidueField ↥A) O.toricRank),
      toFibrePt x = (O.L.baseChange (resPt A ≫ Λ.σA)).mul (𝟙 _)
        (NeronModelInfra.schemeHomOverComp τ O.torusFibre) (toFibrePt y) := by
  letI G1 := (O.L.baseChange (resPt A ≫ Λ.σA)).pointGroup (𝟙 (Spec (CommRingCat.of (ResidueField ↥A))))
  letI G2 := (Λ.L.baseChange (resPt A ≫ Λ.σA)).pointGroup (𝟙 (Spec (CommRingCat.of (ResidueField ↥A))))
  let φ : Fin 2 → (SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g) →*
      SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) Λ.f)) := fun i =>
    MonoidHom.mk' (fun z => NeronModelInfra.schemeHomOverComp z (O.abqFibre i))
      (fun a b => O.abqFibre_mul i (𝟙 _) a b)
  have hxy : ∀ i, φ i (toFibrePt x) = φ i (toFibrePt y) := fun i => ofFibrePt_injective (h i)
  have hu : ∀ i, NeronModelInfra.schemeHomOverComp (toFibrePt x * (toFibrePt y)⁻¹) (O.abqFibre i) =
      (Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _) := by
    intro i
    change φ i (toFibrePt x * (toFibrePt y)⁻¹) = 1
    rw [map_mul, map_inv, hxy i, mul_inv_cancel]
  obtain ⟨τ, hτ⟩ := (O.abqFibre_eq_one_iff (𝟙 _) (toFibrePt x * (toFibrePt y)⁻¹)).mp hu
  refine ⟨τ, ?_⟩
  change toFibrePt x = (NeronModelInfra.schemeHomOverComp τ O.torusFibre) * toFibrePt y
  rw [hτ, inv_mul_cancel_right]

theorem exists_finset_kernel_coset_representatives (hΛ : Λ.IsJacobian) (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
    (hfin : (Function.fixedPoints (O.frobSp ∘ O.frobSp)).Finite) :
    ∃ S : Finset (SchemeHomOver (resPt A ≫ Λ.σA) O.g),
      (∀ s ∈ S, ∀ i, NeronModelInfra.schemeHomOverComp s (O.degeneracyHom i) = Λ.L.one (resPt A ≫ Λ.σA)) ∧
      ∀ x : SchemeHomOver (resPt A ≫ Λ.σA) O.g,
        (∀ i, NeronModelInfra.schemeHomOverComp x (O.degeneracyHom i) = Λ.L.one (resPt A ≫ Λ.σA)) →
        ∃ s ∈ S, ∃ τ : SchemeHomOver (𝟙 _) (torusStr (ResidueField ↥A) O.toricRank),
          toFibrePt x = (O.L.baseChange (resPt A ≫ Λ.σA)).mul (𝟙 _)
            (NeronModelInfra.schemeHomOverComp τ O.torusFibre) (toFibrePt s) := by
  classical

  let K : Set (SchemeHomOver (resPt A ≫ Λ.σA) O.g) :=
    {x | ∀ i, NeronModelInfra.schemeHomOverComp x (O.degeneracyHom i) = Λ.L.one (resPt A ≫ Λ.σA)}
  let a : SchemeHomOver (resPt A ≫ Λ.σA) O.g → JZeroC (ResidueField ↥A) N₀ :=
    fun x => Λ.ptsSp.symm (fibreMap (O.abqFibre 1) x)
  have haK : a '' K ⊆ Function.fixedPoints (O.frobSp ∘ O.frobSp) := by
    rintro _ ⟨x, hx, rfl⟩
    exact (ribet_coords' hΛ O x (hx 0) (hx 1)).1
  have hKfin : (a '' K).Finite := hfin.subset haK

  have hrep : ∀ e : a '' K, ∃ x ∈ K, a x = e := fun e => e.2
  choose rep hrepK hrepa using hrep
  haveI : Fintype (a '' K) := hKfin.fintype
  refine ⟨Finset.univ.image rep, ?_, ?_⟩
  · intro s hs
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hs
    exact hrepK e
  · intro x hx
    refine ⟨rep ⟨a x, x, hx, rfl⟩, Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
    apply exists_torus_mul_of_abqFibre_eq O

    have h1 : a x = a (rep ⟨a x, x, hx, rfl⟩) := (hrepa ⟨a x, x, hx, rfl⟩).symm
    have h0 : Λ.ptsSp.symm (fibreMap (O.abqFibre 0) x) =
        Λ.ptsSp.symm (fibreMap (O.abqFibre 0) (rep ⟨a x, x, hx, rfl⟩)) := by
      rw [(ribet_coords' hΛ O x (hx 0) (hx 1)).2,
        (ribet_coords' hΛ O _ (hrepK ⟨a x, x, hx, rfl⟩ 0) (hrepK ⟨a x, x, hx, rfl⟩ 1)).2]
      exact congrArg _ (congrArg _ h1)
    intro i
    fin_cases i
    · exact Λ.ptsSp.symm.injective h0
    · exact Λ.ptsSp.symm.injective h1

end ModularCurve.JZeroNeronObjectAtP
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian.RelativeGroupLaw"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian.RelativeGroupLaw"

namespace ModularCurve
p2m_export "ModularCurve" "JZeroNeronObjectAtP.LevelData JZeroNeronObjectAtP jZeroTorsion JZero JZeroC instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable jZeroTorsionFinite JZeroNeronObjectAtP.isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le JZeroNeronObjectAtP.finite_fixedPoints_frobSp_comp_self"
namespace JZeroNeronObjectAtP
p2m_export "ModularCurve.JZeroNeronObjectAtP" "base genPt barPt resPt overId toFibrePt ofFibrePt fibreMap torusCoord torusStr torusPt LevelData abqFibre_eq_one_iff L G pts_add abqFibre_mul degeneracyHom torusFibre abqFibre degeneracyHom_mul g frobSp separated toricRank degeneracyHom_special pts locallyOfFiniteType isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le finite_fixedPoints_frobSp_comp_self"
p2m_open "ModularCurve.JZeroNeronObjectAtP ModularCurve"

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  {Λ : LevelData N₀ p A}

section TorusPoints
variable (S : Type) [CommRing S] (t : ℕ)

theorem exists_torusPt_eq' (τ : SchemeHomOver (𝟙 _) (torusStr S t)) :
    ∃ χ : torusCoord S t →ₐ[S] S, torusPt S t χ = τ := by
  let ψ : CommRingCat.of (torusCoord S t) ⟶ CommRingCat.of S := Spec.preimage τ.1
  have hψ : Spec.map ψ = τ.1 := Spec.map_preimage _
  have hcomp : (CommRingCat.ofHom (algebraMap S (torusCoord S t))) ≫ ψ = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_id, hψ]
    exact τ.2
  refine ⟨{ ψ.hom with commutes' := fun r => ?_ }, ?_⟩
  · have := congrArg (fun g : CommRingCat.of S ⟶ CommRingCat.of S => g.hom r) hcomp
    simpa using this
  · apply Subtype.ext
    show Spec.map _ = τ.1
    rw [← hψ]
    rfl
end TorusPoints
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian.RelativeGroupLaw"

scoped instance torus_locallyOfFiniteType' (S : Type) [Field S] (t : ℕ) : LocallyOfFiniteType (torusStr S t) := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

theorem toFibrePt_ofFibrePt {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
    {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} {f : X ⟶ Spec (CommRingCat.of R)}
    (y : SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr ι f)) : toFibrePt (ofFibrePt y) = y := by
  change RelativeGroupLaw.baseChangePointOfBase ι _ = y
  have h : overId (ofFibrePt y) = RelativeGroupLaw.baseChangePointToBase ι y := Subtype.ext rfl
  rw [h, RelativeGroupLaw.baseChangePointOfBase_toBase]

theorem torusFibre_comp_fibreRestrictAlong_degeneracyHom_eq (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (i : Fin 2) :
    O.torusFibre.1 ≫ (NeronSpecialFibreInfra.fibreRestrictAlong (resPt A ≫ Λ.σA) Λ.f O.g (O.degeneracyHom i)).1 =
      torusStr (ResidueField ↥A) O.toricRank ≫ ((Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)).1 := by
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  haveI : IsSeparated Λ.f := hΛ.1.proper.toIsSeparated
  haveI : LocallyOfFinitePresentation (torusStr (ResidueField ↥A) O.toricRank) := inferInstance
  refine AlgebraicGeometry.ext_of_forall_geometricPoint_comp_eq_of_flat (RingHom.id (ResidueField ↥A))
    Function.injective_id (torusStr (ResidueField ↥A) O.toricRank)
    (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) Λ.f) ?_ ?_ ?_
  · rw [Category.assoc, (NeronSpecialFibreInfra.fibreRestrictAlong _ _ _ _).2, O.torusFibre.2]
  · rw [Category.assoc, ((Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)).2, Category.comp_id]
  intro y hy
  have hy' : y ≫ torusStr (ResidueField ↥A) O.toricRank = 𝟙 _ := by
    rw [hy]; change Spec.map (𝟙 _) = _; exact Spec.map_id _
  obtain ⟨χ, hχ⟩ := exists_torusPt_eq' _ _ ⟨y, hy'⟩
  have hyχ : y = (torusPt _ _ χ).1 := (congrArg Subtype.val hχ).symm

  let xb : SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g) :=
    NeronModelInfra.schemeHomOverComp (torusPt _ _ χ) O.torusFibre
  have habq : ∀ j, NeronModelInfra.schemeHomOverComp xb (O.abqFibre j) =
      (Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _) :=
    (O.abqFibre_eq_one_iff (𝟙 _) xb).mpr ⟨torusPt _ _ χ, rfl⟩
  let x : SchemeHomOver (resPt A ≫ Λ.σA) O.g := ofFibrePt xb
  have hone : ofFibrePt ((Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 (Spec (CommRingCat.of (ResidueField ↥A))))) =
      Λ.L.one (resPt A ≫ Λ.σA) := by
    apply Subtype.ext
    change (RelativeGroupLaw.baseChangePointToBase (resPt A ≫ Λ.σA) ((Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _))).1 = _
    rw [RelativeGroupLaw.baseChangePointToBase_one, RelativeGroupLaw.one_coe_eq Λ.L (𝟙 _ ≫ (resPt A ≫ Λ.σA)),
      RelativeGroupLaw.one_coe_eq Λ.L (resPt A ≫ Λ.σA), Category.id_comp]
  have hfm : ∀ j, fibreMap (O.abqFibre j) x = Λ.L.one (resPt A ≫ Λ.σA) := by
    intro j
    change ofFibrePt (NeronModelInfra.schemeHomOverComp (toFibrePt (ofFibrePt xb)) (O.abqFibre j)) = _
    rw [toFibrePt_ofFibrePt, habq j, hone]

  have hz : Λ.ptsSp.symm (Λ.L.one (resPt A ≫ Λ.σA)) = 0 := by
    rw [Equiv.symm_apply_eq, LevelData.ptsSp_zero hΛ]
  have hdeg : NeronModelInfra.schemeHomOverComp x (O.degeneracyHom i) = Λ.L.one (resPt A ≫ Λ.σA) := by
    obtain ⟨e0, e1⟩ := O.degeneracyHom_special x
    rw [hfm 0, hfm 1, hz, map_zero, add_zero] at e0
    rw [hfm 0, hfm 1, hz, map_zero, zero_add] at e1
    fin_cases i
    · exact Λ.ptsSp.symm.injective (e0.trans hz.symm)
    · exact Λ.ptsSp.symm.injective (e1.trans hz.symm)

  have hdegb : NeronModelInfra.schemeHomOverComp xb
      (NeronSpecialFibreInfra.fibreRestrictAlong (resPt A ≫ Λ.σA) Λ.f O.g (O.degeneracyHom i)) =
      (Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _) := by
    apply (RelativeGroupLaw.baseChangePointEquiv (resPt A ≫ Λ.σA) (𝟙 _)).injective
    change RelativeGroupLaw.baseChangePointToBase _ _ = RelativeGroupLaw.baseChangePointToBase _ _
    rw [RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong, RelativeGroupLaw.baseChangePointToBase_one]
    have h1 : RelativeGroupLaw.baseChangePointToBase (resPt A ≫ Λ.σA) xb = overId x := by
      rw [← toFibrePt_ofFibrePt xb]
      exact RelativeGroupLaw.baseChangePointToBase_ofBase _ _
    rw [h1]
    have h2 : NeronModelInfra.schemeHomOverComp (overId x) (O.degeneracyHom i) =
        overId (NeronModelInfra.schemeHomOverComp x (O.degeneracyHom i)) := Subtype.ext rfl
    rw [h2, hdeg]
    apply Subtype.ext
    change (Λ.L.one (resPt A ≫ Λ.σA)).1 = (Λ.L.one (𝟙 _ ≫ (resPt A ≫ Λ.σA))).1
    rw [RelativeGroupLaw.one_coe_eq Λ.L (𝟙 _ ≫ (resPt A ≫ Λ.σA)), RelativeGroupLaw.one_coe_eq Λ.L (resPt A ≫ Λ.σA),
      Category.id_comp]
  have := congrArg Subtype.val hdegb
  rw [NeronModelInfra.schemeHomOverComp_coe] at this
  change ((torusPt _ _ χ).1 ≫ O.torusFibre.1) ≫ _ = _ at this
  rw [hyχ, ← Category.assoc, this, ← Category.assoc, (torusPt _ _ χ).2, Category.id_comp]

end ModularCurve.JZeroNeronObjectAtP
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.ModularCurve.JZeroNeronObjectAtP"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.ModularCurve"

namespace ModularCurve p2m_export "ModularCurve" "JZeroNeronObjectAtP.LevelData JZeroNeronObjectAtP jZeroTorsion JZero JZeroC instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable jZeroTorsionFinite JZeroNeronObjectAtP.isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le JZeroNeronObjectAtP.finite_fixedPoints_frobSp_comp_self" namespace JZeroNeronObjectAtP p2m_export "ModularCurve.JZeroNeronObjectAtP" "base genPt barPt resPt overId toFibrePt ofFibrePt fibreMap torusCoord torusStr torusPt LevelData abqFibre_eq_one_iff L G pts_add abqFibre_mul degeneracyHom torusFibre abqFibre degeneracyHom_mul g frobSp separated toricRank degeneracyHom_special pts locallyOfFiniteType isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le finite_fixedPoints_frobSp_comp_self" end ModularCurve.JZeroNeronObjectAtP
p2m_open_scoped "ModularCurve ModularCurve.JZeroNeronObjectAtP" in

theorem ModularCurve.JZeroNeronObjectAtP.exists_isPullback_schemeKer_kerPairLaw_residue
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) :
    letI LHκ := GoodReductionJacobian.RelativeGroupLaw.kerPairLaw
      (O.L.baseChange (resPt A ≫ Λ.σA)) (Λ.L.baseChange (resPt A ≫ Λ.σA))
      (fun i => NeronSpecialFibreInfra.fibreRestrictAlong (resPt A ≫ Λ.σA) Λ.f O.g (O.degeneracyHom i))
      (fun i => GoodReductionJacobian.RelativeGroupLaw.IsHom.fibreRestrictAlong (resPt A ≫ Λ.σA)
        (fun t x y => O.degeneracyHom_mul i t x y))
    letI LHA := GoodReductionJacobian.RelativeGroupLaw.kerPairLaw
      (O.L.baseChange Λ.σA) (Λ.L.baseChange Λ.σA)
      (fun i => NeronSpecialFibreInfra.fibreRestrictAlong Λ.σA Λ.f O.g (O.degeneracyHom i))
      (fun i => GoodReductionJacobian.RelativeGroupLaw.IsHom.fibreRestrictAlong Λ.σA
        (fun t x y => O.degeneracyHom_mul i t x y))
    ∃ π : LHκ.schemeKer m ⟶ LHA.schemeKer m,
      IsPullback π (LHκ.schemeKerStr m) (LHA.schemeKerStr m) (resPt A) := by
  exact GoodReductionJacobian.RelativeGroupLaw.exists_isPullback_schemeKer_kerPairLaw_baseChange Λ.σA (resPt A)
    O.L Λ.L O.degeneracyHom (fun i => by intro T t x y; exact O.degeneracyHom_mul i t x y) m

namespace ModularCurve
p2m_export "ModularCurve" "JZeroNeronObjectAtP.LevelData JZeroNeronObjectAtP jZeroTorsion JZero JZeroC instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable jZeroTorsionFinite JZeroNeronObjectAtP.isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le JZeroNeronObjectAtP.finite_fixedPoints_frobSp_comp_self"
namespace JZeroNeronObjectAtP
p2m_export "ModularCurve.JZeroNeronObjectAtP" "base genPt barPt resPt overId toFibrePt ofFibrePt fibreMap torusCoord torusStr torusPt LevelData abqFibre_eq_one_iff L G pts_add abqFibre_mul degeneracyHom torusFibre abqFibre degeneracyHom_mul g frobSp separated toricRank degeneracyHom_special pts locallyOfFiniteType isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le finite_fixedPoints_frobSp_comp_self"
p2m_open "ModularCurve.JZeroNeronObjectAtP ModularCurve"

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  {Λ : LevelData N₀ p A}

scoped instance kerATorsStr_locallyOfFiniteType [hΛ : Fact Λ.IsJacobian] (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) :
    LocallyOfFiniteType (kerATorsStr O m) := by
  haveI : IsSeparated Λ.f := hΛ.out.1.proper.toIsSeparated
  haveI : LocallyOfFiniteType O.g := O.locallyOfFiniteType
  haveI : IsSeparated O.g := O.separated
  haveI : LocallyOfFiniteType ((kerALaw O).schemeNsmul m ≫ RelativeGroupLaw.kerPairStr (Λ.L.baseChange Λ.σA) (degA O)) := by
    rw [RelativeGroupLaw.schemeNsmul_over]; infer_instance
  haveI : LocallyOfFiniteType ((kerALaw O).schemeNsmul m) :=
    locallyOfFiniteType_of_comp _ (RelativeGroupLaw.kerPairStr (Λ.L.baseChange Λ.σA) (degA O))
  infer_instance

end ModularCurve.JZeroNeronObjectAtP
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.ModularCurve.JZeroNeronObjectAtP"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.ModularCurve.JZeroNeronObjectAtP"

namespace ModularCurve
p2m_export "ModularCurve" "JZeroNeronObjectAtP.LevelData JZeroNeronObjectAtP jZeroTorsion JZero JZeroC instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable jZeroTorsionFinite JZeroNeronObjectAtP.isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le JZeroNeronObjectAtP.finite_fixedPoints_frobSp_comp_self"
namespace JZeroNeronObjectAtP
p2m_export "ModularCurve.JZeroNeronObjectAtP" "base genPt barPt resPt overId toFibrePt ofFibrePt fibreMap torusCoord torusStr torusPt LevelData abqFibre_eq_one_iff L G pts_add abqFibre_mul degeneracyHom torusFibre abqFibre degeneracyHom_mul g frobSp separated toricRank degeneracyHom_special pts locallyOfFiniteType isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le finite_fixedPoints_frobSp_comp_self"
p2m_open "ModularCurve.JZeroNeronObjectAtP ModularCurve"

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  {Λ : LevelData N₀ p A}

omit [Fact p.Prime] [NeZero p] in

theorem eq_closedPoint_or_mem_range_barPt (A : ValuationSubring (AlgebraicClosure ℚ))
    (y : Spec (CommRingCat.of ↥A)) : y = IsLocalRing.closedPoint ↥A ∨ y ∈ Set.range (barPt A).base := by
  by_cases h : y.asIdeal = ⊥
  · right
    refine ⟨IsLocalRing.closedPoint (AlgebraicClosure ℚ), ?_⟩
    apply PrimeSpectrum.ext
    change Ideal.comap (A.subtype) (IsLocalRing.closedPoint (AlgebraicClosure ℚ)).asIdeal = y.asIdeal
    rw [h]
    have h0 : (IsLocalRing.closedPoint (AlgebraicClosure ℚ)).asIdeal = ⊥ := by
      change IsLocalRing.maximalIdeal _ = ⊥
      exact IsLocalRing.maximalIdeal_eq_bot
    rw [h0, ← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).mp Subtype.val_injective
  · left
    haveI hQ : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by convert AlgebraicClosure.isAlgebraic ℚ <;> first | with_reducible_and_instances rfl | rfl | exact Subsingleton.elim _ _
    haveI : Ring.KrullDimLE 1 ↥A := ValuationSubring.krullDimLE_one_of_isAlgebraic_rat A
    have hmax : y.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal_of_ne_bot y.isPrime h
    apply PrimeSpectrum.ext
    exact IsLocalRing.eq_maximalIdeal hmax

omit [NeZero N₀] [Fact p.Prime] [NeZero p] in

theorem range_resPt (A : ValuationSubring (AlgebraicClosure ℚ)) :
    Set.range (resPt A).base = {IsLocalRing.closedPoint ↥A} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact PrimeSpectrum.comap_residue (↥A) x
  · intro hy
    rw [Set.eq_of_mem_singleton hy]
    exact ⟨IsLocalRing.closedPoint _, PrimeSpectrum.comap_residue (↥A) _⟩

end ModularCurve.JZeroNeronObjectAtP
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.ModularCurve.JZeroNeronObjectAtP"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.ModularCurve.JZeroNeronObjectAtP"

noncomputable section

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.nsmul_zero RelativeGroupLaw.nsmul_succ RelativeGroupLaw.schemeNsmul_over RelativeGroupLaw.baseChangeStr RelativeGroupLaw.baseChangePointToBase RelativeGroupLaw.baseChangePointOfBase RelativeGroupLaw.baseChangePointToBase_ofBase RelativeGroupLaw.baseChangePointOfBase_toBase RelativeGroupLaw.baseChangePointEquiv RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong RelativeGroupLaw.baseChangePointToBase_one RelativeGroupLaw.IsHom RelativeGroupLaw.IsHom.fibreRestrictAlong RelativeGroupLaw.kerPair RelativeGroupLaw.kerPairStr RelativeGroupLaw.one_coe_eq RelativeGroupLaw.kerPairLaw RelativeGroupLaw.exists_isPullback_schemeKer_kerPairLaw_baseChange"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "pointGroup mul_inv_cancel one_natural mul_assoc one inv one_mul inv_mul_cancel mul nsmul nsmul_zero nsmul_succ nsmul_natural idPoint schemeNsmul schemeNsmul_over schemeKer schemeKerStr baseChangeStr baseChangePointToBase baseChangePointOfBase baseChangePointToBase_coe baseChangePointToBase_ofBase baseChangePointOfBase_toBase baseChangePointEquiv baseChangePointToBase_comp_fibreRestrictAlong baseChange baseChangePointToBase_mul baseChangePointToBase_one fibre IsHom IsHom.fibreRestrictAlong kerPair kerPairι kerPairStr kerLeg_snd_eq kerPair_snd_fst one_coe_eq kerPairPointEquiv kerPairPointEquiv_apply_coe_coe kerPairPointEquiv_symm_apply_coe kerPairLaw kerPairPointEquiv_one kerPairPointEquiv_nsmul kerPair_snd_fst_assoc exists_isPullback_schemeKer_kerPairLaw_baseChange"
namespace FibIso
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

section KerPts

variable {S : Type u} [CommRing S] {Y : Scheme.{u}} {h : Y ⟶ Spec (CommRingCat.of S)}
  (H : RelativeGroupLaw S h) (n : ℕ)

theorem comp_schemeNsmul {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (z : SchemeHomOver t h) :
    z.1 ≫ H.schemeNsmul n = (H.nsmul t n z).1 := by
  have e : GoodReductionJacobian.schemeHomOverComp z.1 z.2 (idPoint (f := h)) = z :=
    Subtype.ext (Category.comp_id _)
  have key := congrArg Subtype.val (H.nsmul_natural h t z.1 z.2 n idPoint)
  rw [e, GoodReductionJacobian.schemeHomOverComp_coe] at key
  exact key

theorem schemeKer_fst_comp {T : Scheme.{u}} (a : T ⟶ H.schemeKer n) :
    (a ≫ pullback.fst _ _) ≫ h = a ≫ H.schemeKerStr n := by
  calc (a ≫ pullback.fst _ _) ≫ h
      = a ≫ pullback.fst _ _ ≫ (H.schemeNsmul n ≫ h) := by rw [H.schemeNsmul_over, Category.assoc]
    _ = a ≫ (pullback.fst _ _ ≫ H.schemeNsmul n) ≫ h := by simp only [Category.assoc]
    _ = a ≫ (pullback.snd _ _ ≫ (H.one (𝟙 _)).1) ≫ h := by rw [pullback.condition]
    _ = a ≫ H.schemeKerStr n := by rw [Category.assoc, (H.one (𝟙 _)).2, Category.comp_id]

def kerPtOut {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (a : T ⟶ H.schemeKer n)
    (ha : a ≫ H.schemeKerStr n = t) : SchemeHomOver t h :=
  ⟨a ≫ pullback.fst _ _, (schemeKer_fst_comp H n a).trans ha⟩

@[scoped simp]
theorem kerPtOut_coe {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (a : T ⟶ H.schemeKer n)
    (ha : a ≫ H.schemeKerStr n = t) : (kerPtOut H n t a ha).1 = a ≫ pullback.fst _ _ :=
  rfl

theorem nsmul_kerPtOut {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (a : T ⟶ H.schemeKer n)
    (ha : a ≫ H.schemeKerStr n = t) : H.nsmul t n (kerPtOut H n t a ha) = H.one t := by
  apply Subtype.ext
  rw [← comp_schemeNsmul, one_coe_eq, kerPtOut_coe, ← ha]
  simp only [Category.assoc, pullback.condition]

def kerPtIn {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (z : SchemeHomOver t h)
    (hz : H.nsmul t n z = H.one t) : T ⟶ H.schemeKer n :=
  pullback.lift z.1 t (by rw [comp_schemeNsmul, hz, one_coe_eq])

@[scoped simp]
theorem kerPtIn_fst {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (z : SchemeHomOver t h)
    (hz : H.nsmul t n z = H.one t) : kerPtIn H n t z hz ≫ pullback.fst _ _ = z.1 :=
  pullback.lift_fst _ _ _

@[scoped simp]
theorem kerPtIn_str {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (z : SchemeHomOver t h)
    (hz : H.nsmul t n z = H.one t) : kerPtIn H n t z hz ≫ H.schemeKerStr n = t :=
  pullback.lift_snd _ _ _

theorem schemeKer_hom_ext {T : Scheme.{u}} {a b : T ⟶ H.schemeKer n}
    (h1 : a ≫ pullback.fst _ _ = b ≫ pullback.fst _ _) : a = b := by
  apply pullback.hom_ext h1
  change a ≫ H.schemeKerStr n = b ≫ H.schemeKerStr n
  rw [← schemeKer_fst_comp, ← schemeKer_fst_comp, h1]

end KerPts
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.ModularCurve.JZeroNeronObjectAtP"

section Reb

variable {R : Type u} [CommRing R] {X X' : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
  {f' : X' ⟶ Spec (CommRingCat.of R)}

def reb {T : Scheme.{u}} {s s' : T ⟶ Spec (CommRingCat.of R)} (e : s = s') (x : SchemeHomOver s f) :
    SchemeHomOver s' f :=
  ⟨x.1, x.2.trans e⟩

@[scoped simp]
theorem reb_coe {T : Scheme.{u}} {s s' : T ⟶ Spec (CommRingCat.of R)} (e : s = s') (x : SchemeHomOver s f) :
    (reb e x).1 = x.1 :=
  rfl

theorem comp_reb {T : Scheme.{u}} {s s' : T ⟶ Spec (CommRingCat.of R)} (e : s = s') (x : SchemeHomOver s f)
    (ψ : SchemeHomOver f f') :
    NeronModelInfra.schemeHomOverComp (reb e x) ψ = reb e (NeronModelInfra.schemeHomOverComp x ψ) :=
  Subtype.ext rfl

theorem reb_one (G : RelativeGroupLaw R f) {T : Scheme.{u}} {s s' : T ⟶ Spec (CommRingCat.of R)} (e : s = s') :
    reb e (G.one s) = G.one s' := by
  cases e; rfl

theorem nsmul_reb (G : RelativeGroupLaw R f) {T : Scheme.{u}} {s s' : T ⟶ Spec (CommRingCat.of R)} (e : s = s')
    (n : ℕ) (x : SchemeHomOver s f) : G.nsmul s' n (reb e x) = reb e (G.nsmul s n x) := by
  cases e; rfl

end Reb
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.ModularCurve.JZeroNeronObjectAtP"

section BCnsmul

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
  (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)) {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}

theorem baseChangePointToBase_nsmul (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of R')) (n : ℕ) (x : SchemeHomOver t' (baseChangeStr ι f)) :
    baseChangePointToBase ι ((G.baseChange ι).nsmul t' n x) = G.nsmul (t' ≫ ι) n (baseChangePointToBase ι x) := by
  induction n with
  | zero => rw [nsmul_zero, nsmul_zero, baseChangePointToBase_one]
  | succ n ih => rw [nsmul_succ, nsmul_succ, baseChangePointToBase_mul, ih]

end BCnsmul
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.ModularCurve.JZeroNeronObjectAtP"

section Q

variable {R : Type u} [CommRing R] {X X' : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
  {f' : X' ⟶ Spec (CommRingCat.of R)}
  (G : RelativeGroupLaw R f) (G' : RelativeGroupLaw R f') (φ : Fin 2 → SchemeHomOver f f')
  (hφ : ∀ i, IsHom G G' (φ i)) {S : Type u} [CommRing S] (ι : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R))
  (m : ℕ)

abbrev φbc : Fin 2 → SchemeHomOver (baseChangeStr ι f) (baseChangeStr ι f') :=
  fun i => NeronSpecialFibreInfra.fibreRestrictAlong ι f' f (φ i)

abbrev Lbc : RelativeGroupLaw S (kerPairStr (G'.baseChange ι) (φbc φ ι)) :=
  kerPairLaw (G.baseChange ι) (G'.baseChange ι) (fun i => NeronSpecialFibreInfra.fibreRestrictAlong ι f' f (φ i))
    (fun i => IsHom.fibreRestrictAlong ι (hφ i))

theorem kerPair_hom_ext {R₁ : Type u} [CommRing R₁] {A A' : Scheme.{u}} {g : A ⟶ Spec (CommRingCat.of R₁)}
    {g' : A' ⟶ Spec (CommRingCat.of R₁)} (K' : RelativeGroupLaw R₁ g') (ψ : Fin 2 → SchemeHomOver g g')
    {T : Scheme.{u}} {a b : T ⟶ kerPair K' ψ} (hab : a ≫ kerPairι K' ψ = b ≫ kerPairι K' ψ) : a = b := by
  have hab' : a ≫ pullback.fst _ _ ≫ pullback.fst (ψ 0).1 (K'.one (𝟙 _)).1 =
      b ≫ pullback.fst _ _ ≫ pullback.fst (ψ 0).1 (K'.one (𝟙 _)).1 := hab
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simpa only [Category.assoc] using hab'
    · rw [kerLeg_snd_eq K' ψ 0]
      simp only [Category.assoc]
      rw [reassoc_of% hab']
  · apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [kerPair_snd_fst, hab]
    · rw [kerLeg_snd_eq K' ψ 1]
      simp only [Category.assoc]
      rw [kerPair_snd_fst_assoc, reassoc_of% hab']

variable {G G' φ hφ ι m} in

theorem Q_hom_ext {T : Scheme.{u}} {a b : T ⟶ (Lbc G G' φ hφ ι).schemeKer m}
    (hX : a ≫ pullback.fst _ _ ≫ kerPairι _ _ ≫ pullback.fst f ι = b ≫ pullback.fst _ _ ≫ kerPairι _ _ ≫ pullback.fst f ι)
    (hS : a ≫ (Lbc G G' φ hφ ι).schemeKerStr m = b ≫ (Lbc G G' φ hφ ι).schemeKerStr m) : a = b := by
  apply schemeKer_hom_ext
  apply kerPair_hom_ext
  apply pullback.hom_ext
  · simpa only [Category.assoc] using hX
  · have ha := schemeKer_fst_comp (Lbc G G' φ hφ ι) m a
    have hb := schemeKer_fst_comp (Lbc G G' φ hφ ι) m b
    simp only [Category.assoc] at ha hb ⊢
    rw [ha, hb, hS]

theorem Q_mk_aux1 {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver (t ≫ ι) f)
    (hx1 : ∀ i, NeronModelInfra.schemeHomOverComp x (φ i) = G'.one (t ≫ ι)) (i : Fin 2) :
    NeronModelInfra.schemeHomOverComp (baseChangePointOfBase ι x)
      (NeronSpecialFibreInfra.fibreRestrictAlong ι f' f (φ i)) = (G'.baseChange ι).one t := by
  apply (baseChangePointEquiv ι (f := f') t).injective
  change baseChangePointToBase ι _ = baseChangePointToBase ι _
  rw [baseChangePointToBase_comp_fibreRestrictAlong, baseChangePointToBase_one, baseChangePointToBase_ofBase]
  exact hx1 i

def zOf {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver (t ≫ ι) f)
    (hx1 : ∀ i, NeronModelInfra.schemeHomOverComp x (φ i) = G'.one (t ≫ ι)) :
    SchemeHomOver t (kerPairStr (G'.baseChange ι) (φbc φ ι)) :=
  (kerPairPointEquiv (G'.baseChange ι) (φbc φ ι) t).symm ⟨baseChangePointOfBase ι x, Q_mk_aux1 G' φ ι t x hx1⟩

theorem Q_mk_aux2 {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver (t ≫ ι) f)
    (hx1 : ∀ i, NeronModelInfra.schemeHomOverComp x (φ i) = G'.one (t ≫ ι))
    (hx2 : G.nsmul (t ≫ ι) m x = G.one (t ≫ ι)) :
    (Lbc G G' φ hφ ι).nsmul t m (zOf G' φ ι t x hx1) = (Lbc G G' φ hφ ι).one t := by
  apply (kerPairPointEquiv (G'.baseChange ι) (φbc φ ι) t).injective
  apply Subtype.ext
  rw [kerPairPointEquiv_nsmul, kerPairPointEquiv_one, zOf, Equiv.apply_symm_apply]
  apply (baseChangePointEquiv ι (f := f) t).injective
  change baseChangePointToBase ι _ = baseChangePointToBase ι _
  rw [baseChangePointToBase_nsmul, baseChangePointToBase_one, baseChangePointToBase_ofBase]
  exact hx2

def Q_mk {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver (t ≫ ι) f)
    (hx1 : ∀ i, NeronModelInfra.schemeHomOverComp x (φ i) = G'.one (t ≫ ι))
    (hx2 : G.nsmul (t ≫ ι) m x = G.one (t ≫ ι)) : T ⟶ (Lbc G G' φ hφ ι).schemeKer m :=
  kerPtIn (Lbc G G' φ hφ ι) m t (zOf G' φ ι t x hx1) (Q_mk_aux2 G G' φ hφ ι m t x hx1 hx2)

theorem Q_mk_X {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver (t ≫ ι) f)
    (hx1 : ∀ i, NeronModelInfra.schemeHomOverComp x (φ i) = G'.one (t ≫ ι))
    (hx2 : G.nsmul (t ≫ ι) m x = G.one (t ≫ ι)) :
    Q_mk G G' φ hφ ι m t x hx1 hx2 ≫ pullback.fst _ _ ≫ kerPairι _ _ ≫ pullback.fst f ι = x.1 := by
  rw [Q_mk, ← Category.assoc, kerPtIn_fst, zOf, ← Category.assoc, kerPairPointEquiv_symm_apply_coe]
  exact pullback.lift_fst _ _ _

theorem Q_mk_str {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver (t ≫ ι) f)
    (hx1 : ∀ i, NeronModelInfra.schemeHomOverComp x (φ i) = G'.one (t ≫ ι))
    (hx2 : G.nsmul (t ≫ ι) m x = G.one (t ≫ ι)) :
    Q_mk G G' φ hφ ι m t x hx1 hx2 ≫ (Lbc G G' φ hφ ι).schemeKerStr m = t := by
  rw [Q_mk, kerPtIn_str]

def Q_out {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (a : T ⟶ (Lbc G G' φ hφ ι).schemeKer m)
    (ha : a ≫ (Lbc G G' φ hφ ι).schemeKerStr m = t) : SchemeHomOver (t ≫ ι) f :=
  baseChangePointToBase ι
    (kerPairPointEquiv (G'.baseChange ι) (φbc φ ι) t (kerPtOut (Lbc G G' φ hφ ι) m t a ha)).1

theorem Q_out_coe {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (a : T ⟶ (Lbc G G' φ hφ ι).schemeKer m)
    (ha : a ≫ (Lbc G G' φ hφ ι).schemeKerStr m = t) :
    (Q_out G G' φ hφ ι m t a ha).1 = a ≫ pullback.fst _ _ ≫ kerPairι _ _ ≫ pullback.fst f ι := by
  simp only [Q_out, baseChangePointToBase_coe, kerPairPointEquiv_apply_coe_coe, kerPtOut_coe, Category.assoc]

theorem Q_out_comp {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (a : T ⟶ (Lbc G G' φ hφ ι).schemeKer m)
    (ha : a ≫ (Lbc G G' φ hφ ι).schemeKerStr m = t) (i : Fin 2) :
    NeronModelInfra.schemeHomOverComp (Q_out G G' φ hφ ι m t a ha) (φ i) = G'.one (t ≫ ι) := by
  have h2 : NeronModelInfra.schemeHomOverComp
      (kerPairPointEquiv (G'.baseChange ι) (φbc φ ι) t (kerPtOut (Lbc G G' φ hφ ι) m t a ha)).1
      (NeronSpecialFibreInfra.fibreRestrictAlong ι f' f (φ i)) = (G'.baseChange ι).one t :=
    (kerPairPointEquiv (G'.baseChange ι) (φbc φ ι) t (kerPtOut (Lbc G G' φ hφ ι) m t a ha)).2 i
  have h3 := congrArg (baseChangePointToBase ι) h2
  rw [baseChangePointToBase_comp_fibreRestrictAlong, baseChangePointToBase_one] at h3
  exact h3

theorem Q_out_nsmul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (a : T ⟶ (Lbc G G' φ hφ ι).schemeKer m)
    (ha : a ≫ (Lbc G G' φ hφ ι).schemeKerStr m = t) :
    G.nsmul (t ≫ ι) m (Q_out G G' φ hφ ι m t a ha) = G.one (t ≫ ι) := by
  rw [Q_out, ← baseChangePointToBase_nsmul,
    ← kerPairPointEquiv_nsmul (G.baseChange ι) (G'.baseChange ι)
      (fun i => NeronSpecialFibreInfra.fibreRestrictAlong ι f' f (φ i)) (fun i => IsHom.fibreRestrictAlong ι (hφ i)),
    nsmul_kerPtOut, kerPairPointEquiv_one, baseChangePointToBase_one]

end Q
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.ModularCurve.JZeroNeronObjectAtP"

end GoodReductionJacobian.RelativeGroupLaw.FibIso
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.ModularCurve.JZeroNeronObjectAtP P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian.RelativeGroupLaw.FibIso"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.ModularCurve.JZeroNeronObjectAtP"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.ModularCurve.JZeroNeronObjectAtP"

namespace ModularCurve
p2m_export "ModularCurve" "JZeroNeronObjectAtP.LevelData JZeroNeronObjectAtP jZeroTorsion JZero JZeroC instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable jZeroTorsionFinite JZeroNeronObjectAtP.isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le JZeroNeronObjectAtP.finite_fixedPoints_frobSp_comp_self"
namespace JZeroNeronObjectAtP
p2m_export "ModularCurve.JZeroNeronObjectAtP" "base genPt barPt resPt overId toFibrePt ofFibrePt fibreMap torusCoord torusStr torusPt LevelData abqFibre_eq_one_iff L G pts_add abqFibre_mul degeneracyHom torusFibre abqFibre degeneracyHom_mul g frobSp separated toricRank degeneracyHom_special pts locallyOfFiniteType isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le finite_fixedPoints_frobSp_comp_self"
namespace GenFib
p2m_open "ModularCurve.JZeroNeronObjectAtP ModularCurve"

p2m_open "GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian.RelativeGroupLaw.FibIso"

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p} {Λ : LevelData N₀ p A}

theorem eq_one_of_mul_self {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f)
    (h : G.mul t x x = x) : x = G.one t :=
  calc x = G.mul t (G.one t) x := (G.one_mul t x).symm
    _ = G.mul t (G.mul t (G.inv t x) x) x := by rw [G.inv_mul_cancel]
    _ = G.mul t (G.inv t x) (G.mul t x x) := by rw [G.mul_assoc]
    _ = G.mul t (G.inv t x) x := by rw [h]
    _ = G.one t := G.inv_mul_cancel t x

theorem degHom_isHom (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (i : Fin 2) : IsHom O.L Λ.L (O.degeneracyHom i) :=
  O.degeneracyHom_mul i

theorem pts_zero (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) : O.pts 0 = O.L.one (genPt p) := by
  apply eq_one_of_mul_self
  have h := O.pts_add 0 0
  rw [add_zero] at h
  exact h.symm

theorem pts_nsmul (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (n : ℕ) (x : JZero (N₀ * p)) :
    O.pts (n • x) = O.L.nsmul (genPt p) n (O.pts x) := by
  induction n with
  | zero => rw [zero_nsmul, pts_zero, RelativeGroupLaw.nsmul_zero]
  | succ n ih => rw [succ_nsmul, O.pts_add, ih, RelativeGroupLaw.nsmul_succ]

abbrev LA (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) :=
  Lbc O.L Λ.L O.degeneracyHom (degHom_isHom O) Λ.σA

def toJZero (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ)
    (a : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ (LA O).schemeKer m)
    (ha : a ≫ (LA O).schemeKerStr m = barPt A) : JZero (N₀ * p) :=
  O.pts.symm (reb Λ.hσA (Q_out O.L Λ.L O.degeneracyHom (degHom_isHom O) Λ.σA m
    (barPt A) a ha))

theorem nsmul_toJZero (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ)
    (a : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ (LA O).schemeKer m)
    (ha : a ≫ (LA O).schemeKerStr m = barPt A) : m • toJZero O m a ha = 0 := by
  apply O.pts.injective
  rw [pts_nsmul, toJZero, Equiv.apply_symm_apply, nsmul_reb, Q_out_nsmul, reb_one, pts_zero]

theorem coe_pts_toJZero (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ)
    (a : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ (LA O).schemeKer m)
    (ha : a ≫ (LA O).schemeKerStr m = barPt A) :
    (O.pts (toJZero O m a ha)).1 = a ≫ pullback.fst _ _ ≫ kerPairι _ _ ≫ pullback.fst O.g Λ.σA := by
  rw [toJZero, Equiv.apply_symm_apply, reb_coe, Q_out_coe]

theorem toJZero_injective (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ)
    {a b : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ (LA O).schemeKer m}
    (ha : a ≫ (LA O).schemeKerStr m = barPt A) (hb : b ≫ (LA O).schemeKerStr m = barPt A)
    (h : toJZero O m a ha = toJZero O m b hb) : a = b := by
  refine Q_hom_ext (G := O.L) (G' := Λ.L) (φ := O.degeneracyHom) (hφ := degHom_isHom O) (ι := Λ.σA) (m := m) ?_ ?_
  · rw [← coe_pts_toJZero O m a ha, ← coe_pts_toJZero O m b hb, h]
  · rw [ha, hb]

end ModularCurve.JZeroNeronObjectAtP.GenFib
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.ModularCurve.JZeroNeronObjectAtP P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian.RelativeGroupLaw.FibIso"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.ModularCurve.JZeroNeronObjectAtP P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian.RelativeGroupLaw.FibIso"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.ModularCurve.JZeroNeronObjectAtP P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian.RelativeGroupLaw.FibIso"

end
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.ModularCurve.JZeroNeronObjectAtP P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw.GoodReductionJacobian.RelativeGroupLaw.FibIso"

p2m_open_scoped "ModularCurve ModularCurve.JZeroNeronObjectAtP" in
open GoodReductionJacobian.RelativeGroupLaw.FibIso ModularCurve.JZeroNeronObjectAtP.GenFib in
set_option synthInstance.maxHeartbeats 1600000 in

theorem ModularCurve.JZeroNeronObjectAtP.finite_preimage_schemeKerStr_kerPairLaw_range_barPt
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) (hm : 0 < m) :
    letI LHA := GoodReductionJacobian.RelativeGroupLaw.kerPairLaw
      (O.L.baseChange Λ.σA) (Λ.L.baseChange Λ.σA)
      (fun i => NeronSpecialFibreInfra.fibreRestrictAlong Λ.σA Λ.f O.g (O.degeneracyHom i))
      (fun i => GoodReductionJacobian.RelativeGroupLaw.IsHom.fibreRestrictAlong Λ.σA
        (fun t x y => O.degeneracyHom_mul i t x y))
    ((LHA.schemeKerStr m).base ⁻¹' Set.range (barPt A).base).Finite := by
  haveI : LocallyOfFiniteType (RelativeGroupLaw.baseChangeStr Λ.σA O.g) :=
    MorphismProperty.pullback_snd (P := @LocallyOfFiniteType) _ _ O.locallyOfFiniteType
  haveI : IsSeparated (RelativeGroupLaw.baseChangeStr Λ.σA Λ.f) :=
    MorphismProperty.pullback_snd (P := @IsSeparated) _ _ hΛ.1.proper.toIsSeparated
  change ((((LA O).schemeKerStr m)).base ⁻¹' Set.range (barPt A).base).Finite

  haveI : LocallyOfFiniteType ((LA O).schemeNsmul m) := by
    have : LocallyOfFiniteType ((LA O).schemeNsmul m ≫ RelativeGroupLaw.kerPairStr _ _) := by
      rw [RelativeGroupLaw.schemeNsmul_over]; infer_instance
    exact locallyOfFiniteType_of_comp _ (RelativeGroupLaw.kerPairStr _ _)
  haveI : LocallyOfFiniteType ((LA O).schemeKerStr m) := inferInstance

  haveI : Finite ↥(jZeroTorsion (N₀ * p) m) := jZeroTorsionFinite (N₀ * p) m hm
  let fQ := pullback.snd ((LA O).schemeKerStr m) (barPt A)
  have hsec : ∀ s : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ pullback ((LA O).schemeKerStr m) (barPt A) //
      s ≫ fQ = 𝟙 _}, (s.1 ≫ pullback.fst _ _) ≫ (LA O).schemeKerStr m = barPt A := fun s => by
    rw [Category.assoc, pullback.condition, ← Category.assoc, s.2, Category.id_comp]
  let ψ : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ pullback ((LA O).schemeKerStr m) (barPt A) //
      s ≫ fQ = 𝟙 _} → ↥(jZeroTorsion (N₀ * p) m) := fun s =>
    ⟨toJZero O m (s.1 ≫ pullback.fst _ _) (hsec s), by
      rw [jZeroTorsion, Submodule.mem_toAddSubgroup, Submodule.mem_torsionBy_iff, natCast_zsmul]
      exact nsmul_toJZero O m _ (hsec s)⟩
  have hψ : Function.Injective ψ := fun s₁ s₂ h => by
    have h' := toJZero_injective O m (hsec s₁) (hsec s₂) (congrArg Subtype.val h)
    apply Subtype.ext
    apply pullback.hom_ext h'
    rw [s₁.2, s₂.2]
  haveI : Finite {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ pullback ((LA O).schemeKerStr m) (barPt A) //
      s ≫ fQ = 𝟙 _} := Finite.of_injective ψ hψ

  haveI : IsFinite fQ := isFinite_of_finite_setOf_exists_section_of_isAlgClosed fQ (by
    have hset : {x : ↥(pullback ((LA O).schemeKerStr m) (barPt A)) |
        ∃ s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ pullback ((LA O).schemeKerStr m) (barPt A),
          s ≫ fQ = 𝟙 _ ∧ s (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) = x} =
        Set.range (fun s : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
            pullback ((LA O).schemeKerStr m) (barPt A) // s ≫ fQ = 𝟙 _} =>
          s.1 (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_range, Subtype.exists, exists_prop]
    rw [hset]
    exact Set.finite_range _)

  haveI : IsIntegralHom fQ := inferInstance
  haveI : IsAffineHom fQ := inferInstance
  haveI : QuasiCompact fQ := inferInstance
  haveI : LocallyQuasiFinite fQ := inferInstance
  have huniv : (Set.univ : Set ↥(pullback ((LA O).schemeKerStr m) (barPt A))).Finite := by
    have h1 := fQ.finite_preimage_singleton (IsLocalRing.closedPoint (AlgebraicClosure ℚ))
    exact h1.subset fun x _ => Subsingleton.elim (α := PrimeSpectrum (AlgebraicClosure ℚ)) _ _
  haveI : Finite ↥(pullback ((LA O).schemeKerStr m) (barPt A)) := Set.finite_univ_iff.mp huniv
  rw [← Scheme.Pullback.range_fst]
  exact Set.finite_range _

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) (hm : 0 < m) :
    letI LHA := GoodReductionJacobian.RelativeGroupLaw.kerPairLaw
      (O.L.baseChange Λ.σA) (Λ.L.baseChange Λ.σA)
      (fun i => NeronSpecialFibreInfra.fibreRestrictAlong Λ.σA Λ.f O.g (O.degeneracyHom i))
      (fun i => GoodReductionJacobian.RelativeGroupLaw.IsHom.fibreRestrictAlong Λ.σA
        (fun t x y => O.degeneracyHom_mul i t x y))
    LocallyQuasiFinite (LHA.schemeKerStr m) := by
  classical
  haveI hΛ' : Fact Λ.IsJacobian := ⟨hΛ⟩
  change LocallyQuasiFinite (kerATorsStr O m)
  haveI : LocallyOfFiniteType (kerATorsStr O m) :=
    ModularCurve.JZeroNeronObjectAtP.kerATorsStr_locallyOfFiniteType (hΛ := hΛ') O m
  refine LocallyQuasiFinite.of_finite_preimage_singleton _ (fun y => ?_)
  rcases ModularCurve.JZeroNeronObjectAtP.eq_closedPoint_or_mem_range_barPt A y with rfl | ⟨η, rfl⟩
  ·
    obtain ⟨S, hSK, hS⟩ := ModularCurve.JZeroNeronObjectAtP.exists_finset_kernel_coset_representatives hΛ O
      (ModularCurve.JZeroNeronObjectAtP.finite_fixedPoints_frobSp_comp_self N₀ p hpN₀ A hA Λ O)
    have hι := fun i => ModularCurve.JZeroNeronObjectAtP.torusFibre_comp_fibreRestrictAlong_degeneracyHom_eq hΛ O i
    obtain ⟨hfinκ, -⟩ := ModularCurve.JZeroNeronObjectAtP.isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le
      N₀ p hpN₀ A hA Λ hΛ O hι S hSK hS m hm
    obtain ⟨π, hπ⟩ := ModularCurve.JZeroNeronObjectAtP.exists_isPullback_schemeKer_kerPairLaw_residue N₀ p hpN₀ A hA Λ O m
    haveI := hfinκ

    set LHκ := GoodReductionJacobian.RelativeGroupLaw.kerPairLaw
      (O.L.baseChange (resPt A ≫ Λ.σA)) (Λ.L.baseChange (resPt A ≫ Λ.σA))
      (fun i => NeronSpecialFibreInfra.fibreRestrictAlong (resPt A ≫ Λ.σA) Λ.f O.g (O.degeneracyHom i))
      (fun i => GoodReductionJacobian.RelativeGroupLaw.IsHom.fibreRestrictAlong (resPt A ≫ Λ.σA)
        (fun t x y => O.degeneracyHom_mul i t x y)) with hLHκ
    haveI hqf : LocallyQuasiFinite (LHκ.schemeKerStr m) := instLocallyQuasiFiniteOfIsFinite _
    haveI haff : IsAffineHom (LHκ.schemeKerStr m) := IsFinite.toIsAffineHom
    haveI hqc : QuasiCompact (LHκ.schemeKerStr m) :=
      quasiCompact_iff_forall_isAffineOpen.mpr fun _ hU => (hU.preimage _).isCompact
    have hYfin : (Set.univ : Set ↥(LHκ.schemeKer m)).Finite :=
      (Scheme.Hom.finite_preimage_singleton (LHκ.schemeKerStr m) (IsLocalRing.closedPoint (ResidueField ↥A))).subset
        (fun z _ => Subsingleton.elim _ _)
    haveI hY : Finite ↥(LHκ.schemeKer m) := Set.finite_univ_iff.mp hYfin
    haveI : Finite ↥(pullback (kerATorsStr O m) (resPt A)) :=
      Finite.of_equiv _ (Scheme.homeoOfIso hπ.isoPullback).toEquiv
    have hr : ((kerATorsStr O m).base ⁻¹' {IsLocalRing.closedPoint ↥A}) =
        Set.range (pullback.fst (kerATorsStr O m) (resPt A)).base := by
      rw [Scheme.Pullback.range_fst, ModularCurve.JZeroNeronObjectAtP.range_resPt]
    exact (Set.finite_range _).subset (le_of_eq hr)
  ·
    refine (ModularCurve.JZeroNeronObjectAtP.finite_preimage_schemeKerStr_kerPairLaw_range_barPt
      N₀ p hpN₀ A hA Λ hΛ O m hm).subset (Set.preimage_mono ?_)
    exact Set.singleton_subset_iff.mpr ⟨η, rfl⟩

end S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw (solution)
