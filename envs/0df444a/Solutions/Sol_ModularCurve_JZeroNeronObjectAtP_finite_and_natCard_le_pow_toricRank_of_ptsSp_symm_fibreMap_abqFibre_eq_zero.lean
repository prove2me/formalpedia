-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/ff66cdbf-4b5c-5070-8acd-a6a67addfcb2

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKerPair
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Theorems.Thm_AlgebraicGeometry_IsSeparated_eq_of_spec_map_subtype_comp_eq
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_ValuationSubring_henselianLocalRing_of_isAlgClosed
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_exists_isOpenImmersion_torus_kerPair_degeneracyHom
import Theorems.Thm_AlgebraicGeometry_finite_and_natCard_sections_closedPoint_mem_le_of_finrank_opens_le
import Theorems.Thm_AlgebraicGeometry_SplitTorus_moduleFinite_and_finrank_sections_preimage_opensRange_schemeKer_eq_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero
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

universe u

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.ModularCurve IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.ModularCurve.JZeroNeronObjectAtP NeronSpecialFibreInfra"

noncomputable section

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.nsmul_zero RelativeGroupLaw.nsmul_succ RelativeGroupLaw.schemeNsmul_over RelativeGroupLaw.baseChangeStr RelativeGroupLaw.baseChangePointToBase RelativeGroupLaw.baseChangePointOfBase RelativeGroupLaw.baseChangePointToBase_ofBase RelativeGroupLaw.baseChangePointOfBase_toBase RelativeGroupLaw.baseChangePointEquiv RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong RelativeGroupLaw.baseChangePointToBase_mul RelativeGroupLaw.baseChangePointToBase_one RelativeGroupLaw.IsHom RelativeGroupLaw.IsHom.fibreRestrictAlong RelativeGroupLaw.kerPair RelativeGroupLaw.kerPairι RelativeGroupLaw.kerPairStr RelativeGroupLaw.one_coe_eq RelativeGroupLaw.kerPairPointEquiv RelativeGroupLaw.kerPairPointEquiv_symm_apply_coe RelativeGroupLaw.kerPairLaw RelativeGroupLaw.kerPairPointEquiv_one RelativeGroupLaw.kerPairPointEquiv_nsmul"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "pointGroup one_natural one mk mul nsmul nsmul_zero nsmul_succ nsmul_natural idPoint schemeNsmul schemeNsmul_over schemeKer schemeKerStr baseChangeStr baseChangePointToBase baseChangePointOfBase baseChangePointToBase_coe baseChangePointToBase_ofBase baseChangePointOfBase_toBase baseChangePointEquiv baseChangePointToBase_comp_fibreRestrictAlong baseChange baseChangePointToBase_mul baseChangePointToBase_one fibre IsHom IsHom.fibreRestrictAlong kerPair kerPairι kerPairStr kerLeg_snd_eq kerPair_snd_fst one_coe_eq kerPairPointEquiv kerPairPointEquiv_apply_coe_coe kerPairPointEquiv_symm_apply_coe kerPairLaw kerPairPointEquiv_one kerPairPointEquiv_nsmul kerPair_snd_fst_assoc"
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

theorem main
    {R R' R'' : Type u} [CommRing R] [CommRing R'] [CommRing R'']
    (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)) (ι' : Spec (CommRingCat.of R'') ⟶ Spec (CommRingCat.of R'))
    {X X' : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} {f' : X' ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) (G' : RelativeGroupLaw R f') (φ : Fin 2 → SchemeHomOver f f')
    (hφ : ∀ i, RelativeGroupLaw.IsHom G G' (φ i)) (m : ℕ) :
    letI L' := RelativeGroupLaw.kerPairLaw (G.baseChange ι) (G'.baseChange ι)
      (fun i => NeronSpecialFibreInfra.fibreRestrictAlong ι f' f (φ i))
      (fun i => RelativeGroupLaw.IsHom.fibreRestrictAlong ι (hφ i))
    letI L'' := RelativeGroupLaw.kerPairLaw (G.baseChange (ι' ≫ ι)) (G'.baseChange (ι' ≫ ι))
      (fun i => NeronSpecialFibreInfra.fibreRestrictAlong (ι' ≫ ι) f' f (φ i))
      (fun i => RelativeGroupLaw.IsHom.fibreRestrictAlong (ι' ≫ ι) (hφ i))
    ∃ π : L''.schemeKer m ⟶ L'.schemeKer m, IsPullback π (L''.schemeKerStr m) (L'.schemeKerStr m) ι' := by

  have e0 : (𝟙 _ ≫ (Lbc G G' φ hφ (ι' ≫ ι)).schemeKerStr m) ≫ ι' ≫ ι =
      ((Lbc G G' φ hφ (ι' ≫ ι)).schemeKerStr m ≫ ι') ≫ ι := by simp only [Category.id_comp, Category.assoc]
  let x0 := reb e0 (Q_out G G' φ hφ (ι' ≫ ι) m _ (𝟙 _) rfl)
  have hx01 : ∀ i, NeronModelInfra.schemeHomOverComp x0 (φ i) = G'.one _ := fun i => by
    rw [comp_reb, Q_out_comp, reb_one]
  have hx02 : G.nsmul _ m x0 = G.one _ := by
    rw [nsmul_reb, Q_out_nsmul, reb_one]
  let π := Q_mk G G' φ hφ ι m ((Lbc G G' φ hφ (ι' ≫ ι)).schemeKerStr m ≫ ι') x0 hx01 hx02
  have hπX : π ≫ pullback.fst _ _ ≫ kerPairι _ _ ≫ pullback.fst f ι =
      pullback.fst _ _ ≫ kerPairι _ _ ≫ pullback.fst f (ι' ≫ ι) := by
    rw [Q_mk_X, reb_coe, Q_out_coe, Category.id_comp]
  have comm : π ≫ (Lbc G G' φ hφ ι).schemeKerStr m = (Lbc G G' φ hφ (ι' ≫ ι)).schemeKerStr m ≫ ι' :=
    Q_mk_str _ _ _ _ _ _ _ _ _ _

  have hl : ∀ s : PullbackCone ((Lbc G G' φ hφ ι).schemeKerStr m) ι',
      (s.fst ≫ (Lbc G G' φ hφ ι).schemeKerStr m) ≫ ι = s.snd ≫ ι' ≫ ι := fun s => by
    rw [s.condition, Category.assoc]
  let xl := fun s : PullbackCone ((Lbc G G' φ hφ ι).schemeKerStr m) ι' =>
    reb (hl s) (Q_out G G' φ hφ ι m _ s.fst rfl)
  have hxl1 : ∀ s i, NeronModelInfra.schemeHomOverComp (xl s) (φ i) = G'.one _ := fun s i => by
    simp only [xl]; rw [comp_reb, Q_out_comp, reb_one]
  have hxl2 : ∀ s, G.nsmul _ m (xl s) = G.one _ := fun s => by
    simp only [xl]; rw [nsmul_reb, Q_out_nsmul, reb_one]
  let lift := fun s : PullbackCone ((Lbc G G' φ hφ ι).schemeKerStr m) ι' =>
    Q_mk G G' φ hφ (ι' ≫ ι) m s.snd (xl s) (hxl1 s) (hxl2 s)
  have hliftX : ∀ s, lift s ≫ pullback.fst _ _ ≫ kerPairι _ _ ≫ pullback.fst f (ι' ≫ ι) =
      s.fst ≫ pullback.fst _ _ ≫ kerPairι _ _ ≫ pullback.fst f ι := fun s => by
    simp only [lift]; rw [Q_mk_X, reb_coe, Q_out_coe]
  have hliftS : ∀ s, lift s ≫ (Lbc G G' φ hφ (ι' ≫ ι)).schemeKerStr m = s.snd := fun s =>
    Q_mk_str _ _ _ _ _ _ _ _ _ _
  refine ⟨π, IsPullback.of_isLimit (c := PullbackCone.mk π _ comm)
    (PullbackCone.IsLimit.mk comm lift (fun s => ?_) hliftS (fun s k hk1 hk2 => ?_))⟩
  · apply Q_hom_ext
    · rw [Category.assoc (lift s) π, hπX, hliftX]
    · rw [Category.assoc (lift s) π, comm, ← Category.assoc (lift s), hliftS, s.condition]
  · apply Q_hom_ext
    · rw [hliftX, ← hk1, Category.assoc k π, hπX]
    · rw [hliftS, hk2]

theorem main'
    {R R' R'' : Type u} [CommRing R] [CommRing R'] [CommRing R'']
    (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)) (ι' : Spec (CommRingCat.of R'') ⟶ Spec (CommRingCat.of R'))
    {X X' : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} {f' : X' ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) (G' : RelativeGroupLaw R f') (φ : Fin 2 → SchemeHomOver f f')
    (hφ : ∀ i, RelativeGroupLaw.IsHom G G' (φ i)) (m : ℕ) :
    letI L' := RelativeGroupLaw.kerPairLaw (G.baseChange ι) (G'.baseChange ι)
      (fun i => NeronSpecialFibreInfra.fibreRestrictAlong ι f' f (φ i))
      (fun i => RelativeGroupLaw.IsHom.fibreRestrictAlong ι (hφ i))
    letI L'' := RelativeGroupLaw.kerPairLaw (G.baseChange (ι' ≫ ι)) (G'.baseChange (ι' ≫ ι))
      (fun i => NeronSpecialFibreInfra.fibreRestrictAlong (ι' ≫ ι) f' f (φ i))
      (fun i => RelativeGroupLaw.IsHom.fibreRestrictAlong (ι' ≫ ι) (hφ i))
    ∃ π : L''.schemeKer m ⟶ L'.schemeKer m, IsPullback π (L''.schemeKerStr m) (L'.schemeKerStr m) ι' ∧
      π ≫ pullback.fst (L'.schemeNsmul m) (L'.one (𝟙 _)).1 ≫
          RelativeGroupLaw.kerPairι (G'.baseChange ι) (fun i => NeronSpecialFibreInfra.fibreRestrictAlong ι f' f (φ i)) ≫
            pullback.fst f ι =
        pullback.fst (L''.schemeNsmul m) (L''.one (𝟙 _)).1 ≫
          RelativeGroupLaw.kerPairι (G'.baseChange (ι' ≫ ι))
            (fun i => NeronSpecialFibreInfra.fibreRestrictAlong (ι' ≫ ι) f' f (φ i)) ≫ pullback.fst f (ι' ≫ ι) := by

  have e0 : (𝟙 _ ≫ (Lbc G G' φ hφ (ι' ≫ ι)).schemeKerStr m) ≫ ι' ≫ ι =
      ((Lbc G G' φ hφ (ι' ≫ ι)).schemeKerStr m ≫ ι') ≫ ι := by simp only [Category.id_comp, Category.assoc]
  let x0 := reb e0 (Q_out G G' φ hφ (ι' ≫ ι) m _ (𝟙 _) rfl)
  have hx01 : ∀ i, NeronModelInfra.schemeHomOverComp x0 (φ i) = G'.one _ := fun i => by
    rw [comp_reb, Q_out_comp, reb_one]
  have hx02 : G.nsmul _ m x0 = G.one _ := by
    rw [nsmul_reb, Q_out_nsmul, reb_one]
  let π := Q_mk G G' φ hφ ι m ((Lbc G G' φ hφ (ι' ≫ ι)).schemeKerStr m ≫ ι') x0 hx01 hx02
  have hπX : π ≫ pullback.fst _ _ ≫ kerPairι _ _ ≫ pullback.fst f ι =
      pullback.fst _ _ ≫ kerPairι _ _ ≫ pullback.fst f (ι' ≫ ι) := by
    rw [Q_mk_X, reb_coe, Q_out_coe, Category.id_comp]
  have comm : π ≫ (Lbc G G' φ hφ ι).schemeKerStr m = (Lbc G G' φ hφ (ι' ≫ ι)).schemeKerStr m ≫ ι' :=
    Q_mk_str _ _ _ _ _ _ _ _ _ _

  have hl : ∀ s : PullbackCone ((Lbc G G' φ hφ ι).schemeKerStr m) ι',
      (s.fst ≫ (Lbc G G' φ hφ ι).schemeKerStr m) ≫ ι = s.snd ≫ ι' ≫ ι := fun s => by
    rw [s.condition, Category.assoc]
  let xl := fun s : PullbackCone ((Lbc G G' φ hφ ι).schemeKerStr m) ι' =>
    reb (hl s) (Q_out G G' φ hφ ι m _ s.fst rfl)
  have hxl1 : ∀ s i, NeronModelInfra.schemeHomOverComp (xl s) (φ i) = G'.one _ := fun s i => by
    simp only [xl]; rw [comp_reb, Q_out_comp, reb_one]
  have hxl2 : ∀ s, G.nsmul _ m (xl s) = G.one _ := fun s => by
    simp only [xl]; rw [nsmul_reb, Q_out_nsmul, reb_one]
  let lift := fun s : PullbackCone ((Lbc G G' φ hφ ι).schemeKerStr m) ι' =>
    Q_mk G G' φ hφ (ι' ≫ ι) m s.snd (xl s) (hxl1 s) (hxl2 s)
  have hliftX : ∀ s, lift s ≫ pullback.fst _ _ ≫ kerPairι _ _ ≫ pullback.fst f (ι' ≫ ι) =
      s.fst ≫ pullback.fst _ _ ≫ kerPairι _ _ ≫ pullback.fst f ι := fun s => by
    simp only [lift]; rw [Q_mk_X, reb_coe, Q_out_coe]
  have hliftS : ∀ s, lift s ≫ (Lbc G G' φ hφ (ι' ≫ ι)).schemeKerStr m = s.snd := fun s =>
    Q_mk_str _ _ _ _ _ _ _ _ _ _
  refine ⟨π, IsPullback.of_isLimit (c := PullbackCone.mk π _ comm)
    (PullbackCone.IsLimit.mk comm lift (fun s => ?_) hliftS (fun s k hk1 hk2 => ?_)), hπX⟩
  · apply Q_hom_ext
    · rw [Category.assoc (lift s) π, hπX, hliftX]
    · rw [Category.assoc (lift s) π, comm, ← Category.assoc (lift s), hliftS, s.condition]
  · apply Q_hom_ext
    · rw [hliftX, ← hk1, Category.assoc k π, hπX]
    · rw [hliftS, hk2]

end GoodReductionJacobian.RelativeGroupLaw.FibIso
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw.FibIso"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian"

end
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw.FibIso"

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.nsmul_zero RelativeGroupLaw.nsmul_succ RelativeGroupLaw.schemeNsmul_over RelativeGroupLaw.baseChangeStr RelativeGroupLaw.baseChangePointToBase RelativeGroupLaw.baseChangePointOfBase RelativeGroupLaw.baseChangePointToBase_ofBase RelativeGroupLaw.baseChangePointOfBase_toBase RelativeGroupLaw.baseChangePointEquiv RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong RelativeGroupLaw.baseChangePointToBase_mul RelativeGroupLaw.baseChangePointToBase_one RelativeGroupLaw.IsHom RelativeGroupLaw.IsHom.fibreRestrictAlong RelativeGroupLaw.kerPair RelativeGroupLaw.kerPairι RelativeGroupLaw.kerPairStr RelativeGroupLaw.one_coe_eq RelativeGroupLaw.kerPairPointEquiv RelativeGroupLaw.kerPairPointEquiv_symm_apply_coe RelativeGroupLaw.kerPairLaw RelativeGroupLaw.kerPairPointEquiv_one RelativeGroupLaw.kerPairPointEquiv_nsmul"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "pointGroup one_natural one mk mul nsmul nsmul_zero nsmul_succ nsmul_natural idPoint schemeNsmul schemeNsmul_over schemeKer schemeKerStr baseChangeStr baseChangePointToBase baseChangePointOfBase baseChangePointToBase_coe baseChangePointToBase_ofBase baseChangePointOfBase_toBase baseChangePointEquiv baseChangePointToBase_comp_fibreRestrictAlong baseChange baseChangePointToBase_mul baseChangePointToBase_one fibre IsHom IsHom.fibreRestrictAlong kerPair kerPairι kerPairStr kerLeg_snd_eq kerPair_snd_fst one_coe_eq kerPairPointEquiv kerPairPointEquiv_apply_coe_coe kerPairPointEquiv_symm_apply_coe kerPairLaw kerPairPointEquiv_one kerPairPointEquiv_nsmul kerPair_snd_fst_assoc"
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
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw.FibIso"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw.FibIso"

namespace ModularCurve
p2m_export "ModularCurve" "JZeroNeronObjectAtP.LevelData JZeroNeronObjectAtP jZeroTorsion JZero instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable degeneracyPushforwardPair JZeroNeronObjectAtP.locallyQuasiFinite_schemeKerStr_kerPairLaw JZeroNeronObjectAtP.exists_isOpenImmersion_torus_kerPair_degeneracyHom"
namespace JZeroNeronObjectAtP
p2m_export "ModularCurve.JZeroNeronObjectAtP" "baseRing base genPt barPt resPt overId toFibrePt ofFibrePt fibreMap torusScheme torusStr LevelData abqFibre_eq_one_iff L G pts_add mk degeneracyHom quasiCompact torusFibre abqFibre degeneracyHom_mul g degeneracyHom_pts separated toricRank pts locallyOfFiniteType comm locallyQuasiFinite_schemeKerStr_kerPairLaw exists_isOpenImmersion_torus_kerPair_degeneracyHom"
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
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw.FibIso"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw.FibIso"

namespace ModularCurve
p2m_export "ModularCurve" "JZeroNeronObjectAtP.LevelData JZeroNeronObjectAtP jZeroTorsion JZero instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable degeneracyPushforwardPair JZeroNeronObjectAtP.locallyQuasiFinite_schemeKerStr_kerPairLaw JZeroNeronObjectAtP.exists_isOpenImmersion_torus_kerPair_degeneracyHom"
namespace JZeroNeronObjectAtP
p2m_export "ModularCurve.JZeroNeronObjectAtP" "baseRing base genPt barPt resPt overId toFibrePt ofFibrePt fibreMap torusScheme torusStr LevelData abqFibre_eq_one_iff L G pts_add mk degeneracyHom quasiCompact torusFibre abqFibre degeneracyHom_mul g degeneracyHom_pts separated toricRank pts locallyOfFiniteType comm locallyQuasiFinite_schemeKerStr_kerPairLaw exists_isOpenImmersion_torus_kerPair_degeneracyHom"
p2m_open "ModularCurve.JZeroNeronObjectAtP ModularCurve"

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  {Λ : LevelData N₀ p A}

theorem pts_nsmul (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (n : ℕ) (x : JZero (N₀ * p)) :
    O.pts (n • x) = O.L.nsmul (genPt p) n (O.pts x) := by
  induction n with
  | zero =>
    rw [zero_nsmul, RelativeGroupLaw.nsmul_zero]

    letI := O.L.pointGroup (genPt p)
    have h : O.pts 0 * O.pts 0 = O.pts 0 := by
      change O.L.mul _ (O.pts 0) (O.pts 0) = O.pts 0
      rw [← O.pts_add, add_zero]
    exact mul_eq_left.mp h
  | succ n ih => rw [succ_nsmul, O.pts_add, ih, RelativeGroupLaw.nsmul_succ]

theorem nsmul_eq_one_of_extends (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) {m : ℕ} {x : JZero (N₀ * p)}
    (hx : m • x = 0) {s : SchemeHomOver Λ.σA O.g} (hs : (O.pts x).1 = barPt A ≫ s.1) :
    O.L.nsmul Λ.σA m s = O.L.one Λ.σA := by
  haveI : IsSeparated O.g := O.separated
  apply Subtype.ext
  refine AlgebraicGeometry.IsSeparated.eq_of_spec_map_subtype_comp_eq O.g A _ _ ?_ ?_
  · have hn := congrArg Subtype.val (O.L.nsmul_natural Λ.σA (genPt p) (barPt A) Λ.hσA m s)
    rw [GoodReductionJacobian.schemeHomOverComp_coe] at hn
    have hxs : GoodReductionJacobian.schemeHomOverComp (barPt A) Λ.hσA s = O.pts x := (Subtype.ext hs).symm
    change barPt A ≫ (O.L.nsmul Λ.σA m s).1 = barPt A ≫ (O.L.one Λ.σA).1
    rw [hn, hxs, ← pts_nsmul, hx]
    have h0 : O.pts 0 = O.L.one (genPt p) := by
      have := pts_nsmul O 0 x
      rwa [zero_nsmul, RelativeGroupLaw.nsmul_zero] at this
    rw [h0]
    exact (congrArg Subtype.val (O.L.one_natural Λ.σA (genPt p) (barPt A) Λ.hσA)).symm
  · rw [(O.L.nsmul Λ.σA m s).2, (O.L.one Λ.σA).2]

end ModularCurve.JZeroNeronObjectAtP
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw.FibIso"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw.FibIso"

namespace ModularCurve
p2m_export "ModularCurve" "JZeroNeronObjectAtP.LevelData JZeroNeronObjectAtP jZeroTorsion JZero instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable degeneracyPushforwardPair JZeroNeronObjectAtP.locallyQuasiFinite_schemeKerStr_kerPairLaw JZeroNeronObjectAtP.exists_isOpenImmersion_torus_kerPair_degeneracyHom"
namespace JZeroNeronObjectAtP
p2m_export "ModularCurve.JZeroNeronObjectAtP" "baseRing base genPt barPt resPt overId toFibrePt ofFibrePt fibreMap torusScheme torusStr LevelData abqFibre_eq_one_iff L G pts_add mk degeneracyHom quasiCompact torusFibre abqFibre degeneracyHom_mul g degeneracyHom_pts separated toricRank pts locallyOfFiniteType comm locallyQuasiFinite_schemeKerStr_kerPairLaw exists_isOpenImmersion_torus_kerPair_degeneracyHom"
p2m_open "ModularCurve.JZeroNeronObjectAtP ModularCurve"

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  {Λ : LevelData N₀ p A}

noncomputable abbrev toAPt {O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ} (s : SchemeHomOver Λ.σA O.g) :
    SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr Λ.σA O.g) :=
  RelativeGroupLaw.baseChangePointOfBase Λ.σA (overId s)

theorem toBase_toAPt {O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ} (s : SchemeHomOver Λ.σA O.g) :
    RelativeGroupLaw.baseChangePointToBase Λ.σA (toAPt s) = overId s :=
  RelativeGroupLaw.baseChangePointToBase_ofBase _ _

theorem overId_one {X : Scheme.{0}} {f : X ⟶ base p} (L : RelativeGroupLaw (baseRing p) f)
    (t : Spec (CommRingCat.of ↥A) ⟶ base p) :
    overId (L.one t) = L.one (𝟙 _ ≫ t) := by
  apply Subtype.ext
  change (L.one t).1 = (L.one (𝟙 _ ≫ t)).1
  rw [RelativeGroupLaw.one_coe_eq L t, RelativeGroupLaw.one_coe_eq L (𝟙 _ ≫ t), Category.id_comp]

theorem overId_eq_schemeHomOverComp {X : Scheme.{0}} {f : X ⟶ base p} {t : Spec (CommRingCat.of ↥A) ⟶ base p}
    (x : SchemeHomOver t f) :
    overId x = GoodReductionJacobian.schemeHomOverComp (𝟙 _) rfl x :=
  Subtype.ext (Category.id_comp _).symm

theorem toAPt_mem_kerA (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) {s : SchemeHomOver Λ.σA O.g}
    (hs : ∀ i, NeronModelInfra.schemeHomOverComp s (O.degeneracyHom i) = Λ.L.one Λ.σA) (i : Fin 2) :
    NeronModelInfra.schemeHomOverComp (toAPt s) (degA O i) = (Λ.L.baseChange Λ.σA).one (𝟙 _) := by
  apply (RelativeGroupLaw.baseChangePointEquiv Λ.σA (𝟙 _)).injective
  change RelativeGroupLaw.baseChangePointToBase Λ.σA _ = RelativeGroupLaw.baseChangePointToBase Λ.σA _
  rw [RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong, toBase_toAPt,
    RelativeGroupLaw.baseChangePointToBase_one, ← overId_one]

  have h : NeronModelInfra.schemeHomOverComp (overId s) (O.degeneracyHom i) =
      overId (NeronModelInfra.schemeHomOverComp s (O.degeneracyHom i)) := Subtype.ext rfl
  rw [h, hs i]

noncomputable def kerAPt (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (s : SchemeHomOver Λ.σA O.g)
    (hs : ∀ i, NeronModelInfra.schemeHomOverComp s (O.degeneracyHom i) = Λ.L.one Λ.σA) :
    SchemeHomOver (𝟙 _) (RelativeGroupLaw.kerPairStr (Λ.L.baseChange Λ.σA) (degA O)) :=
  (RelativeGroupLaw.kerPairPointEquiv _ _ (𝟙 _)).symm ⟨toAPt s, toAPt_mem_kerA O hs⟩

theorem baseChangePointToBase_nsmul' {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
    (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)) {f : X ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of R')) (n : ℕ)
    (x : SchemeHomOver t' (RelativeGroupLaw.baseChangeStr ι f)) :
    RelativeGroupLaw.baseChangePointToBase ι ((G.baseChange ι).nsmul t' n x) =
      G.nsmul _ n (RelativeGroupLaw.baseChangePointToBase ι x) := by
  induction n with
  | zero => rw [RelativeGroupLaw.nsmul_zero, RelativeGroupLaw.nsmul_zero, RelativeGroupLaw.baseChangePointToBase_one]
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ,
      RelativeGroupLaw.baseChangePointToBase_mul, ih]

theorem kerALaw_nsmul_kerAPt (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (s : SchemeHomOver Λ.σA O.g)
    (hs : ∀ i, NeronModelInfra.schemeHomOverComp s (O.degeneracyHom i) = Λ.L.one Λ.σA) {m : ℕ}
    (hm : O.L.nsmul Λ.σA m s = O.L.one Λ.σA) :
    (kerALaw O).nsmul (𝟙 _) m (kerAPt O s hs) = (kerALaw O).one (𝟙 _) := by
  apply (RelativeGroupLaw.kerPairPointEquiv (Λ.L.baseChange Λ.σA) (degA O) (𝟙 _)).injective
  apply Subtype.ext
  rw [RelativeGroupLaw.kerPairPointEquiv_nsmul, RelativeGroupLaw.kerPairPointEquiv_one, kerAPt, Equiv.apply_symm_apply]
  change (O.L.baseChange Λ.σA).nsmul (𝟙 _) m (toAPt s) = (O.L.baseChange Λ.σA).one (𝟙 _)
  apply (RelativeGroupLaw.baseChangePointEquiv Λ.σA (𝟙 _)).injective
  change RelativeGroupLaw.baseChangePointToBase Λ.σA _ = RelativeGroupLaw.baseChangePointToBase Λ.σA _
  rw [baseChangePointToBase_nsmul', toBase_toAPt, RelativeGroupLaw.baseChangePointToBase_one, ← overId_one,
    overId_eq_schemeHomOverComp, ← O.L.nsmul_natural Λ.σA (𝟙 _ ≫ Λ.σA) (𝟙 _) rfl m s, hm,
    ← overId_eq_schemeHomOverComp]

end ModularCurve.JZeroNeronObjectAtP
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw.FibIso"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw.FibIso"

namespace ModularCurve
p2m_export "ModularCurve" "JZeroNeronObjectAtP.LevelData JZeroNeronObjectAtP jZeroTorsion JZero instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable degeneracyPushforwardPair JZeroNeronObjectAtP.locallyQuasiFinite_schemeKerStr_kerPairLaw JZeroNeronObjectAtP.exists_isOpenImmersion_torus_kerPair_degeneracyHom"
namespace JZeroNeronObjectAtP
p2m_export "ModularCurve.JZeroNeronObjectAtP" "baseRing base genPt barPt resPt overId toFibrePt ofFibrePt fibreMap torusScheme torusStr LevelData abqFibre_eq_one_iff L G pts_add mk degeneracyHom quasiCompact torusFibre abqFibre degeneracyHom_mul g degeneracyHom_pts separated toricRank pts locallyOfFiniteType comm locallyQuasiFinite_schemeKerStr_kerPairLaw exists_isOpenImmersion_torus_kerPair_degeneracyHom"
p2m_open "ModularCurve.JZeroNeronObjectAtP ModularCurve"

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  {Λ : LevelData N₀ p A}

namespace LevelData p2m_export "ModularCurve.JZeroNeronObjectAtP.LevelData" "IsJacobian σA X L mk hσA f ptsSp pts" end LevelData
p2m_open_scoped "ModularCurve.JZeroNeronObjectAtP.LevelData" in

theorem LevelData.pts_zero (hΛ : Λ.IsJacobian) : Λ.pts 0 = Λ.L.one (genPt p) := by
  letI := Λ.L.pointGroup (genPt p)
  have hadd := hΛ.2.2.1
  have h : Λ.pts 0 * Λ.pts 0 = Λ.pts 0 := by
    change Λ.L.mul _ (Λ.pts 0) (Λ.pts 0) = Λ.pts 0
    rw [← hadd, add_zero]
  exact mul_eq_left.mp h

theorem schemeHomOverComp_degeneracyHom_eq_one (hΛ : Λ.IsJacobian) (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
    (i : Fin 2) {x : JZero (N₀ * p)} {s : SchemeHomOver Λ.σA O.g} (hs : (O.pts x).1 = barPt A ≫ s.1)
    (hx : degeneracyPushforwardPair N₀ p i x = 0) :
    NeronModelInfra.schemeHomOverComp s (O.degeneracyHom i) = Λ.L.one Λ.σA := by
  haveI : IsSeparated Λ.f := hΛ.1.proper.toIsSeparated
  apply Subtype.ext
  refine AlgebraicGeometry.IsSeparated.eq_of_spec_map_subtype_comp_eq Λ.f A _ _ ?_ ?_
  ·
    change barPt A ≫ (s.1 ≫ (O.degeneracyHom i).1) = barPt A ≫ (Λ.L.one Λ.σA).1
    rw [← Category.assoc, ← hs, ← O.degeneracyHom_pts i x, hx, LevelData.pts_zero hΛ]
    exact (congrArg Subtype.val (Λ.L.one_natural Λ.σA (genPt p) (barPt A) Λ.hσA)).symm
  · rw [(NeronModelInfra.schemeHomOverComp s (O.degeneracyHom i)).2, (Λ.L.one Λ.σA).2]

end ModularCurve.JZeroNeronObjectAtP
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw.FibIso"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw.FibIso"

namespace ModularCurve
p2m_export "ModularCurve" "JZeroNeronObjectAtP.LevelData JZeroNeronObjectAtP jZeroTorsion JZero instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable degeneracyPushforwardPair JZeroNeronObjectAtP.locallyQuasiFinite_schemeKerStr_kerPairLaw JZeroNeronObjectAtP.exists_isOpenImmersion_torus_kerPair_degeneracyHom"
namespace JZeroNeronObjectAtP
p2m_export "ModularCurve.JZeroNeronObjectAtP" "baseRing base genPt barPt resPt overId toFibrePt ofFibrePt fibreMap torusScheme torusStr LevelData abqFibre_eq_one_iff L G pts_add mk degeneracyHom quasiCompact torusFibre abqFibre degeneracyHom_mul g degeneracyHom_pts separated toricRank pts locallyOfFiniteType comm locallyQuasiFinite_schemeKerStr_kerPairLaw exists_isOpenImmersion_torus_kerPair_degeneracyHom"
p2m_open "ModularCurve.JZeroNeronObjectAtP ModularCurve"

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  {Λ : LevelData N₀ p A}

theorem kerAPt_coe_comp (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (s : SchemeHomOver Λ.σA O.g)
    (hs : ∀ i, NeronModelInfra.schemeHomOverComp s (O.degeneracyHom i) = Λ.L.one Λ.σA) :
    (kerAPt O s hs).1 ≫ RelativeGroupLaw.kerPairι (Λ.L.baseChange Λ.σA) (degA O) ≫ pullback.fst O.g Λ.σA = s.1 := by
  rw [← Category.assoc, kerAPt, RelativeGroupLaw.kerPairPointEquiv_symm_apply_coe]
  change (toAPt s).1 ≫ pullback.fst O.g Λ.σA = s.1
  exact congrArg Subtype.val (toBase_toAPt s)

end ModularCurve.JZeroNeronObjectAtP
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw.FibIso"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw.FibIso"

namespace ModularCurve
p2m_export "ModularCurve" "JZeroNeronObjectAtP.LevelData JZeroNeronObjectAtP jZeroTorsion JZero instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable degeneracyPushforwardPair JZeroNeronObjectAtP.locallyQuasiFinite_schemeKerStr_kerPairLaw JZeroNeronObjectAtP.exists_isOpenImmersion_torus_kerPair_degeneracyHom"
namespace JZeroNeronObjectAtP
p2m_export "ModularCurve.JZeroNeronObjectAtP" "baseRing base genPt barPt resPt overId toFibrePt ofFibrePt fibreMap torusScheme torusStr LevelData abqFibre_eq_one_iff L G pts_add mk degeneracyHom quasiCompact torusFibre abqFibre degeneracyHom_mul g degeneracyHom_pts separated toricRank pts locallyOfFiniteType comm locallyQuasiFinite_schemeKerStr_kerPairLaw exists_isOpenImmersion_torus_kerPair_degeneracyHom"
p2m_open "ModularCurve.JZeroNeronObjectAtP ModularCurve"

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  {Λ : LevelData N₀ p A}

p2m_open_scoped "ModularCurve.JZeroNeronObjectAtP.LevelData" in

theorem LevelData.ptsSp_zero (hΛ : Λ.IsJacobian) : Λ.ptsSp 0 = Λ.L.one (resPt A ≫ Λ.σA) := by
  letI := Λ.L.pointGroup (resPt A ≫ Λ.σA)
  have hadd := hΛ.2.2.2.2.1
  have h : Λ.ptsSp 0 * Λ.ptsSp 0 = Λ.ptsSp 0 := by
    change Λ.L.mul _ (Λ.ptsSp 0) (Λ.ptsSp 0) = Λ.ptsSp 0
    rw [← hadd, add_zero]
  exact mul_eq_left.mp h

end ModularCurve.JZeroNeronObjectAtP
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw.FibIso"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw.FibIso"

namespace ModularCurve
p2m_export "ModularCurve" "JZeroNeronObjectAtP.LevelData JZeroNeronObjectAtP jZeroTorsion JZero instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable degeneracyPushforwardPair JZeroNeronObjectAtP.locallyQuasiFinite_schemeKerStr_kerPairLaw JZeroNeronObjectAtP.exists_isOpenImmersion_torus_kerPair_degeneracyHom"
namespace JZeroNeronObjectAtP
p2m_export "ModularCurve.JZeroNeronObjectAtP" "baseRing base genPt barPt resPt overId toFibrePt ofFibrePt fibreMap torusScheme torusStr LevelData abqFibre_eq_one_iff L G pts_add mk degeneracyHom quasiCompact torusFibre abqFibre degeneracyHom_mul g degeneracyHom_pts separated toricRank pts locallyOfFiniteType comm locallyQuasiFinite_schemeKerStr_kerPairLaw exists_isOpenImmersion_torus_kerPair_degeneracyHom"
p2m_open "ModularCurve.JZeroNeronObjectAtP ModularCurve"

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  {Λ : LevelData N₀ p A}

theorem kerATorsStr_locallyOfFiniteType (hΛ : Fact Λ.IsJacobian) (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) :
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
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw.FibIso P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.ModularCurve.JZeroNeronObjectAtP"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw.FibIso P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "JZeroNeronObjectAtP.LevelData JZeroNeronObjectAtP jZeroTorsion JZero instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable degeneracyPushforwardPair JZeroNeronObjectAtP.locallyQuasiFinite_schemeKerStr_kerPairLaw JZeroNeronObjectAtP.exists_isOpenImmersion_torus_kerPair_degeneracyHom"
namespace JZeroNeronObjectAtP
p2m_export "ModularCurve.JZeroNeronObjectAtP" "baseRing base genPt barPt resPt overId toFibrePt ofFibrePt fibreMap torusScheme torusStr LevelData abqFibre_eq_one_iff L G pts_add mk degeneracyHom quasiCompact torusFibre abqFibre degeneracyHom_mul g degeneracyHom_pts separated toricRank pts locallyOfFiniteType comm locallyQuasiFinite_schemeKerStr_kerPairLaw exists_isOpenImmersion_torus_kerPair_degeneracyHom"
p2m_open "ModularCurve.JZeroNeronObjectAtP ModularCurve"

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  {Λ : LevelData N₀ p A}

theorem kerATorsStr_isSeparated (hΛ : Fact Λ.IsJacobian) (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) :
    IsSeparated (kerATorsStr O m) := by
  haveI : IsSeparated Λ.f := hΛ.out.1.proper.toIsSeparated
  haveI : IsSeparated O.g := O.separated
  haveI : IsSeparated ((kerALaw O).schemeNsmul m ≫ RelativeGroupLaw.kerPairStr (Λ.L.baseChange Λ.σA) (degA O)) := by
    rw [RelativeGroupLaw.schemeNsmul_over]; infer_instance
  haveI : IsSeparated ((kerALaw O).schemeNsmul m) := IsSeparated.of_comp ((kerALaw O).schemeNsmul m)
    (RelativeGroupLaw.kerPairStr (Λ.L.baseChange Λ.σA) (degA O))
  infer_instance

theorem kerATorsStr_quasiCompact (hΛ : Fact Λ.IsJacobian) (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) :
    QuasiCompact (kerATorsStr O m) := by
  haveI : IsSeparated Λ.f := hΛ.out.1.proper.toIsSeparated
  haveI : IsSeparated O.g := O.separated
  haveI : QuasiCompact O.g := O.quasiCompact
  haveI : QuasiCompact ((kerALaw O).schemeNsmul m ≫ RelativeGroupLaw.kerPairStr (Λ.L.baseChange Λ.σA) (degA O)) := by
    rw [RelativeGroupLaw.schemeNsmul_over]; infer_instance
  haveI : QuasiCompact ((kerALaw O).schemeNsmul m) := QuasiCompact.of_comp ((kerALaw O).schemeNsmul m)
    (RelativeGroupLaw.kerPairStr (Λ.L.baseChange Λ.σA) (degA O))
  infer_instance

end ModularCurve.JZeroNeronObjectAtP
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw.FibIso P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.ModularCurve.JZeroNeronObjectAtP"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw.FibIso P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.ModularCurve.JZeroNeronObjectAtP"

namespace TRIV

section Fibre

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  {Λ : JZeroNeronObjectAtP.LevelData N₀ p A} (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)

noncomputable abbrev Lκ : RelativeGroupLaw (ResidueField ↥A) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g) :=
  O.L.baseChange (resPt A ≫ Λ.σA)

noncomputable abbrev dκ (i : Fin 2) :
    SchemeHomOver (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g)
      (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) Λ.f) :=
  NeronSpecialFibreInfra.fibreRestrictAlong (resPt A ≫ Λ.σA) Λ.f O.g (O.degeneracyHom i)

theorem dκ_isHom (i : Fin 2) : RelativeGroupLaw.IsHom (Lκ O) (Λ.L.baseChange (resPt A ≫ Λ.σA)) (dκ O i) :=
  RelativeGroupLaw.IsHom.fibreRestrictAlong (resPt A ≫ Λ.σA) (fun t x y => O.degeneracyHom_mul i t x y)

noncomputable abbrev Hκ : Scheme.{0} := RelativeGroupLaw.kerPair (Λ.L.baseChange (resPt A ≫ Λ.σA)) (dκ O)

noncomputable abbrev HκStr : Hκ O ⟶ Spec (CommRingCat.of (ResidueField ↥A)) :=
  RelativeGroupLaw.kerPairStr (Λ.L.baseChange (resPt A ≫ Λ.σA)) (dκ O)

noncomputable abbrev LH : RelativeGroupLaw (ResidueField ↥A) (HκStr O) :=
  RelativeGroupLaw.kerPairLaw (Lκ O) (Λ.L.baseChange (resPt A ≫ Λ.σA)) (dκ O) (dκ_isHom O)

end Fibre
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw.FibIso P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.ModularCurve.JZeroNeronObjectAtP"

end TRIV
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw.FibIso P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.ModularCurve.JZeroNeronObjectAtP"

namespace ModularCurve
p2m_export "ModularCurve" "JZeroNeronObjectAtP.LevelData JZeroNeronObjectAtP jZeroTorsion JZero instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable degeneracyPushforwardPair JZeroNeronObjectAtP.locallyQuasiFinite_schemeKerStr_kerPairLaw JZeroNeronObjectAtP.exists_isOpenImmersion_torus_kerPair_degeneracyHom"
namespace JZeroNeronObjectAtP
p2m_export "ModularCurve.JZeroNeronObjectAtP" "baseRing base genPt barPt resPt overId toFibrePt ofFibrePt fibreMap torusScheme torusStr LevelData abqFibre_eq_one_iff L G pts_add mk degeneracyHom quasiCompact torusFibre abqFibre degeneracyHom_mul g degeneracyHom_pts separated toricRank pts locallyOfFiniteType comm locallyQuasiFinite_schemeKerStr_kerPairLaw exists_isOpenImmersion_torus_kerPair_degeneracyHom"
p2m_open "ModularCurve.JZeroNeronObjectAtP ModularCurve"

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  {Λ : LevelData N₀ p A}

theorem ofFibrePt_injective' {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
    {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} {f : X ⟶ Spec (CommRingCat.of R)} :
    Function.Injective (ofFibrePt (ι := ι) (f := f)) := by
  intro y y' h
  have h1 : (RelativeGroupLaw.baseChangePointToBase ι y).1 = (RelativeGroupLaw.baseChangePointToBase ι y').1 :=
    congrArg Subtype.val h
  exact (RelativeGroupLaw.baseChangePointEquiv ι (𝟙 _)).injective (Subtype.ext h1)

theorem toFibrePt_ofFibrePt' {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
    {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} {f : X ⟶ Spec (CommRingCat.of R)}
    (y : SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr ι f)) : toFibrePt (ofFibrePt y) = y := by
  change RelativeGroupLaw.baseChangePointOfBase ι _ = y
  have h : overId (ofFibrePt y) = RelativeGroupLaw.baseChangePointToBase ι y := Subtype.ext rfl
  rw [h, RelativeGroupLaw.baseChangePointOfBase_toBase]

theorem exists_torusPt_of_ptsSp_symm_eq_zero (hΛ : Λ.IsJacobian) (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
    (y : SchemeHomOver (resPt A ≫ Λ.σA) O.g)
    (h0 : Λ.ptsSp.symm (fibreMap (O.abqFibre 0) y) = 0) (h1 : Λ.ptsSp.symm (fibreMap (O.abqFibre 1) y) = 0) :
    ∃ τ : SchemeHomOver (𝟙 _) (torusStr (ResidueField ↥A) O.toricRank),
      τ.1 ≫ O.torusFibre.1 = (toFibrePt y).1 := by
  have hone : ofFibrePt ((Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 (Spec (CommRingCat.of (ResidueField ↥A))))) =
      Λ.L.one (resPt A ≫ Λ.σA) := by
    apply Subtype.ext
    change (RelativeGroupLaw.baseChangePointToBase (resPt A ≫ Λ.σA)
      ((Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _))).1 = _
    rw [RelativeGroupLaw.baseChangePointToBase_one, RelativeGroupLaw.one_coe_eq Λ.L (𝟙 _ ≫ (resPt A ≫ Λ.σA)),
      RelativeGroupLaw.one_coe_eq Λ.L (resPt A ≫ Λ.σA), Category.id_comp]
  have e0 : fibreMap (O.abqFibre 0) y = Λ.L.one (resPt A ≫ Λ.σA) := by
    have h := congrArg Λ.ptsSp h0
    rwa [Equiv.apply_symm_apply, LevelData.ptsSp_zero hΛ] at h
  have e1 : fibreMap (O.abqFibre 1) y = Λ.L.one (resPt A ≫ Λ.σA) := by
    have h := congrArg Λ.ptsSp h1
    rwa [Equiv.apply_symm_apply, LevelData.ptsSp_zero hΛ] at h
  have hz : ∀ i, fibreMap (O.abqFibre i) y = Λ.L.one (resPt A ≫ Λ.σA) := Fin.forall_fin_two.mpr ⟨e0, e1⟩
  have hu : ∀ i, NeronModelInfra.schemeHomOverComp (toFibrePt y) (O.abqFibre i) =
      (Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _) := by
    intro i
    apply ofFibrePt_injective'
    rw [hone]
    have : fibreMap (O.abqFibre i) y = ofFibrePt (NeronModelInfra.schemeHomOverComp (toFibrePt y) (O.abqFibre i)) := rfl
    rw [← this, hz i]
  obtain ⟨τ, hτ⟩ := (O.abqFibre_eq_one_iff (𝟙 _) (toFibrePt y)).mp hu
  exact ⟨τ, by rw [← hτ, NeronModelInfra.schemeHomOverComp_coe]⟩

end ModularCurve.JZeroNeronObjectAtP
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw.FibIso P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.ModularCurve.JZeroNeronObjectAtP"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw.FibIso P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.ModularCurve.JZeroNeronObjectAtP"

namespace ModularCurve
p2m_export "ModularCurve" "JZeroNeronObjectAtP.LevelData JZeroNeronObjectAtP jZeroTorsion JZero instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable degeneracyPushforwardPair JZeroNeronObjectAtP.locallyQuasiFinite_schemeKerStr_kerPairLaw JZeroNeronObjectAtP.exists_isOpenImmersion_torus_kerPair_degeneracyHom"
namespace JZeroNeronObjectAtP
p2m_export "ModularCurve.JZeroNeronObjectAtP" "baseRing base genPt barPt resPt overId toFibrePt ofFibrePt fibreMap torusScheme torusStr LevelData abqFibre_eq_one_iff L G pts_add mk degeneracyHom quasiCompact torusFibre abqFibre degeneracyHom_mul g degeneracyHom_pts separated toricRank pts locallyOfFiniteType comm locallyQuasiFinite_schemeKerStr_kerPairLaw exists_isOpenImmersion_torus_kerPair_degeneracyHom"
p2m_open "ModularCurve.JZeroNeronObjectAtP ModularCurve"

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  {Λ : LevelData N₀ p A}

theorem closedPoint_mem_image_of_torus (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ)
    (ι : torusScheme (ResidueField ↥A) O.toricRank ⟶ TRIV.Hκ O) [IsOpenImmersion ι]
    (hι1 : ι ≫ RelativeGroupLaw.kerPairι (Λ.L.baseChange (resPt A ≫ Λ.σA)) (TRIV.dκ O) = O.torusFibre.1)
    (π : (TRIV.LH O).schemeKer m ⟶ (kerALaw O).schemeKer m)
    (hπ : IsPullback π ((TRIV.LH O).schemeKerStr m) (kerATorsStr O m) (resPt A))
    (hπX : π ≫ pullback.fst ((kerALaw O).schemeNsmul m) ((kerALaw O).one (𝟙 _)).1 ≫
        RelativeGroupLaw.kerPairι (Λ.L.baseChange Λ.σA) (degA O) ≫ pullback.fst O.g Λ.σA =
      pullback.fst ((TRIV.LH O).schemeNsmul m) ((TRIV.LH O).one (𝟙 _)).1 ≫
        RelativeGroupLaw.kerPairι (Λ.L.baseChange (resPt A ≫ Λ.σA)) (TRIV.dκ O) ≫ pullback.fst O.g (resPt A ≫ Λ.σA))
    (s : SchemeHomOver Λ.σA O.g)
    (hsK : ∀ i, NeronModelInfra.schemeHomOverComp s (O.degeneracyHom i) = Λ.L.one Λ.σA)
    (hsm : O.L.nsmul Λ.σA m s = O.L.one Λ.σA)
    (τ : SchemeHomOver (𝟙 _) (torusStr (ResidueField ↥A) O.toricRank))
    (hτ : τ.1 ≫ O.torusFibre.1 = (toFibrePt (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s)).1) :
    ((kerALaw O).schemeKerLift m (kerAPt O s hsK) (kerALaw_nsmul_kerAPt O s hsK hsm)).1.base
        (IsLocalRing.closedPoint ↥A) ∈
      π.base '' ((pullback.fst ((TRIV.LH O).schemeNsmul m) ((TRIV.LH O).one (𝟙 _)).1) ⁻¹ᵁ
        (Scheme.Hom.opensRange ι) : Set ((TRIV.LH O).schemeKer m)) := by

  let LA := kerALaw O
  let Lκ' := TRIV.LH O
  let σ : SchemeHomOver (𝟙 _) (kerATorsStr O m) :=
    (kerALaw O).schemeKerLift m (kerAPt O s hsK) (kerALaw_nsmul_kerAPt O s hsK hsm)
  let jκ : (TRIV.LH O).schemeKer m ⟶ TRIV.Hκ O := pullback.fst ((TRIV.LH O).schemeNsmul m) ((TRIV.LH O).one (𝟙 _)).1
  let pt : Spec (CommRingCat.of (ResidueField ↥A)) := IsLocalRing.closedPoint (ResidueField ↥A)

  have comm : (resPt A ≫ σ.1) ≫ kerATorsStr O m = 𝟙 _ ≫ resPt A := by
    rw [Category.assoc, Category.id_comp]
    exact (congrArg (resPt A ≫ ·) σ.2).trans (Category.comp_id _)
  let y : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (TRIV.LH O).schemeKer m := hπ.lift (resPt A ≫ σ.1) (𝟙 _) comm
  have hyπ : y ≫ π = resPt A ≫ σ.1 := hπ.lift_fst _ _ _
  have hys : y ≫ (TRIV.LH O).schemeKerStr m = 𝟙 _ := hπ.lift_snd _ _ _

  have key : y ≫ jκ = τ.1 ≫ ι := by
    apply RelativeGroupLaw.FibIso.kerPair_hom_ext
    apply pullback.hom_ext
    · have h1 : (y ≫ jκ) ≫ RelativeGroupLaw.kerPairι _ _ ≫ pullback.fst O.g (resPt A ≫ Λ.σA) = resPt A ≫ s.1 := by
        rw [Category.assoc, ← hπX, ← Category.assoc, hyπ, Category.assoc, ← Category.assoc σ.1,
          RelativeGroupLaw.schemeKerLift_fst, kerAPt_coe_comp]
      have h2 : (τ.1 ≫ ι) ≫ RelativeGroupLaw.kerPairι _ _ ≫ pullback.fst O.g (resPt A ≫ Λ.σA) = resPt A ≫ s.1 := by
        rw [Category.assoc, ← Category.assoc ι, hι1, ← Category.assoc, hτ]
        exact pullback.lift_fst _ _ _
      simp only [Category.assoc] at h1 h2 ⊢
      rw [h1, h2]
    · have h1 : (y ≫ jκ) ≫ RelativeGroupLaw.kerPairι _ _ ≫ pullback.snd O.g (resPt A ≫ Λ.σA) = 𝟙 _ := by
        have h := RelativeGroupLaw.FibIso.schemeKer_fst_comp (TRIV.LH O) m y
        simp only [Category.assoc] at h ⊢
        exact h.trans hys
      have h2 : (τ.1 ≫ ι) ≫ RelativeGroupLaw.kerPairι _ _ ≫ pullback.snd O.g (resPt A ≫ Λ.σA) = 𝟙 _ := by
        rw [Category.assoc, ← Category.assoc ι, hι1, O.torusFibre.2]
        exact τ.2
      simp only [Category.assoc] at h1 h2 ⊢
      rw [h1, h2]

  have hcp : (IsLocalRing.closedPoint ↥A : Spec (CommRingCat.of ↥A)) = (resPt A).base pt :=
    (PrimeSpectrum.comap_residue (↥A) pt).symm
  refine ⟨y.base pt, ?_, ?_⟩
  · show (y.base ≫ jκ.base) pt ∈ Set.range ι.base
    rw [← Scheme.Hom.comp_base, key, Scheme.Hom.comp_base]
    exact ⟨τ.1.base pt, rfl⟩
  · show (y.base ≫ π.base) pt = _
    rw [hcp, ← Scheme.Hom.comp_base, hyπ, Scheme.Hom.comp_base]
    rfl

end ModularCurve.JZeroNeronObjectAtP
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw.FibIso P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.ModularCurve.JZeroNeronObjectAtP"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.GoodReductionJacobian.RelativeGroupLaw.FibIso P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.ModularCurve.JZeroNeronObjectAtP"

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) (hm : 0 < m) :
    {x : JZero (N₀ * p) | x ∈ jZeroTorsion (N₀ * p) m ∧
      (∃ s : SchemeHomOver Λ.σA O.g, (O.pts x).1 = barPt A ≫ s.1 ∧
        Λ.ptsSp.symm (fibreMap (O.abqFibre 0) (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s)) = 0 ∧
        Λ.ptsSp.symm (fibreMap (O.abqFibre 1) (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s)) = 0) ∧
      degeneracyPushforwardPair N₀ p 0 x = 0 ∧ degeneracyPushforwardPair N₀ p 1 x = 0}.Finite ∧
    Nat.card {x : JZero (N₀ * p) | x ∈ jZeroTorsion (N₀ * p) m ∧
      (∃ s : SchemeHomOver Λ.σA O.g, (O.pts x).1 = barPt A ≫ s.1 ∧
        Λ.ptsSp.symm (fibreMap (O.abqFibre 0) (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s)) = 0 ∧
        Λ.ptsSp.symm (fibreMap (O.abqFibre 1) (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s)) = 0) ∧
      degeneracyPushforwardPair N₀ p 0 x = 0 ∧ degeneracyPushforwardPair N₀ p 1 x = 0} ≤ m ^ O.toricRank := by
  classical
  haveI hΛ' : Fact Λ.IsJacobian := ⟨hΛ⟩
  haveI : HenselianLocalRing ↥A := ValuationSubring.henselianLocalRing_of_isAlgClosed A
  haveI : LocallyOfFiniteType (kerATorsStr O m) :=
    ModularCurve.JZeroNeronObjectAtP.kerATorsStr_locallyOfFiniteType hΛ' O m
  haveI : IsSeparated (kerATorsStr O m) := ModularCurve.JZeroNeronObjectAtP.kerATorsStr_isSeparated hΛ' O m
  haveI : QuasiCompact (kerATorsStr O m) := ModularCurve.JZeroNeronObjectAtP.kerATorsStr_quasiCompact hΛ' O m
  haveI : LocallyQuasiFinite (kerATorsStr O m) :=
    ModularCurve.JZeroNeronObjectAtP.locallyQuasiFinite_schemeKerStr_kerPairLaw N₀ p hpN₀ A hA Λ hΛ O m hm

  obtain ⟨ι, hι1, hιopen, hιn⟩ :=
    ModularCurve.JZeroNeronObjectAtP.exists_isOpenImmersion_torus_kerPair_degeneracyHom N₀ p hpN₀ A hA Λ hΛ O
  change torusScheme (ResidueField ↥A) O.toricRank ⟶ TRIV.Hκ O at ι
  haveI : IsOpenImmersion ι := hιopen
  have hιn' : ∀ n : ℕ, ι ≫ (TRIV.LH O).schemeNsmul n =
      Spec.map (CommRingCat.ofHom
        (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) (n • AddMonoidHom.id (Fin O.toricRank → ℤ)))) ≫ ι :=
    hιn
  have hιf : ι ≫ TRIV.HκStr O = torusStr (ResidueField ↥A) O.toricRank := by
    change ι ≫ (RelativeGroupLaw.kerPairι _ _ ≫ _) = _
    rw [← Category.assoc, hι1]
    exact O.torusFibre.2

  obtain ⟨π, hπ, hπX⟩ := GoodReductionJacobian.RelativeGroupLaw.FibIso.main' Λ.σA (resPt A) O.L Λ.L O.degeneracyHom
    (fun i => by intro T t x y; exact O.degeneracyHom_mul i t x y) m
  change (TRIV.LH O).schemeKer m ⟶ (kerALaw O).schemeKer m at π
  have hπ' : IsPullback π ((TRIV.LH O).schemeKerStr m) (kerATorsStr O m) (resPt A) := hπ
  have hπX' : π ≫ pullback.fst ((kerALaw O).schemeNsmul m) ((kerALaw O).one (𝟙 _)).1 ≫
        RelativeGroupLaw.kerPairι (Λ.L.baseChange Λ.σA) (degA O) ≫ pullback.fst O.g Λ.σA =
      pullback.fst ((TRIV.LH O).schemeNsmul m) ((TRIV.LH O).one (𝟙 _)).1 ≫
        RelativeGroupLaw.kerPairι (Λ.L.baseChange (resPt A ≫ Λ.σA)) (TRIV.dκ O) ≫ pullback.fst O.g (resPt A ≫ Λ.σA) :=
    hπX

  let V : ((TRIV.LH O).schemeKer m).Opens :=
    (pullback.fst ((TRIV.LH O).schemeNsmul m) ((TRIV.LH O).one (𝟙 _)).1) ⁻¹ᵁ (Scheme.Hom.opensRange ι)
  obtain ⟨hVfin, hVrank⟩ :=
    AlgebraicGeometry.SplitTorus.moduleFinite_and_finrank_sections_preimage_opensRange_schemeKer_eq_pow
      O.toricRank (TRIV.HκStr O) (TRIV.LH O) ι hιf hιn' m hm

  obtain ⟨hfinT, hcardT⟩ :=
    AlgebraicGeometry.finite_and_natCard_sections_closedPoint_mem_le_of_finrank_opens_le
      (kerATorsStr O m) ((TRIV.LH O).schemeKerStr m) π hπ' V (m ^ O.toricRank) ⟨hVfin, hVrank.le⟩

  set S := {x : JZero (N₀ * p) | x ∈ jZeroTorsion (N₀ * p) m ∧
      (∃ s : SchemeHomOver Λ.σA O.g, (O.pts x).1 = barPt A ≫ s.1 ∧
        Λ.ptsSp.symm (fibreMap (O.abqFibre 0) (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s)) = 0 ∧
        Λ.ptsSp.symm (fibreMap (O.abqFibre 1) (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s)) = 0) ∧
      degeneracyPushforwardPair N₀ p 0 x = 0 ∧ degeneracyPushforwardPair N₀ p 1 x = 0} with hSdef
  have hex : ∀ x : S, ∃ s : SchemeHomOver Λ.σA O.g, (O.pts x.1).1 = barPt A ≫ s.1 ∧
      Λ.ptsSp.symm (fibreMap (O.abqFibre 0) (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s)) = 0 ∧
      Λ.ptsSp.symm (fibreMap (O.abqFibre 1) (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s)) = 0 :=
    fun x => x.2.2.1
  choose s hs hν0 hν1 using hex
  have hsK : ∀ (x : S) (i : Fin 2), NeronModelInfra.schemeHomOverComp (s x) (O.degeneracyHom i) = Λ.L.one Λ.σA := by
    intro x i
    fin_cases i
    · exact schemeHomOverComp_degeneracyHom_eq_one hΛ O 0 (hs x) x.2.2.2.1
    · exact schemeHomOverComp_degeneracyHom_eq_one hΛ O 1 (hs x) x.2.2.2.2
  have hsm : ∀ x : S, O.L.nsmul Λ.σA m (s x) = O.L.one Λ.σA := fun x =>
    nsmul_eq_one_of_extends O (by
      have h := x.2.1
      simpa [jZeroTorsion] using h) (hs x)
  have hτ : ∀ x : S, ∃ τ : SchemeHomOver (𝟙 _) (torusStr (ResidueField ↥A) O.toricRank),
      τ.1 ≫ O.torusFibre.1 = (toFibrePt (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl (s x))).1 :=
    fun x => exists_torusPt_of_ptsSp_symm_eq_zero hΛ O _ (hν0 x) (hν1 x)
  choose τ hτ using hτ
  let Φ : S → {σ : Spec (.of ↥A) ⟶ (kerALaw O).schemeKer m // σ ≫ kerATorsStr O m = 𝟙 _ ∧
      σ.base (IsLocalRing.closedPoint ↥A) ∈ π.base '' (V : Set ((TRIV.LH O).schemeKer m))} := fun x =>
    ⟨((kerALaw O).schemeKerLift m (kerAPt O (s x) (hsK x)) (kerALaw_nsmul_kerAPt O (s x) (hsK x) (hsm x))).1,
      ((kerALaw O).schemeKerLift m _ _).2,
      closedPoint_mem_image_of_torus O m ι hι1 π hπ' hπX' (s x) (hsK x) (hsm x) (τ x) (hτ x)⟩
  have hΦ : Function.Injective Φ := by
    intro x y hxy
    have h1 : (kerAPt O (s x) (hsK x)).1 = (kerAPt O (s y) (hsK y)).1 := by
      have := congrArg (fun σ => σ.1 ≫ pullback.fst _ _) hxy
      dsimp only [Φ] at this
      simpa only [RelativeGroupLaw.schemeKerLift_fst] using this
    have h2 : (s x).1 = (s y).1 := by
      rw [← kerAPt_coe_comp O (s x) (hsK x), ← kerAPt_coe_comp O (s y) (hsK y), h1]
    have h3 : O.pts x.1 = O.pts y.1 := Subtype.ext (by rw [hs x, hs y, h2])
    exact Subtype.ext (O.pts.injective h3)
  haveI := hfinT
  refine ⟨Set.finite_coe_iff.mp (Finite.of_injective Φ hΦ), ?_⟩
  exact (Nat.card_le_card_of_injective Φ hΦ).trans hcardT

end S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero (solution)
