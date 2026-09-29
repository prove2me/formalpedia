-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.finite_and_card_le_of_kernel_coset_representatives
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/8714066b-2b8b-5ee8-8deb-007f9b287f72

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_ToricDescentData
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKerPair
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_AlgebraicGeometry_IsSeparated_eq_of_spec_map_subtype_comp_eq
import Theorems.Thm_AlgebraicGeometry_ext_of_forall_geometricPoint_comp_eq_of_flat
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_ValuationSubring_henselianLocalRing_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_exists_isFinite_isOpenImmersion_disjoint_cover_of_locallyQuasiFinite_of_henselianLocalRing
import Theorems.Thm_AlgebraicGeometry_exists_section_comp_eq_iff_factors_of_universallyClosed_of_valuationRing
import Theorems.Thm_AlgebraicGeometry_finite_and_natCard_le_finrank_tensorProduct_sections_of_isFinite
import Theorems.Thm_AlgebraicGeometry_finrank_sections_eq_finrank_tensorProduct_of_isPullback_residue_of_isFinite
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isPullback_schemeKer_kerPairLaw_baseChange
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_schemeKerStr_kerPairLaw
import Theorems.Thm_AlgebraicGeometry_finite_and_natCard_sections_le_of_finrank_specialFibre_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives
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

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.GoodReductionJacobian ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.ModularCurve IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.ModularCurve.JZeroNeronObjectAtP NeronSpecialFibreInfra"

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.nsmul_zero RelativeGroupLaw.nsmul_succ RelativeGroupLaw.schemeNsmul_over RelativeGroupLaw.baseChangeStr RelativeGroupLaw.baseChangePointToBase RelativeGroupLaw.baseChangePointOfBase RelativeGroupLaw.baseChangePointToBase_ofBase RelativeGroupLaw.baseChangePointOfBase_toBase RelativeGroupLaw.baseChangePointEquiv RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong RelativeGroupLaw.baseChangePointToBase_mul RelativeGroupLaw.baseChangePointToBase_one RelativeGroupLaw.IsHom RelativeGroupLaw.IsHom.fibreRestrictAlong RelativeGroupLaw.kerPair RelativeGroupLaw.kerPairι RelativeGroupLaw.kerPairStr RelativeGroupLaw.one_coe_eq RelativeGroupLaw.kerPairPointEquiv RelativeGroupLaw.kerPairPointEquiv_symm_apply_coe RelativeGroupLaw.kerPairLaw RelativeGroupLaw.kerPairPointEquiv_one RelativeGroupLaw.kerPairPointEquiv_nsmul RelativeGroupLaw.exists_isPullback_schemeKer_kerPairLaw_baseChange"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "pointGroup one_natural one inv mul nsmul nsmul_zero nsmul_succ nsmul_natural idPoint schemeNsmul schemeNsmul_over schemeKer schemeKerStr baseChangeStr baseChangePointToBase baseChangePointOfBase baseChangePointToBase_ofBase baseChangePointOfBase_toBase baseChangePointEquiv baseChangePointToBase_comp_fibreRestrictAlong baseChange baseChangePointToBase_mul baseChangePointToBase_one fibre IsHom IsHom.fibreRestrictAlong kerPair kerPairι kerPairStr one_coe_eq kerPairPointEquiv kerPairPointEquiv_symm_apply_coe kerPairLaw kerPairPointEquiv_one kerPairPointEquiv_nsmul exists_isPullback_schemeKer_kerPairLaw_baseChange"
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
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.GoodReductionJacobian.RelativeGroupLaw"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.GoodReductionJacobian"

namespace ModularCurve
p2m_export "ModularCurve" "JZeroNeronObjectAtP.LevelData JZeroNeronObjectAtP jZeroTorsion JZero instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable degeneracyPushforwardPair JZeroNeronObjectAtP.isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le JZeroNeronObjectAtP.locallyQuasiFinite_schemeKerStr_kerPairLaw"
namespace JZeroNeronObjectAtP
p2m_export "ModularCurve.JZeroNeronObjectAtP" "baseRing base genPt barPt resPt overId toFibrePt ofFibrePt fibreMap torusCoord torusStr torusPt ExtendsToPlace LevelData abqFibre_eq_one_iff L G pts_add degeneracyHom quasiCompact torusFibre abqFibre comp degeneracyHom_mul g degeneracyHom_pts frobSp separated toricRank degeneracyHom_special pts surjective locallyOfFiniteType isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le locallyQuasiFinite_schemeKerStr_kerPairLaw"
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
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.GoodReductionJacobian.RelativeGroupLaw"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.GoodReductionJacobian.RelativeGroupLaw"

namespace ModularCurve
p2m_export "ModularCurve" "JZeroNeronObjectAtP.LevelData JZeroNeronObjectAtP jZeroTorsion JZero instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable degeneracyPushforwardPair JZeroNeronObjectAtP.isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le JZeroNeronObjectAtP.locallyQuasiFinite_schemeKerStr_kerPairLaw"
namespace JZeroNeronObjectAtP
p2m_export "ModularCurve.JZeroNeronObjectAtP" "baseRing base genPt barPt resPt overId toFibrePt ofFibrePt fibreMap torusCoord torusStr torusPt ExtendsToPlace LevelData abqFibre_eq_one_iff L G pts_add degeneracyHom quasiCompact torusFibre abqFibre comp degeneracyHom_mul g degeneracyHom_pts frobSp separated toricRank degeneracyHom_special pts surjective locallyOfFiniteType isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le locallyQuasiFinite_schemeKerStr_kerPairLaw"
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
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.GoodReductionJacobian.RelativeGroupLaw"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.GoodReductionJacobian.RelativeGroupLaw"

namespace ModularCurve
p2m_export "ModularCurve" "JZeroNeronObjectAtP.LevelData JZeroNeronObjectAtP jZeroTorsion JZero instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable degeneracyPushforwardPair JZeroNeronObjectAtP.isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le JZeroNeronObjectAtP.locallyQuasiFinite_schemeKerStr_kerPairLaw"
namespace JZeroNeronObjectAtP
p2m_export "ModularCurve.JZeroNeronObjectAtP" "baseRing base genPt barPt resPt overId toFibrePt ofFibrePt fibreMap torusCoord torusStr torusPt ExtendsToPlace LevelData abqFibre_eq_one_iff L G pts_add degeneracyHom quasiCompact torusFibre abqFibre comp degeneracyHom_mul g degeneracyHom_pts frobSp separated toricRank degeneracyHom_special pts surjective locallyOfFiniteType isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le locallyQuasiFinite_schemeKerStr_kerPairLaw"
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
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.GoodReductionJacobian.RelativeGroupLaw"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.GoodReductionJacobian.RelativeGroupLaw"

namespace ModularCurve
p2m_export "ModularCurve" "JZeroNeronObjectAtP.LevelData JZeroNeronObjectAtP jZeroTorsion JZero instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable degeneracyPushforwardPair JZeroNeronObjectAtP.isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le JZeroNeronObjectAtP.locallyQuasiFinite_schemeKerStr_kerPairLaw"
namespace JZeroNeronObjectAtP
p2m_export "ModularCurve.JZeroNeronObjectAtP" "baseRing base genPt barPt resPt overId toFibrePt ofFibrePt fibreMap torusCoord torusStr torusPt ExtendsToPlace LevelData abqFibre_eq_one_iff L G pts_add degeneracyHom quasiCompact torusFibre abqFibre comp degeneracyHom_mul g degeneracyHom_pts frobSp separated toricRank degeneracyHom_special pts surjective locallyOfFiniteType isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le locallyQuasiFinite_schemeKerStr_kerPairLaw"
p2m_open "ModularCurve.JZeroNeronObjectAtP ModularCurve"

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  {Λ : LevelData N₀ p A}

namespace LevelData p2m_export "ModularCurve.JZeroNeronObjectAtP.LevelData" "IsJacobian σA X L hσA f ptsSp pts" end LevelData
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
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.GoodReductionJacobian.RelativeGroupLaw"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.GoodReductionJacobian.RelativeGroupLaw"

namespace ModularCurve
p2m_export "ModularCurve" "JZeroNeronObjectAtP.LevelData JZeroNeronObjectAtP jZeroTorsion JZero instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable degeneracyPushforwardPair JZeroNeronObjectAtP.isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le JZeroNeronObjectAtP.locallyQuasiFinite_schemeKerStr_kerPairLaw"
namespace JZeroNeronObjectAtP
p2m_export "ModularCurve.JZeroNeronObjectAtP" "baseRing base genPt barPt resPt overId toFibrePt ofFibrePt fibreMap torusCoord torusStr torusPt ExtendsToPlace LevelData abqFibre_eq_one_iff L G pts_add degeneracyHom quasiCompact torusFibre abqFibre comp degeneracyHom_mul g degeneracyHom_pts frobSp separated toricRank degeneracyHom_special pts surjective locallyOfFiniteType isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le locallyQuasiFinite_schemeKerStr_kerPairLaw"
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

theorem exists_injective_toSections_kerATors (hΛ : Λ.IsJacobian) (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) :
    ∃ Φ : {x : JZero (N₀ * p) | x ∈ jZeroTorsion (N₀ * p) m ∧ ExtendsToPlace A Λ.σA (O.pts x) ∧
        degeneracyPushforwardPair N₀ p 0 x = 0 ∧ degeneracyPushforwardPair N₀ p 1 x = 0} →
      {σ : Spec (CommRingCat.of ↥A) ⟶ (kerALaw O).schemeKer m // σ ≫ kerATorsStr O m = 𝟙 _},
      Function.Injective Φ := by
  classical

  have hext : ∀ x : {x : JZero (N₀ * p) | x ∈ jZeroTorsion (N₀ * p) m ∧ ExtendsToPlace A Λ.σA (O.pts x) ∧
      degeneracyPushforwardPair N₀ p 0 x = 0 ∧ degeneracyPushforwardPair N₀ p 1 x = 0},
      ∃ s : SchemeHomOver Λ.σA O.g, (O.pts x.1).1 = barPt A ≫ s.1 := fun x => x.2.2.1
  choose s hs using hext
  have hsK : ∀ x i, NeronModelInfra.schemeHomOverComp (s x) (O.degeneracyHom i) = Λ.L.one Λ.σA := by
    intro x i
    fin_cases i
    · exact schemeHomOverComp_degeneracyHom_eq_one hΛ O 0 (hs x) x.2.2.2.1
    · exact schemeHomOverComp_degeneracyHom_eq_one hΛ O 1 (hs x) x.2.2.2.2
  have hsm : ∀ x, O.L.nsmul Λ.σA m (s x) = O.L.one Λ.σA := fun x =>
    nsmul_eq_one_of_extends O (by
      have h := x.2.1
      simpa [jZeroTorsion] using h) (hs x)
  refine ⟨fun x => ⟨((kerALaw O).schemeKerLift m (kerAPt O (s x) (hsK x)) (kerALaw_nsmul_kerAPt O (s x) (hsK x) (hsm x))).1,
    ((kerALaw O).schemeKerLift m _ _).2⟩, ?_⟩
  intro x y hxy
  have h1 : (kerAPt O (s x) (hsK x)).1 = (kerAPt O (s y) (hsK y)).1 := by
    have := congrArg (fun σ => σ.1 ≫ pullback.fst _ _) hxy
    simpa only [RelativeGroupLaw.schemeKerLift_fst] using this
  have h2 : (s x).1 = (s y).1 := by
    rw [← kerAPt_coe_comp O (s x) (hsK x), ← kerAPt_coe_comp O (s y) (hsK y), h1]
  have h3 : O.pts x.1 = O.pts y.1 := Subtype.ext (by rw [hs x, hs y, h2])
  exact Subtype.ext (O.pts.injective h3)

end ModularCurve.JZeroNeronObjectAtP
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.GoodReductionJacobian.RelativeGroupLaw"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.GoodReductionJacobian.RelativeGroupLaw"

namespace ModularCurve
p2m_export "ModularCurve" "JZeroNeronObjectAtP.LevelData JZeroNeronObjectAtP jZeroTorsion JZero instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable degeneracyPushforwardPair JZeroNeronObjectAtP.isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le JZeroNeronObjectAtP.locallyQuasiFinite_schemeKerStr_kerPairLaw"
namespace JZeroNeronObjectAtP
p2m_export "ModularCurve.JZeroNeronObjectAtP" "baseRing base genPt barPt resPt overId toFibrePt ofFibrePt fibreMap torusCoord torusStr torusPt ExtendsToPlace LevelData abqFibre_eq_one_iff L G pts_add degeneracyHom quasiCompact torusFibre abqFibre comp degeneracyHom_mul g degeneracyHom_pts frobSp separated toricRank degeneracyHom_special pts surjective locallyOfFiniteType isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le locallyQuasiFinite_schemeKerStr_kerPairLaw"
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

end ModularCurve.JZeroNeronObjectAtP
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.GoodReductionJacobian.RelativeGroupLaw"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.GoodReductionJacobian.RelativeGroupLaw"

namespace ModularCurve
p2m_export "ModularCurve" "JZeroNeronObjectAtP.LevelData JZeroNeronObjectAtP jZeroTorsion JZero instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable degeneracyPushforwardPair JZeroNeronObjectAtP.isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le JZeroNeronObjectAtP.locallyQuasiFinite_schemeKerStr_kerPairLaw"
namespace JZeroNeronObjectAtP
p2m_export "ModularCurve.JZeroNeronObjectAtP" "baseRing base genPt barPt resPt overId toFibrePt ofFibrePt fibreMap torusCoord torusStr torusPt ExtendsToPlace LevelData abqFibre_eq_one_iff L G pts_add degeneracyHom quasiCompact torusFibre abqFibre comp degeneracyHom_mul g degeneracyHom_pts frobSp separated toricRank degeneracyHom_special pts surjective locallyOfFiniteType isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le locallyQuasiFinite_schemeKerStr_kerPairLaw"
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
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.GoodReductionJacobian.RelativeGroupLaw"

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
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.ModularCurve.JZeroNeronObjectAtP"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.ModularCurve"

namespace ModularCurve p2m_export "ModularCurve" "JZeroNeronObjectAtP.LevelData JZeroNeronObjectAtP jZeroTorsion JZero instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable degeneracyPushforwardPair JZeroNeronObjectAtP.isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le JZeroNeronObjectAtP.locallyQuasiFinite_schemeKerStr_kerPairLaw" namespace JZeroNeronObjectAtP p2m_export "ModularCurve.JZeroNeronObjectAtP" "baseRing base genPt barPt resPt overId toFibrePt ofFibrePt fibreMap torusCoord torusStr torusPt ExtendsToPlace LevelData abqFibre_eq_one_iff L G pts_add degeneracyHom quasiCompact torusFibre abqFibre comp degeneracyHom_mul g degeneracyHom_pts frobSp separated toricRank degeneracyHom_special pts surjective locallyOfFiniteType isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le locallyQuasiFinite_schemeKerStr_kerPairLaw" end ModularCurve.JZeroNeronObjectAtP
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
p2m_export "ModularCurve" "JZeroNeronObjectAtP.LevelData JZeroNeronObjectAtP jZeroTorsion JZero instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable degeneracyPushforwardPair JZeroNeronObjectAtP.isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le JZeroNeronObjectAtP.locallyQuasiFinite_schemeKerStr_kerPairLaw"
namespace JZeroNeronObjectAtP
p2m_export "ModularCurve.JZeroNeronObjectAtP" "baseRing base genPt barPt resPt overId toFibrePt ofFibrePt fibreMap torusCoord torusStr torusPt ExtendsToPlace LevelData abqFibre_eq_one_iff L G pts_add degeneracyHom quasiCompact torusFibre abqFibre comp degeneracyHom_mul g degeneracyHom_pts frobSp separated toricRank degeneracyHom_special pts surjective locallyOfFiniteType isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le locallyQuasiFinite_schemeKerStr_kerPairLaw"
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
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.ModularCurve.JZeroNeronObjectAtP"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.ModularCurve.JZeroNeronObjectAtP"

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Spec.map_comp Spec.map_preimage HasAffineProperty Scheme.Hom LocallyQuasiFinite IsFinite IsSeparated.of_comp QuasiCompact LocallyOfFiniteType Spec Spec.map Scheme Scheme.Hom.appTop HasAffineProperty.iff_of_isAffine Spec.map_injective locallyOfFiniteType_of_comp IsSeparated Spec.preimage HasRingHomProperty.Spec_iff QuasiCompact.of_comp Spec.map_id LocallyOfFinitePresentation HasRingHomProperty Scheme.ΓSpecIso Scheme.Hom.appLE_eq_app Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom IsSeparated.eq_of_spec_map_subtype_comp_eq ext_of_forall_geometricPoint_comp_eq_of_flat finite_and_natCard_sections_le_of_finrank_specialFibre_le" end AlgebraicGeometry
p2m_open_scoped "AlgebraicGeometry" in

theorem AlgebraicGeometry.moduleFinite_sections_of_isFinite {R : Type u} [CommRing R] {Y : Scheme.{u}}
    (q : Y ⟶ Spec (.of R)) [IsFinite q] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom q ⊤
    Module.Finite R Γ(Y, ⊤) := by
  obtain ⟨_, hfin⟩ := (HasAffineProperty.iff_of_isAffine (P := @IsFinite) (f := q)).mp inferInstance
  letI := Scheme.TwoAffineOpenCover.algebraOfHom q ⊤
  have halg : (algebraMap R Γ(Y, ⊤)) = (q.appTop).hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom := by
    ext r
    rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom, RingHom.comp_apply]
    have happ : q.appLE ⊤ ⊤ le_top = q.appTop := by
      rw [Scheme.Hom.appTop, ← Scheme.Hom.appLE_eq_app]
      rfl
    rw [happ]
  have h2 : ((q.appTop).hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).Finite :=
    RingHom.Finite.comp hfin
      (RingHom.Finite.of_surjective _ (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.surjective)
  rw [← halg] at h2
  exact RingHom.finite_algebraMap.mp h2

namespace ModularCurve
p2m_export "ModularCurve" "JZeroNeronObjectAtP.LevelData JZeroNeronObjectAtP jZeroTorsion JZero instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable degeneracyPushforwardPair JZeroNeronObjectAtP.isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le JZeroNeronObjectAtP.locallyQuasiFinite_schemeKerStr_kerPairLaw"
namespace JZeroNeronObjectAtP
p2m_export "ModularCurve.JZeroNeronObjectAtP" "baseRing base genPt barPt resPt overId toFibrePt ofFibrePt fibreMap torusCoord torusStr torusPt ExtendsToPlace LevelData abqFibre_eq_one_iff L G pts_add degeneracyHom quasiCompact torusFibre abqFibre comp degeneracyHom_mul g degeneracyHom_pts frobSp separated toricRank degeneracyHom_special pts surjective locallyOfFiniteType isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le locallyQuasiFinite_schemeKerStr_kerPairLaw"
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
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.ModularCurve.JZeroNeronObjectAtP"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.GoodReductionJacobian.RelativeGroupLaw P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives.ModularCurve.JZeroNeronObjectAtP"

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
    (S : Finset (SchemeHomOver (resPt A ≫ Λ.σA) O.g))
    (hSK : ∀ s ∈ S, ∀ i, NeronModelInfra.schemeHomOverComp s (O.degeneracyHom i) = Λ.L.one (resPt A ≫ Λ.σA))
    (hS : ∀ x : SchemeHomOver (resPt A ≫ Λ.σA) O.g,
        (∀ i, NeronModelInfra.schemeHomOverComp x (O.degeneracyHom i) = Λ.L.one (resPt A ≫ Λ.σA)) →
        ∃ s ∈ S, ∃ τ : SchemeHomOver (𝟙 _) (torusStr (ResidueField ↥A) O.toricRank),
          toFibrePt x = (O.L.baseChange (resPt A ≫ Λ.σA)).mul (𝟙 _)
            (NeronModelInfra.schemeHomOverComp τ O.torusFibre) (toFibrePt s))
    (m : ℕ) (hm : 0 < m) :
    {x : JZero (N₀ * p) | x ∈ jZeroTorsion (N₀ * p) m ∧ ExtendsToPlace A Λ.σA (O.pts x) ∧
        degeneracyPushforwardPair N₀ p 0 x = 0 ∧ degeneracyPushforwardPair N₀ p 1 x = 0}.Finite ∧
      Nat.card {x : JZero (N₀ * p) | x ∈ jZeroTorsion (N₀ * p) m ∧ ExtendsToPlace A Λ.σA (O.pts x) ∧
        degeneracyPushforwardPair N₀ p 0 x = 0 ∧ degeneracyPushforwardPair N₀ p 1 x = 0} ≤
        S.card * m ^ O.toricRank := by
  classical
  haveI hΛ' : Fact Λ.IsJacobian := ⟨hΛ⟩
  haveI : HenselianLocalRing ↥A := ValuationSubring.henselianLocalRing_of_isAlgClosed A
  haveI : LocallyOfFiniteType (kerATorsStr O m) := ModularCurve.JZeroNeronObjectAtP.kerATorsStr_locallyOfFiniteType hΛ' O m
  haveI : IsSeparated (kerATorsStr O m) := ModularCurve.JZeroNeronObjectAtP.kerATorsStr_isSeparated hΛ' O m
  haveI : QuasiCompact (kerATorsStr O m) := ModularCurve.JZeroNeronObjectAtP.kerATorsStr_quasiCompact hΛ' O m
  haveI : LocallyQuasiFinite (kerATorsStr O m) :=
    ModularCurve.JZeroNeronObjectAtP.locallyQuasiFinite_schemeKerStr_kerPairLaw N₀ p hpN₀ A hA Λ hΛ O m hm

  obtain ⟨Φ, hΦ⟩ := exists_injective_toSections_kerATors hΛ O m

  obtain ⟨π, hπ⟩ := ModularCurve.JZeroNeronObjectAtP.exists_isPullback_schemeKer_kerPairLaw_residue N₀ p hpN₀ A hA Λ O m
  have hι := fun i => torusFibre_comp_fibreRestrictAlong_degeneracyHom_eq hΛ O i
  obtain ⟨hfinκ, hlen⟩ := ModularCurve.JZeroNeronObjectAtP.isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le
    N₀ p hpN₀ A hA Λ hΛ O hι S hSK hS m hm
  haveI := hfinκ
  obtain ⟨hfinS, hcard⟩ := AlgebraicGeometry.finite_and_natCard_sections_le_of_finrank_specialFibre_le
    (AlgebraicClosure ℚ) (kerATorsStr O m) _ π hπ (S.card * m ^ O.toricRank)
    ⟨AlgebraicGeometry.moduleFinite_sections_of_isFinite _, hlen⟩
  haveI := hfinS
  refine ⟨Set.finite_coe_iff.mp (Finite.of_injective Φ hΦ), ?_⟩
  exact (Nat.card_le_card_of_injective Φ hΦ).trans hcard

end S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_finite_and_card_le_of_kernel_coset_representatives (solution)
