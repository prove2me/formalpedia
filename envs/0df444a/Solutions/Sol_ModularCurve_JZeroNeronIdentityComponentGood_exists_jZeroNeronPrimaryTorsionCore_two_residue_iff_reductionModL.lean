-- Prove2me | solution 1 for ModularCurve.JZeroNeronIdentityComponentGood.exists_jZeroNeronPrimaryTorsionCore_two_residue_iff_reductionModL
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/21f8bd01-ddf8-54f3-ae7f-010cbe9ce233

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf
import Definitions.Def_ModularCurve_JZeroNeronIdentityComponentGood
import Definitions.Def_ModularCurve_ReductionModL
import Theorems.Thm_ModularCurve_schemeHomOver_residue_eq_ptsSp_reductionModL_of_isSeparated
import Theorems.Thm_ModularCurve_JZeroNeronIdentityComponent_exists_jZeroNeronPrimaryTorsionCore_forall_exists_points_embedding
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronIdentityComponentGood_exists_jZeroNeronPrimaryTorsionCore_two_residue_iff_reductionModL
p2m_attr_erase "instance" "ModularCurve.JZeroTorsionHopfOrder.instFlat_H ModularCurve.JZeroTorsionHopfOrder.instHopfAlgebra_H ModularCurve.JZeroTorsionHopfOrder.instFiniteType_H ModularCurve.JZeroTorsionHopfOrder.instCommRing_H EtaleCohomologyLES.instAdditiveSheafSchemeFppfTopologyAbEtaleTopologyFppfSheafToEtaleSheaf EtaleCohomologyLES.instFullSheafSchemeFppfTopologyAbEtaleTopologyFppfSheafToEtaleSheaf EtaleCohomologyLES.constSchemeOpAdditive EtaleCohomologyLES.instFaithfulSheafSchemeFppfTopologyAbEtaleTopologyFppfSheafToEtaleSheaf AlgebraicGeometry.Scheme.instAdditiveSheafFppfSmallFppfTopologyAbFppfCohomologyFunctor EtaleCohomologyLES.idIsContinuousEtaleFppf EtaleCohomologyLES.constantSheafEtaleAdditive EtaleCohomologyLES.constantSheafFppfAdditive EtaleCohomologyLES.etaleTopologySubcanonical EtaleCohomologyLES.etaleSheavesIsGrothendieckAbelian AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions"
p2m_attr_erase "instance" "FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper"
p2m_attr_erase "simp" "ModularCurve.JZeroTorsionHopfOrder.mk.injEq ModularCurve.JZeroTorsionHopfOrder.mk.sizeOf_spec EtaleCohomologyLES.sheafInclusionOfLe_obj_obj FppfCohomologyLES.homPostcompAddEquiv_apply EtaleCohomologyLES.fppfSheafToEtaleSheaf_obj_obj AlgebraicGeometry.Scheme.fppfCohomologyZeroNatIso_inv_app_apply FppfCohomologyLES.homPostcompAddEquiv_symm_apply AlgebraicGeometry.Scheme.fppfCohomologyZeroNatIso_hom_app_apply EtaleCohomologyLES.sheafInclusionOfLe_map_hom EtaleCohomologyLES.fppfSheafToEtaleSheaf_map_hom ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring"
p2m_attr_erase "simp" "ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux"
p2m_attr_erase "simp" "HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero"

set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_JZeroNeronIdentityComponentGood_exists_jZeroNeronPrimaryTorsionCore_two_residue_iff_reductionModL.ModularCurve AlgebraicCurve~H1 AlgebraicGeometry AlgebraicGeometry.Scheme"
open CategoryTheory CategoryTheory.Limits Opposite NeronModelInfra GoodReductionJacobian IsLocalRing ValuationSubring

section
namespace ModularCurve
p2m_export "ModularCurve" "eisensteinPrimaryTorsionBar JZeroNeronPrimaryTorsionCore JZero eisensteinNumerator JZeroNeronIdentityComponentGood JZeroNeronIdentityComponent ReductionInputsModL reductionModL schemeHomOver_residue_eq_ptsSp_reductionModL_of_isSeparated JZeroNeronIdentityComponent.exists_jZeroNeronPrimaryTorsionCore_forall_exists_points_embedding"
namespace NTcHelpers
p2m_open "ModularCurve"

variable {R : Type} [CommRing R]

noncomputable abbrev bR (R : Type) [CommRing R] : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of ℤ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℤ R))

theorem comp_bR_eq {S : Scheme.{0}} (t' : S ⟶ Spec (CommRingCat.of R)) (s : S ⟶ Spec (CommRingCat.of ℤ)) :
    t' ≫ bR R = s :=
  specZIsTerminal.hom_ext _ _

variable {G : Scheme.{0}} (g : G ⟶ Spec (CommRingCat.of ℤ))

section H1

variable {S : Scheme.{0}} (t' : S ⟶ Spec (CommRingCat.of R)) (s : S ⟶ Spec (CommRingCat.of ℤ))

noncomputable def pointEquiv : SchemeHomOver s g ≃ SchemeHomOver t' (pullback.snd g (bR R)) where
  toFun X := ⟨pullback.lift X.1 t' (by rw [X.2, comp_bR_eq]), pullback.lift_snd _ _ _⟩
  invFun x := ⟨x.1 ≫ pullback.fst g (bR R), by
    rw [Category.assoc, pullback.condition, ← Category.assoc, x.2, comp_bR_eq]⟩
  left_inv X := Subtype.ext (pullback.lift_fst _ _ _)
  right_inv x := by
    apply Subtype.ext
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
    · rw [pullback.lift_snd]; exact x.2.symm

@[scoped simp]
theorem pointEquiv_apply_coe_fst (X : SchemeHomOver s g) :
    (pointEquiv g t' s X).1 ≫ pullback.fst g (bR R) = X.1 :=
  pullback.lift_fst _ _ _

@[scoped simp]
theorem pointEquiv_apply_coe_snd (X : SchemeHomOver s g) :
    (pointEquiv g t' s X).1 ≫ pullback.snd g (bR R) = t' :=
  pullback.lift_snd _ _ _

@[scoped simp]
theorem pointEquiv_symm_apply_coe (x : SchemeHomOver t' (pullback.snd g (bR R))) :
    ((pointEquiv g t' s).symm x).1 = x.1 ≫ pullback.fst g (bR R) :=
  rfl

theorem ext_of_comp_fst_eq {x y : SchemeHomOver t' (pullback.snd g (bR R))}
    (h : x.1 ≫ pullback.fst g (bR R) = y.1 ≫ pullback.fst g (bR R)) : x = y :=
  (pointEquiv g t' (t' ≫ bR R)).symm.injective (Subtype.ext h)

theorem pointEquiv_symm_comp {S' : Scheme.{0}} (ψ : S' ⟶ S)
    (u' : S' ⟶ Spec (CommRingCat.of R)) (hu' : ψ ≫ t' = u') (s' : S' ⟶ Spec (CommRingCat.of ℤ))
    (x : SchemeHomOver t' (pullback.snd g (bR R))) :
    ((pointEquiv g u' s').symm (GoodReductionJacobian.schemeHomOverComp ψ hu' x)).1 =
      ψ ≫ ((pointEquiv g t' s).symm x).1 := by
  simp only [pointEquiv_symm_apply_coe, GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc]

theorem pointEquiv_comp_coe {S' : Scheme.{0}} (ψ : S' ⟶ S)
    (u' : S' ⟶ Spec (CommRingCat.of R)) (hu' : ψ ≫ t' = u')
    (s' : S' ⟶ Spec (CommRingCat.of ℤ)) (hs' : ψ ≫ s = s') (X : SchemeHomOver s g) :
    (pointEquiv g u' s' (GoodReductionJacobian.schemeHomOverComp ψ hs' X)).1 =
      ψ ≫ (pointEquiv g t' s X).1 := by
  apply pullback.hom_ext
  · rw [pointEquiv_apply_coe_fst, Category.assoc, pointEquiv_apply_coe_fst,
      GoodReductionJacobian.schemeHomOverComp_coe]
  · rw [pointEquiv_apply_coe_snd, Category.assoc, pointEquiv_apply_coe_snd, hu']

end H1

section H2

variable (L : RelativeGroupLaw ℤ g) (L' : RelativeGroupLaw R (pullback.snd g (bR R)))
  (hlaw : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (x y : SchemeHomOver t (pullback.snd g (bR R)))
    (X Y : SchemeHomOver (t ≫ bR R) g),
    X.1 = x.1 ≫ pullback.fst _ _ → Y.1 = y.1 ≫ pullback.fst _ _ →
    (L'.mul t x y).1 ≫ pullback.fst _ _ = (L.mul _ X Y).1)

variable {S : Scheme.{0}} (t' : S ⟶ Spec (CommRingCat.of R)) (s : S ⟶ Spec (CommRingCat.of ℤ))

include hlaw

theorem pointEquiv_symm_mul (x y : SchemeHomOver t' (pullback.snd g (bR R))) :
    (pointEquiv g t' s).symm (L'.mul t' x y) =
      L.mul s ((pointEquiv g t' s).symm x) ((pointEquiv g t' s).symm y) := by
  obtain rfl : t' ≫ bR R = s := comp_bR_eq t' s
  exact Subtype.ext (hlaw t' x y _ _ rfl rfl)

theorem pointEquiv_mul (X Y : SchemeHomOver s g) :
    pointEquiv g t' s (L.mul s X Y) = L'.mul t' (pointEquiv g t' s X) (pointEquiv g t' s Y) := by
  apply (pointEquiv g t' s).symm.injective
  rw [Equiv.symm_apply_apply, pointEquiv_symm_mul g L L' hlaw, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]

theorem pointEquiv_symm_one :
    (pointEquiv g t' s).symm (L'.one t') = L.one s := by
  set e := (pointEquiv g t' s).symm (L'.one t') with he
  have h : L.mul s e e = e := by
    rw [he, ← pointEquiv_symm_mul g L L' hlaw, L'.one_mul]
  calc e = L.mul s (L.one s) e := (L.one_mul s e).symm
    _ = L.mul s (L.mul s (L.inv s e) e) e := by rw [L.inv_mul_cancel]
    _ = L.mul s (L.inv s e) (L.mul s e e) := by rw [L.mul_assoc]
    _ = L.mul s (L.inv s e) e := by rw [h]
    _ = L.one s := L.inv_mul_cancel s e

theorem pointEquiv_one : pointEquiv g t' s (L.one s) = L'.one t' := by
  rw [← pointEquiv_symm_one g L L' hlaw t' s, Equiv.apply_symm_apply]

theorem pointEquiv_symm_nsmul (n : ℕ) (x : SchemeHomOver t' (pullback.snd g (bR R))) :
    (pointEquiv g t' s).symm (L'.nsmul t' n x) = L.nsmul s n ((pointEquiv g t' s).symm x) := by
  induction n with
  | zero => rw [L'.nsmul_zero, L.nsmul_zero, pointEquiv_symm_one g L L' hlaw]
  | succ n ih => rw [L'.nsmul_succ, L.nsmul_succ, pointEquiv_symm_mul g L L' hlaw, ih]

theorem pointEquiv_symm_mem_torsionSubset_iff (n : ℕ) (x : SchemeHomOver t' (pullback.snd g (bR R))) :
    (pointEquiv g t' s).symm x ∈ L.torsionSubset s n ↔ x ∈ L'.torsionSubset t' n := by
  rw [L.mem_torsionSubset, L'.mem_torsionSubset, L.isTorsionPoint_def, L'.isTorsionPoint_def,
    ← pointEquiv_symm_nsmul g L L' hlaw, ← pointEquiv_symm_one g L L' hlaw t' s]
  exact (pointEquiv g t' s).symm.injective.eq_iff

theorem pointEquiv_mem_torsionSubset_iff (n : ℕ) (X : SchemeHomOver s g) :
    pointEquiv g t' s X ∈ L'.torsionSubset t' n ↔ X ∈ L.torsionSubset s n := by
  rw [← pointEquiv_symm_mem_torsionSubset_iff g L L' hlaw t' s n, Equiv.symm_apply_apply]

theorem pointEquiv_symm_inv (x : SchemeHomOver t' (pullback.snd g (bR R))) :
    (pointEquiv g t' s).symm (L'.inv t' x) = L.inv s ((pointEquiv g t' s).symm x) := by
  set y := (pointEquiv g t' s).symm x
  set z := (pointEquiv g t' s).symm (L'.inv t' x) with hz
  have h : L.mul s z y = L.one s := by
    rw [hz, ← pointEquiv_symm_mul g L L' hlaw, L'.inv_mul_cancel, pointEquiv_symm_one g L L' hlaw]
  calc z = L.mul s z (L.one s) := (L.mul_one s z).symm
    _ = L.mul s z (L.mul s y (L.inv s y)) := by rw [L.mul_inv_cancel]
    _ = L.mul s (L.mul s z y) (L.inv s y) := by rw [L.mul_assoc]
    _ = L.inv s y := by rw [h, L.one_mul]

end H2

section H3

variable {K : Type} [Field K] [Algebra R K] {P : Type}
  (pts : P ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ K))) g)
  (pts' : P ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R K))) (pullback.snd g (bR R)))
  (hpts : ∀ x : P, (pts' x).1 ≫ pullback.fst _ _ = (pts x).1)

include hpts

theorem pointEquiv_symm_pts' (x : P) :
    (pointEquiv g (Spec.map (CommRingCat.ofHom (algebraMap R K)))
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ K)))).symm (pts' x) = pts x :=
  Subtype.ext (hpts x)

theorem pointEquiv_pts (x : P) :
    pointEquiv g (Spec.map (CommRingCat.ofHom (algebraMap R K)))
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ K))) (pts x) = pts' x := by
  rw [← pointEquiv_symm_pts' g pts pts' hpts x, Equiv.apply_symm_apply]

theorem pts'_symm_pointEquiv_pts (x : P) :
    pts'.symm (pointEquiv g (Spec.map (CommRingCat.ofHom (algebraMap R K)))
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ K))) (pts x)) = x := by
  rw [pointEquiv_pts g pts pts' hpts, Equiv.symm_apply_apply]

end H3

end ModularCurve.NTcHelpers
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponentGood_exists_jZeroNeronPrimaryTorsionCore_two_residue_iff_reductionModL.ModularCurve P2MW.S_ModularCurve_JZeroNeronIdentityComponentGood_exists_jZeroNeronPrimaryTorsionCore_two_residue_iff_reductionModL.ModularCurve.NTcHelpers"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponentGood_exists_jZeroNeronPrimaryTorsionCore_two_residue_iff_reductionModL.ModularCurve"
end
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponentGood_exists_jZeroNeronPrimaryTorsionCore_two_residue_iff_reductionModL.ModularCurve P2MW.S_ModularCurve_JZeroNeronIdentityComponentGood_exists_jZeroNeronPrimaryTorsionCore_two_residue_iff_reductionModL.ModularCurve.NTcHelpers"

theorem solution
    (p : ℕ) [Fact p.Prime] (h2n : 2 ∣ eisensteinNumerator p)
    (N : JZeroNeronIdentityComponentGood p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (B : ValuationSubring (AlgebraicClosure ℚ)) (hB : B.LiesOverPrime 2)
    (hRI : ReductionInputsModL B p) :
    ∃ C : JZeroNeronPrimaryTorsionCore p 2 A hA, ∀ m : ℕ,
      ∀ φ ψ : C.H m →ₐ[ℤ] ↥B, ∀ φ' ψ' : WithConv (C.H m →ₐ[ℤ] AlgebraicClosure ℚ),
        (∀ h : C.H m, φ' h = B.subtype (φ h)) → (∀ h : C.H m, ψ' h = B.subtype (ψ h)) →
        ((∀ h : C.H m, IsLocalRing.residue ↥B (φ h) = IsLocalRing.residue ↥B (ψ h)) ↔
          reductionModL B p ((C.genericPoints m φ' : ↥(eisensteinPrimaryTorsionBar p 2 m)) : JZero p)
            = reductionModL B p ((C.genericPoints m ψ' : ↥(eisensteinPrimaryTorsionBar p 2 m)) : JZero p)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

  have h2p : (2 : ℕ) ≠ p := by
    rintro rfl
    have h1 : eisensteinNumerator 2 = 1 := by decide
    rw [h1] at h2n
    exact absurd (Nat.le_of_dvd Nat.one_pos h2n) (by decide)
  have hp2 : ¬ 2 ∣ p := fun h => h2p ((Nat.prime_dvd_prime_iff_eq Nat.prime_two Fact.out).mp h)

  have hqn : 2 ∣ ((p : ℤ) - 1).natAbs / ((p : ℤ) - 1).gcd 12 := by
    have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_le
    have hc : ((p : ℤ) - 1) = ((p - 1 : ℕ) : ℤ) := by push_cast [Nat.cast_sub hp1]; ring
    have hg : (((p - 1 : ℕ) : ℤ)).gcd 12 = Nat.gcd (p - 1) 12 := by
      rw [show (12 : ℤ) = ((12 : ℕ) : ℤ) by norm_num, Int.gcd_natCast_natCast]
    rw [hc, Int.natAbs_natCast, hg]
    exact h2n

  obtain ⟨C, hC⟩ :=
    ModularCurve.JZeroNeronIdentityComponent.exists_jZeroNeronPrimaryTorsionCore_forall_exists_points_embedding
      p 2 h2p hqn A hA N.toJZeroNeronIdentityComponent
  refine ⟨C, fun m φ ψ φ' ψ' hφ' hψ' => ?_⟩
  obtain ⟨ρ, hρinj, hρnat, -, hρgen⟩ := hC m

  let d := N.goodPrime 2 hp2
  obtain ⟨σB, ptsA, ptsSp, hptsA, -, hrop⟩ := d.pointsDict B hB
  have hROP := hrop hRI
  have hsep : IsSeparated (pullback.snd N.g (NTcHelpers.bR ↥(GaloisRep.ratLocalizedAt 2))) := d.bundle.proper.toIsSeparated

  let sB : Spec (CommRingCat.of ↥B) ⟶ Spec (CommRingCat.of ℤ) := Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥B))
  let P₂ : (C.H m →ₐ[ℤ] ↥B) → SchemeHomOver σB (pullback.snd N.g (NTcHelpers.bR ↥(GaloisRep.ratLocalizedAt 2))) :=
    fun χ => NTcHelpers.pointEquiv N.g σB sB (ρ ↥B χ)

  have hgen : ∀ (χ : C.H m →ₐ[ℤ] ↥B) (χ' : WithConv (C.H m →ₐ[ℤ] AlgebraicClosure ℚ)),
      (∀ h : C.H m, χ' h = B.subtype (χ h)) →
      Spec.map (CommRingCat.ofHom B.subtype) ≫ (P₂ χ).1
        = (ptsA ((C.genericPoints m χ' : ↥(eisensteinPrimaryTorsionBar p 2 m)) : JZero p)).1 := by
    intro χ χ' hχ'
    let Q : SchemeHomOver (Spec.map (CommRingCat.ofHom B.subtype) ≫ σB) (pullback.snd N.g (NTcHelpers.bR ↥(GaloisRep.ratLocalizedAt 2))) :=
      ⟨Spec.map (CommRingCat.ofHom B.subtype) ≫ (P₂ χ).1, by rw [Category.assoc, (P₂ χ).2]⟩
    have key : Q = ptsA ((C.genericPoints m χ' : ↥(eisensteinPrimaryTorsionBar p 2 m)) : JZero p) := by
      apply NTcHelpers.ext_of_comp_fst_eq
      change (Spec.map (CommRingCat.ofHom B.subtype) ≫ (P₂ χ).1) ≫ pullback.fst N.g (NTcHelpers.bR ↥(GaloisRep.ratLocalizedAt 2)) = _
      rw [Category.assoc, NTcHelpers.pointEquiv_apply_coe_fst, hptsA, d.pts_compat]
      have h1 := hρnat ↥B (AlgebraicClosure ℚ) B.subtype.toIntAlgHom χ
      have h2 : B.subtype.toIntAlgHom.comp χ = WithConv.ofConv χ' :=
        AlgHom.ext fun h => (hχ' h).symm
      rw [h2] at h1
      exact h1.symm.trans (hρgen χ')
    exact congrArg Subtype.val key

  have hsp : ∀ (χ : C.H m →ₐ[ℤ] ↥B) (χ' : WithConv (C.H m →ₐ[ℤ] AlgebraicClosure ℚ)),
      (∀ h : C.H m, χ' h = B.subtype (χ h)) →
      Spec.map (CommRingCat.ofHom (residue ↥B)) ≫ (P₂ χ).1
        = (ptsSp (reductionModL B p ((C.genericPoints m χ' : ↥(eisensteinPrimaryTorsionBar p 2 m)) : JZero p))).1 :=
    fun χ χ' hχ' =>
      ModularCurve.schemeHomOver_residue_eq_ptsSp_reductionModL_of_isSeparated p B _ _ hsep σB ptsA ptsSp
        hROP _ (P₂ χ) (hgen χ χ' hχ')

  let resk : (C.H m →ₐ[ℤ] ↥B) → (C.H m →ₐ[ℤ] ResidueField ↥B) := fun χ => (residue ↥B).toIntAlgHom.comp χ
  have hres : ∀ χ : C.H m →ₐ[ℤ] ↥B,
      (ρ (ResidueField ↥B) (resk χ)).1 = Spec.map (CommRingCat.ofHom (residue ↥B)) ≫ (ρ ↥B χ).1 :=
    fun χ => hρnat ↥B (ResidueField ↥B) (residue ↥B).toIntAlgHom χ
  constructor
  · intro hφψ
    have e1 : resk φ = resk ψ := AlgHom.ext hφψ
    have e2 : Spec.map (CommRingCat.ofHom (residue ↥B)) ≫ (P₂ φ).1
        = Spec.map (CommRingCat.ofHom (residue ↥B)) ≫ (P₂ ψ).1 := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, NTcHelpers.pointEquiv_apply_coe_fst,
          NTcHelpers.pointEquiv_apply_coe_fst, ← hres, ← hres, e1]
      · rw [Category.assoc, Category.assoc, (P₂ φ).2, (P₂ ψ).2]
    have e3 := ((hsp φ φ' hφ').symm.trans e2).trans (hsp ψ ψ' hψ')
    exact ptsSp.injective (Subtype.ext e3)
  · intro hred h
    have e2 : Spec.map (CommRingCat.ofHom (residue ↥B)) ≫ (P₂ φ).1
        = Spec.map (CommRingCat.ofHom (residue ↥B)) ≫ (P₂ ψ).1 := by
      rw [hsp φ φ' hφ', hsp ψ ψ' hψ', hred]
    have e3 : Spec.map (CommRingCat.ofHom (residue ↥B)) ≫ (ρ ↥B φ).1
        = Spec.map (CommRingCat.ofHom (residue ↥B)) ≫ (ρ ↥B ψ).1 := by
      have h' := congrArg (fun k => k ≫ pullback.fst N.g (NTcHelpers.bR ↥(GaloisRep.ratLocalizedAt 2))) e2
      simp only [Category.assoc] at h'
      rw [NTcHelpers.pointEquiv_apply_coe_fst, NTcHelpers.pointEquiv_apply_coe_fst] at h'
      exact h'
    have e4 : ρ (ResidueField ↥B) (resk φ) = ρ (ResidueField ↥B) (resk ψ) :=
      Subtype.ext (by rw [hres, hres, e3])
    exact AlgHom.congr_fun (hρinj _ e4) h

end S_ModularCurve_JZeroNeronIdentityComponentGood_exists_jZeroNeronPrimaryTorsionCore_two_residue_iff_reductionModL
end P2MW
export P2MW.S_ModularCurve_JZeroNeronIdentityComponentGood_exists_jZeroNeronPrimaryTorsionCore_two_residue_iff_reductionModL (solution)
