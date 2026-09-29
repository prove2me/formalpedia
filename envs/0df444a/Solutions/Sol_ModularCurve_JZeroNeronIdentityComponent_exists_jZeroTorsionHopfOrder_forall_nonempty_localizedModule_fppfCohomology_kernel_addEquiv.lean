-- Prove2me | solution 1 for ModularCurve.JZeroNeronIdentityComponent.exists_jZeroTorsionHopfOrder_forall_nonempty_localizedModule_fppfCohomology_kernel_addEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/35db4e01-fb7d-5019-a5e1-3ba99628ecf1

import Definitions.Def_ModularCurve_JZeroNeronIdentityComponent
import Definitions.Def_ModularCurve_JZeroTorsionHopfOrder
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Theorems.Thm_ModularCurve_JZeroNeronIdentityComponent_exists_heckeAlg_tower_idempotent_schemeKer_of_ringHom_of_sectionsEquiv
import Theorems.Thm_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent
import Theorems.Thm_ModularCurve_JZeroNeronIdentityComponent_locallyQuasiFinite_schemeNsmul
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isAffine_schemeKer_of_locallyQuasiFinite
import Theorems.Thm_ModularCurve_jZeroTorsionFinite
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_schemeKer_forall_mem_torsionSubset_iff
import Theorems.Thm_ModularCurve_JZeroNeronIdentityComponent_exists_retract_kernel_zsmul_pointsSheaf_of_eisensteinProjector
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_jZeroTorsionHopfOrder_forall_nonempty_localizedModule_fppfCohomology_kernel_addEquiv
p2m_attr_erase "instance" "CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar"
p2m_attr_erase "instance" "ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left ModularCurve.dualHeckeRep_apply_apply"
p2m_attr_erase "simp" "ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero"
p2m_attr_erase "simp" "HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero"
set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme NeronModelInfra GoodReductionJacobian ModularCurve P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_jZeroTorsionHopfOrder_forall_nonempty_localizedModule_fppfCohomology_kernel_addEquiv.ModularCurve"

universe v u w

section
set_option maxHeartbeats 1600000
theorem S17.addEquiv_localizedModule_of_retract_abstract
    {𝒞 : Type u} [Category.{v} 𝒞] [Abelian 𝒞]
    (R : Type) [CommRing R] (𝔓 : Ideal R) [𝔓.IsPrime]
    (𝒢 : 𝒞) (n : ℤ) (ρ : R →+* End 𝒢)
    (Hc : 𝒞 → Type w) [∀ X, AddCommGroup (Hc X)]
    (Hmap : ∀ {X Y : 𝒞}, (X ⟶ Y) → (Hc X →+ Hc Y))
    (hcomp : ∀ {X Y Z : 𝒞} (φ : X ⟶ Y) (ψ : Y ⟶ Z) (x : Hc X), Hmap (φ ≫ ψ) x = Hmap ψ (Hmap φ x))
    (hid : ∀ {X : 𝒞} (x : Hc X), Hmap (𝟙 X) x = x)
    [Small.{0} (Hc (kernel (n • 𝟙 𝒢)))]
    (inst : Module R (Shrink.{0} (Hc (kernel (n • 𝟙 𝒢)))))
    (hinst : letI := inst
      ∀ r : R, ∃ w : (n • 𝟙 𝒢) ≫ ρ r = ρ r ≫ (n • 𝟙 𝒢),
        ∀ y : Hc (kernel (n • 𝟙 𝒢)),
          r • equivShrink (Hc (kernel (n • 𝟙 𝒢))) y =
            equivShrink (Hc (kernel (n • 𝟙 𝒢))) (Hmap (kernel.map (n • 𝟙 𝒢) (n • 𝟙 𝒢) (ρ r) (ρ r) w) y))
    (𝒥 : 𝒞)
    (F0 : ∃ (ι : 𝒥 ⟶ kernel (n • 𝟙 𝒢)) (π : kernel (n • 𝟙 𝒢) ⟶ 𝒥) (s : R),
      ι ≫ π = 𝟙 𝒥 ∧
      s ∉ 𝔓 ∧
      (∃ w : (n • 𝟙 𝒢) ≫ ρ s = ρ s ≫ (n • 𝟙 𝒢),
        kernel.map (n • 𝟙 𝒢) (n • 𝟙 𝒢) (ρ s) (ρ s) w = π ≫ ι) ∧
      (∀ t : R, ∃ w : (n • 𝟙 𝒢) ≫ ρ t = ρ t ≫ (n • 𝟙 𝒢),
        kernel.map (n • 𝟙 𝒢) (n • 𝟙 𝒢) (ρ t) (ρ t) w ≫ (π ≫ ι)
          = (π ≫ ι) ≫ kernel.map (n • 𝟙 𝒢) (n • 𝟙 𝒢) (ρ t) (ρ t) w) ∧
      (∀ t : R, t ∉ 𝔓 →
        ∃ w : (n • 𝟙 𝒢) ≫ ρ t = ρ t ≫ (n • 𝟙 𝒢),
          IsIso (ι ≫ kernel.map (n • 𝟙 𝒢) (n • 𝟙 𝒢) (ρ t) (ρ t) w ≫ π))) :
    letI := inst
    Nonempty (LocalizedModule 𝔓.primeCompl (Shrink.{0} (Hc (kernel (n • 𝟙 𝒢)))) ≃+ Hc 𝒥) := by
  classical
  letI := inst
  set K : 𝒞 := kernel (n • 𝟙 𝒢) with hK
  have hw : ∀ t : R, (n • 𝟙 𝒢) ≫ ρ t = ρ t ≫ (n • 𝟙 𝒢) := by
    intro t
    rw [Preadditive.zsmul_comp, Category.id_comp, Preadditive.comp_zsmul, Category.comp_id]
  let km : R → (K ⟶ K) := fun t => kernel.map (n • 𝟙 𝒢) (n • 𝟙 𝒢) (ρ t) (ρ t) (hw t)
  have kmι : ∀ t : R, km t ≫ kernel.ι (n • 𝟙 𝒢) = kernel.ι (n • 𝟙 𝒢) ≫ ρ t :=
    fun t => kernel.lift_ι _ _ _
  have km_mul : ∀ a b : R, km (a * b) = km b ≫ km a := by
    intro a b
    apply (cancel_mono (kernel.ι (n • 𝟙 𝒢))).mp
    rw [kmι, Category.assoc, kmι, ← Category.assoc, kmι, Category.assoc, map_mul, End.mul_def]
  have km_comm : ∀ a b : R, km a ≫ km b = km b ≫ km a := fun a b => by
    rw [← km_mul, ← km_mul, mul_comm]
  have km_one : km 1 = 𝟙 K := by
    apply (cancel_mono (kernel.ι (n • 𝟙 𝒢))).mp
    rw [kmι, map_one, End.one_def, Category.id_comp, Category.comp_id]
  obtain ⟨ι, π, s, hιπ, hs𝔓, ⟨ws, hkms⟩, hcomm, hiso⟩ := F0
  have hkms' : km s = π ≫ ι := hkms
  have hiso' : ∀ t : R, t ∉ 𝔓 → IsIso (ι ≫ km t ≫ π) := fun t ht => by
    obtain ⟨w, h⟩ := hiso t ht; exact h
  have hιs : ι ≫ km s = ι := by rw [hkms', ← Category.assoc, hιπ, Category.id_comp]
  have hsπ : km s ≫ π = π := by rw [hkms', Category.assoc, hιπ, Category.comp_id]
  have key : ∀ a b : R, (ι ≫ km b ≫ π) ≫ (ι ≫ km a ≫ π) = ι ≫ km (a * b) ≫ π := by
    intro a b
    rw [km_mul]
    simp only [Category.assoc]
    rw [← Category.assoc π ι, ← hkms', ← Category.assoc (km b) (km s), km_comm b s, Category.assoc,
      ← Category.assoc ι (km s), hιs]
  let H1 : Type w := Hc K
  let Nm : Type w := Hc 𝒥
  let iN : Nm →+ H1 := Hmap ι
  let pN : H1 →+ Nm := Hmap π
  let V : R → (Nm →+ Nm) := fun t => Hmap (ι ≫ km t ≫ π)
  have L5 : ∀ x : Nm, pN (iN x) = x := fun x => by
    show Hmap π (Hmap ι x) = x
    rw [← hcomp, hιπ, hid]
  have L6 : ∀ y : H1, iN (pN y) = Hmap (km s) y := fun y => by
    show Hmap ι (Hmap π y) = _
    rw [← hcomp, hkms']
  have LV : ∀ (t : R) (x : Nm), V t x = pN (Hmap (km t) (iN x)) := fun t x => by
    show Hmap (ι ≫ km t ≫ π) x = Hmap π (Hmap (km t) (Hmap ι x))
    rw [hcomp, hcomp]
  have L2 : ∀ (t : R) (y : H1), pN (Hmap (km t) y) = V t (pN y) := fun t y => by
    rw [LV, L6, ← hcomp, ← hcomp, ← hcomp]
    show Hmap (km t ≫ π) y = Hmap (km s ≫ km t ≫ π) y
    rw [← Category.assoc (km s), km_comm s t, Category.assoc, hsπ]
  have Vmul : ∀ (a b : R) (x : Nm), V (a * b) x = V a (V b x) := fun a b x => by
    show Hmap (ι ≫ km (a * b) ≫ π) x = Hmap (ι ≫ km a ≫ π) (Hmap (ι ≫ km b ≫ π) x)
    rw [← hcomp, key]
  have L3 : ∀ (a b : R) (x : Nm), V a (V b x) = V b (V a x) := fun a b x => by
    rw [← Vmul, ← Vmul, mul_comm]
  have L4 : ∀ u : R, u ∉ 𝔓 → Function.Bijective (V u) := by
    intro u hu
    haveI := hiso' u hu
    have h1 : ∀ x, Hmap (inv (ι ≫ km u ≫ π)) (V u x) = x := fun x => by
      show Hmap (inv (ι ≫ km u ≫ π)) (Hmap (ι ≫ km u ≫ π) x) = x
      rw [← hcomp, IsIso.hom_inv_id, hid]
    have h2 : ∀ x, V u (Hmap (inv (ι ≫ km u ≫ π)) x) = x := fun x => by
      show Hmap (ι ≫ km u ≫ π) (Hmap (inv (ι ≫ km u ≫ π)) x) = x
      rw [← hcomp, IsIso.inv_hom_id, hid]
    exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩
  let M := Shrink.{0} (Hc (kernel (n • 𝟙 𝒢)))
  let toH : M → H1 := fun x => (equivShrink H1).symm x
  have toH_add : ∀ x y : M, toH (x + y) = toH x + toH y := fun x y => by
    show (equivShrink H1).symm (x + y) = _
    rw [equivShrink_symm_add]
  have toH_inj : Function.Injective toH := (equivShrink H1).symm.injective
  have L1' : ∀ (r : R) (y : H1), toH (r • equivShrink H1 y) = Hmap (km r) y := by
    intro r y
    obtain ⟨w, hw'⟩ := hinst r
    show (equivShrink H1).symm (r • equivShrink H1 y) = _
    rw [hw', Equiv.symm_apply_apply]
    try rfl
  have L1 : ∀ (r : R) (x : M), toH (r • x) = Hmap (km r) (toH x) := by
    intro r x
    have hx : equivShrink H1 (toH x) = x := (equivShrink H1).apply_symm_apply x
    have h := L1' r (toH x)
    rw [hx] at h
    exact h
  let S' := 𝔓.primeCompl
  have hS1 : ∀ (u : S') (x : M), toH (u • x) = Hmap (km (u : R)) (toH x) := fun u x => L1 u x
  let Vinv : S' → Nm → Nm := fun u => Function.surjInv (L4 u u.2).2
  have hVinv1 : ∀ (u : S') (x : Nm), V u (Vinv u x) = x := fun u x => Function.surjInv_eq (L4 u u.2).2 x
  have hVinv2 : ∀ (u : S') (x : Nm), Vinv u (V u x) = x := fun u x => (L4 u u.2).1 (hVinv1 u (V u x))
  let fwd0 : M × S' → Nm := fun x => Vinv x.2 (pN (toH x.1))
  have fwd_wd : ∀ (a b : M × S'), a ≈ b → fwd0 a = fwd0 b := by
    rintro ⟨x, u⟩ ⟨x', u'⟩ ⟨v, hv⟩
    have h1 : V v (V u' (pN (toH x))) = V v (V u (pN (toH x'))) := by
      have := congrArg (fun z => pN (toH z)) hv
      simp only at this
      rwa [hS1, hS1, L2, L2, hS1, hS1, L2, L2] at this
    have h2 : V u' (pN (toH x)) = V u (pN (toH x')) := (L4 v v.2).1 h1
    show Vinv u (pN (toH x)) = Vinv u' (pN (toH x'))
    have h3 : V u (V u' (Vinv u (pN (toH x)))) = V u (V u' (Vinv u' (pN (toH x')))) := by
      rw [L3 (u : _) (u' : _) (Vinv u (pN (toH x))), hVinv1, hVinv1]
      exact h2
    exact (L4 u' u'.2).1 ((L4 u u.2).1 h3)
  let fwd : LocalizedModule S' M → Nm := fun z => z.liftOn fwd0 fwd_wd
  have fwd_mk : ∀ (x : M) (u : S'), fwd (LocalizedModule.mk x u) = Vinv u (pN (toH x)) := fun x u => by
    show (LocalizedModule.mk x u).liftOn fwd0 fwd_wd = _
    rw [LocalizedModule.liftOn_mk]
  let bwd : Nm → LocalizedModule S' M := fun x => LocalizedModule.mk (equivShrink H1 (iN x)) 1
  have hV1 : ∀ x : Nm, V 1 x = x := fun x => by
    rw [LV]
    show pN (Hmap (km 1) (iN x)) = x
    rw [km_one, hid, L5]
  have fwd_bwd : ∀ x, fwd (bwd x) = x := fun x => by
    show fwd (LocalizedModule.mk (equivShrink H1 (iN x)) 1) = x
    rw [fwd_mk]
    have : toH (equivShrink H1 (iN x)) = iN x := (equivShrink H1).symm_apply_apply _
    rw [this, L5]
    have h := hVinv2 1 x
    rwa [show ((1 : S') : R) = 1 from rfl, hV1] at h
  have bwd_fwd : ∀ z, bwd (fwd z) = z := by
    intro z
    induction z using LocalizedModule.induction_on with
    | h x u =>
      rw [fwd_mk]
      show LocalizedModule.mk (equivShrink H1 (iN (Vinv u (pN (toH x))))) 1 = LocalizedModule.mk x u
      rw [LocalizedModule.mk_eq]
      refine ⟨⟨s, hs𝔓⟩, ?_⟩
      apply toH_inj
      rw [one_smul, hS1, hS1, hS1]
      have : toH (equivShrink H1 (iN (Vinv u (pN (toH x))))) = iN (Vinv u (pN (toH x))) :=
        (equivShrink H1).symm_apply_apply _
      rw [this]
      show Hmap (km s) (Hmap (km (u : R)) (iN (Vinv u (pN (toH x))))) = Hmap (km s) (toH x)
      rw [← L6, ← L6, L2, L5, hVinv1]
  refine ⟨{ toFun := fwd, invFun := bwd, left_inv := bwd_fwd, right_inv := fwd_bwd, map_add' := ?_ }⟩
  intro a b
  induction a using LocalizedModule.induction_on with
  | h x u =>
    induction b using LocalizedModule.induction_on with
    | h x' u' =>
      rw [LocalizedModule.mk_add_mk, fwd_mk, fwd_mk, fwd_mk]
      apply (L4 _ (u * u').2).1
      rw [hVinv1, map_add, toH_add, map_add, hS1, hS1, L2, L2]
      show V (u' : R) (pN (toH x)) + V (u : R) (pN (toH x')) =
        V ((u : R) * (u' : R)) (Vinv u (pN (toH x))) + V ((u : R) * (u' : R)) (Vinv u' (pN (toH x')))
      rw [Vmul, Vmul, L3 (u : R) (u' : R), hVinv1, hVinv1]

theorem S17.addEquiv_localizedModule_fppfCohomology_of_retract
    (R : Type) [CommRing R] (𝔓 : Ideal R) [𝔓.IsPrime]
    (𝒢 : Sheaf (smallFppfTopology specInt) Ab.{1}) (n : ℤ) (ρ : R →+* End 𝒢)
    [Small.{0} (fppfCohomology specInt (kernel (n • 𝟙 𝒢)) 1)]
    (inst : Module R (Shrink.{0} (fppfCohomology specInt (kernel (n • 𝟙 𝒢)) 1)))
    (hinst : letI := inst
      ∀ r : R, ∃ w : (n • 𝟙 𝒢) ≫ ρ r = ρ r ≫ (n • 𝟙 𝒢),
        ∀ y : fppfCohomology specInt (kernel (n • 𝟙 𝒢)) 1,
          r • equivShrink (fppfCohomology specInt (kernel (n • 𝟙 𝒢)) 1) y =
            equivShrink (fppfCohomology specInt (kernel (n • 𝟙 𝒢)) 1)
              (fppfCohomologyMap specInt (kernel.map (n • 𝟙 𝒢) (n • 𝟙 𝒢) (ρ r) (ρ r) w) 1 y))
    (𝒥 : Sheaf (smallFppfTopology specInt) Ab.{1})
    (F0 : ∃ (ι : 𝒥 ⟶ kernel (n • 𝟙 𝒢)) (π : kernel (n • 𝟙 𝒢) ⟶ 𝒥) (s : R),
      ι ≫ π = 𝟙 𝒥 ∧
      s ∉ 𝔓 ∧
      (∃ w : (n • 𝟙 𝒢) ≫ ρ s = ρ s ≫ (n • 𝟙 𝒢),
        kernel.map (n • 𝟙 𝒢) (n • 𝟙 𝒢) (ρ s) (ρ s) w = π ≫ ι) ∧
      (∀ t : R, ∃ w : (n • 𝟙 𝒢) ≫ ρ t = ρ t ≫ (n • 𝟙 𝒢),
        kernel.map (n • 𝟙 𝒢) (n • 𝟙 𝒢) (ρ t) (ρ t) w ≫ (π ≫ ι)
          = (π ≫ ι) ≫ kernel.map (n • 𝟙 𝒢) (n • 𝟙 𝒢) (ρ t) (ρ t) w) ∧
      (∀ t : R, t ∉ 𝔓 →
        ∃ w : (n • 𝟙 𝒢) ≫ ρ t = ρ t ≫ (n • 𝟙 𝒢),
          IsIso (ι ≫ kernel.map (n • 𝟙 𝒢) (n • 𝟙 𝒢) (ρ t) (ρ t) w ≫ π))) :
    letI := inst
    Nonempty (LocalizedModule 𝔓.primeCompl (Shrink.{0} (fppfCohomology specInt (kernel (n • 𝟙 𝒢)) 1))
      ≃+ fppfCohomology specInt 𝒥 1) :=
  S17.addEquiv_localizedModule_of_retract_abstract R 𝔓 𝒢 n ρ
    (fun F => fppfCohomology specInt F 1)
    (fun φ => fppfCohomologyMap specInt φ 1)
    (fun φ ψ x => fppfCohomologyMap_comp specInt φ ψ 1 x)
    (fun x => fppfCohomologyMap_id specInt 1 x)
    inst hinst 𝒥 F0

end

namespace ModularCurve
p2m_export "ModularCurve" "JZeroNeronIdentityComponent eisensteinPrimaryTorsionBar jZeroTorsion heckeModuleBar JZero HeckeAlg eisensteinMaximalIdeal JZeroTorsionHopfOrder JZeroNeronIdentityComponent.exists_heckeAlg_tower_idempotent_schemeKer_of_ringHom_of_sectionsEquiv JZeroNeronIdentityComponent.exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent jZeroTorsionFinite JZeroNeronIdentityComponent.exists_retract_kernel_zsmul_pointsSheaf_of_eisensteinProjector"
namespace TorsRepTop
p2m_open "ModularCurve"

scoped instance isPrime_eisensteinMaximalIdeal (p q : ℕ) [Fact q.Prime] : (eisensteinMaximalIdeal p q).IsPrime := by
  unfold eisensteinMaximalIdeal
  haveI : (Ideal.span {(q : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : q.Prime).ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp Fact.out)
  exact Ideal.comap_isPrime _ _

variable {p : ℕ} [Fact p.Prime] (q : ℕ) [Fact q.Prime] (N : JZeroNeronIdentityComponent p) (m : ℕ)

private noncomputable abbrev _root_.ModularCurve.TorsRepTop.fst : N.L.schemeKer (q ^ m) ⟶ N.G :=
  pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1

p2m_export "ModularCurve.TorsRepTop" "fst"
theorem hq0 : 0 < q ^ m := pow_pos (Fact.out : q.Prime).pos m

theorem fst_comp_eq : fst q N m ≫ N.g = N.L.schemeKerStr (q ^ m) := by
  obtain ⟨-, hk, -⟩ := GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_schemeKer_forall_mem_torsionSubset_iff
    N.L N.comm (q ^ m)
  exact hk

scoped instance flat_kerStr : Flat (N.L.schemeKerStr (q ^ m)) := by
  haveI : Flat (N.L.schemeNsmul (q ^ m)) := N.nsmul_flat _ (hq0 q m)
  change Flat (pullback.snd _ _); infer_instance

theorem hFlat : Flat (fst q N m ≫ N.g) := by rw [fst_comp_eq]; infer_instance

scoped instance lft_nsmul : LocallyOfFiniteType (N.L.schemeNsmul (q ^ m)) := by
  haveI : LocallyOfFiniteType N.g := N.locallyOfFiniteType
  haveI : LocallyOfFiniteType (N.L.schemeNsmul (q ^ m) ≫ N.g) := by rw [N.L.schemeNsmul_over]; infer_instance
  exact locallyOfFiniteType_of_comp _ N.g

scoped instance lft_kerStr : LocallyOfFiniteType (N.L.schemeKerStr (q ^ m)) := by
  change LocallyOfFiniteType (pullback.snd _ _); infer_instance

theorem hLft : LocallyOfFiniteType (fst q N m ≫ N.g) := by rw [fst_comp_eq]; infer_instance

scoped instance lqf_kerStr : LocallyQuasiFinite (N.L.schemeKerStr (q ^ m)) := by
  haveI := N.locallyQuasiFinite_schemeNsmul (q ^ m) (hq0 q m)
  change LocallyQuasiFinite (pullback.snd _ _); infer_instance

scoped instance qc_kerStr : QuasiCompact (N.L.schemeKerStr (q ^ m)) := by
  haveI : QuasiCompact N.g := N.quasiCompact
  haveI : IsSeparated N.g := N.separated
  haveI : QuasiCompact (N.L.schemeNsmul (q ^ m) ≫ N.g) := by rw [N.L.schemeNsmul_over]; infer_instance
  haveI : QuasiCompact (N.L.schemeNsmul (q ^ m)) := QuasiCompact.of_comp _ N.g
  change QuasiCompact (pullback.snd _ _); infer_instance

theorem isAffine_ker : IsAffine (N.L.schemeKer (q ^ m)) := by
  haveI : IsSeparated N.g := N.separated
  haveI : LocallyOfFiniteType N.g := N.locallyOfFiniteType
  have hR : ringKrullDim ℤ ≤ 1 :=
    (IsPrincipalIdealRing.ringKrullDim_eq_one ℤ (by simpa using Int.not_isField)).le
  exact GoodReductionJacobian.RelativeGroupLaw.isAffine_schemeKer_of_locallyQuasiFinite hR N.L (q ^ m)

theorem hAff : IsAffineHom (fst q N m ≫ N.g) := by
  haveI := isAffine_ker q N m
  exact isAffineHom_of_isAffine _

theorem hSep : IsSeparated (fst q N m ≫ N.g) := by
  haveI := hAff q N m
  infer_instance

theorem hfin : Finite ↥(jZeroTorsion p (q ^ m)) :=
  ModularCurve.jZeroTorsionFinite p (q ^ m) (hq0 q m)

end ModularCurve.TorsRepTop
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_jZeroTorsionHopfOrder_forall_nonempty_localizedModule_fppfCohomology_kernel_addEquiv.ModularCurve P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_jZeroTorsionHopfOrder_forall_nonempty_localizedModule_fppfCohomology_kernel_addEquiv.ModularCurve.TorsRepTop"
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_jZeroTorsionHopfOrder_forall_nonempty_localizedModule_fppfCohomology_kernel_addEquiv.ModularCurve"

open ModularCurve.TorsRepTop in

theorem solution
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hqn : q ∣ ((p : ℤ) - 1).natAbs / ((p : ℤ) - 1).gcd 12)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (N : JZeroNeronIdentityComponent p) (𝒢 : Sheaf (smallFppfTopology specInt) Ab.{1})
    (e : ∀ U : specInt.Fppf, 𝒢.1.obj (op U) ≃ SchemeHomOver U.hom N.g)
    (he_add : ∀ (U : specInt.Fppf) (s s' : 𝒢.1.obj (op U)), e U (s + s') = N.L.mul U.hom (e U s) (e U s'))
    (he : ∀ {U V : specInt.Fppf} (k : U ⟶ V) (s : 𝒢.1.obj (op V)),
        e U (𝒢.1.map k.op s) = schemeHomOverComp k.left (MorphismProperty.Over.w k) (e V s))
    (ρ : letI := heckeModuleBar p; HeckeAlg →+* End 𝒢)
    (hρ : letI := heckeModuleBar p
      ∀ t : HeckeAlg, ∃ φ : SchemeHomOver N.g N.g,
        (∀ x : JZero p, (N.pts (t • x)).1 = (N.pts x).1 ≫ φ.1) ∧
        ∀ (U : specInt.Fppf) (s : 𝒢.1.obj (op U)), (e U ((ρ t).1.app (op U) s)).1 = (e U s).1 ≫ φ.1) :
    letI := heckeModuleBar p
    ∃ C : JZeroTorsionHopfOrder p q A hA (fun m => eisensteinPrimaryTorsionBar p q m),
      ∀ (m : ℕ) (𝒥 : Sheaf (smallFppfTopology specInt) Ab.{1})
        (e𝒥 : ∀ U : specInt.Fppf, 𝒥.1.obj (op U) ≃+ Additive (WithConv (C.H m →ₐ[ℤ] Γ(U.left, ⊤))))
        (_ : ∀ {U W : specInt.Fppf} (f : U ⟶ W) (s : 𝒥.1.obj (op W)) (h : C.H m),
          (Additive.toMul (e𝒥 U (𝒥.1.map f.op s))) h = (Scheme.Γ.map f.left.op) ((Additive.toMul (e𝒥 W s)) h))
        [Small.{0} (fppfCohomology specInt (kernel (((q : ℤ) ^ m) • 𝟙 𝒢)) 1)]
        (inst : Module HeckeAlg (Shrink.{0} (fppfCohomology specInt (kernel (((q : ℤ) ^ m) • 𝟙 𝒢)) 1)))
        (_ : letI := inst
          ∀ r : HeckeAlg, ∃ w : (((q : ℤ) ^ m) • 𝟙 𝒢) ≫ ρ r = ρ r ≫ (((q : ℤ) ^ m) • 𝟙 𝒢),
            ∀ y : fppfCohomology specInt (kernel (((q : ℤ) ^ m) • 𝟙 𝒢)) 1,
              r • equivShrink (fppfCohomology specInt (kernel (((q : ℤ) ^ m) • 𝟙 𝒢)) 1) y =
                equivShrink (fppfCohomology specInt (kernel (((q : ℤ) ^ m) • 𝟙 𝒢)) 1)
                  (fppfCohomologyMap specInt (kernel.map (((q : ℤ) ^ m) • 𝟙 𝒢) (((q : ℤ) ^ m) • 𝟙 𝒢) (ρ r) (ρ r) w) 1 y)),
        letI := inst
        Nonempty (LocalizedModule (eisensteinMaximalIdeal p q).primeCompl
            (Shrink.{0} (fppfCohomology specInt (kernel (((q : ℤ) ^ m) • 𝟙 𝒢)) 1))
          ≃+ fppfCohomology specInt 𝒥 1) := by
  letI := heckeModuleBar p
  have hqp : q ≠ p := by
    have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
    have hnat : ((p : ℤ) - 1).natAbs = p - 1 := by omega
    rw [hnat] at hqn
    have hg : 0 < (p - 1).gcd 12 := Nat.gcd_pos_of_pos_right _ (by norm_num)
    have hgcd : ((p : ℤ) - 1).gcd 12 = (p - 1).gcd 12 := by
      rw [Int.gcd, hnat]; rfl
    rw [hgcd] at hqn
    have hle : (p - 1).gcd 12 ≤ p - 1 := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)
    have hpos : 0 < (p - 1) / (p - 1).gcd 12 := Nat.div_pos hle hg
    have hq_le : q ≤ (p - 1) / (p - 1).gcd 12 := Nat.le_of_dvd hpos hqn
    have : (p - 1) / (p - 1).gcd 12 ≤ p - 1 := Nat.div_le_self _ _
    omega

  obtain ⟨t, φ, eK, ht, hsec, hc⟩ :=
    ModularCurve.JZeroNeronIdentityComponent.exists_heckeAlg_tower_idempotent_schemeKer_of_ringHom_of_sectionsEquiv
      p q N 𝒢 e he_add he ρ hρ (fun m => hfin (p := p) q m)

  obtain ⟨H, instCR, instHA, E, gX, i, j, LE, ePts, gP, pP, 𝒥, sE, levelMap, incl, Q, proj, incl_proj,
      hFT, hFl, hff, hig, hiCl, hji, hjCl, hfix, hXaff, hXflat, hXlft, hLEcomm, hLEhom, hprim, hePts_mul, hePts_nat,
      hptsComm, hgP, hgconv, hggal, hpconv, hpcompat, hsEnat, hlev_surj, hlev_gen, hlev_sE, hmono, hses⟩ :=
    ModularCurve.JZeroNeronIdentityComponent.exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent
      p q hqp A hA N (fun m => hAff q N m) (fun m => hFlat q N m) (fun m => hLft q N m) (fun m => hSep q N m)
      t φ eK (fun m x hx => ((ht m x hx).2.1)) (fun m => (hc m).1) (fun m => (hc m).2.1) (fun m => (hc m).2.2.2.1)
      (fun m => (hc m).2.2.2.2.1) (fun m => (hc m).2.2.2.2.2)

  refine ⟨{ H := H, ff_finite := hff, genericPoints := gP, genericConv := hgconv, genericGalois := hggal,
            pFibrePoints := pP, pFibreConv := hpconv, pFibreGenericCompat := hpcompat,
            pointsComm := hptsComm, levelMap := levelMap, levelMap_surjective := hlev_surj,
            levelMap_genericPoints := fun m _ φ' => hlev_gen m φ' }, ?_⟩

  intro m 𝒥' e𝒥' he𝒥' _ inst hinst
  haveI := hiCl m; haveI := hjCl m; haveI := hXaff m; haveI := hXflat m; haveI := hXlft m
  haveI := hFT m; haveI := hFl m

  obtain ⟨ι, π, s, h1, h2, h3, h4, h5, -⟩ :=
    ModularCurve.JZeroNeronIdentityComponent.exists_retract_kernel_zsmul_pointsSheaf_of_eisensteinProjector
      p q N 𝒢 e he_add he ρ hρ m (hfin (p := p) q m) (t m) (φ m) (eK m)
      (fun x hx => (ht m x hx).2.1) ((hc m).1) ((hc m).2.1) ((hc m).2.2.1) ((hc m).2.2.2.1) ((hc m).2.2.2.2.2)
      (E m) (gX m) (i m) (j m) (LE m) (hig m) (hji m) (hfix m) (hLEcomm m) (hLEhom m) (hprim m)
      (H m) (hff m) (ePts m) (hePts_mul m) (hePts_nat m) 𝒥' e𝒥' he𝒥'
  exact S17.addEquiv_localizedModule_fppfCohomology_of_retract HeckeAlg (eisensteinMaximalIdeal p q) 𝒢 ((q : ℤ) ^ m) ρ
    inst hinst 𝒥' ⟨ι, π, s, h1, h2, h3, h4, h5⟩

end S_ModularCurve_JZeroNeronIdentityComponent_exists_jZeroTorsionHopfOrder_forall_nonempty_localizedModule_fppfCohomology_kernel_addEquiv
end P2MW
export P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_jZeroTorsionHopfOrder_forall_nonempty_localizedModule_fppfCohomology_kernel_addEquiv (solution)
