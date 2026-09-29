-- Prove2me | solution 1 for ModularCurve.frobenius_coordDet_eq_of_basis_rationalTateModule_jZero_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/c7392ace-eb78-579b-a9d0-2cac0f62bf11

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_HeckeInputsAll
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Theorems.Thm_ModularCurve_JZero_divisible
import Theorems.Thm_AlgebraicCurve_Pic0_nonempty_divisorialWeilPairingData
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_isCurveOver_laurentBaseChange_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_exists_frickeAlgEquiv_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_pair_heckeOperatorBar_eq_pair_fricke_heckeOperatorBar
import Theorems.Thm_ModularCurve_ofAlgAut_smul_ofAlgAut_smul_of_fricke
import Theorems.Thm_ModularCurve_galois_smul_ofAlgAut_smul_of_fricke
import Theorems.Thm_ValuationSubring_IsFrobeniusAt_apply_rootOfUnity_eq_pow_of_not_dvd
import Theorems.Thm_AlgebraicCurve_Pic0_exists_nsmul_eq
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_isSeparable
import Theorems.Thm_AlgebraicCurve_DivisorialWeilPairingData_toHom_injective_of_divisible
import Theorems.Thm_ModularCurve_smulCommClass_JZero_of_heckeOperatorsCommuteBar
import Theorems.Thm_ModularCurve_R2geoDet_coordDet_eq_algebraMap_of_similitude
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_frobenius_coordDet_eq_of_basis_rationalTateModule_jZero_of_ne
p2m_attr_erase "instance" "CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.CuspSpace.instNonempty"
p2m_attr_erase "instance" "ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.jqNModC_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk"
p2m_attr_erase "simp" "ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.tateMap_apply AlgebraicCurve.abelJacobiDiv_single"
p2m_attr_erase "simp" "AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec"

set_option autoImplicit false

namespace ModularCurve
p2m_export "ModularCurve" "heckeOperatorBar HeckeOperatorsCommuteBar heckeModuleBar heckeModuleBar_heckeGen_smul arithmeticGalois galois_smul_pic0_def modularFunctionFieldBar JZero qExpand jq modularFunctionFieldFull coeffEmb HeckeAlg heckeGen HeckeInputsAll tateHeckeRep RationalTateModule rationalGaloisRep rationalGaloisRep_apply rationalGaloisRep_tmul rationalHeckeRep rationalHeckeRep_apply rationalHeckeAlgebra JZero.divisible exists_transcendental_finiteDimensional_modularFunctionFieldBar isCurveOver_laurentBaseChange_modularFunctionFieldFull exists_frickeAlgEquiv_modularFunctionFieldBar pair_heckeOperatorBar_eq_pair_fricke_heckeOperatorBar ofAlgAut_smul_ofAlgAut_smul_of_fricke galois_smul_ofAlgAut_smul_of_fricke smulCommClass_JZero_of_heckeOperatorsCommuteBar R2geoDet.coordDet_eq_algebraMap_of_similitude"
namespace PEdge
p2m_open "ModularCurve"
variable (p : ℕ) (J : Type) [AddCommGroup J]

def Tors (k : ℕ) (x : J) : Prop := ((p ^ k : ℕ) : ℤ) • x = 0

def IsBiadditive (a : (k : ℕ) → J → J → ZMod (p ^ k)) : Prop :=
  (∀ (k : ℕ) (x x' y : J), Tors p J k x → Tors p J k x' → Tors p J k y →
      a k (x + x') y = a k x y + a k x' y) ∧
  (∀ (k : ℕ) (x y y' : J), Tors p J k x → Tors p J k y → Tors p J k y' →
      a k x (y + y') = a k x y + a k x y')

def IsCompatible (a : (k : ℕ) → J → J → ZMod (p ^ k)) : Prop :=
  ∀ (k : ℕ) (x y : J), Tors p J (k + 1) x → Tors p J (k + 1) y →
    ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k)) (a (k + 1) x y)
      = a k (((p : ℕ) : ℤ) • x) (((p : ℕ) : ℤ) • y)

def IsAnti (a : (k : ℕ) → J → J → ZMod (p ^ k)) : Prop :=
  ∀ (k : ℕ) (x y : J), Tors p J k x → Tors p J k y → a k y x = - a k x y

def IsNondegLeft (a : (k : ℕ) → J → J → ZMod (p ^ k)) : Prop :=
  ∀ (k : ℕ) (x : J), Tors p J k x → (∀ y : J, Tors p J k y → a k x y = 0) → x = 0

def IsAdjointPair (a : (k : ℕ) → J → J → ZMod (p ^ k)) {G G' : Type} [Monoid G] [Monoid G']
    [DistribMulAction G J] [DistribMulAction G' J] (g : G) (g' : G') : Prop :=
  ∀ (k : ℕ) (x y : J), Tors p J k x → Tors p J k y → a k (g • x) y = a k x (g' • y)

def IsSimilitude (a : (k : ℕ) → J → J → ZMod (p ^ k)) {G : Type} [Monoid G] [DistribMulAction G J]
    (g : G) (c : ℕ) : Prop :=
  ∀ (k : ℕ) (x y : J), Tors p J k x → Tors p J k y → a k (g • x) (g • y) = c • a k x y

def PDivisible : Prop :=
  ∀ (k : ℕ) (y : J), Tors p J k y → ∃ y' : J, ((p : ℕ) : ℤ) • y' = y
end ModularCurve.PEdge
noncomputable section
open scoped TensorProduct
namespace ModularCurve
p2m_export "ModularCurve" "heckeOperatorBar HeckeOperatorsCommuteBar heckeModuleBar heckeModuleBar_heckeGen_smul arithmeticGalois galois_smul_pic0_def modularFunctionFieldBar JZero qExpand jq modularFunctionFieldFull coeffEmb HeckeAlg heckeGen HeckeInputsAll tateHeckeRep RationalTateModule rationalGaloisRep rationalGaloisRep_apply rationalGaloisRep_tmul rationalHeckeRep rationalHeckeRep_apply rationalHeckeAlgebra JZero.divisible exists_transcendental_finiteDimensional_modularFunctionFieldBar isCurveOver_laurentBaseChange_modularFunctionFieldFull exists_frickeAlgEquiv_modularFunctionFieldBar pair_heckeOperatorBar_eq_pair_fricke_heckeOperatorBar ofAlgAut_smul_ofAlgAut_smul_of_fricke galois_smul_ofAlgAut_smul_of_fricke smulCommClass_JZero_of_heckeOperatorsCommuteBar R2geoDet.coordDet_eq_algebraMap_of_similitude"
namespace PEdge
p2m_open "ModularCurve"

section CompatSeq
variable (p : ℕ)

def compatSeq : Subring ((k : ℕ) → ZMod (p ^ k)) where
  carrier := {s | ∀ k : ℕ,
    ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k)) (s (k + 1)) = s k}
  mul_mem' {s t} hs ht := fun k => by rw [Pi.mul_apply, map_mul, hs k, ht k, Pi.mul_apply]
  one_mem' := fun k => by rw [Pi.one_apply, map_one, Pi.one_apply]
  add_mem' {s t} hs ht := fun k => by rw [Pi.add_apply, map_add, hs k, ht k, Pi.add_apply]
  zero_mem' := fun k => by rw [Pi.zero_apply, map_zero, Pi.zero_apply]
  neg_mem' {s} hs := fun k => by rw [Pi.neg_apply, map_neg, hs k, Pi.neg_apply]

def evalSeq (k : ℕ) : compatSeq p →+* ZMod (p ^ k) :=
  (Pi.evalRingHom (fun j : ℕ => ZMod (p ^ j)) k).comp (compatSeq p).subtype

theorem evalSeq_compat (k1 k2 : ℕ) (hk : k1 ≤ k2) :
    (ZMod.castHom (pow_dvd_pow p hk) (ZMod (p ^ k1))).comp (evalSeq p k2) = evalSeq p k1 := by
  induction k2, hk using Nat.le_induction with
  | base =>
    refine RingHom.ext fun s => ?_
    rw [RingHom.comp_apply, ZMod.castHom_apply, ZMod.cast_id]
  | succ k2 hk ih =>
    have hfac : ZMod.castHom (pow_dvd_pow p (Nat.le_succ_of_le hk)) (ZMod (p ^ k1))
        = (ZMod.castHom (pow_dvd_pow p hk) (ZMod (p ^ k1))).comp
            (ZMod.castHom (pow_dvd_pow p (Nat.le_succ k2)) (ZMod (p ^ k2))) :=
      RingHom.ext_zmod _ _
    have hstep : (ZMod.castHom (pow_dvd_pow p (Nat.le_succ k2)) (ZMod (p ^ k2))).comp
        (evalSeq p (k2 + 1)) = evalSeq p k2 :=
      RingHom.ext fun s => s.2 k2
    rw [hfac, RingHom.comp_assoc, hstep, ih]

def toPadicInt [Fact p.Prime] : compatSeq p →+* ℤ_[p] :=
  PadicInt.lift (evalSeq_compat p)

theorem toZModPow_toPadicInt [Fact p.Prime] (s : compatSeq p) (k : ℕ) :
    PadicInt.toZModPow k (toPadicInt p s) = (s : (j : ℕ) → ZMod (p ^ j)) k :=
  RingHom.congr_fun (PadicInt.lift_spec (evalSeq_compat p) k) s
end CompatSeq

section LevelAlgebra
variable {p : ℕ} {J : Type} [AddCommGroup J] {a : (k : ℕ) → J → J → ZMod (p ^ k)}
theorem tors_zero (k : ℕ) : Tors p J k (0 : J) := smul_zero _

theorem tors_neg {k : ℕ} {x : J} (hx : Tors p J k x) : Tors p J k (-x) := by
  unfold Tors at *
  rw [smul_neg, hx, neg_zero]

theorem tors_zsmul {k : ℕ} {x : J} (m : ℤ) (hx : Tors p J k x) : Tors p J k (m • x) := by
  unfold Tors at *
  rw [smul_comm, hx, smul_zero]

theorem level_zero_left (hbi : IsBiadditive p J a) (k : ℕ) {y : J} (hy : Tors p J k y) :
    a k 0 y = 0 := by
  have h := hbi.1 k 0 0 y (tors_zero k) (tors_zero k) hy
  rw [add_zero] at h
  have h2 : a k 0 y + a k 0 y = a k 0 y + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel h2

theorem level_zero_right (hbi : IsBiadditive p J a) (k : ℕ) {x : J} (hx : Tors p J k x) :
    a k x 0 = 0 := by
  have h := hbi.2 k x 0 0 hx (tors_zero k) (tors_zero k)
  rw [add_zero] at h
  have h2 : a k x 0 + a k x 0 = a k x 0 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel h2

theorem level_neg_left (hbi : IsBiadditive p J a) (k : ℕ) {x y : J} (hx : Tors p J k x)
    (hy : Tors p J k y) : a k (-x) y = - a k x y := by
  have h := hbi.1 k x (-x) y hx (tors_neg hx) hy
  rw [add_neg_cancel, level_zero_left hbi k hy] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem level_neg_right (hbi : IsBiadditive p J a) (k : ℕ) {x y : J} (hx : Tors p J k x)
    (hy : Tors p J k y) : a k x (-y) = - a k x y := by
  have h := hbi.2 k x y (-y) hx hy (tors_neg hy)
  rw [add_neg_cancel, level_zero_right hbi k hx] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem level_natCast_zsmul_left (hbi : IsBiadditive p J a) (k : ℕ) {x y : J} (hx : Tors p J k x)
    (hy : Tors p J k y) (m : ℕ) : a k ((m : ℤ) • x) y = m • a k x y := by
  induction m with
  | zero => rw [Nat.cast_zero, zero_smul, zero_smul, level_zero_left hbi k hy]
  | succ m ih =>
    rw [Nat.cast_succ, add_smul, one_smul, hbi.1 k _ _ y (tors_zsmul _ hx) hx hy, ih, succ_nsmul]

theorem level_natCast_zsmul_right (hbi : IsBiadditive p J a) (k : ℕ) {x y : J} (hx : Tors p J k x)
    (hy : Tors p J k y) (m : ℕ) : a k x ((m : ℤ) • y) = m • a k x y := by
  induction m with
  | zero => rw [Nat.cast_zero, zero_smul, zero_smul, level_zero_right hbi k hx]
  | succ m ih =>
    rw [Nat.cast_succ, add_smul, one_smul, hbi.2 k x _ _ hx (tors_zsmul _ hy) hy, ih, succ_nsmul]

theorem level_zsmul_left (hbi : IsBiadditive p J a) (k : ℕ) {x y : J} (hx : Tors p J k x)
    (hy : Tors p J k y) (m : ℤ) : a k (m • x) y = m • a k x y := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · rw [level_natCast_zsmul_left hbi k hx hy, natCast_zsmul]
  · rw [neg_smul, neg_smul, level_neg_left hbi k (tors_zsmul _ hx) hy,
      level_natCast_zsmul_left hbi k hx hy, natCast_zsmul]

theorem level_zsmul_right (hbi : IsBiadditive p J a) (k : ℕ) {x y : J} (hx : Tors p J k x)
    (hy : Tors p J k y) (m : ℤ) : a k x (m • y) = m • a k x y := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · rw [level_natCast_zsmul_right hbi k hx hy, natCast_zsmul]
  · rw [neg_smul, neg_smul, level_neg_right hbi k hx (tors_zsmul _ hy),
      level_natCast_zsmul_right hbi k hx hy, natCast_zsmul]
end LevelAlgebra

section LimForm
variable {p : ℕ} [Fact p.Prime] {J : Type} [AddCommGroup J]
variable (a : (k : ℕ) → J → J → ZMod (p ^ k)) (hbi : IsBiadditive p J a) (hco : IsCompatible p J a)

def seqOf (t t' : TateModule p J) : compatSeq p :=
  ⟨fun k => a k ((t : ℕ → J) k) ((t' : ℕ → J) k), fun k => by
    have h := hco k ((t : ℕ → J) (k + 1)) ((t' : ℕ → J) (k + 1))
      (TateModule.torsion t (k + 1)) (TateModule.torsion t' (k + 1))
    rw [TateModule.compat, TateModule.compat] at h
    exact h⟩

def limFun (t t' : TateModule p J) : ℤ_[p] :=
  toPadicInt p (seqOf a hco t t')

theorem toZModPow_limFun (t t' : TateModule p J) (k : ℕ) :
    PadicInt.toZModPow k (limFun a hco t t') = a k ((t : ℕ → J) k) ((t' : ℕ → J) k) :=
  toZModPow_toPadicInt p (seqOf a hco t t') k

include hbi

theorem limFun_add_left (t₁ t₂ t' : TateModule p J) :
    limFun a hco (t₁ + t₂) t' = limFun a hco t₁ t' + limFun a hco t₂ t' := by
  refine (PadicInt.ext_of_toZModPow).1 (fun k => ?_)
  rw [map_add, toZModPow_limFun, toZModPow_limFun, toZModPow_limFun, TateModule.coe_add,
    Pi.add_apply]
  exact hbi.1 k _ _ _ (TateModule.torsion t₁ k) (TateModule.torsion t₂ k) (TateModule.torsion t' k)

theorem limFun_add_right (t t₁ t₂ : TateModule p J) :
    limFun a hco t (t₁ + t₂) = limFun a hco t t₁ + limFun a hco t t₂ := by
  refine (PadicInt.ext_of_toZModPow).1 (fun k => ?_)
  rw [map_add, toZModPow_limFun, toZModPow_limFun, toZModPow_limFun, TateModule.coe_add,
    Pi.add_apply]
  exact hbi.2 k _ _ _ (TateModule.torsion t k) (TateModule.torsion t₁ k) (TateModule.torsion t₂ k)

theorem limFun_smul_left (c : ℤ_[p]) (t t' : TateModule p J) :
    limFun a hco (c • t) t' = c • limFun a hco t t' := by
  refine (PadicInt.ext_of_toZModPow).1 (fun k => ?_)
  rw [smul_eq_mul, map_mul, toZModPow_limFun, toZModPow_limFun, TateModule.smul_apply,
    level_zsmul_left hbi k (TateModule.torsion t k) (TateModule.torsion t' k),
    TateModule.toZModPow_eq_appr, natCast_zsmul, nsmul_eq_mul]

theorem limFun_smul_right (c : ℤ_[p]) (t t' : TateModule p J) :
    limFun a hco t (c • t') = c • limFun a hco t t' := by
  refine (PadicInt.ext_of_toZModPow).1 (fun k => ?_)
  rw [smul_eq_mul, map_mul, toZModPow_limFun, toZModPow_limFun, TateModule.smul_apply,
    level_zsmul_right hbi k (TateModule.torsion t k) (TateModule.torsion t' k),
    TateModule.toZModPow_eq_appr, natCast_zsmul, nsmul_eq_mul]

def limForm : TateModule p J →ₗ[ℤ_[p]] TateModule p J →ₗ[ℤ_[p]] ℤ_[p] :=
  LinearMap.mk₂ ℤ_[p] (limFun a hco) (limFun_add_left a hbi hco) (limFun_smul_left a hbi hco)
    (limFun_add_right a hbi hco) (limFun_smul_right a hbi hco)

theorem toZModPow_limForm (t t' : TateModule p J) (k : ℕ) :
    PadicInt.toZModPow k (limForm a hbi hco t t') = a k ((t : ℕ → J) k) ((t' : ℕ → J) k) :=
  toZModPow_limFun a hco t t' k

def ratForm : RationalTateModule p J →ₗ[ℚ_[p]] RationalTateModule p J →ₗ[ℚ_[p]] ℚ_[p] :=
  LinearMap.BilinForm.tmul (LinearMap.mul ℚ_[p] ℚ_[p]) (limForm a hbi hco)

theorem ratForm_tmul (q q' : ℚ_[p]) (t t' : TateModule p J) :
    ratForm a hbi hco (q ⊗ₜ t) (q' ⊗ₜ t')
      = q * q' * algebraMap ℤ_[p] ℚ_[p] (limForm a hbi hco t t') := by
  simp only [ratForm, LinearMap.BilinForm.tmul, LinearMap.BilinForm.tensorDistrib_tmul,
    LinearMap.mul_apply', Algebra.smul_def]
  ring

theorem limForm_rep_left {G G' : Type} [Monoid G] [Monoid G'] [DistribMulAction G J]
    [DistribMulAction G' J] {g : G} {g' : G'} (h : IsAdjointPair p J a g g')
    (t t' : TateModule p J) :
    limForm a hbi hco (TateModule.rep p J G g t) t'
      = limForm a hbi hco t (TateModule.rep p J G' g' t') := by
  refine (PadicInt.ext_of_toZModPow).1 (fun k => ?_)
  rw [toZModPow_limForm, toZModPow_limForm, TateModule.rep_apply, TateModule.rep_apply]
  exact h k _ _ (TateModule.torsion t k) (TateModule.torsion t' k)

theorem ratForm_rationalGaloisRep_left {G G' : Type} [Monoid G] [Monoid G'] [DistribMulAction G J]
    [DistribMulAction G' J] {g : G} {g' : G'} (h : IsAdjointPair p J a g g')
    (v w : RationalTateModule p J) :
    ratForm a hbi hco (rationalGaloisRep p J G g v) w
      = ratForm a hbi hco v (rationalGaloisRep p J G' g' w) := by
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | tmul q t =>
    induction w using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul q' t' =>
      rw [rationalGaloisRep_tmul, rationalGaloisRep_tmul, ratForm_tmul, ratForm_tmul,
        limForm_rep_left a hbi hco h]
    | add w₁ w₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | add v₁ v₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]

theorem limForm_rep_rep {G : Type} [Monoid G] [DistribMulAction G J] {g : G} {c : ℕ}
    (h : IsSimilitude p J a g c) (t t' : TateModule p J) :
    limForm a hbi hco (TateModule.rep p J G g t) (TateModule.rep p J G g t')
      = (c : ℤ_[p]) * limForm a hbi hco t t' := by
  refine (PadicInt.ext_of_toZModPow).1 (fun k => ?_)
  rw [map_mul, map_natCast, toZModPow_limForm, toZModPow_limForm, TateModule.rep_apply,
    TateModule.rep_apply, ← nsmul_eq_mul]
  exact h k _ _ (TateModule.torsion t k) (TateModule.torsion t' k)

theorem ratForm_rationalGaloisRep_rationalGaloisRep {G : Type} [Monoid G] [DistribMulAction G J]
    {g : G} {c : ℕ} (h : IsSimilitude p J a g c) (v w : RationalTateModule p J) :
    ratForm a hbi hco (rationalGaloisRep p J G g v) (rationalGaloisRep p J G g w)
      = (c : ℚ_[p]) • ratForm a hbi hco v w := by
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply, smul_zero]
  | tmul q t =>
    induction w using TensorProduct.induction_on with
    | zero => simp only [map_zero, smul_zero]
    | tmul q' t' =>
      rw [rationalGaloisRep_tmul, rationalGaloisRep_tmul, ratForm_tmul, ratForm_tmul,
        limForm_rep_rep a hbi hco h, map_mul, map_natCast, smul_eq_mul]
      ring
    | add w₁ w₂ h₁ h₂ => simp only [map_add, smul_add, h₁, h₂]
  | add v₁ v₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, smul_add, h₁, h₂]

theorem limForm_swap (h : IsAnti p J a) (t t' : TateModule p J) :
    limForm a hbi hco t' t = - limForm a hbi hco t t' := by
  refine (PadicInt.ext_of_toZModPow).1 (fun k => ?_)
  rw [map_neg, toZModPow_limForm, toZModPow_limForm]
  exact h k _ _ (TateModule.torsion t k) (TateModule.torsion t' k)

theorem ratForm_swap (h : IsAnti p J a) (v w : RationalTateModule p J) :
    ratForm a hbi hco w v = - ratForm a hbi hco v w := by
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply, neg_zero]
  | tmul q t =>
    induction w using TensorProduct.induction_on with
    | zero => simp only [map_zero, LinearMap.zero_apply, neg_zero]
    | tmul q' t' =>
      rw [ratForm_tmul, ratForm_tmul, limForm_swap a hbi hco h, map_neg]
      ring
    | add w₁ w₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, neg_add, h₁, h₂]
  | add v₁ v₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, neg_add, h₁, h₂]

theorem ratForm_self_eq_zero (h : IsAnti p J a) (v : RationalTateModule p J) :
    ratForm a hbi hco v v = 0 :=
  add_self_eq_zero.1 (eq_neg_iff_add_eq_zero.1 (ratForm_swap a hbi hco h v v))

omit [Fact p.Prime] hbi in

theorem exists_tateModule_apply_eq (hdiv : PDivisible p J) (k : ℕ) {y : J} (hy : Tors p J k y) :
    ∃ t : TateModule p J, (t : ℕ → J) k = y := by
  have hnext' : ∀ (n : ℕ) (m : Submodule.torsionBy ℤ J ((p ^ n : ℕ) : ℤ)),
      ∃ m' : Submodule.torsionBy ℤ J ((p ^ (n + 1) : ℕ) : ℤ), ((p : ℕ) : ℤ) • (m' : J) = m := by
    intro n m
    obtain ⟨y', hy'⟩ := hdiv n m ((Submodule.mem_torsionBy_iff _ _).1 m.2)
    refine ⟨⟨y', (Submodule.mem_torsionBy_iff _ _).2 ?_⟩, hy'⟩
    rw [pow_succ, Nat.cast_mul, mul_smul, hy']
    exact (Submodule.mem_torsionBy_iff _ _).1 m.2
  choose next hnext using hnext'
  refine ⟨⟨TateModule.liftFun next k ⟨y, (Submodule.mem_torsionBy_iff _ _).2 hy⟩,
    TateModule.liftFun_mem hnext k _⟩, ?_⟩
  show TateModule.liftFun next k _ k = y
  rw [TateModule.liftFun_of_le le_rfl, TateModule.coe_liftAux_congr (Nat.sub_self k)]
  rfl

theorem limForm_left_eq_zero (hnd : IsNondegLeft p J a) (hdiv : PDivisible p J) {t : TateModule p J}
    (h : ∀ t' : TateModule p J, limForm a hbi hco t t' = 0) : t = 0 := by
  refine Subtype.ext (funext fun k => ?_)
  rw [TateModule.coe_zero, Pi.zero_apply]
  refine hnd k _ (TateModule.torsion t k) (fun y hy => ?_)
  obtain ⟨t', ht'⟩ := exists_tateModule_apply_eq hdiv k hy
  have h1 := congrArg (PadicInt.toZModPow k) (h t')
  rw [map_zero, toZModPow_limForm, ht'] at h1
  exact h1

theorem ratForm_left_nondeg (hnd : IsNondegLeft p J a) (hdiv : PDivisible p J)
    (v : RationalTateModule p J) (h : ∀ w : RationalTateModule p J, ratForm a hbi hco v w = 0) :
    v = 0 := by
  obtain ⟨⟨t, s⟩, hs⟩ :=
    IsLocalizedModule.surj (nonZeroDivisors ℤ_[p]) (TensorProduct.mk ℤ_[p] ℚ_[p] (TateModule p J) 1) v
  rw [Submonoid.smul_def, TensorProduct.mk_apply, ← algebraMap_smul ℚ_[p] (s : ℤ_[p]) v] at hs

  have hne : algebraMap ℤ_[p] ℚ_[p] (s : ℤ_[p]) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective ℤ_[p] ℚ_[p])).2 (nonZeroDivisors.coe_ne_zero s)
  have ht : t = 0 := by
    refine limForm_left_eq_zero a hbi hco hnd hdiv (fun t' => ?_)
    have h2 : ratForm a hbi hco (algebraMap ℤ_[p] ℚ_[p] (s : ℤ_[p]) • v) ((1 : ℚ_[p]) ⊗ₜ t') = 0 := by
      rw [LinearMap.map_smul, LinearMap.smul_apply, h, smul_zero]
    rw [hs, ratForm_tmul, one_mul, one_mul] at h2
    exact (map_eq_zero_iff _ (IsFractionRing.injective ℤ_[p] ℚ_[p])).1 h2
  rw [ht, TensorProduct.tmul_zero] at hs
  rw [← inv_smul_smul₀ hne v, hs, smul_zero]
end LimForm
section BalAssembly
variable (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module HeckeAlg J]

theorem rationalHeckeRep_eq_rationalGaloisRep (t : HeckeAlg) :
    rationalHeckeRep p J t = rationalGaloisRep p J HeckeAlg t :=
  rfl

theorem rationalHeckeRep_selfAdjoint
    (B : RationalTateModule p J →ₗ[ℚ_[p]] RationalTateModule p J →ₗ[ℚ_[p]] ℚ_[p])
    (hgen : ∀ (ℓ : Nat.Primes) (v w : RationalTateModule p J),
      B (rationalHeckeRep p J (heckeGen ℓ) v) w = B v (rationalHeckeRep p J (heckeGen ℓ) w))
    (t : HeckeAlg) (v w : RationalTateModule p J) :
    B (rationalHeckeRep p J t v) w = B v (rationalHeckeRep p J t w) := by
  have hgen' : ∀ (ℓ : Nat.Primes) (v w : RationalTateModule p J),
      B (rationalHeckeRep p J (MvPolynomial.X ℓ) v) w = B v (rationalHeckeRep p J (MvPolynomial.X ℓ) w) := hgen
  induction t using MvPolynomial.induction_on generalizing v w with
  | C a =>
    rw [← MvPolynomial.algebraMap_eq, eq_intCast, map_intCast, Module.End.intCast_apply,
      Module.End.intCast_apply, map_zsmul, LinearMap.smul_apply, map_zsmul]
  | add f g hf hg =>
    rw [map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, LinearMap.add_apply, map_add, hf, hg]
  | mul_X f ℓ hf =>

    have hc : rationalHeckeRep p J f * rationalHeckeRep p J (MvPolynomial.X ℓ)
        = rationalHeckeRep p J (MvPolynomial.X ℓ) * rationalHeckeRep p J f := by
      rw [← map_mul, ← map_mul, mul_comm]
    rw [map_mul, hc, Module.End.mul_apply, Module.End.mul_apply, hgen' ℓ, hf]
    exact congrArg (B v) (LinearMap.congr_fun hc w)

theorem smul_left_eq_smul_right_of_heckeGen
    (B : RationalTateModule p J →ₗ[ℚ_[p]] RationalTateModule p J →ₗ[ℚ_[p]] ℚ_[p])
    (hgen : ∀ (ℓ : Nat.Primes) (v w : RationalTateModule p J),
      B (rationalHeckeRep p J (heckeGen ℓ) v) w = B v (rationalHeckeRep p J (heckeGen ℓ) w))
    (a : rationalHeckeAlgebra p J) (v w : RationalTateModule p J) :
    B (a • v) w = B v (a • w) := by
  change B ((a : Module.End ℚ_[p] (RationalTateModule p J)) v) w
    = B v ((a : Module.End ℚ_[p] (RationalTateModule p J)) w)
  obtain ⟨f, hf⟩ := a
  simp only

  have hMC : IsMulCommutative (rationalHeckeAlgebra p J) :=
    Algebra.isMulCommutative_adjoin ℚ_[p] (by
      rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
      rw [← map_mul, ← map_mul, mul_comm])
  induction hf using Algebra.adjoin_induction generalizing v w with
  | mem x hx =>
    obtain ⟨t, rfl⟩ := hx
    exact rationalHeckeRep_selfAdjoint p J B hgen t v w
  | algebraMap r =>
    rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul, LinearMap.smul_apply, map_smul]
  | add x y hx hy ihx ihy =>
    rw [LinearMap.add_apply, LinearMap.add_apply, map_add, LinearMap.add_apply, map_add, ihx, ihy]
  | mul x y hx hy ihx ihy =>
    have hc : x * y = y * x :=
      congrArg Subtype.val (hMC.is_comm.comm (⟨x, hx⟩ : rationalHeckeAlgebra p J) ⟨y, hy⟩)
    conv_rhs => rw [hc]
    rw [Module.End.mul_apply, Module.End.mul_apply, ihx, ihy]
end BalAssembly

section Core
p2m_open "AlgebraicCurve P2MW.S_ModularCurve_frobenius_coordDet_eq_of_basis_rationalTateModule_jZero_of_ne.AlgebraicCurve ModularCurve P2MW.S_ModularCurve_frobenius_coordDet_eq_of_basis_rationalTateModule_jZero_of_ne.ModularCurve"

theorem pDivisible_jZero (N p : ℕ) [NeZero N] [Fact p.Prime] : PDivisible p (JZero N) := by
  intro k y _
  obtain ⟨y', hy'⟩ := ModularCurve.JZero.divisible N p (Nat.Prime.ne_zero Fact.out) y
  exact ⟨y', by rw [natCast_zsmul, hy']⟩

theorem exists_form_of_tower (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hin : ModularCurve.HeckeInputsAll N) (hcomm : ModularCurve.HeckeOperatorsCommuteBar N)
    (a : (k : ℕ) → JZero N → JZero N → ZMod (p ^ k))
    (hbi : IsBiadditive p (JZero N) a) (hco : IsCompatible p (JZero N) a)
    (hanti : IsAnti p (JZero N) a) (hndl : IsNondegLeft p (JZero N) a)
    (hadj : letI := ModularCurve.heckeModuleBar N
      ∀ ℓ : Nat.Primes, IsAdjointPair p (JZero N) a (heckeGen ℓ) (heckeGen ℓ))
    (hsim : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      ∀ A' : ValuationSubring (AlgebraicClosure ℚ), A'.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A'.IsFrobeniusAt σ ℓ →
          IsSimilitude p (JZero N) a σ ℓ) :
    letI := ModularCurve.heckeModuleBar N
    ∃ B : ModularCurve.RationalTateModule p (ModularCurve.JZero N) →ₗ[ℚ_[p]]
          ModularCurve.RationalTateModule p (ModularCurve.JZero N) →ₗ[ℚ_[p]] ℚ_[p],
      (∀ (a : ModularCurve.rationalHeckeAlgebra p (ModularCurve.JZero N))
         (v w : ModularCurve.RationalTateModule p (ModularCurve.JZero N)),
          B (a • v) w = B v (a • w))
      ∧ (∀ v, B v v = 0)
      ∧ (∀ v, (∀ w, B v w = 0) → v = 0)
      ∧ (∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
          ∀ A' : ValuationSubring (AlgebraicClosure ℚ), A'.LiesOverPrime ℓ →
            ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A'.IsFrobeniusAt σ ℓ →
              ∀ v w, B (ModularCurve.rationalGaloisRep p (ModularCurve.JZero N)
                      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ v)
                  (ModularCurve.rationalGaloisRep p (ModularCurve.JZero N)
                      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ w)
                = (ℓ : ℚ_[p]) • B v w) := by
  have _ := hin
  have _ := hcomm
  letI := ModularCurve.heckeModuleBar N
  refine ⟨ratForm a hbi hco, ?_, ratForm_self_eq_zero a hbi hco hanti,
    fun v hv => ratForm_left_nondeg a hbi hco hndl (pDivisible_jZero N p) v hv, ?_⟩
  · refine smul_left_eq_smul_right_of_heckeGen p (JZero N) (ratForm a hbi hco) (fun ℓ v w => ?_)
    rw [rationalHeckeRep_eq_rationalGaloisRep]
    exact ratForm_rationalGaloisRep_left a hbi hco (hadj ℓ) v w
  · intro ℓ hℓ hℓNp A' hA' σ hσ v w
    exact ratForm_rationalGaloisRep_rationalGaloisRep a hbi hco (hsim ℓ hℓ hℓNp A' hA' σ hσ) v w
end Core
end ModularCurve.PEdge
namespace PedgeLevel
variable {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
theorem exists_isPrimitiveRoot_prime (p : ℕ) [Fact p.Prime] :
    ∃ ζ : K, IsPrimitiveRoot ζ p := by
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).ne_zero⟩
  have hdeg : (Polynomial.cyclotomic p K).degree ≠ 0 := by
    have h1 : 0 < (Polynomial.cyclotomic p K).degree := by
      rw [Polynomial.degree_cyclotomic]
      exact_mod_cast Nat.pos_of_ne_zero (Nat.totient_pos.mpr (Fact.out (p := p.Prime)).pos).ne'
    exact h1.ne'
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic p K) hdeg
  exact ⟨ζ, (Polynomial.isRoot_cyclotomic_iff).mp hζ⟩

variable (K) in
def zetaTower (p : ℕ) [Fact p.Prime] : ℕ → K
  | 0 => 1
  | 1 => Classical.choose (exists_isPrimitiveRoot_prime (K := K) p)
  | (k + 2) => Classical.choose (IsAlgClosed.exists_pow_nat_eq
      (zetaTower p (k + 1)) (Fact.out (p := p.Prime)).pos)

variable (p : ℕ) [Fact p.Prime]
theorem zetaTower_one_spec : IsPrimitiveRoot (zetaTower K p 1) p :=
  Classical.choose_spec (exists_isPrimitiveRoot_prime (K := K) p)

theorem zetaTower_succ_pow (k : ℕ) : zetaTower K p (k + 2) ^ p = zetaTower K p (k + 1) :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq
    (zetaTower K p (k + 1)) (Fact.out (p := p.Prime)).pos)

theorem isPrimitiveRoot_zetaTower : ∀ k : ℕ, IsPrimitiveRoot (zetaTower K p k) (p ^ k)
  | 0 => by simp only [zetaTower, pow_zero]; exact IsPrimitiveRoot.one
  | 1 => by simpa only [pow_one] using zetaTower_one_spec (K := K) p
  | (k + 2) => by
      have ih := isPrimitiveRoot_zetaTower (k + 1)
      have hpow := zetaTower_succ_pow (K := K) p k
      set ζ := zetaTower K p (k + 2) with hζdef
      have hp : p.Prime := Fact.out

      have h1 : ζ ^ p ^ (k + 2) = 1 := by
        have h2 : ζ ^ p ^ (k + 2) = (ζ ^ p) ^ p ^ (k + 1) := by
          rw [← pow_mul, ← pow_succ']
        rw [h2, hpow]
        exact ih.pow_eq_one
      refine ⟨h1, fun {l} hl => ?_⟩

      have hl1 : zetaTower K p (k + 1) ^ l = 1 := by
        rw [← hpow, ← pow_mul, mul_comm, pow_mul, hl, one_pow]
      have hd1 : p ^ (k + 1) ∣ l := ih.dvd_of_pow_eq_one l hl1
      obtain ⟨m, hm⟩ := hd1

      set ξ := ζ ^ p ^ (k + 1) with hξdef
      have hξp : ξ ^ p = 1 := by
        rw [hξdef, ← pow_mul, ← pow_succ]
        exact h1
      have hξne : ξ ≠ 1 := by
        intro hξ1
        have h3 : zetaTower K p (k + 1) ^ p ^ k = 1 := by
          have h4 : zetaTower K p (k + 1) ^ p ^ k = (ζ ^ p) ^ p ^ k := by rw [hpow]
          rw [h4, ← pow_mul, ← pow_succ', ← hξdef] at *
          exact hξ1
        have h5 : p ^ (k + 1) ∣ p ^ k := ih.dvd_of_pow_eq_one _ h3
        have h6 := Nat.le_of_dvd (pow_pos hp.pos k) h5
        have h7 := Nat.pow_lt_pow_succ hp.one_lt (n := k)
        omega
      have hξm : ξ ^ m = 1 := by
        rw [hξdef, ← pow_mul, ← hm, hl]

      have hordξ : orderOf ξ = p := by
        have hdvd : orderOf ξ ∣ p := orderOf_dvd_of_pow_eq_one hξp
        rcases (Nat.Prime.eq_one_or_self_of_dvd hp _ hdvd) with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) hξne
        · exact h
      have hpm : p ∣ m := hordξ ▸ orderOf_dvd_of_pow_eq_one hξm
      obtain ⟨m', hm'⟩ := hpm
      exact ⟨m', by rw [hm, hm', pow_succ]; ring⟩

def zetaUnit (k : ℕ) : Kˣ :=
  ((isPrimitiveRoot_zetaTower (K := K) p k).isUnit (pow_ne_zero k (Fact.out (p := p.Prime)).ne_zero)).unit

theorem isPrimitiveRoot_zetaUnit (k : ℕ) : IsPrimitiveRoot (zetaUnit (K := K) p k) (p ^ k) :=
  (isPrimitiveRoot_zetaTower (K := K) p k).isUnit_unit
    (pow_ne_zero k (Fact.out (p := p.Prime)).ne_zero)

def dlogAt (k : ℕ) (u : Kˣ) (hu : u ^ (p ^ k) = 1) : ZMod (p ^ k) := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k (Fact.out (p := p.Prime)).ne_zero⟩
  exact ((isPrimitiveRoot_zetaUnit (K := K) p k).zmodEquivZPowers).symm ⟨u, by
    rw [(isPrimitiveRoot_zetaUnit (K := K) p k).zpowers_eq]
    exact (mem_rootsOfUnity _ u).mpr hu⟩

theorem zetaUnit_pow_dlogAt (k : ℕ) (u : Kˣ) (hu : u ^ (p ^ k) = 1) :
    (zetaUnit (K := K) p k) ^ (dlogAt (K := K) p k u hu).val = u := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k (Fact.out (p := p.Prime)).ne_zero⟩
  have hζ := isPrimitiveRoot_zetaUnit (K := K) p k
  have hmem : u ∈ Subgroup.zpowers (zetaUnit (K := K) p k) := by
    rw [hζ.zpowers_eq]
    exact (mem_rootsOfUnity _ u).mpr hu
  have h1 : hζ.zmodEquivZPowers (dlogAt (K := K) p k u hu) = ⟨u, hmem⟩ :=
    hζ.zmodEquivZPowers.apply_symm_apply ⟨u, hmem⟩
  have h2 := congrArg Subtype.val
    (IsPrimitiveRoot.zmodEquivZPowers_apply_coe_nat hζ (dlogAt (K := K) p k u hu).val)
  rw [ZMod.natCast_val, ZMod.cast_id] at h2
  rw [h1] at h2
  exact h2.symm

theorem dlogAt_unique (k : ℕ) (u : Kˣ) (hu : u ^ (p ^ k) = 1) (a : ZMod (p ^ k))
    (ha : (zetaUnit (K := K) p k) ^ a.val = u) : a = dlogAt (K := K) p k u hu := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k (Fact.out (p := p.Prime)).ne_zero⟩
  have hζ := isPrimitiveRoot_zetaUnit (K := K) p k
  refine hζ.zmodEquivZPowers.injective (Subtype.ext ?_)
  have ha' := congrArg Subtype.val (IsPrimitiveRoot.zmodEquivZPowers_apply_coe_nat hζ a.val)
  have hd' := congrArg Subtype.val
    (IsPrimitiveRoot.zmodEquivZPowers_apply_coe_nat hζ (dlogAt (K := K) p k u hu).val)
  rw [ZMod.natCast_val, ZMod.cast_id] at ha' hd'
  rw [ha', hd']
  show (zetaUnit (K := K) p k) ^ a.val = (zetaUnit (K := K) p k) ^ (dlogAt (K := K) p k u hu).val
  rw [ha, zetaUnit_pow_dlogAt (K := K) p k u hu]

theorem zetaUnit_pow_val_add (k : ℕ) (a b : ZMod (p ^ k)) :
    (zetaUnit (K := K) p k) ^ (a + b).val
      = (zetaUnit (K := K) p k) ^ a.val * (zetaUnit (K := K) p k) ^ b.val := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k (Fact.out (p := p.Prime)).ne_zero⟩
  have hζ := isPrimitiveRoot_zetaUnit (K := K) p k
  rw [← pow_add, ZMod.val_add]
  conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) (p ^ k)]
  rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]

theorem dlogAt_mul (k : ℕ) (u v : Kˣ) (hu : u ^ (p ^ k) = 1) (hv : v ^ (p ^ k) = 1) :
    dlogAt (K := K) p k (u * v) (by rw [mul_pow, hu, hv, one_mul])
      = dlogAt (K := K) p k u hu + dlogAt (K := K) p k v hv := by
  refine (dlogAt_unique (K := K) p k _ _ _ ?_).symm
  rw [zetaUnit_pow_val_add, zetaUnit_pow_dlogAt, zetaUnit_pow_dlogAt]

theorem dlogAt_one (k : ℕ) : dlogAt (K := K) p k 1 (one_pow _) = 0 := by
  refine (dlogAt_unique (K := K) p k _ _ _ ?_).symm
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k (Fact.out (p := p.Prime)).ne_zero⟩
  rw [ZMod.val_zero, pow_zero]

theorem zetaUnit_succ_pow (k : ℕ) :
    (zetaUnit (K := K) p (k + 1)) ^ p = zetaUnit (K := K) p k := by
  refine Units.ext ?_
  have h1 : ((zetaUnit (K := K) p (k + 1) : Kˣ) : K) = zetaTower K p (k + 1) := rfl
  have h2 : ((zetaUnit (K := K) p k : Kˣ) : K) = zetaTower K p k := rfl
  rw [Units.val_pow_eq_pow_val, h1, h2]
  cases k with
  | zero =>

      have := (zetaTower_one_spec (K := K) p).pow_eq_one
      simpa [zetaTower] using this
  | succ k' => exact zetaTower_succ_pow (K := K) p k'

theorem dlogAt_pow_p (k : ℕ) (u : Kˣ) (hu : u ^ (p ^ (k + 1)) = 1) :
    dlogAt (K := K) p k (u ^ p)
        (by rw [← pow_mul, ← pow_succ']; exact hu)
      = ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k))
          (dlogAt (K := K) p (k + 1) u hu) := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k (Fact.out (p := p.Prime)).ne_zero⟩
  haveI : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero (k + 1) (Fact.out (p := p.Prime)).ne_zero⟩
  refine (dlogAt_unique (K := K) p k _ _ _ ?_).symm
  set a := dlogAt (K := K) p (k + 1) u hu with hadef

  have hc : ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k)) a
      = ((a.val : ℕ) : ZMod (p ^ k)) := by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  rw [hc, ZMod.val_natCast]

  have hζk := isPrimitiveRoot_zetaUnit (K := K) p k
  have h1 : (zetaUnit (K := K) p k) ^ (a.val % p ^ k) = (zetaUnit (K := K) p k) ^ a.val := by
    conv_rhs => rw [← Nat.mod_add_div a.val (p ^ k), pow_add, pow_mul, hζk.pow_eq_one, one_pow,
      mul_one]
  rw [h1, ← zetaUnit_succ_pow (K := K) p k, ← pow_mul, mul_comm p a.val, pow_mul,
    zetaUnit_pow_dlogAt (K := K) p (k + 1) u hu]

theorem dlogAt_congr (k : ℕ) {u v : Kˣ} (h : u = v) (hu : u ^ (p ^ k) = 1) (hv : v ^ (p ^ k) = 1) :
    dlogAt (K := K) p k u hu = dlogAt (K := K) p k v hv := by
  subst h
  rfl

theorem dlogAt_inv (k : ℕ) (u : Kˣ) (hu : u ^ (p ^ k) = 1) :
    dlogAt (K := K) p k u⁻¹ (by rw [inv_pow, hu, inv_one]) = - dlogAt (K := K) p k u hu := by
  have h := dlogAt_mul (K := K) p k u u⁻¹ hu (by rw [inv_pow, hu, inv_one])
  rw [dlogAt_congr (K := K) p k (mul_inv_cancel u) _ (one_pow _), dlogAt_one] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem dlogAt_pow (k : ℕ) (u : Kˣ) (hu : u ^ (p ^ k) = 1) (m : ℕ) :
    dlogAt (K := K) p k (u ^ m) (by rw [← pow_mul, mul_comm, pow_mul, hu, one_pow]) = m • dlogAt (K := K) p k u hu := by
  induction m with
  | zero =>
    rw [zero_nsmul]
    exact (dlogAt_congr (K := K) p k (pow_zero u) _ (one_pow _)).trans (dlogAt_one (K := K) p k)
  | succ m ih =>
    rw [succ_nsmul, ← ih]
    exact (dlogAt_congr (K := K) p k (pow_succ u m) _ _).trans (dlogAt_mul (K := K) p k _ _ _ hu)
end PedgeLevel
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor HasPrincipalDivisors Pic Pic0 Pic0.mk Pic0.torsion Pic0.mem_torsion SemilinearAut SemilinearAut.baseAut SemilinearAut.ofAlgAut SemilinearAut.baseAut_ofAlgAut SemilinearAut.smulValuationSubringEquiv SemilinearAut.smul_toValuationSubring SemilinearAut.ord_smul SemilinearAut.smulResidueRingEquiv SemilinearAut.smulResidueRingEquiv_algebraMap SemilinearAut.divisor_smul_def SemilinearAut.divisor_smul_apply_smul SemilinearAut.divisor_smul_apply SemilinearAut.pic0_smul_mk SemilinearAut.smul_zsmul SemilinearAut.coe_torsion_smul IsCurveOver DivisorialWeilPairingData DivisorialWeilPairingData.toChar_apply WeilDatum Place.IsRational Divisor.evalFun Divisor.evalFun_natCast_smul_divisor Pic0.nonempty_divisorialWeilPairingData Pic0.exists_nsmul_eq isCurveOver_of_transcendental_of_isSeparable DivisorialWeilPairingData.toHom_injective_of_divisible"
namespace WeilDatum
p2m_export "AlgebraicCurve.WeilDatum" "degZeroLeft degZeroRight classLeft classRight coe_classLeft coe_classRight ord_f₁_eq_zero_of_mem_support ord_f₂_eq_zero_of_mem_support rational_of_mem_support_left rational_of_mem_support_right galSmul pairing symm f₁ ord_f₁ D₁ f₁_ne_zero mk disjoint ord_f₂ D₂ f₂_ne_zero f₂ rational"
p2m_open "AlgebraicCurve.WeilDatum AlgebraicCurve"
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private def _root_.AlgebraicCurve.WeilDatum.pedgeScale {m k : ℕ} (d : WeilDatum K F (m * k)) : WeilDatum K F m where
  D₁ := (k : ℤ) • d.D₁
  D₂ := (k : ℤ) • d.D₂
  f₁ := d.f₁
  f₂ := d.f₂
  f₁_ne_zero := d.f₁_ne_zero
  f₂_ne_zero := d.f₂_ne_zero
  ord_f₁ v := by rw [d.ord_f₁ v, Finsupp.smul_apply, smul_eq_mul, Nat.cast_mul, mul_assoc]
  ord_f₂ v := by rw [d.ord_f₂ v, Finsupp.smul_apply, smul_eq_mul, Nat.cast_mul, mul_assoc]
  disjoint v := by
    rcases d.disjoint v with h | h
    · exact Or.inl (by rw [Finsupp.smul_apply, smul_eq_mul, h, mul_zero])
    · exact Or.inr (by rw [Finsupp.smul_apply, smul_eq_mul, h, mul_zero])
  rational v hv := by
    refine d.rational v ?_
    rcases hv with h | h
    · exact Or.inl (fun h0 => h (by rw [Finsupp.smul_apply, smul_eq_mul, h0, mul_zero]))
    · exact Or.inr (fun h0 => h (by rw [Finsupp.smul_apply, smul_eq_mul, h0, mul_zero]))

p2m_export "AlgebraicCurve.WeilDatum" "pedgeScale"
theorem pedgeScale_pairing {m k : ℕ} (d : WeilDatum K F (m * k)) : d.pedgeScale.pairing = d.pairing ^ k := by
  show Divisor.evalFun d.f₁ ((k : ℤ) • d.D₂) / Divisor.evalFun d.f₂ ((k : ℤ) • d.D₁)
    = (Divisor.evalFun d.f₁ d.D₂ / Divisor.evalFun d.f₂ d.D₁) ^ k
  rw [Divisor.evalFun_natCast_smul_divisor, Divisor.evalFun_natCast_smul_divisor, div_pow]

variable [HasPrincipalDivisors K F]
theorem coe_classLeft_pedgeScale {m k : ℕ} [NeZero m] [NeZero (m * k)] (d : WeilDatum K F (m * k)) :
    (d.pedgeScale.classLeft : Pic0 K F) = (k : ℤ) • (d.classLeft : Pic0 K F) := by
  show QuotientAddGroup.mk d.pedgeScale.degZeroLeft = (k : ℤ) • QuotientAddGroup.mk d.degZeroLeft
  exact (congrArg QuotientAddGroup.mk
      (Subtype.ext rfl : d.pedgeScale.degZeroLeft = (k : ℤ) • d.degZeroLeft)).trans
    (QuotientAddGroup.mk_zsmul _ _ _)

theorem coe_classRight_pedgeScale {m k : ℕ} [NeZero m] [NeZero (m * k)] (d : WeilDatum K F (m * k)) :
    (d.pedgeScale.classRight : Pic0 K F) = (k : ℤ) • (d.classRight : Pic0 K F) := by
  show QuotientAddGroup.mk d.pedgeScale.degZeroRight = (k : ℤ) • QuotientAddGroup.mk d.degZeroRight
  exact (congrArg QuotientAddGroup.mk
      (Subtype.ext rfl : d.pedgeScale.degZeroRight = (k : ℤ) • d.degZeroRight)).trans
    (QuotientAddGroup.mk_zsmul _ _ _)
end AlgebraicCurve.WeilDatum
section
p2m_open "AlgebraicCurve P2MW.S_ModularCurve_frobenius_coordDet_eq_of_basis_rationalTateModule_jZero_of_ne.AlgebraicCurve"
namespace ModularCurve
p2m_export "ModularCurve" "heckeOperatorBar HeckeOperatorsCommuteBar heckeModuleBar heckeModuleBar_heckeGen_smul arithmeticGalois galois_smul_pic0_def modularFunctionFieldBar JZero qExpand jq modularFunctionFieldFull coeffEmb HeckeAlg heckeGen HeckeInputsAll tateHeckeRep RationalTateModule rationalGaloisRep rationalGaloisRep_apply rationalGaloisRep_tmul rationalHeckeRep rationalHeckeRep_apply rationalHeckeAlgebra JZero.divisible exists_transcendental_finiteDimensional_modularFunctionFieldBar isCurveOver_laurentBaseChange_modularFunctionFieldFull exists_frickeAlgEquiv_modularFunctionFieldBar pair_heckeOperatorBar_eq_pair_fricke_heckeOperatorBar ofAlgAut_smul_ofAlgAut_smul_of_fricke galois_smul_ofAlgAut_smul_of_fricke smulCommClass_JZero_of_heckeOperatorsCommuteBar R2geoDet.coordDet_eq_algebraMap_of_similitude"
namespace PEdge
p2m_open "ModularCurve"
variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]

theorem pair_eq_pair_pow_of_coe_eq_smul {m k : ℕ} [NeZero m] [NeZero (m * k)]
    (e : DivisorialWeilPairingData K F m) (e' : DivisorialWeilPairingData K F (m * k))
    (x y : Pic0.torsion K F (m * k)) (X Y : Pic0.torsion K F m)
    (hX : (X : Pic0 K F) = (k : ℤ) • (x : Pic0 K F)) (hY : (Y : Pic0 K F) = (k : ℤ) • (y : Pic0 K F)) :
    e.pair X Y = e'.pair x y ^ k := by
  obtain ⟨d, hdx, hdy⟩ := e'.exists_datum x y
  have hX' : X = d.pedgeScale.classLeft :=
    Subtype.ext (by rw [hX, WeilDatum.coe_classLeft_pedgeScale, hdx])
  have hY' : Y = d.pedgeScale.classRight :=
    Subtype.ext (by rw [hY, WeilDatum.coe_classRight_pedgeScale, hdy])
  rw [hX', hY', e.compatible, ← hdx, ← hdy, e'.compatible, WeilDatum.pedgeScale_pairing]
end ModularCurve.PEdge
namespace ModularCurve
p2m_export "ModularCurve" "heckeOperatorBar HeckeOperatorsCommuteBar heckeModuleBar heckeModuleBar_heckeGen_smul arithmeticGalois galois_smul_pic0_def modularFunctionFieldBar JZero qExpand jq modularFunctionFieldFull coeffEmb HeckeAlg heckeGen HeckeInputsAll tateHeckeRep RationalTateModule rationalGaloisRep rationalGaloisRep_apply rationalGaloisRep_tmul rationalHeckeRep rationalHeckeRep_apply rationalHeckeAlgebra JZero.divisible exists_transcendental_finiteDimensional_modularFunctionFieldBar isCurveOver_laurentBaseChange_modularFunctionFieldFull exists_frickeAlgEquiv_modularFunctionFieldBar pair_heckeOperatorBar_eq_pair_fricke_heckeOperatorBar ofAlgAut_smul_ofAlgAut_smul_of_fricke galois_smul_ofAlgAut_smul_of_fricke smulCommClass_JZero_of_heckeOperatorsCommuteBar R2geoDet.coordDet_eq_algebraMap_of_similitude"
namespace PEdge
p2m_open "ModularCurve"
variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]

theorem pair_eq_pair_pow_of_coe_eq_smul' {m k n' : ℕ} [NeZero m] [NeZero n'] (hn : n' = m * k)
    (e : DivisorialWeilPairingData K F m) (e' : DivisorialWeilPairingData K F n')
    (x y : Pic0.torsion K F n') (X Y : Pic0.torsion K F m)
    (hX : (X : Pic0 K F) = (k : ℤ) • (x : Pic0 K F)) (hY : (Y : Pic0 K F) = (k : ℤ) • (y : Pic0 K F)) :
    e.pair X Y = e'.pair x y ^ k := by
  subst hn
  exact pair_eq_pair_pow_of_coe_eq_smul e e' x y X Y hX hY

theorem pair_pow_eq_one' {n : ℕ} [NeZero n] (e : DivisorialWeilPairingData K F n) (x y : Pic0.torsion K F n) :
    e.pair x y ^ n = 1 := by
  have h : ∀ m : ℕ, e.pair x y ^ m = e.pair (m • x) y := by
    intro m
    induction m with
    | zero => rw [pow_zero, zero_nsmul, e.pair_zero_left]
    | succ m ih => rw [pow_succ, ih, succ_nsmul, e.pair_add_left]
  have hn : n • x = 0 :=
    Subtype.ext (show n • (x : Pic0 K F) = 0 by rw [← natCast_zsmul]; exact Pic0.mem_torsion.mp x.2)
  rw [h, hn, e.pair_zero_left]

def pairUnit {n : ℕ} [NeZero n] (e : DivisorialWeilPairingData K F n) (x y : Pic0.torsion K F n) : Kˣ :=
  Units.mk0 (e.pair x y) (e.pair_ne_zero x y)

theorem val_pairUnit {n : ℕ} [NeZero n] (e : DivisorialWeilPairingData K F n) (x y : Pic0.torsion K F n) :
    (pairUnit e x y : K) = e.pair x y :=
  rfl

theorem pairUnit_pow_eq_one {n : ℕ} [NeZero n] (e : DivisorialWeilPairingData K F n) (x y : Pic0.torsion K F n) :
    pairUnit e x y ^ n = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, val_pairUnit, pair_pow_eq_one', Units.val_one])

omit [HasPrincipalDivisors K F] in

theorem smul_mem_torsion_of_distribMulAction {G : Type} [Monoid G] [DistribMulAction G (Pic0 K F)] (g : G) {n : ℕ}
    {x : Pic0 K F} (hx : x ∈ Pic0.torsion K F n) : g • x ∈ Pic0.torsion K F n := by
  rw [Pic0.mem_torsion] at hx ⊢
  show (n : ℤ) • DistribSMul.toAddMonoidHom (Pic0 K F) g x = 0
  rw [← map_zsmul, hx, map_zero]
end ModularCurve.PEdge
end

namespace ModularCurve
p2m_export "ModularCurve" "heckeOperatorBar HeckeOperatorsCommuteBar heckeModuleBar heckeModuleBar_heckeGen_smul arithmeticGalois galois_smul_pic0_def modularFunctionFieldBar JZero qExpand jq modularFunctionFieldFull coeffEmb HeckeAlg heckeGen HeckeInputsAll tateHeckeRep RationalTateModule rationalGaloisRep rationalGaloisRep_apply rationalGaloisRep_tmul rationalHeckeRep rationalHeckeRep_apply rationalHeckeAlgebra JZero.divisible exists_transcendental_finiteDimensional_modularFunctionFieldBar isCurveOver_laurentBaseChange_modularFunctionFieldFull exists_frickeAlgEquiv_modularFunctionFieldBar pair_heckeOperatorBar_eq_pair_fricke_heckeOperatorBar ofAlgAut_smul_ofAlgAut_smul_of_fricke galois_smul_ofAlgAut_smul_of_fricke smulCommClass_JZero_of_heckeOperatorsCommuteBar R2geoDet.coordDet_eq_algebraMap_of_similitude"
namespace PEdge
p2m_open "ModularCurve"
section Tower
p2m_open "AlgebraicCurve P2MW.S_ModularCurve_frobenius_coordDet_eq_of_basis_rationalTateModule_jZero_of_ne.AlgebraicCurve ModularCurve P2MW.S_ModularCurve_frobenius_coordDet_eq_of_basis_rationalTateModule_jZero_of_ne.ModularCurve"
variable (N p : ℕ) [NeZero N] [hp : Fact p.Prime]
scoped instance instIsCurveOver_modularFunctionFieldBar (M : ℕ) [NeZero M] :
    IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar M) :=
  ModularCurve.isCurveOver_laurentBaseChange_modularFunctionFieldFull (AlgebraicClosure ℚ) M

scoped instance instNeZeroPrimePow (k : ℕ) : NeZero (p ^ k) := ⟨pow_ne_zero k hp.out.ne_zero⟩

scoped instance instNeZeroMulPrimes (M : ℕ) [NeZero M] (ℓ : Nat.Primes) : NeZero (M * ℓ) :=
  ⟨mul_ne_zero (NeZero.ne M) ℓ.2.ne_zero⟩

def ePair (M : ℕ) [NeZero M] (n : ℕ) [NeZero n] :
    DivisorialWeilPairingData (AlgebraicClosure ℚ) (modularFunctionFieldBar M) n :=
  (AlgebraicCurve.Pic0.nonempty_divisorialWeilPairingData (AlgebraicClosure ℚ) (modularFunctionFieldBar M)
    (ModularCurve.exists_transcendental_finiteDimensional_modularFunctionFieldBar M) n).some

def frickeAut : modularFunctionFieldBar N ≃ₐ[AlgebraicClosure ℚ] modularFunctionFieldBar N :=
  (ModularCurve.exists_frickeAlgEquiv_modularFunctionFieldBar N).choose

theorem frickeAut_spec :
    ∀ (a b : ℕ) [NeZero a] [NeZero b], a * b = N →
      ∀ x : modularFunctionFieldBar N,
        (x : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ a jq) →
          ((frickeAut N x : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
            = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ b jq) :=
  (ModularCurve.exists_frickeAlgEquiv_modularFunctionFieldBar N).choose_spec

open scoped Classical in

def twistTower (k : ℕ) (x y : JZero N) : ZMod (p ^ k) :=
  if h : x ∈ Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (p ^ k)
      ∧ y ∈ Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (p ^ k) then
    PedgeLevel.dlogAt p k
      (pairUnit (ePair N (p ^ k)) ⟨x, h.1⟩ (SemilinearAut.ofAlgAut (frickeAut N) • ⟨y, h.2⟩))
      (pairUnit_pow_eq_one _ _ _)
  else 0

variable {N p}

theorem twistTower_coe (k : ℕ)
    (X Y : Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (p ^ k)) :
    twistTower N p k X Y
      = PedgeLevel.dlogAt p k (pairUnit (ePair N (p ^ k)) X (SemilinearAut.ofAlgAut (frickeAut N) • Y))
          (pairUnit_pow_eq_one _ _ _) := by
  unfold twistTower
  exact dif_pos (⟨X.2, Y.2⟩ : (X : JZero N) ∈ _ ∧ (Y : JZero N) ∈ _)

theorem twistTower_add_left (k : ℕ)
    (X X' Y : Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (p ^ k)) :
    twistTower N p k ((X + X' : Pic0.torsion _ _ _) : JZero N) Y = twistTower N p k X Y + twistTower N p k X' Y := by
  rw [twistTower_coe, twistTower_coe, twistTower_coe]
  refine (PedgeLevel.dlogAt_congr p k ?_ _ _).trans (PedgeLevel.dlogAt_mul p k _ _ _ _)
  exact Units.ext ((ePair N (p ^ k)).pair_add_left X X' (SemilinearAut.ofAlgAut (frickeAut N) • Y))

theorem twistTower_add_right (k : ℕ)
    (X Y Y' : Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (p ^ k)) :
    twistTower N p k X ((Y + Y' : Pic0.torsion _ _ _) : JZero N) = twistTower N p k X Y + twistTower N p k X Y' := by
  rw [twistTower_coe, twistTower_coe, twistTower_coe]
  refine (PedgeLevel.dlogAt_congr p k ?_ _ _).trans (PedgeLevel.dlogAt_mul p k _ _ _ _)
  have hw : SemilinearAut.ofAlgAut (frickeAut N) • (Y + Y')
      = SemilinearAut.ofAlgAut (frickeAut N) • Y + SemilinearAut.ofAlgAut (frickeAut N) • Y' := smul_add _ _ _
  exact Units.ext ((congrArg ((ePair N (p ^ k)).pair X) hw).trans ((ePair N (p ^ k)).pair_add_right X _ _))

omit [NeZero N] hp in

theorem zsmul_mem_torsion_of_succ (k : ℕ)
    (X : Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (p ^ (k + 1))) :
    ((p : ℕ) : ℤ) • (X : JZero N) ∈ Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (p ^ k) := by
  rw [Pic0.mem_torsion, smul_smul, ← Nat.cast_mul, ← pow_succ]
  exact Pic0.mem_torsion.mp X.2

theorem twistTower_compat (k : ℕ)
    (X Y : Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (p ^ (k + 1))) :
    ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k)) (twistTower N p (k + 1) X Y)
      = twistTower N p k
          ((⟨_, zsmul_mem_torsion_of_succ k X⟩ : Pic0.torsion _ _ (p ^ k)) : JZero N)
          ((⟨_, zsmul_mem_torsion_of_succ k Y⟩ : Pic0.torsion _ _ (p ^ k)) : JZero N) := by
  rw [twistTower_coe, twistTower_coe, ← PedgeLevel.dlogAt_pow_p p k]
  refine PedgeLevel.dlogAt_congr p k (Units.ext ?_) _ _
  rw [Units.val_pow_eq_pow_val, val_pairUnit, val_pairUnit]
  symm
  refine pair_eq_pair_pow_of_coe_eq_smul' (pow_succ p k) (ePair N (p ^ k)) (ePair N (p ^ (k + 1))) X _ _ _ rfl ?_
  show SemilinearAut.ofAlgAut (frickeAut N) • (((p : ℕ) : ℤ) • (Y : JZero N))
    = ((p : ℕ) : ℤ) • (SemilinearAut.ofAlgAut (frickeAut N) • (Y : JZero N))
  exact SemilinearAut.smul_zsmul _ _ _

theorem fricke_smul_fricke_smul_torsion {n : ℕ} [NeZero n]
    (Y : Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) n) :
    SemilinearAut.ofAlgAut (frickeAut N) • (SemilinearAut.ofAlgAut (frickeAut N) • Y) = Y :=
  Subtype.ext (ModularCurve.ofAlgAut_smul_ofAlgAut_smul_of_fricke N (frickeAut N) (frickeAut_spec N) (Y : JZero N))

variable (hgal : ∀ {n : ℕ} [NeZero n]
  (e : DivisorialWeilPairingData (AlgebraicClosure ℚ) (modularFunctionFieldBar N) n)
  (g : SemilinearAut (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
  (x y : Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) n),
    e.pair (g • x) (g • y) = SemilinearAut.baseAut g (e.pair x y))

include hgal in
theorem twistTower_swap (k : ℕ) (X Y : Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (p ^ k)) :
    twistTower N p k Y X = - twistTower N p k X Y := by
  rw [twistTower_coe, twistTower_coe, ← PedgeLevel.dlogAt_inv p k]
  refine PedgeLevel.dlogAt_congr p k (Units.ext ?_) _ _
  rw [Units.val_inv_eq_inv_val, val_pairUnit, val_pairUnit]
  have hww := fricke_smul_fricke_smul_torsion (N := N) Y
  calc (ePair N (p ^ k)).pair Y (SemilinearAut.ofAlgAut (frickeAut N) • X)
      = (ePair N (p ^ k)).pair
          (SemilinearAut.ofAlgAut (frickeAut N) • (SemilinearAut.ofAlgAut (frickeAut N) • Y))
          (SemilinearAut.ofAlgAut (frickeAut N) • X) := by rw [hww]
    _ = (ePair N (p ^ k)).pair (SemilinearAut.ofAlgAut (frickeAut N) • Y) X := by
        rw [hgal, SemilinearAut.baseAut_ofAlgAut]
        rfl
    _ = ((ePair N (p ^ k)).pair X (SemilinearAut.ofAlgAut (frickeAut N) • Y))⁻¹ :=
        (ePair N (p ^ k)).pair_swap_eq_inv X _

theorem pair_galois_fricke' {n : ℕ} [NeZero n]
    (e : DivisorialWeilPairingData (AlgebraicClosure ℚ) (modularFunctionFieldBar N) n)
    (hgal1 : ∀ (g : SemilinearAut (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
      (x y : Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) n),
        e.pair (g • x) (g • y) = SemilinearAut.baseAut g (e.pair x y))
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (x y τx wy wτy : Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) n)
    (hτx : (τx : JZero N) = τ • (x : JZero N))
    (hwy : (wy : JZero N) = SemilinearAut.ofAlgAut (frickeAut N) • (y : JZero N))
    (hwτy : (wτy : JZero N) = SemilinearAut.ofAlgAut (frickeAut N) • (τ • (y : JZero N))) :
    e.pair τx wτy = τ (e.pair x wy) := by
  have h1 : τx = arithmeticGalois (modularFunctionFieldFull N) τ • x :=
    Subtype.ext (by rw [SemilinearAut.coe_torsion_smul, hτx, galois_smul_pic0_def])
  have h2 : wτy = arithmeticGalois (modularFunctionFieldFull N) τ • wy :=
    Subtype.ext (by
      rw [SemilinearAut.coe_torsion_smul, hwτy, hwy,
        ← ModularCurve.galois_smul_ofAlgAut_smul_of_fricke N (frickeAut N) (frickeAut_spec N), galois_smul_pic0_def])
  rw [h1, h2, hgal1]
  rfl

include hgal in
theorem twistTower_frob {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓNp : ℓ ≠ p)
    (A' : ValuationSubring (AlgebraicClosure ℚ)) (hA' : A'.LiesOverPrime ℓ)
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hτ : A'.IsFrobeniusAt τ ℓ) (k : ℕ)
    (X Y : Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (p ^ k)) :
    twistTower N p k (τ • (X : JZero N)) (τ • (Y : JZero N)) = ℓ • twistTower N p k X Y := by
  have hndvd : ¬ ℓ ∣ p ^ k := fun h => hℓNp ((Nat.prime_dvd_prime_iff_eq hℓ hp.out).mp (hℓ.dvd_of_dvd_pow h))
  have hτX := smul_mem_torsion_of_distribMulAction τ X.2
  have hτY := smul_mem_torsion_of_distribMulAction τ Y.2
  rw [show τ • (X : JZero N) = ((⟨_, hτX⟩ : Pic0.torsion _ _ (p ^ k)) : JZero N) from rfl,
    show τ • (Y : JZero N) = ((⟨_, hτY⟩ : Pic0.torsion _ _ (p ^ k)) : JZero N) from rfl,
    twistTower_coe, twistTower_coe, ← PedgeLevel.dlogAt_pow p k]
  refine PedgeLevel.dlogAt_congr p k (Units.ext ?_) _ _
  rw [Units.val_pow_eq_pow_val, val_pairUnit, val_pairUnit,
    pair_galois_fricke' (ePair N (p ^ k)) (hgal _) τ X Y ⟨_, hτX⟩ (SemilinearAut.ofAlgAut (frickeAut N) • Y)
      (SemilinearAut.ofAlgAut (frickeAut N) • ⟨_, hτY⟩) rfl rfl rfl]
  exact ValuationSubring.IsFrobeniusAt.apply_rootOfUnity_eq_pow_of_not_dvd hℓ A' hA' hτ hndvd _
    (pair_pow_eq_one' _ _ _)

theorem twistTower_hecke (hcomm : ModularCurve.HeckeOperatorsCommuteBar N) (ℓ : Nat.Primes) (k : ℕ)
    (X Y : Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (p ^ k)) :
    letI := ModularCurve.heckeModuleBar N
    twistTower N p k (heckeGen ℓ • (X : JZero N)) Y = twistTower N p k X (heckeGen ℓ • (Y : JZero N)) := by
  letI := ModularCurve.heckeModuleBar N
  have hTX := smul_mem_torsion_of_distribMulAction (heckeGen ℓ) X.2
  have hTY := smul_mem_torsion_of_distribMulAction (heckeGen ℓ) Y.2
  rw [show heckeGen ℓ • (X : JZero N) = ((⟨_, hTX⟩ : Pic0.torsion _ _ (p ^ k)) : JZero N) from rfl,
    show heckeGen ℓ • (Y : JZero N) = ((⟨_, hTY⟩ : Pic0.torsion _ _ (p ^ k)) : JZero N) from rfl,
    twistTower_coe, twistTower_coe]
  refine PedgeLevel.dlogAt_congr p k (Units.ext ?_) _ _
  rw [val_pairUnit, val_pairUnit]
  exact ModularCurve.pair_heckeOperatorBar_eq_pair_fricke_heckeOperatorBar N ℓ (p ^ k)
    (ePair N (p ^ k)) (frickeAut N) (frickeAut_spec N) X Y ⟨_, hTX⟩
    (SemilinearAut.ofAlgAut (frickeAut N) • Y) (SemilinearAut.ofAlgAut (frickeAut N) • ⟨_, hTY⟩)
    (ModularCurve.heckeModuleBar_heckeGen_smul hcomm ℓ X) rfl
    (by
      show SemilinearAut.ofAlgAut (frickeAut N) • (heckeGen ℓ • (Y : JZero N))
        = SemilinearAut.ofAlgAut (frickeAut N) • heckeOperatorBar N ℓ (Y : JZero N)
      rw [ModularCurve.heckeModuleBar_heckeGen_smul hcomm ℓ])

variable (hnd : ∀ {n : ℕ} [NeZero n]
  (e : DivisorialWeilPairingData (AlgebraicClosure ℚ) (modularFunctionFieldBar N) n)
  (x : Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) n),
    (∀ y : Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) n, e.pair x y = 1) → x = 0)

include hnd in
theorem twistTower_left_eq_zero (k : ℕ) (X : Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (p ^ k))
    (h : ∀ Y : Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (p ^ k), twistTower N p k X Y = 0) :
    X = 0 := by
  refine hnd (ePair N (p ^ k)) X (fun Y => ?_)
  have h0 := h (SemilinearAut.ofAlgAut (frickeAut N) • Y)
  rw [twistTower_coe, fricke_smul_fricke_smul_torsion] at h0
  have hU : pairUnit (ePair N (p ^ k)) X Y = 1 := by
    rw [← PedgeLevel.zetaUnit_pow_dlogAt p k (pairUnit (ePair N (p ^ k)) X Y) (pairUnit_pow_eq_one _ _ _), h0,
      ZMod.val_zero, pow_zero]
  exact (congrArg Units.val hU).trans Units.val_one

variable (N p)
theorem twistTower_isBiadditive : IsBiadditive p (JZero N) (twistTower N p) :=
  ⟨fun k x x' y hx hx' hy =>
      twistTower_add_left k ⟨x, Pic0.mem_torsion.mpr hx⟩ ⟨x', Pic0.mem_torsion.mpr hx'⟩ ⟨y, Pic0.mem_torsion.mpr hy⟩,
    fun k x y y' hx hy hy' =>
      twistTower_add_right k ⟨x, Pic0.mem_torsion.mpr hx⟩ ⟨y, Pic0.mem_torsion.mpr hy⟩ ⟨y', Pic0.mem_torsion.mpr hy'⟩⟩

theorem twistTower_isCompatible : IsCompatible p (JZero N) (twistTower N p) :=
  fun k x y hx hy => twistTower_compat k ⟨x, Pic0.mem_torsion.mpr hx⟩ ⟨y, Pic0.mem_torsion.mpr hy⟩

include hgal in
theorem twistTower_isAnti : IsAnti p (JZero N) (twistTower N p) :=
  fun k x y hx hy => twistTower_swap hgal k ⟨x, Pic0.mem_torsion.mpr hx⟩ ⟨y, Pic0.mem_torsion.mpr hy⟩

include hnd in
theorem twistTower_isNondegLeft : IsNondegLeft p (JZero N) (twistTower N p) :=
  fun k x hx h => congrArg Subtype.val
    (twistTower_left_eq_zero hnd k ⟨x, Pic0.mem_torsion.mpr hx⟩ (fun Y => h Y (Pic0.mem_torsion.mp Y.2)))

theorem twistTower_isAdjointPair (hcomm : ModularCurve.HeckeOperatorsCommuteBar N) (ℓ : Nat.Primes) :
    letI := ModularCurve.heckeModuleBar N
    IsAdjointPair p (JZero N) (twistTower N p) (heckeGen ℓ) (heckeGen ℓ) := by
  letI := ModularCurve.heckeModuleBar N
  intro k x y hx hy
  exact twistTower_hecke hcomm ℓ k ⟨x, Pic0.mem_torsion.mpr hx⟩ ⟨y, Pic0.mem_torsion.mpr hy⟩

include hgal in
theorem twistTower_isSimilitude {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓNp : ℓ ≠ p)
    (A' : ValuationSubring (AlgebraicClosure ℚ)) (hA' : A'.LiesOverPrime ℓ)
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hτ : A'.IsFrobeniusAt τ ℓ) :
    IsSimilitude p (JZero N) (twistTower N p) τ ℓ :=
  fun k x y hx hy => twistTower_frob hgal hℓ hℓNp A' hA' τ hτ k ⟨x, Pic0.mem_torsion.mpr hx⟩ ⟨y, Pic0.mem_torsion.mpr hy⟩

include hgal hnd in
theorem exists_form_of_hgal_hnd (hin : ModularCurve.HeckeInputsAll N) (hcomm : ModularCurve.HeckeOperatorsCommuteBar N) :
    letI := ModularCurve.heckeModuleBar N
    ∃ B : ModularCurve.RationalTateModule p (ModularCurve.JZero N) →ₗ[ℚ_[p]]
          ModularCurve.RationalTateModule p (ModularCurve.JZero N) →ₗ[ℚ_[p]] ℚ_[p],
      (∀ (a : ModularCurve.rationalHeckeAlgebra p (ModularCurve.JZero N))
         (v w : ModularCurve.RationalTateModule p (ModularCurve.JZero N)),
          B (a • v) w = B v (a • w))
      ∧ (∀ v, B v v = 0)
      ∧ (∀ v, (∀ w, B v w = 0) → v = 0)
      ∧ (∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
          ∀ A' : ValuationSubring (AlgebraicClosure ℚ), A'.LiesOverPrime ℓ →
            ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A'.IsFrobeniusAt σ ℓ →
              ∀ v w, B (ModularCurve.rationalGaloisRep p (ModularCurve.JZero N)
                      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ v)
                  (ModularCurve.rationalGaloisRep p (ModularCurve.JZero N)
                      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ w)
                = (ℓ : ℚ_[p]) • B v w) :=
  exists_form_of_tower N p hin hcomm (twistTower N p) (twistTower_isBiadditive N p) (twistTower_isCompatible N p)
    (twistTower_isAnti N p hgal) (twistTower_isNondegLeft N p hnd)
    (fun ℓ => twistTower_isAdjointPair N p hcomm ℓ)
    (fun _ hℓ hℓNp A' hA' σ hσ => twistTower_isSimilitude N p hgal hℓ hℓNp A' hA' σ hσ)
end Tower
end ModularCurve.PEdge
p2m_reactivate "P2MW.S_ModularCurve_frobenius_coordDet_eq_of_basis_rationalTateModule_jZero_of_ne.ModularCurve P2MW.S_ModularCurve_frobenius_coordDet_eq_of_basis_rationalTateModule_jZero_of_ne.ModularCurve.PEdge"
p2m_reactivate "P2MW.S_ModularCurve_frobenius_coordDet_eq_of_basis_rationalTateModule_jZero_of_ne.ModularCurve"

section
open IsLocalRing
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor HasPrincipalDivisors Pic Pic0 Pic0.mk Pic0.torsion Pic0.mem_torsion SemilinearAut SemilinearAut.baseAut SemilinearAut.ofAlgAut SemilinearAut.baseAut_ofAlgAut SemilinearAut.smulValuationSubringEquiv SemilinearAut.smul_toValuationSubring SemilinearAut.ord_smul SemilinearAut.smulResidueRingEquiv SemilinearAut.smulResidueRingEquiv_algebraMap SemilinearAut.divisor_smul_def SemilinearAut.divisor_smul_apply_smul SemilinearAut.divisor_smul_apply SemilinearAut.pic0_smul_mk SemilinearAut.smul_zsmul SemilinearAut.coe_torsion_smul IsCurveOver DivisorialWeilPairingData DivisorialWeilPairingData.toChar_apply WeilDatum Place.IsRational Divisor.evalFun Divisor.evalFun_natCast_smul_divisor Pic0.nonempty_divisorialWeilPairingData Pic0.exists_nsmul_eq isCurveOver_of_transcendental_of_isSeparable DivisorialWeilPairingData.toHom_injective_of_divisible"
p2m_open "AlgebraicCurve"
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField smul_toValuationSubring ord_smul toValuationSubring mk IsRational algebraMap_residueField_injective evalAt algebraMap_evalAt mem_toValuationSubring_of_ord_nonneg_alt"
p2m_open "AlgebraicCurve.Place"
variable (g : SemilinearAut K F) (v : Place K F)

theorem mem_smul_toValuationSubring_iff_semi (f : F) :
    g • f ∈ (g • v).toValuationSubring ↔ f ∈ v.toValuationSubring := by
  rw [SemilinearAut.smul_toValuationSubring]
  constructor
  · intro h
    have h1 := (ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem
      (g := g) (S := v.toValuationSubring) (x := g • f)).mp h
    rwa [inv_smul_smul] at h1
  · exact fun h => ValuationSubring.smul_mem_pointwise_smul g f v.toValuationSubring h

theorem isRational_smul_semi (hv : v.IsRational) : (g • v).IsRational := by
  intro x
  obtain ⟨a, ha⟩ := hv ((SemilinearAut.smulResidueRingEquiv g v).symm x)
  refine ⟨SemilinearAut.baseAut g a, ?_⟩
  have h1 := congrArg (SemilinearAut.smulResidueRingEquiv g v) ha
  rwa [SemilinearAut.smulResidueRingEquiv_algebraMap, RingEquiv.apply_symm_apply] at h1

theorem residue_smul_semi {f : F} (hf : f ∈ v.toValuationSubring) :
    residue (g • v).toValuationSubring
        (⟨g • f, (mem_smul_toValuationSubring_iff_semi g v f).mpr hf⟩ :
          (g • v).toValuationSubring)
      = SemilinearAut.smulResidueRingEquiv g v (residue v.toValuationSubring ⟨f, hf⟩) := by
  show _ = IsLocalRing.ResidueField.mapEquiv
      (SemilinearAut.smulValuationSubringEquiv g v.toValuationSubring)
      (residue v.toValuationSubring ⟨f, hf⟩)
  rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  exact congrArg _ (Subtype.ext rfl)

theorem evalAt_smul_semi (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    (g • v).evalAt (g • f) = SemilinearAut.baseAut g (v.evalAt f) := by
  have hv' : (g • v).IsRational := isRational_smul_semi g v hv
  have hmem : g • f ∈ (g • v).toValuationSubring :=
    (mem_smul_toValuationSubring_iff_semi g v f).mpr hf
  apply (g • v).algebraMap_residueField_injective
  rw [(g • v).algebraMap_evalAt hv' hmem, residue_smul_semi g v hf,
    ← v.algebraMap_evalAt hv hf, SemilinearAut.smulResidueRingEquiv_algebraMap]
end Place
p2m_reactivate "P2MW.S_ModularCurve_frobenius_coordDet_eq_of_basis_rationalTateModule_jZero_of_ne.ModularCurve P2MW.S_ModularCurve_frobenius_coordDet_eq_of_basis_rationalTateModule_jZero_of_ne.ModularCurve.PEdge"

namespace Divisor
p2m_export "AlgebraicCurve.Divisor" "degree smul_def smul_apply evalFun evalFun_natCast_smul_divisor"
p2m_open "AlgebraicCurve.Divisor"
variable (g : SemilinearAut K F)

theorem evalFun_smul_semi {f : F} (D : Divisor K F)
    (hrat : ∀ v ∈ D.support, Place.IsRational v)
    (hmem : ∀ v ∈ D.support, f ∈ v.toValuationSubring) :
    evalFun (g • f) (g • D) = SemilinearAut.baseAut g (evalFun f D) := by
  classical
  calc evalFun (g • f) (g • D)
      = (g • D).prod fun v n => v.evalAt (g • f) ^ n := rfl
    _ = D.prod fun v n => (g • v).evalAt (g • f) ^ n := by
        rw [SemilinearAut.divisor_smul_def,
          Finsupp.prod_mapDomain_index_inj (MulAction.injective g)]
    _ = D.prod fun v n => (SemilinearAut.baseAut g (v.evalAt f)) ^ n :=
        Finsupp.prod_congr fun v hv => by
          rw [Place.evalAt_smul_semi g v (hrat v hv) (hmem v hv)]
    _ = SemilinearAut.baseAut g (D.prod fun v n => v.evalAt f ^ n) := by
        rw [Finsupp.prod, Finsupp.prod, map_prod]
        exact Finset.prod_congr rfl fun v _ => (map_zpow₀ _ _ _).symm
    _ = SemilinearAut.baseAut g (evalFun f D) := rfl
end Divisor
p2m_reactivate "P2MW.S_ModularCurve_frobenius_coordDet_eq_of_basis_rationalTateModule_jZero_of_ne.ModularCurve P2MW.S_ModularCurve_frobenius_coordDet_eq_of_basis_rationalTateModule_jZero_of_ne.ModularCurve.PEdge"

namespace WeilDatum
p2m_export "AlgebraicCurve.WeilDatum" "degZeroLeft degZeroRight classLeft classRight coe_classLeft coe_classRight ord_f₁_eq_zero_of_mem_support ord_f₂_eq_zero_of_mem_support rational_of_mem_support_left rational_of_mem_support_right galSmul pairing symm f₁ ord_f₁ D₁ f₁_ne_zero mk disjoint ord_f₂ D₂ f₂_ne_zero f₂ rational"
p2m_open "AlgebraicCurve.WeilDatum"
variable {n : ℕ} (g : SemilinearAut K F)

private def _root_.AlgebraicCurve.WeilDatum.galSmulSemi (d : WeilDatum K F n) : WeilDatum K F n where
  D₁ := g • d.D₁
  D₂ := g • d.D₂
  f₁ := g • d.f₁
  f₂ := g • d.f₂
  f₁_ne_zero := fun h => d.f₁_ne_zero (by
    have h1 := congrArg (fun z => g⁻¹ • z) h
    simpa [inv_smul_smul] using h1)
  f₂_ne_zero := fun h => d.f₂_ne_zero (by
    have h1 := congrArg (fun z => g⁻¹ • z) h
    simpa [inv_smul_smul] using h1)
  ord_f₁ := by
    intro v
    rw [show v = g • (g⁻¹ • v) from (smul_inv_smul g v).symm, SemilinearAut.ord_smul,
      SemilinearAut.divisor_smul_apply_smul]
    exact d.ord_f₁ (g⁻¹ • v)
  ord_f₂ := by
    intro v
    rw [show v = g • (g⁻¹ • v) from (smul_inv_smul g v).symm, SemilinearAut.ord_smul,
      SemilinearAut.divisor_smul_apply_smul]
    exact d.ord_f₂ (g⁻¹ • v)
  disjoint := by
    intro v
    rw [SemilinearAut.divisor_smul_apply, SemilinearAut.divisor_smul_apply]
    exact d.disjoint (g⁻¹ • v)
  rational := by
    intro v hv
    rw [SemilinearAut.divisor_smul_apply, SemilinearAut.divisor_smul_apply] at hv
    have h1 : (g⁻¹ • v).IsRational := d.rational (g⁻¹ • v) hv
    have h2 := Place.isRational_smul_semi g (g⁻¹ • v) h1
    rwa [smul_inv_smul] at h2

p2m_export "AlgebraicCurve.WeilDatum" "galSmulSemi"

theorem galSmulSemi_pairing (d : WeilDatum K F n) :
    (d.galSmulSemi g).pairing = SemilinearAut.baseAut g d.pairing := by
  show Divisor.evalFun (g • d.f₁) (g • d.D₂) / Divisor.evalFun (g • d.f₂) (g • d.D₁) = _
  rw [Divisor.evalFun_smul_semi g d.D₂ (fun v hv => d.rational_of_mem_support_right hv)
      (fun v hv => v.mem_toValuationSubring_of_ord_nonneg_alt d.f₁_ne_zero
        (d.ord_f₁_eq_zero_of_mem_support hv).ge),
    Divisor.evalFun_smul_semi g d.D₁ (fun v hv => d.rational_of_mem_support_left hv)
      (fun v hv => v.mem_toValuationSubring_of_ord_nonneg_alt d.f₂_ne_zero
        (d.ord_f₂_eq_zero_of_mem_support hv).ge)]
  exact (map_div₀ _ _ _).symm

variable [NeZero n] [HasPrincipalDivisors K F]

theorem coe_classLeft_galSmulSemi (d : WeilDatum K F n) :
    ((d.galSmulSemi g).classLeft : Pic0 K F) = g • (d.classLeft : Pic0 K F) := by
  rw [coe_classLeft, coe_classLeft, SemilinearAut.pic0_smul_mk]
  exact congrArg Pic0.mk (Subtype.ext rfl)

theorem coe_classRight_galSmulSemi (d : WeilDatum K F n) :
    ((d.galSmulSemi g).classRight : Pic0 K F) = g • (d.classRight : Pic0 K F) := by
  rw [coe_classRight, coe_classRight, SemilinearAut.pic0_smul_mk]
  exact congrArg Pic0.mk (Subtype.ext rfl)

theorem classLeft_galSmulSemi (d : WeilDatum K F n) :
    (d.galSmulSemi g).classLeft = g • d.classLeft :=
  Subtype.ext (by
    rw [coe_classLeft_galSmulSemi, SemilinearAut.coe_torsion_smul])

theorem classRight_galSmulSemi (d : WeilDatum K F n) :
    (d.galSmulSemi g).classRight = g • d.classRight :=
  Subtype.ext (by
    rw [coe_classRight_galSmulSemi, SemilinearAut.coe_torsion_smul])
end WeilDatum
p2m_reactivate "P2MW.S_ModularCurve_frobenius_coordDet_eq_of_basis_rationalTateModule_jZero_of_ne.ModularCurve P2MW.S_ModularCurve_frobenius_coordDet_eq_of_basis_rationalTateModule_jZero_of_ne.ModularCurve.PEdge"

namespace DivisorialWeilPairingData
p2m_export "AlgebraicCurve.DivisorialWeilPairingData" "exists_datum pair_ne_zero pair_add_left pair_zero_left pair_swap_eq_inv pair_add_right pair_pow_eq_one toChar toChar_apply toHom mk compatible pair toHom_injective_of_divisible"
p2m_open "AlgebraicCurve.DivisorialWeilPairingData"
variable {n : ℕ} [NeZero n] [HasPrincipalDivisors K F]

theorem pair_smul_semilinear (e : DivisorialWeilPairingData K F n)
    (g : SemilinearAut K F) (x y : Pic0.torsion K F n) :
    e.pair (g • x) (g • y) = SemilinearAut.baseAut g (e.pair x y) := by
  obtain ⟨d, hdx, hdy⟩ := e.exists_datum x y
  have h1 := e.compatible (d.galSmulSemi g)
  rw [WeilDatum.classLeft_galSmulSemi, WeilDatum.classRight_galSmulSemi, hdx, hdy] at h1
  rw [h1, WeilDatum.galSmulSemi_pairing]
  have h2 := e.compatible d
  rw [hdx, hdy] at h2
  rw [h2]
end DivisorialWeilPairingData
p2m_reactivate "P2MW.S_ModularCurve_frobenius_coordDet_eq_of_basis_rationalTateModule_jZero_of_ne.ModularCurve P2MW.S_ModularCurve_frobenius_coordDet_eq_of_basis_rationalTateModule_jZero_of_ne.ModularCurve.PEdge"
end AlgebraicCurve
p2m_reactivate "P2MW.S_ModularCurve_frobenius_coordDet_eq_of_basis_rationalTateModule_jZero_of_ne.ModularCurve P2MW.S_ModularCurve_frobenius_coordDet_eq_of_basis_rationalTateModule_jZero_of_ne.ModularCurve.PEdge"
end
p2m_reactivate "P2MW.S_ModularCurve_frobenius_coordDet_eq_of_basis_rationalTateModule_jZero_of_ne.ModularCurve P2MW.S_ModularCurve_frobenius_coordDet_eq_of_basis_rationalTateModule_jZero_of_ne.ModularCurve.PEdge"

namespace NdlGlue
p2m_open "AlgebraicCurve P2MW.S_ModularCurve_frobenius_coordDet_eq_of_basis_rationalTateModule_jZero_of_ne.AlgebraicCurve"
variable {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
variable {L' : Type} [Field L'] [Algebra K L'] [Algebra (RatFunc K) L']
  [IsScalarTower K (RatFunc K) L'] [FiniteDimensional (RatFunc K) L']

omit [IsAlgClosed K] [CharZero K] [FiniteDimensional (RatFunc K) L'] in

theorem transcendental_algebraMap_ratFunc_X :
    Transcendental K (algebraMap (RatFunc K) L' RatFunc.X) :=
  (transcendental_algebraMap_iff (algebraMap (RatFunc K) L').injective).mpr
    RatFunc.transcendental_X

omit [IsAlgClosed K] [CharZero K] [FiniteDimensional (RatFunc K) L'] in

theorem algebraMap_eq_val_algEquivOfTranscendental :
    algebraMap (RatFunc K) L'
      = ((IntermediateField.adjoin K
            ({algebraMap (RatFunc K) L' RatFunc.X} : Set L')).val).toRingHom.comp
          (RatFunc.algEquivOfTranscendental _
            (transcendental_algebraMap_ratFunc_X (K := K) (L' := L'))).toAlgHom.toRingHom := by
  apply IsFractionRing.ringHom_ext (A := Polynomial K)
  intro g
  have hcomp : (algebraMap (RatFunc K) L').comp (algebraMap (Polynomial K) (RatFunc K))
      = (((IntermediateField.adjoin K
            ({algebraMap (RatFunc K) L' RatFunc.X} : Set L')).val).toRingHom.comp
          (RatFunc.algEquivOfTranscendental _
            (transcendental_algebraMap_ratFunc_X (K := K) (L' := L'))).toAlgHom.toRingHom).comp
          (algebraMap (Polynomial K) (RatFunc K)) := by
    apply Polynomial.ringHom_ext
    · intro a
      have hCa : RatFunc.C a = algebraMap K (RatFunc K) a := by
        rw [← RatFunc.algebraMap_C,
          IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K), Polynomial.algebraMap_eq]
      simp only [RingHom.comp_apply]
      rw [RatFunc.algebraMap_C, hCa]
      show algebraMap (RatFunc K) L' (algebraMap K (RatFunc K) a)
        = ((IntermediateField.adjoin K
              ({algebraMap (RatFunc K) L' RatFunc.X} : Set L')).val)
            ((RatFunc.algEquivOfTranscendental _
              (transcendental_algebraMap_ratFunc_X (K := K) (L' := L')))
              (algebraMap K (RatFunc K) a))
      rw [← IsScalarTower.algebraMap_apply K (RatFunc K) L', AlgEquiv.commutes]
      exact IsScalarTower.algebraMap_apply K
        (IntermediateField.adjoin K
          ({algebraMap (RatFunc K) L' RatFunc.X} : Set L')) L' a
    · simp only [RingHom.comp_apply]
      show algebraMap (RatFunc K) L' (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)
        = ((IntermediateField.adjoin K
              ({algebraMap (RatFunc K) L' RatFunc.X} : Set L')).val)
            ((RatFunc.algEquivOfTranscendental _
              (transcendental_algebraMap_ratFunc_X (K := K) (L' := L')))
              (algebraMap (Polynomial K) (RatFunc K) Polynomial.X))
      rw [RatFunc.algEquivOfTranscendental_algebraMap, Polynomial.aeval_X, RatFunc.algebraMap_X]
      rfl
  exact congrFun (congrArg DFunLike.coe hcomp) g

omit [IsAlgClosed K] [CharZero K] in

theorem finiteDimensional_adjoin_ratFunc_X :
    FiniteDimensional
      (IntermediateField.adjoin K
        ({algebraMap (RatFunc K) L' RatFunc.X} : Set L')) L' := by
  set x := algebraMap (RatFunc K) L' RatFunc.X with hxdef
  set e := RatFunc.algEquivOfTranscendental x
    (transcendental_algebraMap_ratFunc_X (K := K) (L' := L')) with hedef
  letI : Algebra (RatFunc K) (IntermediateField.adjoin K ({x} : Set L')) :=
    e.toAlgHom.toRingHom.toAlgebra
  haveI : IsScalarTower (RatFunc K) (IntermediateField.adjoin K ({x} : Set L')) L' :=
    IsScalarTower.of_algebraMap_eq'
      (algebraMap_eq_val_algEquivOfTranscendental (K := K) (L' := L'))
  exact FiniteDimensional.right (RatFunc K) _ L'

omit [IsAlgClosed K] [CharZero K] in

theorem hfg_of_finiteDimensional :
    ∃ x : L', Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set L')) L' :=
  ⟨algebraMap (RatFunc K) L' RatFunc.X,
    transcendental_algebraMap_ratFunc_X,
    finiteDimensional_adjoin_ratFunc_X⟩

omit [IsAlgClosed K] [Algebra (RatFunc K) L'] [IsScalarTower K (RatFunc K) L']
  [FiniteDimensional (RatFunc K) L'] in

theorem isSeparable_adjoin_glue (x : L')
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set L')) L') :
    Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set L')) L' := by
  haveI : CharZero (IntermediateField.adjoin K ({x} : Set L')) :=
    charZero_of_injective_algebraMap
      (algebraMap K (IntermediateField.adjoin K ({x} : Set L'))).injective
  infer_instance

omit [IsAlgClosed K] in

theorem isCurveOver_of_finiteDimensional : IsCurveOver K L' := by
  obtain ⟨x, hx, hfin⟩ := hfg_of_finiteDimensional (K := K) (L' := L')
  exact AlgebraicCurve.isCurveOver_of_transcendental_of_isSeparable K L' x hx hfin
    (isSeparable_adjoin_glue x hfin)

theorem pic0_exists_nsmul_eq_of_finiteDimensional (n : ℕ) (hn : n ≠ 0)
    (z : Pic0 K L') : ∃ y : Pic0 K L', n • y = z := by
  haveI : IsCurveOver K L' := isCurveOver_of_finiteDimensional
  exact AlgebraicCurve.Pic0.exists_nsmul_eq K L'
    (hfg_of_finiteDimensional (K := K) (L' := L')) n hn z
end NdlGlue
p2m_reactivate "P2MW.S_ModularCurve_frobenius_coordDet_eq_of_basis_rationalTateModule_jZero_of_ne.ModularCurve P2MW.S_ModularCurve_frobenius_coordDet_eq_of_basis_rationalTateModule_jZero_of_ne.ModularCurve.PEdge"

namespace HndBridge
p2m_open "AlgebraicCurve P2MW.S_ModularCurve_frobenius_coordDet_eq_of_basis_rationalTateModule_jZero_of_ne.AlgebraicCurve"
variable {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
variable {L : Type} [Field L] [Algebra K L]

theorem toHom_injective_of_transcendental [HasPrincipalDivisors K L] {n : ℕ} [NeZero n]
    (t : L) (ht : Transcendental K t)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({t} : Set L)) L)
    (e : DivisorialWeilPairingData K L n) :
    Function.Injective e.toHom := by
  letI e₀ := RatFunc.algEquivOfTranscendental t ht
  letI : Algebra (RatFunc K) L :=
    (((IntermediateField.adjoin K ({t} : Set L)).val.comp e₀.toAlgHom)).toRingHom.toAlgebra
  haveI : IsScalarTower K (RatFunc K) L :=
    IsScalarTower.of_algebraMap_eq'
      (AlgHom.comp_algebraMap
        ((IntermediateField.adjoin K ({t} : Set L)).val.comp e₀.toAlgHom)).symm
  haveI : FiniteDimensional (RatFunc K) L := by
    refine Module.Finite.of_equiv_equiv
      (e₀.symm : (IntermediateField.adjoin K ({t} : Set L)) ≃+* RatFunc K)
      (RingEquiv.refl L) ?_
    ext u
    show algebraMap (RatFunc K) L (e₀.symm u) = algebraMap _ L u
    show (IntermediateField.adjoin K ({t} : Set L)).val (e₀ (e₀.symm u))
      = algebraMap _ L u
    rw [AlgEquiv.apply_symm_apply]
    rfl
  refine AlgebraicCurve.DivisorialWeilPairingData.toHom_injective_of_divisible ?_ e
  intro L' _ _ _ _ _ m hm z
  obtain ⟨y, hy⟩ := NdlGlue.pic0_exists_nsmul_eq_of_finiteDimensional (K := K) (L' := L')
    m.natAbs (Int.natAbs_ne_zero.mpr hm) z
  rcases Int.natAbs_eq m with h | h
  · refine ⟨y, ?_⟩
    rw [h, natCast_zsmul, hy]
  · refine ⟨-y, ?_⟩
    rw [h, neg_zsmul, zsmul_neg, neg_neg, natCast_zsmul, hy]

theorem eq_zero_of_forall_pair_eq_one [HasPrincipalDivisors K L] {n : ℕ} [NeZero n]
    (t : L) (ht : Transcendental K t)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({t} : Set L)) L)
    (e : DivisorialWeilPairingData K L n) (x : Pic0.torsion K L n)
    (hx : ∀ y, e.pair x y = 1) : x = 0 := by
  apply toHom_injective_of_transcendental t ht hfin e
  rw [map_zero]
  show Additive.ofMul (e.toChar x) = 0
  rw [← ofMul_one]
  congr 1
  ext y
  rw [DivisorialWeilPairingData.toChar_apply, hx y, AddChar.one_apply]
end HndBridge
p2m_reactivate "P2MW.S_ModularCurve_frobenius_coordDet_eq_of_basis_rationalTateModule_jZero_of_ne.ModularCurve P2MW.S_ModularCurve_frobenius_coordDet_eq_of_basis_rationalTateModule_jZero_of_ne.ModularCurve.PEdge"

namespace ModularCurve
p2m_export "ModularCurve" "heckeOperatorBar HeckeOperatorsCommuteBar heckeModuleBar heckeModuleBar_heckeGen_smul arithmeticGalois galois_smul_pic0_def modularFunctionFieldBar JZero qExpand jq modularFunctionFieldFull coeffEmb HeckeAlg heckeGen HeckeInputsAll tateHeckeRep RationalTateModule rationalGaloisRep rationalGaloisRep_apply rationalGaloisRep_tmul rationalHeckeRep rationalHeckeRep_apply rationalHeckeAlgebra JZero.divisible exists_transcendental_finiteDimensional_modularFunctionFieldBar isCurveOver_laurentBaseChange_modularFunctionFieldFull exists_frickeAlgEquiv_modularFunctionFieldBar pair_heckeOperatorBar_eq_pair_fricke_heckeOperatorBar ofAlgAut_smul_ofAlgAut_smul_of_fricke galois_smul_ofAlgAut_smul_of_fricke smulCommClass_JZero_of_heckeOperatorsCommuteBar R2geoDet.coordDet_eq_algebraMap_of_similitude"
namespace PEdge
p2m_open "ModularCurve"

theorem pair_smul_semilinear_modularFunctionFieldBar (N : ℕ) [NeZero N] :
    ∀ {n : ℕ} [NeZero n]
      (e : AlgebraicCurve.DivisorialWeilPairingData (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N) n)
      (g : AlgebraicCurve.SemilinearAut (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N))
      (x y : AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N) n),
        e.pair (g • x) (g • y) = AlgebraicCurve.SemilinearAut.baseAut g (e.pair x y) :=
  fun e g x y => AlgebraicCurve.DivisorialWeilPairingData.pair_smul_semilinear e g x y

theorem eq_zero_of_forall_pair_eq_one_modularFunctionFieldBar (N : ℕ) [NeZero N] :
    ∀ {n : ℕ} [NeZero n]
      (e : AlgebraicCurve.DivisorialWeilPairingData (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N) n)
      (x : AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N) n),
        (∀ y : AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N) n, e.pair x y = 1) → x = 0 := by
  obtain ⟨t, ht, hfin⟩ := ModularCurve.exists_transcendental_finiteDimensional_modularFunctionFieldBar N
  exact fun e x hx => HndBridge.eq_zero_of_forall_pair_eq_one t ht hfin e x hx

end ModularCurve.PEdge
p2m_reactivate "P2MW.S_ModularCurve_frobenius_coordDet_eq_of_basis_rationalTateModule_jZero_of_ne.ModularCurve P2MW.S_ModularCurve_frobenius_coordDet_eq_of_basis_rationalTateModule_jZero_of_ne.ModularCurve.PEdge"
p2m_reactivate "P2MW.S_ModularCurve_frobenius_coordDet_eq_of_basis_rationalTateModule_jZero_of_ne.ModularCurve P2MW.S_ModularCurve_frobenius_coordDet_eq_of_basis_rationalTateModule_jZero_of_ne.ModularCurve.PEdge"

end
p2m_reactivate "P2MW.S_ModularCurve_frobenius_coordDet_eq_of_basis_rationalTateModule_jZero_of_ne.ModularCurve P2MW.S_ModularCurve_frobenius_coordDet_eq_of_basis_rationalTateModule_jZero_of_ne.ModularCurve.PEdge"

namespace ModularCurve p2m_export "ModularCurve" "heckeOperatorBar HeckeOperatorsCommuteBar heckeModuleBar heckeModuleBar_heckeGen_smul arithmeticGalois galois_smul_pic0_def modularFunctionFieldBar JZero qExpand jq modularFunctionFieldFull coeffEmb HeckeAlg heckeGen HeckeInputsAll tateHeckeRep RationalTateModule rationalGaloisRep rationalGaloisRep_apply rationalGaloisRep_tmul rationalHeckeRep rationalHeckeRep_apply rationalHeckeAlgebra JZero.divisible exists_transcendental_finiteDimensional_modularFunctionFieldBar isCurveOver_laurentBaseChange_modularFunctionFieldFull exists_frickeAlgEquiv_modularFunctionFieldBar pair_heckeOperatorBar_eq_pair_fricke_heckeOperatorBar ofAlgAut_smul_ofAlgAut_smul_of_fricke galois_smul_ofAlgAut_smul_of_fricke smulCommClass_JZero_of_heckeOperatorsCommuteBar R2geoDet.coordDet_eq_algebraMap_of_similitude" namespace PEdge end ModularCurve.PEdge
p2m_open_scoped "ModularCurve" in
theorem ModularCurve.PEdge.exists_frobeniusSimilitudePairing_allPlaces
    (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hin : ModularCurve.HeckeInputsAll N) (hcomm : ModularCurve.HeckeOperatorsCommuteBar N) :
    letI := ModularCurve.heckeModuleBar N
    ∃ B : ModularCurve.RationalTateModule p (ModularCurve.JZero N) →ₗ[ℚ_[p]]
          ModularCurve.RationalTateModule p (ModularCurve.JZero N) →ₗ[ℚ_[p]] ℚ_[p],
      (∀ (a : ModularCurve.rationalHeckeAlgebra p (ModularCurve.JZero N))
         (v w : ModularCurve.RationalTateModule p (ModularCurve.JZero N)),
          B (a • v) w = B v (a • w))
      ∧ (∀ v, B v v = 0)
      ∧ (∀ v, (∀ w, B v w = 0) → v = 0)
      ∧ (∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
          ∀ A' : ValuationSubring (AlgebraicClosure ℚ), A'.LiesOverPrime ℓ →
            ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A'.IsFrobeniusAt σ ℓ →
              ∀ v w, B (ModularCurve.rationalGaloisRep p (ModularCurve.JZero N)
                      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ v)
                  (ModularCurve.rationalGaloisRep p (ModularCurve.JZero N)
                      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ w)
                = (ℓ : ℚ_[p]) • B v w) :=
  ModularCurve.PEdge.exists_form_of_hgal_hnd N p (ModularCurve.PEdge.pair_smul_semilinear_modularFunctionFieldBar N)
    (ModularCurve.PEdge.eq_zero_of_forall_pair_eq_one_modularFunctionFieldBar N) hin hcomm

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "heckeOperatorBar HeckeOperatorsCommuteBar heckeModuleBar heckeModuleBar_heckeGen_smul arithmeticGalois galois_smul_pic0_def modularFunctionFieldBar JZero qExpand jq modularFunctionFieldFull coeffEmb HeckeAlg heckeGen HeckeInputsAll tateHeckeRep RationalTateModule rationalGaloisRep rationalGaloisRep_apply rationalGaloisRep_tmul rationalHeckeRep rationalHeckeRep_apply rationalHeckeAlgebra JZero.divisible exists_transcendental_finiteDimensional_modularFunctionFieldBar isCurveOver_laurentBaseChange_modularFunctionFieldFull exists_frickeAlgEquiv_modularFunctionFieldBar pair_heckeOperatorBar_eq_pair_fricke_heckeOperatorBar ofAlgAut_smul_ofAlgAut_smul_of_fricke galois_smul_ofAlgAut_smul_of_fricke smulCommClass_JZero_of_heckeOperatorsCommuteBar R2geoDet.coordDet_eq_algebraMap_of_similitude"
namespace DetSol
p2m_open "ModularCurve"

variable (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module HeckeAlg J]
  (G : Type) [Monoid G] [DistribMulAction G J]

theorem isMulCommutative_rationalHeckeAlgebra : IsMulCommutative (rationalHeckeAlgebra p J) :=
  Algebra.isMulCommutative_adjoin ℚ_[p] (by
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm])

abbrev commRing : CommRing (rationalHeckeAlgebra p J) :=
  { (inferInstance : Ring (rationalHeckeAlgebra p J)) with
    mul_comm := fun a b => (isMulCommutative_rationalHeckeAlgebra p J).is_comm.comm a b }

theorem rep_mul_tateHeckeRep [SMulCommClass G HeckeAlg J] (g : G) (t : HeckeAlg) :
    TateModule.rep p J G g * tateHeckeRep p J t = tateHeckeRep p J t * TateModule.rep p J G g := by
  refine LinearMap.ext fun x => Subtype.ext (funext fun n => ?_)
  show g • (t • (x : ℕ → J) n) = t • (g • (x : ℕ → J) n)
  exact smul_comm g t ((x : ℕ → J) n)

theorem rationalGaloisRep_mul_rationalHeckeRep [SMulCommClass G HeckeAlg J] (g : G) (t : HeckeAlg) :
    rationalGaloisRep p J G g * rationalHeckeRep p J t
      = rationalHeckeRep p J t * rationalGaloisRep p J G g := by
  rw [rationalGaloisRep_apply, rationalHeckeRep_apply, ← LinearMap.baseChange_mul,
    ← LinearMap.baseChange_mul, rep_mul_tateHeckeRep]

theorem commute_rationalGaloisRep_of_mem [SMulCommClass G HeckeAlg J] (g : G)
    {a : Module.End ℚ_[p] (RationalTateModule p J)} (ha : a ∈ rationalHeckeAlgebra p J) :
    Commute (rationalGaloisRep p J G g) a :=
  Algebra.commute_of_mem_adjoin_of_forall_mem_commute ha (by
    rintro _ ⟨t, rfl⟩
    exact rationalGaloisRep_mul_rationalHeckeRep p J G g t)

theorem rationalGaloisRep_smul [SMulCommClass G HeckeAlg J] (g : G)
    (a : rationalHeckeAlgebra p J) (v : RationalTateModule p J) :
    rationalGaloisRep p J G g (a • v) = a • rationalGaloisRep p J G g v := by
  change rationalGaloisRep p J G g ((a : Module.End ℚ_[p] (RationalTateModule p J)) v)
      = (a : Module.End ℚ_[p] (RationalTateModule p J)) (rationalGaloisRep p J G g v)
  exact LinearMap.congr_fun (commute_rationalGaloisRep_of_mem p J G g a.2).eq v

end ModularCurve.DetSol
p2m_reactivate "P2MW.S_ModularCurve_frobenius_coordDet_eq_of_basis_rationalTateModule_jZero_of_ne.ModularCurve P2MW.S_ModularCurve_frobenius_coordDet_eq_of_basis_rationalTateModule_jZero_of_ne.ModularCurve.PEdge"
p2m_reactivate "P2MW.S_ModularCurve_frobenius_coordDet_eq_of_basis_rationalTateModule_jZero_of_ne.ModularCurve P2MW.S_ModularCurve_frobenius_coordDet_eq_of_basis_rationalTateModule_jZero_of_ne.ModularCurve.PEdge"

theorem solution
    (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hin : ModularCurve.HeckeInputsAll N) (hcomm : ModularCurve.HeckeOperatorsCommuteBar N) :
    letI := ModularCurve.heckeModuleBar N
    ∀ (b : Module.Basis (Fin 2) (ModularCurve.rationalHeckeAlgebra p (ModularCurve.JZero N))
        (ModularCurve.RationalTateModule p (ModularCurve.JZero N)))
      (ℓ : ℕ), ℓ.Prime → ℓ ≠ p →
      ∀ A' : ValuationSubring (AlgebraicClosure ℚ), A'.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A'.IsFrobeniusAt σ ℓ →
          (b.repr (ModularCurve.rationalGaloisRep p (ModularCurve.JZero N)
                (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ (b 0))) 0
              * (b.repr (ModularCurve.rationalGaloisRep p (ModularCurve.JZero N)
                (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ (b 1))) 1
            - (b.repr (ModularCurve.rationalGaloisRep p (ModularCurve.JZero N)
                (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ (b 1))) 0
              * (b.repr (ModularCurve.rationalGaloisRep p (ModularCurve.JZero N)
                (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ (b 0))) 1
            = (ℓ : ModularCurve.rationalHeckeAlgebra p (ModularCurve.JZero N)) := by
  intro b ℓ hℓ hNp A' hA' σ hσ
  refine (ModularCurve.PEdge.exists_frobeniusSimilitudePairing_allPlaces N p hin hcomm).elim ?_
  intro B hB
  exact (@ModularCurve.R2geoDet.coordDet_eq_algebraMap_of_similitude ℚ_[p] _ _
      (@ModularCurve.rationalHeckeAlgebra p _ (ModularCurve.JZero N) _ (ModularCurve.heckeModuleBar N))
      (@ModularCurve.DetSol.commRing p _ (ModularCurve.JZero N) _ (ModularCurve.heckeModuleBar N))
      (Subalgebra.algebra _)
      (ModularCurve.RationalTateModule p (ModularCurve.JZero N)) _ _
      (Subalgebra.moduleLeft _) (Subalgebra.isScalarTower_mid _)
      b B hB.1 hB.2.1 hB.2.2.1
      (ModularCurve.rationalGaloisRep p (ModularCurve.JZero N)
        (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ)
      (@ModularCurve.DetSol.rationalGaloisRep_smul p _ (ModularCurve.JZero N) _
        (ModularCurve.heckeModuleBar N) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) _ _
        (ModularCurve.smulCommClass_JZero_of_heckeOperatorsCommuteBar N hcomm) σ)
      (ℓ : ℚ_[p]) (hB.2.2.2 ℓ hℓ hNp A' hA' σ hσ)).trans
    (map_natCast _ ℓ)

end
p2m_reactivate "P2MW.S_ModularCurve_frobenius_coordDet_eq_of_basis_rationalTateModule_jZero_of_ne.ModularCurve P2MW.S_ModularCurve_frobenius_coordDet_eq_of_basis_rationalTateModule_jZero_of_ne.ModularCurve.PEdge"

end S_ModularCurve_frobenius_coordDet_eq_of_basis_rationalTateModule_jZero_of_ne
end P2MW
export P2MW.S_ModularCurve_frobenius_coordDet_eq_of_basis_rationalTateModule_jZero_of_ne (solution)
