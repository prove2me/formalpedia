-- Prove2me | solution 1 for ModularCurve.JZero.finiteIndex_range_nsmul_two_invariants
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/ff1ee9b0-f95d-5746-bb18-f69e534460af

import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_AlgebraicClosure_exists_uniform_level_of_characters_unramified_outside
import Theorems.Thm_ModularCurve_jZeroTorsionFinite
import Mathlib.Algebra.Ring.Action.Submonoid
import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Index
import Theorems.Thm_ModularCurve_JZero_exists_finiteDimensional_fixingSubgroup_smul_eq
import Theorems.Thm_ModularCurve_JZero_exists_finset_inertiaSubgroupIn_smul_eq_of_prime_smul_sub_eq_zero
import Theorems.Thm_ModularCurve_JZero_divisible
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_finiteIndex_range_nsmul_two_invariants
p2m_attr_erase "instance" "CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree WeierstrassCurve.Affine.Point.instFinite WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2"
p2m_attr_erase "instance" "HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.jqNModC_one"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X"
p2m_attr_erase "simp" "ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL"
p2m_attr_erase "simp" "HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option Elab.async false
set_option autoImplicit false

open ModularCurve AlgebraicCurve

theorem cure_isAlgebraic : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
  convert AlgebraicClosure.isAlgebraic ℚ <;> first | rfl | exact Subsingleton.elim _ _
theorem cure_isAlgClosure : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
  (isAlgClosure_iff (k := ℚ) (K := AlgebraicClosure ℚ)).mpr ⟨inferInstance, cure_isAlgebraic⟩
attribute [local instance] cure_isAlgClosure

section WM2Aux1

variable {N : ℕ}

private theorem wm2n_two_nsmul_sub_eq_zero (Q : JZero N)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (h : σ • (2 • Q) = 2 • Q) :
    2 • (σ • Q - Q) = 0 := by
  rw [two_nsmul, smul_add] at h
  rw [two_nsmul, sub_add_sub_comm, h, sub_self]

private theorem wm2n_sub_mem_torsion (Q : JZero N)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (h : σ • (2 • Q) = 2 • Q) :
    σ • Q - Q ∈ Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) 2 := by
  rw [Pic0.mem_torsion, natCast_zsmul]
  exact wm2n_two_nsmul_sub_eq_zero Q σ h

private theorem wm2n_mul_smul_sub (Q : JZero N)
    (σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hfix : σ • (τ • Q - Q) = τ • Q - Q) :
    (σ * τ) • Q - Q = (σ • Q - Q) + (τ • Q - Q) := by
  rw [smul_sub] at hfix
  rw [mul_smul, ← hfix, sub_add_sub_cancel']

open Classical in

private noncomputable def wm2nKappa (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (Q : JZero N)
    (hQ : ∀ σ ∈ K.fixingSubgroup, σ • (2 • Q) = 2 • Q)
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ↥(Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) 2) :=
  if hτ : τ ∈ K.fixingSubgroup then ⟨τ • Q - Q, wm2n_sub_mem_torsion Q τ (hQ τ hτ)⟩ else 0

private theorem wm2nKappa_coe (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (Q : JZero N)
    (hQ : ∀ σ ∈ K.fixingSubgroup, σ • (2 • Q) = 2 • Q)
    {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hτ : τ ∈ K.fixingSubgroup) :
    (wm2nKappa K Q hQ τ : JZero N) = τ • Q - Q := by
  unfold wm2nKappa
  rw [dif_pos hτ]

private theorem wm2nKappa_eq_zero (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (Q : JZero N)
    (hQ : ∀ σ ∈ K.fixingSubgroup, σ • (2 • Q) = 2 • Q)
    {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (h : τ • Q = Q) :
    wm2nKappa K Q hQ τ = 0 := by
  unfold wm2nKappa
  split_ifs with hτ
  · exact Subtype.ext (sub_eq_zero.mpr h)
  · rfl

private theorem wm2n_exists_level (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (h2 : Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) 2 ≤ JZero N ^+ ↥K.fixingSubgroup) :
    ∃ M : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ M ∧ K ≤ M ∧
      ∀ Q : JZero N, (∀ σ ∈ K.fixingSubgroup, σ • (2 • Q) = 2 • Q) →
        ∀ σ ∈ M.fixingSubgroup, σ • Q = Q := by
  obtain ⟨S, hS⟩ := JZero.exists_finset_inertiaSubgroupIn_smul_eq_of_prime_smul_sub_eq_zero N
  haveI : NumberField K := ⟨⟩
  obtain ⟨M, hMfd, hKM, hM⟩ :=
    AlgebraicClosure.exists_uniform_level_of_characters_unramified_outside K 2 Nat.prime_two (insert 2 S)
  refine ⟨M, hMfd, hKM, fun Q hQ σ hσ => ?_⟩
  have hσK : σ ∈ K.fixingSubgroup := IntermediateField.fixingSubgroup_le hKM hσ

  have hmul : ∀ σ' τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ' ∈ K.fixingSubgroup → τ ∈ K.fixingSubgroup →
        wm2nKappa K Q hQ (σ' * τ) = wm2nKappa K Q hQ σ' + wm2nKappa K Q hQ τ := by
    intro σ' τ hσ' hτ
    apply Subtype.ext
    rw [AddSubgroup.coe_add, wm2nKappa_coe K Q hQ (mul_mem hσ' hτ), wm2nKappa_coe K Q hQ hσ',
      wm2nKappa_coe K Q hQ hτ]
    exact wm2n_mul_smul_sub Q σ' τ (h2 (wm2n_sub_mem_torsion Q τ (hQ τ hτ)) ⟨σ', hσ'⟩)

  suffices hκσ : wm2nKappa K Q hQ σ = 0 by
    have h0 := congrArg Subtype.val hκσ
    rw [wm2nKappa_coe K Q hQ hσK] at h0
    exact sub_eq_zero.mp h0

  refine (Module.forall_dual_apply_eq_zero_iff (ZMod 2) (wm2nKappa K Q hQ σ)).mp fun f => ?_
  refine hM (fun τ => f (wm2nKappa K Q hQ τ)) ?_ ?_ ?_ σ hσ
  · intro σ' τ hσ' hτ
    show f (wm2nKappa K Q hQ (σ' * τ)) = f (wm2nKappa K Q hQ σ') + f (wm2nKappa K Q hQ τ)
    rw [hmul σ' τ hσ' hτ, map_add]
  · obtain ⟨L₀, hL₀, hfix⟩ := JZero.exists_finiteDimensional_fixingSubgroup_smul_eq N Q
    refine ⟨L₀, hL₀, fun τ hτ => ?_⟩
    show f (wm2nKappa K Q hQ τ) = 0
    rw [wm2nKappa_eq_zero K Q hQ (hfix τ hτ), map_zero]
  · intro q hq hqS A hA τ hτA hτK
    have h2q : (2 : ℕ) ≠ q := by
      rintro rfl
      exact hqS (Finset.mem_insert_self 2 S)
    have hqS' : q ∉ S := fun h => hqS (Finset.mem_insert_of_mem h)
    show f (wm2nKappa K Q hQ τ) = 0
    rw [wm2nKappa_eq_zero K Q hQ (hS q hq hqS' A hA τ hτA 2 Nat.prime_two h2q Q
      (wm2n_two_nsmul_sub_eq_zero Q τ (hQ τ hτK))), map_zero]

end WM2Aux1

section WM2Aux1Finish

variable {N : ℕ}

open Classical in

private noncomputable def wm2nCoord (K M : IntermediateField ℚ (AlgebraicClosure ℚ))
    (half : JZero N → JZero N) (hhalf : ∀ x : JZero N, 2 • half x = x)
    (P : ↥(JZero N ^+ ↥K.fixingSubgroup))
    (c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ M.fixingSubgroup) :
    ↥(Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) 2) :=
  if hc : c.out ∈ K.fixingSubgroup then
    ⟨c.out • half P - half P,
      wm2n_sub_mem_torsion (half P) c.out (by rw [hhalf]; exact P.2 ⟨c.out, hc⟩)⟩
  else 0

private theorem wm2nCoord_coe (K M : IntermediateField ℚ (AlgebraicClosure ℚ))
    (half : JZero N → JZero N) (hhalf : ∀ x : JZero N, 2 • half x = x)
    (P : ↥(JZero N ^+ ↥K.fixingSubgroup))
    {c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ M.fixingSubgroup} (hc : c.out ∈ K.fixingSubgroup) :
    (wm2nCoord K M half hhalf P c : JZero N) = c.out • half P - half P := by
  unfold wm2nCoord
  rw [dif_pos hc]

private theorem wm2n_sub_mem_range (K M : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKM : K ≤ M)
    (half : JZero N → JZero N) (hhalf : ∀ x : JZero N, 2 • half x = x)
    (hfix : ∀ Q : JZero N, (∀ σ ∈ K.fixingSubgroup, σ • (2 • Q) = 2 • Q) →
      ∀ σ ∈ M.fixingSubgroup, σ • Q = Q)
    {P P' : ↥(JZero N ^+ ↥K.fixingSubgroup)}
    (h : wm2nCoord K M half hhalf P = wm2nCoord K M half hhalf P') :
    P - P' ∈ (nsmulAddMonoidHom 2 :
      ↥(JZero N ^+ ↥K.fixingSubgroup) →+ ↥(JZero N ^+ ↥K.fixingSubgroup)).range := by

  have hP : ∀ σ ∈ M.fixingSubgroup, σ • half P = half P :=
    hfix (half P) fun σ hσ => by rw [hhalf]; exact P.2 ⟨σ, hσ⟩
  have hP' : ∀ σ ∈ M.fixingSubgroup, σ • half P' = half P' :=
    hfix (half P') fun σ hσ => by rw [hhalf]; exact P'.2 ⟨σ, hσ⟩

  have hD : half P - half P' ∈ JZero N ^+ ↥K.fixingSubgroup := by
    rw [FixedPoints.mem_addSubgroup]
    rintro ⟨σ, hσ⟩
    obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul M.fixingSubgroup σ
    have hs : (QuotientGroup.mk σ : _ ⧸ M.fixingSubgroup).out ∈ K.fixingSubgroup := by
      rw [hm]
      exact mul_mem hσ (IntermediateField.fixingSubgroup_le hKM m.2)
    have hc := congrArg Subtype.val (congrFun h (QuotientGroup.mk σ))
    rw [wm2nCoord_coe K M half hhalf P hs, wm2nCoord_coe K M half hhalf P' hs, hm, mul_smul, mul_smul,
      hP _ m.2, hP' _ m.2, sub_eq_sub_iff_sub_eq_sub] at hc
    show σ • (half P - half P') = _
    rw [smul_sub]
    exact hc
  rw [AddMonoidHom.mem_range]
  refine ⟨⟨half P - half P', hD⟩, Subtype.ext ?_⟩
  show 2 • (half P - half P') = (P : JZero N) - P'
  rw [two_nsmul, sub_add_sub_comm, ← two_nsmul, ← two_nsmul, hhalf, hhalf]

private theorem wm2n_mk_eq_mk (K M : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKM : K ≤ M)
    (half : JZero N → JZero N) (hhalf : ∀ x : JZero N, 2 • half x = x)
    (hfix : ∀ Q : JZero N, (∀ σ ∈ K.fixingSubgroup, σ • (2 • Q) = 2 • Q) →
      ∀ σ ∈ M.fixingSubgroup, σ • Q = Q)
    {P P' : ↥(JZero N ^+ ↥K.fixingSubgroup)}
    (h : wm2nCoord K M half hhalf P = wm2nCoord K M half hhalf P') :
    (QuotientAddGroup.mk P : ↥(JZero N ^+ ↥K.fixingSubgroup) ⧸ (nsmulAddMonoidHom 2 :
      ↥(JZero N ^+ ↥K.fixingSubgroup) →+ ↥(JZero N ^+ ↥K.fixingSubgroup)).range) =
      QuotientAddGroup.mk P' := by
  rw [QuotientAddGroup.eq, neg_add_eq_sub]
  exact wm2n_sub_mem_range K M hKM half hhalf hfix h.symm

end WM2Aux1Finish

theorem solution (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (h2 : Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) 2 ≤ JZero N ^+ ↥K.fixingSubgroup) :
    (nsmulAddMonoidHom 2 : ↥(JZero N ^+ ↥K.fixingSubgroup) →+ ↥(JZero N ^+ ↥K.fixingSubgroup)).range.FiniteIndex := by
  classical

  obtain ⟨M, hMfd, hKM, hfix⟩ := wm2n_exists_level N K h2

  choose half hhalf using JZero.divisible N 2 two_ne_zero

  haveI : Finite ↥(Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) 2) :=
    jZeroTorsionFinite N 2 two_pos
  haveI : FiniteDimensional ℚ ↥M := hMfd
  haveI : M.fixingSubgroup.FiniteIndex :=
    ⟨fun h => Module.finrank_pos.ne' ((IntermediateField.finrank_eq_fixingSubgroup_index _ M).trans h)⟩

  haveI : Finite (↥(JZero N ^+ ↥K.fixingSubgroup) ⧸ (nsmulAddMonoidHom 2 :
      ↥(JZero N ^+ ↥K.fixingSubgroup) →+ ↥(JZero N ^+ ↥K.fixingSubgroup)).range) := by
    refine Finite.of_surjective
      (fun y : ↥(Set.range (wm2nCoord K M half hhalf)) =>
        (QuotientAddGroup.mk (Classical.choose (Set.mem_range.mp y.2)) : _ ⧸ (nsmulAddMonoidHom 2 :
          ↥(JZero N ^+ ↥K.fixingSubgroup) →+ ↥(JZero N ^+ ↥K.fixingSubgroup)).range))
      fun q => ?_
    obtain ⟨P, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact ⟨⟨wm2nCoord K M half hhalf P, Set.mem_range_self P⟩, wm2n_mk_eq_mk K M hKM half hhalf hfix
      (Classical.choose_spec (Set.mem_range.mp (Set.mem_range_self (f := wm2nCoord K M half hhalf) P)))⟩
  exact AddSubgroup.finiteIndex_of_finite_quotient

end S_ModularCurve_JZero_finiteIndex_range_nsmul_two_invariants
end P2MW
export P2MW.S_ModularCurve_JZero_finiteIndex_range_nsmul_two_invariants (solution)
