-- Prove2me | solution 1 for ModularCurve.exists_submodule_quotient_heckeTorsion_jZero_linearEquiv_galoisStable_of_baseChange_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/cf07bfb7-9c57-5a99-a804-e78ec46b736f

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_GaloisRep_FrobeniusPowerDense
import Theorems.Thm_ModularCurve_exists_matrixRep_trace_det_frobenius_of_heckeTorsion_ne_bot
import Theorems.Thm_FrobeniusDensity_exists_isFrobeniusAt_conj_mem_of_le_ker
import Theorems.Thm_BrauerNesbitt_exists_linearEquiv_of_span_range_eq_top_of_trace_eq
import Theorems.Thm_ModularCurve_exists_linearBlrBlock_of_span_eq_top_of_frobeniusQuadratic_of_dense
import Theorems.Thm_ModularCurve_frobeniusQuadratic_JZero
import Theorems.Thm_ResidualGaloisRep_isAbsolutelyIrreducible_iff_span_eq_top
import Theorems.Thm_Matrix_span_image_map_eq_top_of_span_eq_top
import Theorems.Thm_ModularCurve_mTorsionGaloisRep_jZero_galoisFactorsThroughFiniteLevel
import Theorems.Thm_ModularCurve_heckeOperatorsCommuteBar
import Theorems.Thm_ModularCurve_smulCommClass_JZero_of_heckeOperatorsCommuteBar
import Theorems.Thm_ModularCurve_JZero_cardinalityAJ_genusFF
import Theorems.Thm_ModularCurve_JZero_finite_torsion_pow_of_cardinalityAJ
import Theorems.Thm_FreyPackage_frobeniusPowerDense_inf_of_restrictionKer_le

import Mathlib.LinearAlgebra.Quotient.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_submodule_quotient_heckeTorsion_jZero_linearEquiv_galoisStable_of_baseChange_equiv
p2m_attr_erase "instance" "GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule TateModule.instModule TateModule.instSMul AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions"
p2m_attr_erase "instance" "FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE ValuationSubring.instIsAlgClosedResidueField WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G"
p2m_attr_erase "simp" "GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add"
p2m_attr_erase "simp" "ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero"
p2m_attr_erase "simp" "ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none WeierstrassCurve.veluPointMap2_zero"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one"
p2m_attr_erase "simp" "HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply AlgebraicCurve.DivisorialWeilPairingData.toChar_apply AlgebraicCurve.WeilDatum.coe_classRight AlgebraicCurve.WeilDatum.coe_degZeroRight AlgebraicCurve.DivisorialWeilPairingData.mk.sizeOf_spec AlgebraicCurve.WeilDatum.coe_classLeft AlgebraicCurve.WeilDatum.coe_degZeroLeft AlgebraicCurve.DivisorialWeilPairingData.mk.injEq AlgebraicCurve.DivisorialWeilPairingData.toHom_apply_apply AlgebraicCurve.WeilDatum.mk.sizeOf_spec AlgebraicCurve.WeilDatum.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_zero AlgebraicCurve.PrincipalPolarization.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_apply AlgebraicCurve.H1Gm.degree_ofPic0 AlgebraicCurve.WeilPairingData.mk.sizeOf_spec AlgebraicCurve.HomPic0Gm.map_one AlgebraicCurve.PrincipalPolarization.mk.sizeOf_spec AlgebraicCurve.WeilPairingData.autodualityEquiv_apply AlgebraicCurve.WeilPairingData.eval_zero_right AlgebraicCurve.H1Gm.ofPic0_mk AlgebraicCurve.WeilPairingData.eval_neg_left AlgebraicCurve.HomPic0Gm.map_apply"
p2m_attr_erase "simp" "AlgebraicCurve.H1Gm.degree_mk AlgebraicCurve.HomPic0Gm.map_id AlgebraicCurve.WeilPairingData.mk.injEq AlgebraicCurve.WeilPairingData.congr_eval AlgebraicCurve.WeilPairingData.eval_neg_right AlgebraicCurve.WeilPairingData.eval_zero_left AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.tateMap_apply AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero"
p2m_attr_erase "simp" "TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false

open ModularCurve
open scoped TensorProduct

namespace BLBody

theorem finite_heckeTorsion (M : ℕ) [NeZero M] (p : ℕ) [Fact p.Prime] (𝔪 : Ideal HeckeAlg)
    (hp𝔪 : ((p : ℕ) : HeckeAlg) ∈ 𝔪) :
    letI := heckeModuleBar M
    Finite ↥(heckeTorsion (JZero M) 𝔪) := by
  letI := heckeModuleBar M
  have hfin := JZero.finite_torsion_pow_of_cardinalityAJ M p (JZero.cardinalityAJ_genusFF M p) 1
  rw [pow_one] at hfin
  let f : ↥(heckeTorsion (JZero M) 𝔪) →
      ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar M) p) :=
    fun x => ⟨(x : JZero M), by
      rw [AlgebraicCurve.Pic0.mem_torsion]
      have hx := (mem_heckeTorsion_iff (JZero M) 𝔪 x).mp x.2 _ hp𝔪
      have hC : ((p : ℕ) : HeckeAlg) = MvPolynomial.C (p : ℤ) := by simp
      rw [hC, heckeModuleBar_C_smul] at hx
      exact hx⟩
  exact Finite.of_injective f fun x y h => Subtype.ext (congrArg Subtype.val h :)

local instance instIsAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ
local instance instIsAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
local instance instNormalQbar : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

theorem dense_aux {Mx : Type} [MulOneClass Mx]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Mx)
    {J : Type} [AddCommGroup J] [Module HeckeAlg J]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg J]
    (𝔪 : Ideal HeckeAlg)
    (hker : GaloisFactorsThroughFiniteLevel ρ)
    (hcont : GaloisFactorsThroughFiniteLevel
      (mTorsionGaloisRep (G := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J 𝔪))
    (S : Finset ℕ) :
    FrobeniusPowerDense S
      (ρ.ker ⊓ fixingSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (heckeTorsion J 𝔪 : Set J)) := by
  classical
  obtain ⟨L, hLfin, hL⟩ := hker
  obtain ⟨L', hL'fin, hL'⟩ := hcont
  haveI : FiniteDimensional ℚ L := hLfin
  haveI : FiniteDimensional ℚ L' := hL'fin
  let Lc : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.normalClosure ℚ (↥(L ⊔ L')) (AlgebraicClosure ℚ)
  haveI : CharZero Lc := charZero_of_injective_algebraMap (algebraMap ℚ Lc).injective
  haveI : FiniteDimensional ℚ Lc :=
    normalClosure.is_finiteDimensional ℚ (↥(L ⊔ L')) (AlgebraicClosure ℚ)
  haveI : Normal ℚ Lc := normalClosure.normal ℚ (↥(L ⊔ L')) (AlgebraicClosure ℚ)
  haveI : NumberField Lc := NumberField.mk
  haveI : IsGalois ℚ Lc := IsGalois.mk
  have hLLc : L ≤ Lc := le_sup_left.trans (IntermediateField.le_normalClosure (L ⊔ L'))
  have hL'Lc : L' ≤ Lc := le_sup_right.trans (IntermediateField.le_normalClosure (L ⊔ L'))
  have hfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ∈ (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) Lc).ker →
        ∀ x : AlgebraicClosure ℚ, x ∈ Lc → σ x = x := by
    intro σ hσ x hx
    have h1 : AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) Lc σ = 1 :=
      MonoidHom.mem_ker.mp hσ
    have h := AlgEquiv.restrictNormalHom_apply Lc σ ⟨x, hx⟩
    exact h.symm.trans
      (congrArg (fun y : Lc => (y : AlgebraicClosure ℚ)) (DFunLike.congr_fun h1 ⟨x, hx⟩))
  refine FreyPackage.frobeniusPowerDense_inf_of_restrictionKer_le Lc ρ _ ?_ ?_ S
  · intro σ hσ
    rw [MonoidHom.mem_ker]
    exact hL σ (fun x hx => hfix σ hσ x (hLLc hx))
  · intro σ hσ
    have hσ1 : mTorsionGaloisRep (G := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J 𝔪 σ = 1 :=
      hL' σ (fun x hx => hfix σ hσ x (hL'Lc hx))
    rw [mem_fixingSubgroup_iff]
    intro y hy
    have h := congrArg (fun f => ((f ⟨y, hy⟩ : heckeTorsion J 𝔪) : J)) hσ1
    simpa using h

theorem trace_eq (M : ℕ) [NeZero M] (p : ℕ) [Fact p.Prime]
    (𝔪 : Ideal HeckeAlg)
    {k : Type} [Field k] (ι : HeckeAlg ⧸ 𝔪 →+* k)
    (ρbar : ResidualGaloisRep k) (S₀ : Finset ℕ)
    (hatt : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S₀ → ¬ ℓ ∣ M → ℓ ≠ p →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.trace k ρbar.V (ρbar.ρ σ) = ι (Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩)))
    (ρJ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) (HeckeAlg ⧸ 𝔪))
    (hfinlev : GaloisFactorsThroughFiniteLevel ρJ)
    (SJ : Finset ℕ)
    (hattJ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ SJ → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)),
      A.LiesOverPrime ℓ → ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ ℓ →
        Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩) = (ρJ σ).trace ∧
          Ideal.Quotient.mk 𝔪 ((ℓ : HeckeAlg)) = (ρJ σ).det)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ((ρJ σ).map ι).trace = LinearMap.trace k ρbar.V (ρbar.ρ σ) := by
  classical
  obtain ⟨L, hLfin, hL⟩ := hfinlev
  obtain ⟨L', hL'fin, hL'⟩ := ρbar.factorsThroughFiniteLevel
  haveI : FiniteDimensional ℚ L := hLfin
  haveI : FiniteDimensional ℚ L' := hL'fin
  let Lc : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.normalClosure ℚ (↥(L ⊔ L')) (AlgebraicClosure ℚ)
  haveI : CharZero Lc := charZero_of_injective_algebraMap (algebraMap ℚ Lc).injective
  haveI : FiniteDimensional ℚ Lc :=
    normalClosure.is_finiteDimensional ℚ (↥(L ⊔ L')) (AlgebraicClosure ℚ)
  haveI : Normal ℚ Lc := normalClosure.normal ℚ (↥(L ⊔ L')) (AlgebraicClosure ℚ)
  haveI : NumberField Lc := NumberField.mk
  haveI : IsGalois ℚ Lc := IsGalois.mk
  have hLLc : L ≤ Lc := le_sup_left.trans (IntermediateField.le_normalClosure (L ⊔ L'))
  have hL'Lc : L' ≤ Lc := le_sup_right.trans (IntermediateField.le_normalClosure (L ⊔ L'))
  have hfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ∈ (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) Lc).ker →
        ∀ x : AlgebraicClosure ℚ, x ∈ Lc → σ x = x := by
    intro σ hσ x hx
    have h1 : AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) Lc σ = 1 :=
      MonoidHom.mem_ker.mp hσ
    have h := AlgEquiv.restrictNormalHom_apply Lc σ ⟨x, hx⟩
    exact h.symm.trans
      (congrArg (fun y : Lc => (y : AlgebraicClosure ℚ)) (DFunLike.congr_fun h1 ⟨x, hx⟩))

  let H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) := ρJ.ker ⊓ ρbar.ρ.ker
  have hker : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) Lc).ker ≤ H := by
    intro τ hτ
    exact Subgroup.mem_inf.mpr
      ⟨MonoidHom.mem_ker.mpr (hL τ (fun x hx => hfix τ hτ x (hLLc hx))),
        MonoidHom.mem_ker.mpr (hL' τ (fun x hx => hfix τ hτ x (hL'Lc hx)))⟩
  let S : Finset ℕ := SJ ∪ S₀ ∪ (M * p).primeFactors
  obtain ⟨ℓ, A, τ, g, hℓ, hℓS, hA, hτ, hmem⟩ :=
    FrobeniusDensity.exists_isFrobeniusAt_conj_mem_of_le_ker Lc hker S σ
  have hℓSJ : ℓ ∉ SJ := fun h => hℓS (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hℓS₀ : ℓ ∉ S₀ := fun h => hℓS (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have hMp : M * p ≠ 0 := Nat.mul_ne_zero (NeZero.ne M) (Fact.out : p.Prime).ne_zero
  have hℓMp : ¬ ℓ ∣ M * p := fun hdvd =>
    hℓS (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hℓ, hdvd, hMp⟩))
  have hℓM : ¬ ℓ ∣ M := fun h => hℓMp (h.mul_right p)
  have hℓp : ℓ ≠ p := fun h => hℓMp (h ▸ dvd_mul_left p M)

  have h1 : Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩) = (ρJ τ).trace := (hattJ ℓ hℓ hℓSJ A hA τ hτ).1
  have h2 : LinearMap.trace k ρbar.V (ρbar.ρ τ) = ι (Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩)) :=
    hatt ℓ hℓ hℓS₀ hℓM hℓp A hA τ hτ

  have hσ : σ = (g * τ * g⁻¹ * σ⁻¹)⁻¹ * (g * τ * g⁻¹) := by group
  have hinvJ : ρJ (g * τ * g⁻¹ * σ⁻¹)⁻¹ = 1 := MonoidHom.mem_ker.mp (H.inv_mem hmem).1
  have hinvB : ρbar.ρ (g * τ * g⁻¹ * σ⁻¹)⁻¹ = 1 := MonoidHom.mem_ker.mp (H.inv_mem hmem).2
  have hρJσ : ρJ σ = ρJ g * ρJ τ * ρJ g⁻¹ := by
    conv_lhs => rw [hσ]
    rw [MonoidHom.map_mul, hinvJ, one_mul, MonoidHom.map_mul, MonoidHom.map_mul]
  have htrJ : (ρJ σ).trace = (ρJ τ).trace := by
    rw [hρJσ, Matrix.trace_mul_cycle, ← MonoidHom.map_mul, inv_mul_cancel, MonoidHom.map_one, one_mul]
  have hρBσ : ρbar.ρ σ = ρbar.ρ g * ρbar.ρ τ * ρbar.ρ g⁻¹ := by
    conv_lhs => rw [hσ]
    rw [MonoidHom.map_mul, hinvB, one_mul, MonoidHom.map_mul, MonoidHom.map_mul]
  have htrB : LinearMap.trace k ρbar.V (ρbar.ρ σ) = LinearMap.trace k ρbar.V (ρbar.ρ τ) := by
    rw [hρBσ, LinearMap.trace_mul_cycle, ← MonoidHom.map_mul, inv_mul_cancel, MonoidHom.map_one, one_mul]
  rw [← AddMonoidHom.map_trace ι (ρJ σ), htrJ, ← h1, ← h2, htrB]

theorem eq_zero_of_forall_trace_mul_eq_zero {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (D : Module.End k V)
    (h : ∀ f : Module.End k V, LinearMap.trace k V (f * D) = 0) : D = 0 := by
  by_contra hD
  obtain ⟨v, hv⟩ : ∃ v, D v ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hD (LinearMap.ext hall)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual k V, φ (D v) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hv ((Module.forall_dual_apply_eq_zero_iff k (D v)).mp hall)
  have := h (LinearMap.smulRight φ v)
  rw [show LinearMap.smulRight φ v * D = LinearMap.smulRight (φ ∘ₗ D) v from by
    ext w; simp [LinearMap.smulRight_apply]] at this
  rw [LinearMap.trace_smulRight] at this
  exact hφ this

theorem false_of_span_eq_top_of_trace_eq_of_comm {k K V G : Type*} [Field k] [CommRing K] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] (hV : Module.finrank k V = 2)
    (ι : K →+* k) (ρ : G →* Module.End k V)
    (hspan : Submodule.span k (Set.range ⇑ρ) = ⊤)
    (A : G →* Matrix (Fin 2) (Fin 2) K) (hcomm : ∀ σ τ : G, A σ * A τ = A τ * A σ)
    (htr : ∀ σ : G, ((A σ).map ι).trace = LinearMap.trace k V (ρ σ)) : False := by
  classical

  have hzero : ∀ σ τ υ : G, LinearMap.trace k V (ρ σ * (ρ τ * ρ υ - ρ υ * ρ τ)) = 0 := by
    intro σ τ υ
    rw [mul_sub, map_sub, ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← htr, ← htr,
      map_mul, map_mul, map_mul, map_mul, hcomm τ υ, sub_self]

  have hcommρ : ∀ τ υ : G, ρ τ * ρ υ = ρ υ * ρ τ := by
    intro τ υ
    have hD : ρ τ * ρ υ - ρ υ * ρ τ = 0 := by
      apply eq_zero_of_forall_trace_mul_eq_zero
      intro f
      have hf : f ∈ Submodule.span k (Set.range ⇑ρ) := by rw [hspan]; trivial
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
      · rintro _ ⟨σ, rfl⟩; exact hzero σ τ υ
      · rw [zero_mul, map_zero]
      · intro x y _ _ hx hy; rw [add_mul, map_add, hx, hy, add_zero]
      · intro c x _ hx; rw [smul_mul_assoc, map_smul, hx, smul_zero]
    exact sub_eq_zero.mp hD

  have hall : ∀ f g : Module.End k V, f * g = g * f := by
    have h1 : ∀ (τ : G) (g : Module.End k V), ρ τ * g = g * ρ τ := by
      intro τ g
      have hg : g ∈ Submodule.span k (Set.range ⇑ρ) := by rw [hspan]; trivial
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hg
      · rintro _ ⟨υ, rfl⟩; exact hcommρ τ υ
      · rw [mul_zero, zero_mul]
      · intro x y _ _ hx hy; rw [mul_add, add_mul, hx, hy]
      · intro c x _ hx; rw [mul_smul_comm, smul_mul_assoc, hx]
    intro f g
    have hf : f ∈ Submodule.span k (Set.range ⇑ρ) := by rw [hspan]; trivial
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
    · rintro _ ⟨τ, rfl⟩; exact h1 τ g
    · rw [mul_zero, zero_mul]
    · intro x y _ _ hx hy; rw [mul_add, add_mul, hx, hy]
    · intro c x _ hx; rw [mul_smul_comm, smul_mul_assoc, hx]
  obtain ⟨b⟩ : Nonempty (Module.Basis (Fin 2) k V) := by
    have := Module.finBasisOfFinrankEq k V hV
    exact ⟨this⟩
  let f : Module.End k V := b.constr k (fun i => if i = 0 then b 1 else 0)
  let g : Module.End k V := b.constr k (fun i => if i = 1 then b 0 else 0)
  have hfg := congrArg (fun h : Module.End k V => h (b 1)) (hall f g)
  simp only [Module.End.mul_apply, f, g, Module.Basis.constr_basis] at hfg

  simp at hfg
  exact b.ne_zero 1 hfg

theorem blockGen (M : ℕ) [NeZero M] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal] (hp𝔪 : ((p : ℕ) : HeckeAlg) ∈ 𝔪)
    (ρJ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) (HeckeAlg ⧸ 𝔪))
    (hfinlev : GaloisFactorsThroughFiniteLevel ρJ)
    (SJ : Finset ℕ)
    (hattJ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ SJ → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)),
      A.LiesOverPrime ℓ → ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), A.IsFrobeniusAt σ ℓ →
        Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩) = (ρJ σ).trace ∧
          Ideal.Quotient.mk 𝔪 ((ℓ : HeckeAlg)) = (ρJ σ).det)
    (hspan : Submodule.span (HeckeAlg ⧸ 𝔪) (Set.range (fun g : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) => ρJ g)) = ⊤)
    {W : Type} [AddCommGroup W] [Module (HeckeAlg ⧸ 𝔪) W] [Finite W] [Nontrivial W]
    (ρW : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End (HeckeAlg ⧸ 𝔪) W)
    (hcontW : GaloisFactorsThroughFiniteLevel ρW)
    (hESW : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ M * p → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)),
      A.LiesOverPrime ℓ → ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), A.IsFrobeniusAt σ ℓ →
        ∀ w : W, ρW σ (ρW σ w) - (Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩)) • ρW σ w
          + ((ℓ : ℕ) : HeckeAlg ⧸ 𝔪) • w = 0) :
    ∃ ιW : (Fin 2 → HeckeAlg ⧸ 𝔪) →ₗ[HeckeAlg ⧸ 𝔪] W, Function.Injective ιW ∧
      ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (v : Fin 2 → HeckeAlg ⧸ 𝔪), ιW ((ρJ σ).mulVec v) = ρW σ (ιW v) := by
  classical
  letI instMod : Module HeckeAlg W := Module.compHom W (Ideal.Quotient.mk 𝔪)
  letI instDMA : DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) W :=
    { smul := fun σ w => ρW σ w
      one_smul := fun w => by show ρW 1 w = w; rw [map_one]; rfl
      mul_smul := fun σ τ w => by show ρW (σ * τ) w = ρW σ (ρW τ w); rw [map_mul]; rfl
      smul_zero := fun σ => map_zero (ρW σ)
      smul_add := fun σ x y => map_add (ρW σ) x y }
  haveI instSMC : SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg W :=
    ⟨fun σ t w => by
      show ρW σ ((Ideal.Quotient.mk 𝔪 t) • w) = (Ideal.Quotient.mk 𝔪 t) • ρW σ w
      exact map_smul (ρW σ) _ w⟩
  have htors : heckeTorsion W 𝔪 = ⊤ := by
    refine eq_top_iff.mpr fun w _ => (mem_heckeTorsion_iff W 𝔪 w).mpr fun t ht => ?_
    show (Ideal.Quotient.mk 𝔪 t) • w = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ht]; exact zero_smul (HeckeAlg ⧸ 𝔪) w
  have hne : heckeTorsion W 𝔪 ≠ ⊥ := by rw [htors]; exact top_ne_bot
  have hfin : Finite ↥(heckeTorsion W 𝔪) := Subtype.finite
  have hES : FrobeniusQuadratic (K := ℚ) (L := AlgebraicClosure ℚ) M p W := by
    intro ℓ hℓ hℓMp A hA σ hσ w _
    show ρW σ (ρW σ w) - (Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩)) • ρW σ w + ℓ • w = 0
    rw [← Nat.cast_smul_eq_nsmul (HeckeAlg ⧸ 𝔪) ℓ w]
    exact hESW ℓ hℓ hℓMp A hA σ hσ w
  have hcont' : GaloisFactorsThroughFiniteLevel
      (mTorsionGaloisRep (G := (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) W 𝔪) := by
    obtain ⟨L, hLfin, hL⟩ := hcontW
    refine ⟨L, hLfin, fun σ hσ => ?_⟩
    apply LinearMap.ext; intro x; apply Subtype.ext
    show ρW σ (x : W) = x
    rw [hL σ hσ]; rfl
  letI : Field (HeckeAlg ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  have hpz : ((p : ℕ) : HeckeAlg ⧸ 𝔪) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk 𝔪) p]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hp𝔪
  haveI : CharP (HeckeAlg ⧸ 𝔪) p := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hpz
  have h2 : (2 : HeckeAlg ⧸ 𝔪) ≠ 0 := by
    rw [show ((2 : HeckeAlg ⧸ 𝔪)) = ((2 : ℕ) : HeckeAlg ⧸ 𝔪) by norm_cast, Ne,
      CharP.cast_eq_zero_iff (HeckeAlg ⧸ 𝔪) p 2]
    exact fun hdvd => hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hdvd)
  let S : Finset ℕ := SJ ∪ (M * p).primeFactors
  have hMp : M * p ≠ 0 := Nat.mul_ne_zero (NeZero.ne M) (Fact.out : p.Prime).ne_zero
  have hS : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ M * p := by
    intro ℓ hℓ hℓS hdvd
    exact hℓS (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hℓ, hdvd, hMp⟩))
  have hatt' : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)),
      A.LiesOverPrime ℓ → ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), A.IsFrobeniusAt σ ℓ →
        Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩) = (ρJ σ).trace ∧
          Ideal.Quotient.mk 𝔪 ((ℓ : HeckeAlg)) = (ρJ σ).det :=
    fun ℓ hℓ hℓS => hattJ ℓ hℓ (fun h => hℓS (Finset.mem_union_left _ h))
  have hdense := dense_aux ρJ (J := W) 𝔪 hfinlev hcont' S
  obtain ⟨ι₀, hι₀inj, hι₀⟩ :=
    exists_linearBlrBlock_of_span_eq_top_of_frobeniusQuadratic_of_dense (J := W) M p 𝔪 hp𝔪
      ρJ h2 hspan hES hS hatt' hdense hfin hne
  let val : ↥(heckeTorsion W 𝔪) →ₗ[HeckeAlg ⧸ 𝔪] W :=
    { toFun := fun x => (x : W)
      map_add' := fun _ _ => rfl
      map_smul' := fun c x => by
        obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective c
        rw [Submodule.torsionBySet.mk_smul]; rfl }
  refine ⟨val ∘ₗ ι₀, fun a b h => hι₀inj (Subtype.ext h), fun σ v => ?_⟩
  show ((ι₀ ((ρJ σ).mulVec v) : ↥(heckeTorsion W 𝔪)) : W) = ρW σ ((ι₀ v : ↥(heckeTorsion W 𝔪)) : W)
  rw [hι₀ σ v]; rfl

end BLBody

set_option maxHeartbeats 32000000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (M : ℕ) [NeZero M] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpM : ¬ p ∣ M)
    (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal] (hp𝔪 : ((p : ℕ) : HeckeAlg) ∈ 𝔪)
    {k : Type} [Field k] (ι : HeckeAlg ⧸ 𝔪 →+* k)
    (ρbar : ResidualGaloisRep k) (hirr : ρbar.IsAbsolutelyIrreducible) (S₀ : Finset ℕ)
    (hatt : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S₀ → ¬ ℓ ∣ M → ℓ ≠ p →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.trace k ρbar.V (ρbar.ρ σ) = ι (Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩)))
    (hsmc : letI := heckeModuleBar M
      SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg (JZero M))

    (V : letI := heckeModuleBar M; Submodule (HeckeAlg ⧸ 𝔪) ↥(heckeTorsion (JZero M) 𝔪))
    (σV : letI := heckeModuleBar M
      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End (HeckeAlg ⧸ 𝔪) ↥V)
    (hσV : letI := heckeModuleBar M; haveI := hsmc
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : ↥V),
        ((σV σ v : ↥V) : ↥(heckeTorsion (JZero M) 𝔪)) =
          mTorsionGaloisRep (JZero M) 𝔪 σ (v : ↥(heckeTorsion (JZero M) 𝔪)))
    (hfin : letI := heckeModuleBar M; Module.finrank (HeckeAlg ⧸ 𝔪) ↥V = 2)
    (e : letI := heckeModuleBar M; letI := ι.toAlgebra; (k ⊗[HeckeAlg ⧸ 𝔪] ↥V) ≃ₗ[k] ρbar.V)
    (he : letI := heckeModuleBar M; letI := ι.toAlgebra
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : k) (v : ↥V),
        e (c ⊗ₜ σV σ v) = ρbar.ρ σ (e (c ⊗ₜ v)))
    (hV : letI := heckeModuleBar M; haveI := hsmc
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ∀ x ∈ V, mTorsionGaloisRep (JZero M) 𝔪 σ x ∈ V) :
    letI := heckeModuleBar M
    haveI := hsmc
    V ≠ ⊤ →
      ∃ (V' : Submodule (HeckeAlg ⧸ 𝔪) (↥(heckeTorsion (JZero M) 𝔪) ⧸ V)) (ι' : ↥V ≃ₗ[HeckeAlg ⧸ 𝔪] ↥V'),
        (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ∀ x ∈ V',
          Submodule.mapQ V V (mTorsionGaloisRep (JZero M) 𝔪 σ) (fun y hy => hV σ y hy) x ∈ V') ∧
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : ↥V),
          ((ι' ⟨mTorsionGaloisRep (JZero M) 𝔪 σ v, hV σ v v.2⟩ : ↥V') : ↥(heckeTorsion (JZero M) 𝔪) ⧸ V) =
            Submodule.mapQ V V (mTorsionGaloisRep (JZero M) 𝔪 σ) (fun y hy => hV σ y hy)
              ((ι' v : ↥V') : ↥(heckeTorsion (JZero M) 𝔪) ⧸ V) := by
  classical
  letI := heckeModuleBar M
  haveI := hsmc
  letI := ι.toAlgebra
  letI instκN : Module (HeckeAlg ⧸ 𝔪) ↥(heckeTorsion (JZero M) 𝔪) := inferInstance
  intro hVtop
  have hfinJ : Finite ↥(heckeTorsion (JZero M) 𝔪) := BLBody.finite_heckeTorsion M p 𝔪 hp𝔪

  haveI : Nontrivial ↥V := Module.nontrivial_of_finrank_eq_succ hfin
  have hsupp : heckeTorsion (JZero M) 𝔪 ≠ ⊥ := by
    intro hbot
    obtain ⟨x, hx⟩ := exists_ne (0 : ↥V)
    apply hx
    apply Subtype.ext; apply Subtype.ext
    exact (Submodule.eq_bot_iff _).mp hbot _ ((x : ↥V) : ↥(heckeTorsion (JZero M) 𝔪)).2

  obtain ⟨ρJ, hfinlev, ⟨SJ, hattJ⟩, hspan_or_comm⟩ :=
    ModularCurve.exists_matrixRep_trace_det_frobenius_of_heckeTorsion_ne_bot M 𝔪 hsupp
  have htr : ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ((ρJ σ).map ι).trace = LinearMap.trace k ρbar.V (ρbar.ρ σ) :=
    fun σ => BLBody.trace_eq M p 𝔪 ι ρbar S₀ hatt ρJ hfinlev SJ hattJ σ
  have hspan : Submodule.span (HeckeAlg ⧸ 𝔪) (Set.range fun g : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) => ρJ g) = ⊤ := by
    rcases hspan_or_comm with h | hcomm
    · exact h
    · haveI : FiniteDimensional k ρbar.V := Module.finite_of_finrank_eq_succ ρbar.finrank_eq
      exact (BLBody.false_of_span_eq_top_of_trace_eq_of_comm ρbar.finrank_eq ι ρbar.ρ
        ((ResidualGaloisRep.isAbsolutelyIrreducible_iff_span_eq_top ρbar).mp hirr) ρJ hcomm htr).elim

  have hES := frobeniusQuadratic_JZero M p (heckeOperatorsCommuteBar M) hsmc
  have hESN : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ M * p → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)),
      A.LiesOverPrime ℓ → ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), A.IsFrobeniusAt σ ℓ →
        ∀ y : ↥(heckeTorsion (JZero M) 𝔪),
          mTorsionGaloisRep (JZero M) 𝔪 σ (mTorsionGaloisRep (JZero M) 𝔪 σ y)
            - (Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩)) • mTorsionGaloisRep (JZero M) 𝔪 σ y
            + ((ℓ : ℕ) : HeckeAlg ⧸ 𝔪) • y = 0 := by
    intro ℓ hℓ hℓMp A hA σ hσ y
    have hpx : (p : HeckeAlg) • (y : JZero M) = 0 := (mem_heckeTorsion_iff (JZero M) 𝔪 _).mp y.2 _ hp𝔪
    have hx := hES ℓ hℓ hℓMp A hA σ hσ (y : JZero M) ⟨1, by rw [pow_one, ← Nat.cast_smul_eq_nsmul HeckeAlg]; exact hpx⟩
    apply Subtype.ext
    rw [Submodule.coe_add, Submodule.coe_sub, coe_mTorsionGaloisRep_apply, coe_mTorsionGaloisRep_apply,
      Submodule.torsionBySet.mk_smul, Submodule.coe_smul, coe_mTorsionGaloisRep_apply,
      ← map_natCast (Ideal.Quotient.mk 𝔪) ℓ, Submodule.torsionBySet.mk_smul, Submodule.coe_smul,
      Nat.cast_smul_eq_nsmul, hx]
    rfl
  have hcont := mTorsionGaloisRep_jZero_galoisFactorsThroughFiniteLevel M 𝔪 hsmc hfinJ

  have hcontV : GaloisFactorsThroughFiniteLevel σV := by
    obtain ⟨L, hLfin, hL⟩ := hcont
    refine ⟨L, hLfin, fun σ hσ => ?_⟩
    apply LinearMap.ext; intro v; apply Subtype.ext
    rw [hσV, hL σ hσ]; rfl
  have hESV : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ M * p → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)),
      A.LiesOverPrime ℓ → ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), A.IsFrobeniusAt σ ℓ →
        ∀ w : ↥V, σV σ (σV σ w) - (Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩)) • σV σ w
          + ((ℓ : ℕ) : HeckeAlg ⧸ 𝔪) • w = 0 := by
    intro ℓ hℓ hℓMp A hA σ hσ w
    apply Subtype.ext
    rw [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_smul, hσV, hσV,
      hESN ℓ hℓ hℓMp A hA σ hσ]
    rfl
  haveI : Finite ↥V := Subtype.finite
  obtain ⟨ι₁, hι₁inj, hι₁⟩ := BLBody.blockGen M p hp2 𝔪 hp𝔪 ρJ hfinlev SJ hattJ hspan σV hcontV hESV
  obtain ⟨e₁, he₁⟩ : ∃ e₁ : (Fin 2 → HeckeAlg ⧸ 𝔪) ≃ₗ[HeckeAlg ⧸ 𝔪] ↥V, ∀ w, e₁ w = ι₁ w := by
    letI instF : Field (HeckeAlg ⧸ 𝔪) := Ideal.Quotient.field 𝔪
    haveI : Module.Finite (HeckeAlg ⧸ 𝔪) ↥V := Module.finite_of_finrank_eq_succ hfin
    have hsurj : Function.Surjective ι₁ := by
      have hinj := LinearMap.finrank_range_of_inj hι₁inj
      rw [Module.finrank_fin_fun] at hinj
      have htop : LinearMap.range ι₁ = ⊤ := Submodule.eq_top_of_finrank_eq (hinj.trans hfin.symm)
      exact LinearMap.range_eq_top.mp htop
    exact ⟨LinearEquiv.ofBijective ι₁ ⟨hι₁inj, hsurj⟩, fun w => rfl⟩

  let ρQ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End (HeckeAlg ⧸ 𝔪) (↥(heckeTorsion (JZero M) 𝔪) ⧸ V) :=
    { toFun := fun σ => Submodule.mapQ V V (mTorsionGaloisRep (JZero M) 𝔪 σ) (fun y hy => hV σ y hy)
      map_one' := by
        apply LinearMap.ext; intro q
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective V q
        rw [Submodule.mapQ_apply, map_one]; rfl
      map_mul' := fun σ τ => by
        apply LinearMap.ext; intro q
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective V q
        rw [Submodule.mapQ_apply, map_mul, Module.End.mul_apply, Module.End.mul_apply, Submodule.mapQ_apply,
          Submodule.mapQ_apply] }
  have hρQ : ∀ σ, ρQ σ = Submodule.mapQ V V (mTorsionGaloisRep (JZero M) 𝔪 σ) (fun y hy => hV σ y hy) := fun σ => rfl
  haveI : Finite (↥(heckeTorsion (JZero M) 𝔪) ⧸ V) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective V)
  haveI : Nontrivial (↥(heckeTorsion (JZero M) 𝔪) ⧸ V) := Submodule.Quotient.nontrivial_iff.mpr hVtop
  have hcontQ : GaloisFactorsThroughFiniteLevel ρQ := by
    obtain ⟨L, hLfin, hL⟩ := hcont
    refine ⟨L, hLfin, fun σ hσ => ?_⟩
    apply LinearMap.ext; intro q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective V q
    rw [hρQ, Submodule.mapQ_apply, hL σ hσ]; rfl
  have hESQ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ M * p → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)),
      A.LiesOverPrime ℓ → ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), A.IsFrobeniusAt σ ℓ →
        ∀ q : ↥(heckeTorsion (JZero M) 𝔪) ⧸ V, ρQ σ (ρQ σ q) - (Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩)) • ρQ σ q
          + ((ℓ : ℕ) : HeckeAlg ⧸ 𝔪) • q = 0 := by
    intro ℓ hℓ hℓMp A hA σ hσ q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective V q
    rw [hρQ, Submodule.mapQ_apply, Submodule.mapQ_apply, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
      ← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_add, hESN ℓ hℓ hℓMp A hA σ hσ y, Submodule.Quotient.mk_zero]
  obtain ⟨ι₂, hι₂inj, hι₂⟩ := BLBody.blockGen M p hp2 𝔪 hp𝔪 ρJ hfinlev SJ hattJ hspan ρQ hcontQ hESQ

  let φ : ↥V →ₗ[HeckeAlg ⧸ 𝔪] (↥(heckeTorsion (JZero M) 𝔪) ⧸ V) :=
    ι₂ ∘ₗ (e₁.symm : ↥V →ₗ[HeckeAlg ⧸ 𝔪] (Fin 2 → HeckeAlg ⧸ 𝔪))
  have hφ : ∀ v : ↥V, φ v = ι₂ (e₁.symm v) := fun v => rfl
  have hφinj : Function.Injective φ := hι₂inj.comp e₁.symm.injective
  have hφσ : ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (v : ↥V),
      φ ⟨mTorsionGaloisRep (JZero M) 𝔪 σ (v : ↥(heckeTorsion (JZero M) 𝔪)), hV σ _ v.2⟩ =
        Submodule.mapQ V V (mTorsionGaloisRep (JZero M) 𝔪 σ) (fun y hy => hV σ y hy) (φ v) := by
    intro σ v
    obtain ⟨w, rfl⟩ := e₁.surjective v
    have hσv : (⟨mTorsionGaloisRep (JZero M) 𝔪 σ (e₁ w : ↥V), hV σ _ (e₁ w).2⟩ : ↥V) = e₁ ((ρJ σ).mulVec w) := by
      apply Subtype.ext
      rw [he₁, he₁, hι₁ σ w, hσV]
    calc φ ⟨mTorsionGaloisRep (JZero M) 𝔪 σ (e₁ w : ↥V), hV σ _ (e₁ w).2⟩
        = φ (e₁ ((ρJ σ).mulVec w)) := congrArg φ hσv
      _ = ι₂ ((ρJ σ).mulVec w) := by rw [hφ, LinearEquiv.symm_apply_apply]
      _ = ρQ σ (ι₂ w) := hι₂ σ w
      _ = ρQ σ (φ (e₁ w)) := by rw [hφ, LinearEquiv.symm_apply_apply]
  refine ⟨LinearMap.range φ, LinearEquiv.ofInjective φ hφinj, ?_, ?_⟩
  · rintro σ _ ⟨v, rfl⟩
    exact ⟨_, hφσ σ v⟩
  · intro σ v
    exact (LinearEquiv.ofInjective_apply φ (h := hφinj) _).trans
      ((hφσ σ v).trans (congrArg _ (LinearEquiv.ofInjective_apply φ (h := hφinj) v).symm))

end S_ModularCurve_exists_submodule_quotient_heckeTorsion_jZero_linearEquiv_galoisStable_of_baseChange_equiv
end P2MW
export P2MW.S_ModularCurve_exists_submodule_quotient_heckeTorsion_jZero_linearEquiv_galoisStable_of_baseChange_equiv (solution)
