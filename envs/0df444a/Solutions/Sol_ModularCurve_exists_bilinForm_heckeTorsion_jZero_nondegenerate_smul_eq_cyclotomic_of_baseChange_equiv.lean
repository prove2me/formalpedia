-- Prove2me | solution 1 for ModularCurve.exists_bilinForm_heckeTorsion_jZero_nondegenerate_smul_eq_cyclotomic_of_baseChange_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/fe1d82de-965d-5cb8-8bad-796147e58ace

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_GaloisRep_Residual
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib
import Theorems.Thm_ModularCurve_frobeniusQuadratic_JZero
import Theorems.Thm_ModularCurve_heckeOperatorsCommuteBar
import Theorems.Thm_GaloisRepAdic_detIsCyclotomic_of_forall_frobenius_det_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_bilinForm_heckeTorsion_jZero_nondegenerate_smul_eq_cyclotomic_of_baseChange_equiv
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "instance" "FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow"
p2m_attr_erase "simp" "ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one"
p2m_attr_erase "simp" "ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false
set_option maxHeartbeats 160000000
set_option synthInstance.maxHeartbeats 1600000
open ModularCurve in
open scoped TensorProduct in

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
        e (c ⊗ₜ σV σ v) = ρbar.ρ σ (e (c ⊗ₜ v))) :
    letI := heckeModuleBar M
    ∃ B : ↥V →ₗ[HeckeAlg ⧸ 𝔪] ↥V →ₗ[HeckeAlg ⧸ 𝔪] (HeckeAlg ⧸ 𝔪),
      (∀ x : ↥V, (∀ y : ↥V, B x y = 0) → x = 0) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a : ℕ),
        (∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ a) →
          ∀ x y : ↥V, B (σV σ x) (σV σ y) = (a : HeckeAlg ⧸ 𝔪) • B x y) := by
  classical
  letI := heckeModuleBar M
  haveI := hsmc
  letI := ι.toAlgebra
  letI instF : Field (HeckeAlg ⧸ 𝔪) := Ideal.Quotient.field 𝔪

  haveI : Module.Finite (HeckeAlg ⧸ 𝔪) ↥V := Module.finite_of_finrank_eq_succ hfin
  let b : Module.Basis (Fin 2) (HeckeAlg ⧸ 𝔪) ↥V := Module.finBasisOfFinrankEq (HeckeAlg ⧸ 𝔪) ↥V hfin
  let B : ↥V →ₗ[(HeckeAlg ⧸ 𝔪)] ↥V →ₗ[(HeckeAlg ⧸ 𝔪)] (HeckeAlg ⧸ 𝔪) :=
    (b.coord 0).smulRight (b.coord 1) - (b.coord 1).smulRight (b.coord 0)
  have hBapply : ∀ x y : ↥V, B x y = b.repr x 0 * b.repr y 1 - b.repr x 1 * b.repr y 0 := fun x y => by
    simp [B, LinearMap.smulRight_apply, Module.Basis.coord_apply, smul_eq_mul]
  have hBdet : ∀ x y : ↥V, B x y = b.det ![x, y] := by
    intro x y
    rw [hBapply, Module.Basis.det_apply, Matrix.det_fin_two]
    simp [Module.Basis.toMatrix_apply]; ring
  have hBf : ∀ (f : ↥V →ₗ[(HeckeAlg ⧸ 𝔪)] ↥V) (x y : ↥V), B (f x) (f y) = LinearMap.det f * B x y := by
    intro f x y
    have hv : (⇑f ∘ ![x, y]) = ![f x, f y] := by
      ext i; fin_cases i <;> simp
    rw [hBdet, hBdet, ← hv, Module.Basis.det_comp]

  haveI : Module.Free (HeckeAlg ⧸ 𝔪) ↥V := Module.Free.of_divisionRing _ _
  have hconj : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ρbar.ρ σ = (e : (k ⊗[HeckeAlg ⧸ 𝔪] ↥V) →ₗ[k] ρbar.V) ∘ₗ (σV σ).baseChange k ∘ₗ
        (e.symm : ρbar.V →ₗ[k] (k ⊗[HeckeAlg ⧸ 𝔪] ↥V)) := by
    intro σ
    have h1 : (e : (k ⊗[HeckeAlg ⧸ 𝔪] ↥V) →ₗ[k] ρbar.V) ∘ₗ (σV σ).baseChange k =
        ρbar.ρ σ ∘ₗ (e : (k ⊗[HeckeAlg ⧸ 𝔪] ↥V) →ₗ[k] ρbar.V) := by
      refine LinearMap.ext fun x => ?_
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul c v => simpa [LinearMap.baseChange_tmul] using he σ c v
      | add x y hx hy => rw [map_add, map_add, hx, hy]
    rw [← LinearMap.comp_assoc, h1, LinearMap.comp_assoc]
    simp
  have htrk : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      LinearMap.trace k ρbar.V (ρbar.ρ σ) = ι (LinearMap.trace (HeckeAlg ⧸ 𝔪) ↥V (σV σ)) := by
    intro σ
    rw [hconj σ, ← LinearMap.comp_assoc, ← LinearEquiv.conj_apply, LinearMap.trace_conj', LinearMap.trace_baseChange]
    rfl
  have hdetk : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      LinearMap.det (ρbar.ρ σ) = ι (LinearMap.det (σV σ)) := by
    intro σ
    rw [hconj σ, LinearMap.det_conj, LinearMap.det_baseChange]
    rfl
  have hιinj : Function.Injective ι := ι.injective
  refine ⟨B, ?_, ?_⟩
  ·
    intro x hx
    have h1 := hx (b 1)
    have h0 := hx (b 0)
    rw [hBapply] at h1 h0
    simp only [Module.Basis.repr_self, Finsupp.single_eq_same, ne_eq, one_ne_zero, not_false_eq_true,
      Finsupp.single_eq_of_ne, zero_ne_one, mul_one, mul_zero, sub_zero, zero_sub, neg_eq_zero, Fin.one_eq_zero_iff,
      Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, Finsupp.single_eq_of_ne'] at h1 h0
    refine b.ext_elem fun i => ?_
    fin_cases i
    · simpa using h1
    · simpa using h0
  ·
    have hES := ModularCurve.frobeniusQuadratic_JZero M p (ModularCurve.heckeOperatorsCommuteBar M) hsmc

    have hdetFrob : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S₀ → ¬ ℓ ∣ M → ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            LinearMap.det (σV σ) = (ℓ : HeckeAlg ⧸ 𝔪) := by
      intro ℓ hℓ hℓS hℓM hℓp A hA σ hσ
      have hℓMp : ¬ ℓ ∣ M * p := by
        intro h; rcases (Nat.Prime.dvd_mul hℓ).mp h with h | h
        · exact hℓM h
        · exact hℓp ((Nat.prime_dvd_prime_iff_eq hℓ Fact.out).mp h)

      have hESV : σV σ * σV σ - (Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩)) • σV σ
          + ((ℓ : ℕ) : HeckeAlg ⧸ 𝔪) • (1 : Module.End (HeckeAlg ⧸ 𝔪) ↥V) = 0 := by
        ext v
        have hpx : (p : HeckeAlg) • ((v : ↥(heckeTorsion (JZero M) 𝔪)) : JZero M) = 0 :=
          (mem_heckeTorsion_iff (JZero M) 𝔪 _).mp (v : ↥(heckeTorsion (JZero M) 𝔪)).2 _ hp𝔪
        have hx := hES ℓ hℓ hℓMp A hA σ hσ ((v : ↥(heckeTorsion (JZero M) 𝔪)) : JZero M)
          ⟨1, by rw [pow_one, ← Nat.cast_smul_eq_nsmul HeckeAlg]; exact hpx⟩
        have hcoe : ∀ w : ↥V, (((σV σ w : ↥V) : ↥(heckeTorsion (JZero M) 𝔪)) : JZero M) =
            σ • ((w : ↥(heckeTorsion (JZero M) 𝔪)) : JZero M) := fun w => by rw [hσV]; rfl
        have e1 : (((σV σ (σV σ v) : ↥V) : ↥(heckeTorsion (JZero M) 𝔪)) : JZero M) =
            σ • σ • ((v : ↥(heckeTorsion (JZero M) 𝔪)) : JZero M) := by rw [hcoe, hcoe]
        have e2 : ((((Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩)) • σV σ v : ↥V) : ↥(heckeTorsion (JZero M) 𝔪)) : JZero M) =
            heckeGen ⟨ℓ, hℓ⟩ • (σ • ((v : ↥(heckeTorsion (JZero M) 𝔪)) : JZero M)) := by
          rw [Submodule.coe_smul, Submodule.torsionBySet.mk_smul, Submodule.coe_smul, hcoe]
        have e3 : (((((ℓ : ℕ) : HeckeAlg ⧸ 𝔪) • v : ↥V) : ↥(heckeTorsion (JZero M) 𝔪)) : JZero M) =
            ℓ • ((v : ↥(heckeTorsion (JZero M) 𝔪)) : JZero M) := by
          rw [Submodule.coe_smul, ← map_natCast (Ideal.Quotient.mk 𝔪) ℓ, Submodule.torsionBySet.mk_smul,
            Submodule.coe_smul, Nat.cast_smul_eq_nsmul]
        rw [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, LinearMap.smul_apply,
          Module.End.one_apply, LinearMap.zero_apply, Submodule.coe_add, Submodule.coe_sub, Submodule.coe_add,
          Submodule.coe_sub, e1, e2, e3, hx]
        rfl

      have htr : LinearMap.trace (HeckeAlg ⧸ 𝔪) ↥V (σV σ) = Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩) :=
        hιinj ((htrk σ).symm.trans (hatt ℓ hℓ hℓS hℓM hℓp A hA σ hσ))

      have htrA : (LinearMap.toMatrix b b (σV σ)).trace = Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩) := by
        rw [← LinearMap.trace_eq_matrix_trace (HeckeAlg ⧸ 𝔪) b, htr]
      have hmatES : LinearMap.toMatrix b b (σV σ) * LinearMap.toMatrix b b (σV σ)
          - (Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩)) • LinearMap.toMatrix b b (σV σ)
          + ((ℓ : ℕ) : HeckeAlg ⧸ 𝔪) • (1 : Matrix (Fin 2) (Fin 2) (HeckeAlg ⧸ 𝔪)) = 0 := by
        have h := congrArg (LinearMap.toMatrix b b) hESV
        simpa [LinearMap.toMatrix_mul, LinearMap.toMatrix_one, map_add, map_sub, map_smul] using h
      rw [htrA.symm] at hmatES
      have h00 := congrFun (congrFun hmatES 0) 0
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
        Matrix.trace_fin_two, Matrix.one_apply_eq, smul_eq_mul, mul_one, Matrix.zero_apply] at h00
      rw [← LinearMap.det_toMatrix b, Matrix.det_fin_two]
      linear_combination -h00

    have hpκ : ((p : ℕ) : HeckeAlg ⧸ 𝔪) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk 𝔪) p]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hp𝔪
    have hpk : ((p : ℕ) : k) = 0 := by rw [← map_natCast ι p, hpκ, map_zero]
    have hdetc : (GaloisRepAdic.ofResidualGaloisRep ρbar).DetIsCyclotomic p := by
      refine GaloisRepAdic.detIsCyclotomic_of_forall_frobenius_det_eq (GaloisRepAdic.ofResidualGaloisRep ρbar)
        Fact.out (by rw [hpk]; exact Ideal.zero_mem _) (S₀ ∪ (M * p).primeFactors) ?_
      intro ℓ hℓ hℓS A τ hA hτ
      rw [Finset.mem_union, not_or] at hℓS
      have hℓMp : ¬ ℓ ∣ M * p := fun h =>
        hℓS.2 (Nat.mem_primeFactors.mpr ⟨hℓ, h, mul_ne_zero (NeZero.ne M) (Fact.out : p.Prime).ne_zero⟩)
      have hℓM : ¬ ℓ ∣ M := fun h => hℓMp (h.mul_right p)
      have hℓp : ℓ ≠ p := fun h => hℓMp (h ▸ dvd_mul_left p M)
      show LinearMap.det (ρbar.ρ τ) = (ℓ : k)
      rw [hdetk τ, hdetFrob ℓ hℓ hℓS.1 hℓM hℓp A hA τ hτ, map_natCast]

    intro σ a hμ x y
    have hdσ : LinearMap.det (ρbar.ρ σ) = (a : k) := by
      have h := hdetc.2 1 σ a (by simpa only [pow_one] using hμ)
      rw [pow_one, hpk, Ideal.span_singleton_zero, Ideal.mem_bot, sub_eq_zero] at h
      exact h
    have hdV : LinearMap.det (σV σ) = (a : HeckeAlg ⧸ 𝔪) :=
      hιinj ((hdetk σ).symm.trans (hdσ.trans (map_natCast ι a).symm))
    rw [hBf, hdV, smul_eq_mul]

end S_ModularCurve_exists_bilinForm_heckeTorsion_jZero_nondegenerate_smul_eq_cyclotomic_of_baseChange_equiv
end P2MW
export P2MW.S_ModularCurve_exists_bilinForm_heckeTorsion_jZero_nondegenerate_smul_eq_cyclotomic_of_baseChange_equiv (solution)
