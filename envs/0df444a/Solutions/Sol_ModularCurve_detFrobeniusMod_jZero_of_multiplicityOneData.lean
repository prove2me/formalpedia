-- Prove2me | solution 1 for ModularCurve.detFrobeniusMod_jZero_of_multiplicityOneData
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/4c7fe21e-4718-5745-9e63-80dd33e3cdf5

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_HeckeGalois_EichlerShimura
import Theorems.Thm_ModularCurve_heckeTorsion_jZero_finite_of_natCast_mem
import Theorems.Thm_ModularCurve_exists_pairing_family_pow_nsmul_eq_zero_galois_hecke_compat
import Theorems.Thm_ModularCurve_frobeniusQuadratic_JZero
import Theorems.Thm_ModularCurve_heckeOperatorsCommuteBar
import Theorems.Thm_ValuationSubring_IsFrobeniusAt_apply_eq_pow_of_pow_eq_one
import Mathlib.RingTheory.Finiteness.Nakayama
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_detFrobeniusMod_jZero_of_multiplicityOneData
p2m_attr_erase "instance" "CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE"
p2m_attr_erase "instance" "AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.coe_towerInclBar"
p2m_attr_erase "simp" "ModularCurve.coe_towerSubstBar PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk"
p2m_attr_erase "simp" "ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero AlgebraicCurve.DivisorialWeilPairingData.toChar_apply AlgebraicCurve.WeilDatum.coe_classRight AlgebraicCurve.WeilDatum.coe_degZeroRight AlgebraicCurve.DivisorialWeilPairingData.mk.sizeOf_spec AlgebraicCurve.WeilDatum.coe_classLeft AlgebraicCurve.WeilDatum.coe_degZeroLeft AlgebraicCurve.DivisorialWeilPairingData.mk.injEq AlgebraicCurve.DivisorialWeilPairingData.toHom_apply_apply"
p2m_attr_erase "simp" "AlgebraicCurve.WeilDatum.mk.sizeOf_spec AlgebraicCurve.WeilDatum.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_zero AlgebraicCurve.PrincipalPolarization.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_apply AlgebraicCurve.H1Gm.degree_ofPic0 AlgebraicCurve.WeilPairingData.mk.sizeOf_spec AlgebraicCurve.HomPic0Gm.map_one AlgebraicCurve.PrincipalPolarization.mk.sizeOf_spec AlgebraicCurve.WeilPairingData.autodualityEquiv_apply AlgebraicCurve.WeilPairingData.eval_zero_right AlgebraicCurve.H1Gm.ofPic0_mk AlgebraicCurve.WeilPairingData.eval_neg_left AlgebraicCurve.HomPic0Gm.map_apply AlgebraicCurve.H1Gm.degree_mk AlgebraicCurve.HomPic0Gm.map_id AlgebraicCurve.WeilPairingData.mk.injEq AlgebraicCurve.WeilPairingData.congr_eval AlgebraicCurve.WeilPairingData.eval_neg_right AlgebraicCurve.WeilPairingData.eval_zero_left AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.tateMap_apply TateModule.smul_apply TateModule.coe_mulP"
p2m_attr_erase "simp" "TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero"
p2m_attr_erase "simp" "WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"
p2m_attr_erase "simp" "FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false

namespace FrobeniusDeterminant

open ModularCurve

section LastLayer

variable {T : Type*} [CommRing T] {J : Type*} [AddCommGroup J] [Module T J]

private theorem pow_succ_smul_eq (I : Ideal T) (W : Submodule T J) (k : ℕ) :
    I ^ (k + 1) • W = I • (I ^ k • W) := by
  rw [pow_succ', Submodule.mul_smul]

private theorem pow_succ_smul_le (I : Ideal T) (W : Submodule T J) (k : ℕ) : I ^ (k + 1) • W ≤ I ^ k • W := by
  rw [pow_succ_smul_eq]
  exact Submodule.smul_le_right

private theorem pow_zero_smul_eq (I : Ideal T) (W : Submodule T J) : I ^ 0 • W = W := by
  rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]

private theorem exists_pow_succ_smul_eq (I : Ideal T) (W : Submodule T J) [Finite W] :
    ∃ k : ℕ, I ^ (k + 1) • W = I ^ k • W := by
  by_contra h
  push Not at h
  have hfin : (W : Set J).Finite := Set.toFinite _
  have hle : ∀ k : ℕ, ((I ^ k • W : Submodule T J) : Set J) ⊆ (W : Set J) := fun k =>
    (Submodule.smul_le_right : I ^ k • W ≤ W)
  have hcard : ∀ k : ℕ, ((I ^ k • W : Submodule T J) : Set J).ncard + k ≤ (W : Set J).ncard := by
    intro k
    induction k with
    | zero => rw [pow_zero_smul_eq, add_zero]
    | succ k ih =>
      have hlt : ((I ^ (k + 1) • W : Submodule T J) : Set J) ⊂ ((I ^ k • W : Submodule T J) : Set J) :=
        SetLike.coe_ssubset_coe.mpr (lt_of_le_of_ne (pow_succ_smul_le I W k) (h k))
      have hlt' := Set.ncard_lt_ncard hlt (hfin.subset (hle k))
      omega
  have h' := hcard ((W : Set J).ncard + 1)
  omega

private theorem smul_eq_zero_of_forall (I' : Ideal T) (W : Submodule T J) (s : T)
    (h : ∀ u ∈ I', ∀ x ∈ W, s • u • x = 0) : ∀ y ∈ I' • W, s • y = 0 := by
  intro y hy
  refine Submodule.smul_induction_on hy h ?_
  intro y z ihy ihz
  rw [smul_add, ihy, ihz, add_zero]

private theorem exists_last_layer (I : Ideal T) (W : Submodule T J) [Finite W]
    (hVW : Submodule.torsionBySet T J I ≤ W) (hV : Submodule.torsionBySet T J I ≠ ⊥) :
    ∃ t : T, (∀ w ∈ W, ∀ m ∈ I, m • t • w = 0) ∧ ∃ w ∈ W, t • w ≠ 0 := by
  classical

  have hex := exists_pow_succ_smul_eq I W
  set n := Nat.find hex with hn
  have hstab : I ^ (n + 1) • W = I ^ n • W := Nat.find_spec hex

  have hfg : (I ^ n • W : Submodule T J).FG := by
    rw [Submodule.fg_def]
    refine ⟨((I ^ n • W : Submodule T J) : Set J), ?_, Submodule.span_eq _⟩
    exact (Set.toFinite (W : Set J)).subset (Submodule.smul_le_right : I ^ n • W ≤ W)
  obtain ⟨s, hs1, hs⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I (I ^ n • W) hfg
    (by rw [← pow_succ_smul_eq, hstab])

  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hV
  have hvI : ∀ m ∈ I, m • v = 0 := fun m hm => (Submodule.mem_torsionBySet_iff (I : Set T) v).mp hv ⟨m, hm⟩
  have hsv : s • v = v := by
    have h1 : (s - 1) • v = 0 := hvI _ hs1
    rwa [sub_smul, one_smul, sub_eq_zero] at h1

  have hn0 : n ≠ 0 := by
    intro h0
    apply hv0
    rw [← hsv]
    apply hs
    rw [h0, pow_zero_smul_eq]
    exact hVW hv
  obtain ⟨n', hn'⟩ := Nat.exists_eq_succ_of_ne_zero hn0

  have hlt : I ^ (n' + 1) • W ≠ I ^ n' • W := Nat.find_min hex (by rw [← hn, hn']; exact Nat.lt_succ_self n')

  have hux : ∃ u ∈ I ^ n', ∃ x ∈ W, s • u • x ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hlt
    refine le_antisymm (pow_succ_smul_le I W n') ?_
    intro y hy
    have hsy : s • y = 0 := smul_eq_zero_of_forall (I ^ n') W s hall y hy
    have hy' : y = -((s - 1) • y) := by
      rw [sub_smul, one_smul, hsy, zero_sub, neg_neg]
    rw [hy', pow_succ_smul_eq]
    exact Submodule.neg_mem _ (Submodule.smul_mem_smul hs1 hy)
  obtain ⟨u, hu, x, hx, hsux⟩ := hux
  refine ⟨s * u, ?_, x, hx, by rwa [mul_smul]⟩
  intro w hw m hm
  have hmu : (m * u) • w ∈ I ^ n • W := by
    rw [hn']
    exact Submodule.smul_mem_smul (by rw [pow_succ']; exact Ideal.mul_mem_mul hm hu) hw
  calc m • (s * u) • w = s • ((m * u) • w) := by rw [mul_smul, smul_comm m s, mul_smul]
    _ = 0 := hs _ hmu

end LastLayer

section Scalar

variable {T : Type*} [CommRing T] {J : Type*} [AddCommGroup J] [Module T J] {L : Type*} [Field L]

private theorem pairing_zero_right (W : Submodule T J) (B : J → J → L)
    (hmul : ∀ x y y' : J, x ∈ W → y ∈ W → y' ∈ W → B x (y + y') = B x y * B x y')
    (hne : ∀ x y : J, x ∈ W → y ∈ W → B x y ≠ 0) {x : J} (hx : x ∈ W) : B x 0 = 1 := by
  have h := hmul x 0 0 hx W.zero_mem W.zero_mem
  rw [add_zero] at h
  exact ((mul_eq_left₀ (hne x 0 hx W.zero_mem)).mp h.symm)

private theorem pairing_nsmul_right (W : Submodule T J) (B : J → J → L)
    (hmul : ∀ x y y' : J, x ∈ W → y ∈ W → y' ∈ W → B x (y + y') = B x y * B x y')
    (hne : ∀ x y : J, x ∈ W → y ∈ W → B x y ≠ 0) {x y : J} (hx : x ∈ W) (hy : y ∈ W) (n : ℕ) :
    B x (n • y) = B x y ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, pairing_zero_right W B hmul hne hx]
  | succ n ih => rw [succ_nsmul, hmul x _ _ hx (nsmul_mem hy n) hy, ih, pow_succ]

private theorem mul_self_sub_natCast_mem_of_scalar (𝔪 : Ideal T) [𝔪.IsMaximal] (W : Submodule T J)
    (B : J → J → L)
    (hmul : ∀ x y y' : J, x ∈ W → y ∈ W → y' ∈ W → B x (y + y') = B x y * B x y')
    (hbal : ∀ (a : T) (x y : J), x ∈ W → y ∈ W → B (a • x) y = B x (a • y))
    (hperf : ∀ y ∈ W, (∀ x ∈ W, B x y = 1) → y = 0)
    (hne : ∀ x y : J, x ∈ W → y ∈ W → B x y ≠ 0)
    (g : J →ₗ[T] J) (hgW : ∀ x ∈ W, g x ∈ W) (ℓ : ℕ)
    (hg : ∀ x y : J, x ∈ W → y ∈ W → B (g x) (g y) = B x y ^ ℓ)
    (c : T) (hc : ∀ v ∈ Submodule.torsionBySet T J 𝔪, g v = c • v)
    (t : T) (htV : ∀ w ∈ W, ∀ m ∈ 𝔪, m • t • w = 0) (htne : ∃ w ∈ W, t • w ≠ 0) :
    c * c - ℓ ∈ 𝔪 := by

  have htors : ∀ w ∈ W, t • w ∈ Submodule.torsionBySet T J 𝔪 := fun w hw =>
    (Submodule.mem_torsionBySet_iff (𝔪 : Set T) (t • w)).mpr fun m => htV w hw m m.2
  have hgt : ∀ w ∈ W, g (t • w) = c • t • w := fun w hw => hc _ (htors w hw)

  have hkill : ∀ y ∈ W, (c * c - ℓ) • t • y = 0 := by
    intro y hy
    have hty : t • y ∈ W := W.smul_mem t hy
    have hgy : g y ∈ W := hgW y hy

    have hcomp : ∀ x ∈ W, B (t • x) (c • g y) = B (t • x) (ℓ • y) := by
      intro x hx
      have htx : t • x ∈ W := W.smul_mem t hx
      rw [← hbal c (t • x) (g y) htx hgy, ← hgt x hx, hg (t • x) y htx hy,
        pairing_nsmul_right W B hmul hne htx hy ℓ]

    have hz : c • g y - ℓ • y ∈ W := W.sub_mem (W.smul_mem c hgy) (nsmul_mem hy ℓ)
    have hone : ∀ x ∈ W, B x (t • (c • g y - ℓ • y)) = 1 := by
      intro x hx
      have htx : t • x ∈ W := W.smul_mem t hx
      have h := hmul (t • x) (c • g y - ℓ • y) (ℓ • y) htx hz (nsmul_mem hy ℓ)
      rw [sub_add_cancel, hcomp x hx] at h
      rw [← hbal t x _ hx hz]
      exact (mul_eq_right₀ (hne (t • x) (ℓ • y) htx (nsmul_mem hy ℓ))).mp h.symm

    have hzero : t • (c • g y - ℓ • y) = 0 := hperf _ (W.smul_mem t hz) hone
    rw [smul_sub, smul_comm t c, ← g.map_smul, hgt y hy, smul_comm t ℓ, ← smul_assoc] at hzero
    rw [sub_smul, Nat.cast_smul_eq_nsmul]
    rwa [smul_eq_mul] at hzero

  by_contra hnot
  obtain ⟨r, i, hi, hri⟩ := Ideal.IsMaximal.exists_inv ‹𝔪.IsMaximal› hnot
  obtain ⟨w, hw, htw⟩ := htne
  apply htw
  calc t • w = (r * (c * c - ℓ) + i) • t • w := by rw [hri, one_smul]
    _ = r • ((c * c - ℓ) • t • w) + i • t • w := by rw [add_smul, mul_smul]
    _ = 0 := by rw [hkill w hw, smul_zero, zero_add, htV w hw i hi]

end Scalar

private theorem det_eq_of_not_scalar {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (h2 : Module.finrank F V = 2) (f : V →ₗ[F] V) (a d : F)
    (hf : f * f - a • f + d • (1 : V →ₗ[F] V) = 0) (hns : ∀ c : F, f ≠ c • (1 : V →ₗ[F] V)) :
    LinearMap.det f = d := by
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (by rw [h2]; exact two_pos)
  let b : Module.Basis (Fin 2) F V := Module.finBasisOfFinrankEq F V h2
  set A : Matrix (Fin 2) (Fin 2) F := LinearMap.toMatrix b b f with hA
  have hM : A * A - a • A + d • (1 : Matrix (Fin 2) (Fin 2) F) = 0 := by
    have h := congrArg (LinearMap.toMatrix b b) hf
    rwa [map_zero, map_add, map_sub, map_smul, map_smul, LinearMap.toMatrix_mul, LinearMap.toMatrix_one] at h
  have E : ∀ i j : Fin 2, (A * A - a • A + d • (1 : Matrix (Fin 2) (Fin 2) F)) i j = 0 := fun i j => by
    rw [hM]; rfl
  have e00 := E 0 0
  have e01 := E 0 1
  have e10 := E 1 0
  have e11 := E 1 1
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), smul_eq_mul, mul_one, mul_zero, Fin.isValue]
    at e00 e01 e10 e11
  rw [← LinearMap.det_toMatrix b, ← hA, Matrix.det_fin_two]
  by_cases htr : A 0 0 + A 1 1 = a
  · linear_combination (-1 : F) * e00 + A 0 0 * htr
  · exfalso
    have hsub : A 0 0 + A 1 1 - a ≠ 0 := sub_ne_zero.mpr htr
    have h01 : A 0 1 = 0 := by
      have : A 0 1 * (A 0 0 + A 1 1 - a) = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_right hsub
    have h10 : A 1 0 = 0 := by
      have : A 1 0 * (A 0 0 + A 1 1 - a) = 0 := by linear_combination e10
      exact (mul_eq_zero.mp this).resolve_right hsub
    have hdiag : A 0 0 = A 1 1 := by
      have : (A 0 0 - A 1 1) * (A 0 0 + A 1 1 - a) = 0 := by
        linear_combination e00 - e11 + (A 1 0 - A 1 0) * h01
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hsub)
    apply hns (A 0 0)
    apply (LinearMap.toMatrix b b).injective
    rw [map_smul, LinearMap.toMatrix_one, ← hA]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.smul_apply, h01, h10, hdiag]

private theorem det_smul_one {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (h2 : Module.finrank F V = 2) (c : F) :
    LinearMap.det (c • (1 : V →ₗ[F] V)) = c * c := by
  rw [LinearMap.det_smul, map_one, h2, mul_one, sq]

private theorem sub_smul_add_smul_one_eq_zero {G : Type*} [Group G] {J : Type} [AddCommGroup J]
    [Module HeckeAlg J] [DistribMulAction G J] [SMulCommClass G HeckeAlg J] (𝔪 : Ideal HeckeAlg)
    (σ : G) (Tl : HeckeAlg) (ℓ : ℕ)
    (h : ∀ x ∈ heckeTorsion J 𝔪, σ • σ • x - Tl • (σ • x) + ℓ • x = 0) :
    mTorsionGaloisRep J 𝔪 σ * mTorsionGaloisRep J 𝔪 σ -
        Ideal.Quotient.mk 𝔪 Tl • mTorsionGaloisRep J 𝔪 σ +
        (ℓ : HeckeAlg ⧸ 𝔪) • (1 : Module.End (HeckeAlg ⧸ 𝔪) (heckeTorsion J 𝔪)) = 0 := by
  ext x
  have hx := h x x.2
  simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    Module.End.one_apply, LinearMap.zero_apply, Submodule.coe_add, Submodule.coe_sub, Submodule.coe_zero,
    coe_mTorsionGaloisRep_apply]
  rw [← map_natCast (Ideal.Quotient.mk 𝔪) ℓ, Submodule.torsionBySet.mk_smul, Submodule.torsionBySet.mk_smul,
    Submodule.coe_smul, Submodule.coe_smul, Nat.cast_smul_eq_nsmul]
  exact hx

private theorem smul_eq_smul_of_eq_smul_one {G : Type*} [Group G] {J : Type} [AddCommGroup J]
    [Module HeckeAlg J] [DistribMulAction G J] [SMulCommClass G HeckeAlg J] (𝔪 : Ideal HeckeAlg)
    (σ : G) (c : HeckeAlg)
    (h : mTorsionGaloisRep J 𝔪 σ =
      Ideal.Quotient.mk 𝔪 c • (1 : Module.End (HeckeAlg ⧸ 𝔪) (heckeTorsion J 𝔪))) :
    ∀ v ∈ heckeTorsion J 𝔪, σ • v = c • v := by
  intro v hv
  have hv' := congrArg
    (fun φ : Module.End (HeckeAlg ⧸ 𝔪) (heckeTorsion J 𝔪) => ((φ ⟨v, hv⟩ : heckeTorsion J 𝔪) : J)) h
  simpa only [coe_mTorsionGaloisRep_apply, LinearMap.smul_apply, Module.End.one_apply,
    Submodule.torsionBySet.mk_smul, Submodule.coe_smul] using hv'

private theorem mem_heckeTorsion_span_natCast_iff {J : Type} [AddCommGroup J] [Module HeckeAlg J]
    (p : ℕ) (x : J) : x ∈ heckeTorsion J (Ideal.span {(p : HeckeAlg)}) ↔ p • x = 0 := by
  rw [mem_heckeTorsion_iff]
  constructor
  · intro hx
    rw [← Nat.cast_smul_eq_nsmul HeckeAlg]
    exact hx _ (Ideal.mem_span_singleton_self _)
  · intro hx t ht
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp ht
    rw [mul_smul, Nat.cast_smul_eq_nsmul, hx, smul_zero]

private theorem heckeTorsion_le_heckeTorsion {J : Type} [AddCommGroup J] [Module HeckeAlg J]
    {I I' : Ideal HeckeAlg} (h : I ≤ I') : heckeTorsion J I' ≤ heckeTorsion J I := by
  intro x hx
  rw [mem_heckeTorsion_iff] at hx ⊢
  exact fun t ht => hx t (h ht)

private theorem det_eq_natCast_of_pairing {J : Type} [AddCommGroup J] [Module HeckeAlg J]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg J]
    (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal] {p : ℕ} (hp : p.Prime) (hp𝔪 : (p : HeckeAlg) ∈ 𝔪)
    (hrank : Module.finrank (HeckeAlg ⧸ 𝔪) (heckeTorsion J 𝔪) = 2)
    [Finite (heckeTorsion J (Ideal.span {(p : HeckeAlg)}))]
    (B : J → J → AlgebraicClosure ℚ)
    (hroot : ∀ x y : J, p ^ 1 • x = 0 → p ^ 1 • y = 0 → B x y ^ p ^ 1 = 1)
    (hmul : ∀ x y y' : J, p ^ 1 • x = 0 → p ^ 1 • y = 0 → p ^ 1 • y' = 0 →
      B x (y + y') = B x y * B x y')
    (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hgal : ∀ x y : J, p ^ 1 • x = 0 → p ^ 1 • y = 0 → B (σ • x) (σ • y) = σ (B x y))
    (hbal : ∀ (t : HeckeAlg) (x y : J), p ^ 1 • x = 0 → p ^ 1 • y = 0 → B (t • x) y = B x (t • y))
    (hperf : ∀ y : J, p ^ 1 • y = 0 → (∀ x : J, p ^ 1 • x = 0 → B x y = 1) → y = 0)
    {ℓ : ℕ} (T : HeckeAlg)
    (hFQ : ∀ x : J, (∃ n : ℕ, p ^ n • x = 0) → σ • σ • x - T • (σ • x) + ℓ • x = 0)
    (hμ : ∀ z : AlgebraicClosure ℚ, z ^ p = 1 → σ z = z ^ ℓ) :
    LinearMap.det (mTorsionGaloisRep J 𝔪 σ) = (ℓ : HeckeAlg ⧸ 𝔪) := by
  letI : Field (HeckeAlg ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  haveI : FiniteDimensional (HeckeAlg ⧸ 𝔪) (heckeTorsion J 𝔪) :=
    Module.finite_of_finrank_eq_succ hrank

  have hVW : heckeTorsion J 𝔪 ≤ heckeTorsion J (Ideal.span {(p : HeckeAlg)}) :=
    heckeTorsion_le_heckeTorsion ((Ideal.span_singleton_le_iff_mem 𝔪).mpr hp𝔪)
  have hW : ∀ x : J, x ∈ heckeTorsion J (Ideal.span {(p : HeckeAlg)}) ↔ p ^ 1 • x = 0 :=
    fun x => by rw [pow_one]; exact mem_heckeTorsion_span_natCast_iff p x

  have hES := sub_smul_add_smul_one_eq_zero 𝔪 σ T ℓ
    (fun x hx => hFQ x ⟨1, (hW x).mp (hVW hx)⟩)
  by_cases hsc : ∃ c : HeckeAlg ⧸ 𝔪, mTorsionGaloisRep J 𝔪 σ =
      c • (1 : Module.End (HeckeAlg ⧸ 𝔪) (heckeTorsion J 𝔪))
  ·
    obtain ⟨c, hc⟩ := hsc
    obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [hc, det_smul_one hrank]

    have hVne : heckeTorsion J 𝔪 ≠ ⊥ := by
      intro h
      haveI : Subsingleton (heckeTorsion J 𝔪) :=
        ⟨fun a b => Subtype.ext (((Submodule.eq_bot_iff _).mp h a.1 a.2).trans
          ((Submodule.eq_bot_iff _).mp h b.1 b.2).symm)⟩
      have h0 : Module.finrank (HeckeAlg ⧸ 𝔪) (heckeTorsion J 𝔪) = 0 :=
        Module.finrank_zero_of_subsingleton
      omega
    have hlayer := exists_last_layer 𝔪 (heckeTorsion J (Ideal.span {(p : HeckeAlg)})) hVW hVne
    obtain ⟨t, htV, htne⟩ := hlayer

    have hmul' : ∀ x y y' : J, x ∈ heckeTorsion J (Ideal.span {(p : HeckeAlg)}) →
        y ∈ heckeTorsion J (Ideal.span {(p : HeckeAlg)}) → y' ∈ heckeTorsion J (Ideal.span {(p : HeckeAlg)}) →
        B x (y + y') = B x y * B x y' :=
      fun x y y' hx hy hy' => hmul x y y' ((hW x).mp hx) ((hW y).mp hy) ((hW y').mp hy')
    have hbal' : ∀ (a : HeckeAlg) (x y : J), x ∈ heckeTorsion J (Ideal.span {(p : HeckeAlg)}) →
        y ∈ heckeTorsion J (Ideal.span {(p : HeckeAlg)}) → B (a • x) y = B x (a • y) :=
      fun a x y hx hy => hbal a x y ((hW x).mp hx) ((hW y).mp hy)
    have hperf' : ∀ y ∈ heckeTorsion J (Ideal.span {(p : HeckeAlg)}),
        (∀ x ∈ heckeTorsion J (Ideal.span {(p : HeckeAlg)}), B x y = 1) → y = 0 :=
      fun y hy h1 => hperf y ((hW y).mp hy) (fun x hx => h1 x ((hW x).mpr hx))
    have hne' : ∀ x y : J, x ∈ heckeTorsion J (Ideal.span {(p : HeckeAlg)}) →
        y ∈ heckeTorsion J (Ideal.span {(p : HeckeAlg)}) → B x y ≠ 0 := by
      intro x y hx hy h0
      have h1 := hroot x y ((hW x).mp hx) ((hW y).mp hy)
      rw [h0, zero_pow (pow_ne_zero 1 hp.ne_zero)] at h1
      exact zero_ne_one h1
    have hgW : ∀ x ∈ heckeTorsion J (Ideal.span {(p : HeckeAlg)}),
        DistribSMul.toLinearMap HeckeAlg J σ x ∈ heckeTorsion J (Ideal.span {(p : HeckeAlg)}) :=
      fun x hx => smul_mem_heckeTorsion J σ hx
    have hg' : ∀ x y : J, x ∈ heckeTorsion J (Ideal.span {(p : HeckeAlg)}) →
        y ∈ heckeTorsion J (Ideal.span {(p : HeckeAlg)}) →
        B (DistribSMul.toLinearMap HeckeAlg J σ x) (DistribSMul.toLinearMap HeckeAlg J σ y) =
          B x y ^ ℓ := by
      intro x y hx hy
      show B (σ • x) (σ • y) = B x y ^ ℓ
      rw [hgal x y ((hW x).mp hx) ((hW y).mp hy)]
      apply hμ
      rw [← pow_one p]
      exact hroot x y ((hW x).mp hx) ((hW y).mp hy)
    have hc' : ∀ v ∈ Submodule.torsionBySet HeckeAlg J (𝔪 : Set HeckeAlg),
        DistribSMul.toLinearMap HeckeAlg J σ v = c' • v := by
      intro v hv
      show σ • v = c' • v
      exact smul_eq_smul_of_eq_smul_one 𝔪 σ c' hc v hv
    have key : c' * c' - ℓ ∈ 𝔪 :=
      mul_self_sub_natCast_mem_of_scalar 𝔪 (heckeTorsion J (Ideal.span {(p : HeckeAlg)})) B hmul' hbal'
        hperf' hne' (DistribSMul.toLinearMap HeckeAlg J σ) hgW ℓ hg' c' hc' t htV htne
    rw [← map_mul, ← map_natCast (Ideal.Quotient.mk 𝔪), ← sub_eq_zero, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr key
  ·
    exact det_eq_of_not_scalar hrank _ _ _ hES (fun c h => hsc ⟨c, h⟩)

end FrobeniusDeterminant

open ModularCurve in

theorem solution
    (M : ℕ) [NeZero M] (p : ℕ) [Fact p.Prime] (𝔪 : Ideal HeckeAlg)
    (hmultone :
      letI := heckeModuleBar M
      MultiplicityOneData p (JZero M) 𝔪)
    (hsmul :
      letI := heckeModuleBar M
      SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg (JZero M)) :
    letI := heckeModuleBar M
    haveI : SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg (JZero M) := hsmul
    DetFrobeniusMod (K := ℚ) (L := AlgebraicClosure ℚ) M p (JZero M) 𝔪 := by
  letI := heckeModuleBar M
  haveI : SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg (JZero M) := hsmul
  intro ℓ hℓ hℓMp A hA σ hσ
  have hp : p.Prime := Fact.out
  haveI : 𝔪.IsMaximal := hmultone.isMaximal
  haveI : Finite (heckeTorsion (JZero M) (Ideal.span {(p : HeckeAlg)})) :=
    ModularCurve.heckeTorsion_jZero_finite_of_natCast_mem M (Ideal.span {(p : HeckeAlg)}) p hp.pos
      (Ideal.subset_span (Set.mem_singleton _))
  have hpair :=
    ModularCurve.exists_pairing_family_pow_nsmul_eq_zero_galois_hecke_compat M p hp.ne_zero
  obtain ⟨B, hB⟩ := hpair
  have hB1 := hB 1
  obtain ⟨hroot, -, hmul, -, hgal, hbal, hperf, -, -⟩ := hB1
  have hFQ := ModularCurve.frobeniusQuadratic_JZero M p (ModularCurve.heckeOperatorsCommuteBar M) hsmul
  have hpℓ : p.Coprime ℓ :=
    (Nat.coprime_primes hp hℓ).mpr (fun h => hℓMp (h ▸ dvd_mul_left p M))
  exact FrobeniusDeterminant.det_eq_natCast_of_pairing 𝔪 hp hmultone.resChar hmultone.finrank_two
    (B 1) hroot hmul σ (hgal σ) hbal hperf (heckeGen ⟨ℓ, hℓ⟩) (hFQ ℓ hℓ hℓMp A hA σ hσ)
    (fun z hz => ValuationSubring.IsFrobeniusAt.apply_eq_pow_of_pow_eq_one A σ ℓ p hA hσ hpℓ z hz)

end S_ModularCurve_detFrobeniusMod_jZero_of_multiplicityOneData
end P2MW
export P2MW.S_ModularCurve_detFrobeniusMod_jZero_of_multiplicityOneData (solution)
