-- Prove2me | solution 1 for ModularCurve.exists_isEigenformIdeal_heckeTorsion_jZero_ne_bot_of_isMaximal_heckeAlgebra_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/479ece95-d12e-5130-9cd0-9944faa59f73

import Mathlib
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_HeckeInputsAll
import Definitions.Def_ModularCurve_EigenformIdeal
import Theorems.Thm_CuspForm_exists_isNormalizedEigenform_of_isMaximal_heckeAlgebra
import Theorems.Thm_CuspForm_moduleFinite_heckeAlgebra_two
import Theorems.Thm_CuspForm_IsNormalizedEigenform_heckeTLin_apply_eq_qCoeff_smul
import Theorems.Thm_CuspForm_IsNormalizedEigenform_heckeULin_apply_eq_qCoeff_smul
import Theorems.Thm_ModularCurve_eigenformSupportAt_jZero
import Theorems.Thm_ModularCurve_heckeInputsAll
import Theorems.Thm_ModularCurve_heckeOperatorsCommuteBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_isEigenformIdeal_heckeTorsion_jZero_ne_bot_of_isMaximal_heckeAlgebra_two
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "instance" "ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0"
p2m_attr_erase "simp" "PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero"

namespace P2dOcc

open CuspForm ModularFormClass

abbrev V (M : ℕ) : Type := CuspForm (CongruenceSubgroup.Gamma0 M) 2

section Stab

variable {M : ℕ}

def stab (g : V M) : Subalgebra ℤ (Module.End ℂ (V M)) where
  carrier := {t | ∃ a : ℂ, t g = a • g}
  mul_mem' := by
    rintro s t ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a * b, by rw [Module.End.mul_apply, hb, map_smul, ha, smul_smul, mul_comm]⟩
  one_mem' := ⟨1, by simp⟩
  add_mem' := by
    rintro s t ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, by rw [LinearMap.add_apply, ha, hb, add_smul]⟩
  zero_mem' := ⟨0, by simp⟩
  algebraMap_mem' := fun r =>
    ⟨(r : ℂ), by
      rw [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply,
        Int.cast_smul_eq_zsmul]⟩

lemma mem_stab {g : V M} {t : Module.End ℂ (V M)} : t ∈ stab g ↔ ∃ a : ℂ, t g = a • g :=
  Iff.rfl

lemma heckeAlgebra_le_stab [NeZero M] {g : V M} (hg : g.IsNormalizedEigenform) (S : Set ℕ) :
    heckeAlgebra M 2 S ≤ stab g := by
  refine Algebra.adjoin_le ?_
  rintro T (⟨ℓ, hℓ, hℓN, -, rfl⟩ | ⟨q, hqN, hq, -, rfl⟩)
  · exact ⟨qCoeff g ℓ,
      CuspForm.IsNormalizedEigenform.heckeTLin_apply_eq_qCoeff_smul M g hg ℓ hℓ hℓN⟩
  · exact ⟨qCoeff g q,
      CuspForm.IsNormalizedEigenform.heckeULin_apply_eq_qCoeff_smul M g hg q hq hqN⟩

end Stab

section EigenChar

variable {M : ℕ} [NeZero M] {g : V M} (hg : g.IsNormalizedEigenform)

noncomputable def eig (t : heckeAlgebra M 2 (∅ : Set ℕ)) : ℂ :=
  Classical.choose (heckeAlgebra_le_stab hg ∅ t.2)

lemma eig_spec (t : heckeAlgebra M 2 (∅ : Set ℕ)) :
    (t : Module.End ℂ (V M)) g = eig hg t • g :=
  Classical.choose_spec (heckeAlgebra_le_stab hg ∅ t.2)

omit [NeZero M] in
include hg in
lemma smul_inj {a b : ℂ} (h : a • g = b • g) : a = b :=
  smul_left_injective ℂ hg.ne_zero h

lemma eig_eq_of_apply_eq (t : heckeAlgebra M 2 (∅ : Set ℕ)) {a : ℂ}
    (h : (t : Module.End ℂ (V M)) g = a • g) : eig hg t = a :=
  smul_inj hg ((eig_spec hg t).symm.trans h)

noncomputable def theta : heckeAlgebra M 2 (∅ : Set ℕ) →+* ℂ where
  toFun := eig hg
  map_one' := eig_eq_of_apply_eq hg 1 (by simp)
  map_mul' s t := by
    apply eig_eq_of_apply_eq hg
    rw [Subalgebra.coe_mul, Module.End.mul_apply, eig_spec hg t, map_smul, eig_spec hg s,
      smul_smul, mul_comm]
  map_zero' := eig_eq_of_apply_eq hg 0 (by simp)
  map_add' s t := by
    apply eig_eq_of_apply_eq hg
    rw [Subalgebra.coe_add, LinearMap.add_apply, eig_spec hg s, eig_spec hg t, add_smul]

lemma theta_spec (t : heckeAlgebra M 2 (∅ : Set ℕ)) :
    (t : Module.End ℂ (V M)) g = theta hg t • g :=
  eig_spec hg t

lemma theta_eq_of_apply_eq (t : heckeAlgebra M 2 (∅ : Set ℕ)) {a : ℂ}
    (h : (t : Module.End ℂ (V M)) g = a • g) : theta hg t = a :=
  eig_eq_of_apply_eq hg t h

lemma theta_T {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    theta hg (heckeAlgebra.T hℓ hℓM (Set.notMem_empty ℓ)) = qCoeff g ℓ :=
  theta_eq_of_apply_eq hg _ (by
    rw [heckeAlgebra.coe_T]
    exact CuspForm.IsNormalizedEigenform.heckeTLin_apply_eq_qCoeff_smul M g hg ℓ hℓ hℓM)

lemma theta_U {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) :
    theta hg (heckeAlgebra.U hq hqM (Set.notMem_empty q)) = qCoeff g q :=
  theta_eq_of_apply_eq hg _ (by
    rw [heckeAlgebra.coe_U]
    exact CuspForm.IsNormalizedEigenform.heckeULin_apply_eq_qCoeff_smul M g hg q hq hqM)

lemma qCoeff_mem_range (ℓ : Nat.Primes) : qCoeff g ℓ ∈ (theta hg).range := by
  by_cases h : (ℓ : ℕ) ∣ M
  · exact ⟨_, theta_U hg ℓ.2 h⟩
  · exact ⟨_, theta_T hg ℓ.2 h⟩

lemma moduleFinite_range : Module.Finite ℤ (theta hg).range := by
  haveI : Module.Finite ℤ (heckeAlgebra M 2 (∅ : Set ℕ)) :=
    CuspForm.moduleFinite_heckeAlgebra_two M ∅
  exact Module.Finite.of_surjective (theta hg).rangeRestrict.toAddMonoidHom.toIntLinearMap
    (theta hg).rangeRestrict_surjective

lemma isIntegral_of_mem_range {x : ℂ} (hx : x ∈ (theta hg).range) : IsIntegral ℤ x := by
  haveI : Module.Finite ℤ (heckeAlgebra M 2 (∅ : Set ℕ)) :=
    CuspForm.moduleFinite_heckeAlgebra_two M ∅
  haveI : Algebra.IsIntegral ℤ (heckeAlgebra M 2 (∅ : Set ℕ)) := Algebra.IsIntegral.of_finite ℤ _
  obtain ⟨t, rfl⟩ := hx
  have h := (Algebra.IsIntegral.isIntegral (R := ℤ) t).map (theta hg).toIntAlgHom
  simpa using h

noncomputable def iota : (theta hg).range →+* integralClosure ℤ ℂ where
  toFun x := ⟨x, isIntegral_of_mem_range hg x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

@[scoped simp] lemma coe_iota (x : (theta hg).range) : ((iota hg x : integralClosure ℤ ℂ) : ℂ) = x := rfl

end EigenChar

lemma finite_of_moduleFinite_of_natCast_eq_zero (R : Type*) [CommRing R] [Module.Finite ℤ R]
    {p : ℕ} (hp : p.Prime) (hpR : (p : R) = 0) : Finite R := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  letI : Module (ZMod p) R :=
    AddCommMonoid.zmodModule (fun x => by rw [nsmul_eq_mul, hpR, zero_mul])
  haveI hf : Module.Finite (ZMod p) R := Module.Finite.of_restrictScalars_finite ℤ (ZMod p) R
  exact @Module.finite_of_finite (ZMod p) R _ _ _ _ hf

end P2dOcc
p2m_reactivate "P2MW.S_ModularCurve_exists_isEigenformIdeal_heckeTorsion_jZero_ne_bot_of_isMaximal_heckeAlgebra_two.P2dOcc"

open CuspForm ModularFormClass P2dOcc

set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3200000 in
theorem solution
    (M : ℕ) [NeZero M] (p : ℕ) [Fact p.Prime] (S : Set ℕ) (Q : ℕ → Prop) (c : ℕ → ℤ)
    (𝔪₂ : Ideal (CuspForm.heckeAlgebra M 2 S)) (h𝔪₂ : 𝔪₂.IsMaximal)
    (hp𝔪₂ : (p : CuspForm.heckeAlgebra M 2 S) ∈ 𝔪₂)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M), Q ℓ →
      CuspForm.heckeAlgebra.T hℓ hℓM hℓS - ((c ℓ : ℤ) : CuspForm.heckeAlgebra M 2 S) ∈ 𝔪₂) :
    letI := ModularCurve.heckeModuleBar M
    ∃ 𝔪 : Ideal ModularCurve.HeckeAlg, 𝔪.IsMaximal ∧ ModularCurve.IsEigenformIdeal M 𝔪 ∧
      ((p : ℕ) : ModularCurve.HeckeAlg) ∈ 𝔪 ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ¬ ℓ ∣ M → Q ℓ →
        ModularCurve.heckeGen ⟨ℓ, hℓ⟩ - ((c ℓ : ℤ) : ModularCurve.HeckeAlg) ∈ 𝔪) ∧
      ModularCurve.heckeTorsion (ModularCurve.JZero M) 𝔪 ≠ ⊥ := by
  have hp : p.Prime := Fact.out

  obtain ⟨g, 𝔐, hg, h𝔐, hsc⟩ :=
    CuspForm.exists_isNormalizedEigenform_of_isMaximal_heckeAlgebra M S 𝔪₂ h𝔪₂
  have hg0 : g ≠ 0 := hg.ne_zero

  have hp𝔐 : (p : integralClosure ℤ ℂ) ∈ 𝔐 := by
    obtain ⟨a, ha, hamem⟩ := hsc (p : heckeAlgebra M 2 S)
    have h1 : ((p : heckeAlgebra M 2 S) : Module.End ℂ (V M)) g = (p : ℂ) • g := by
      rw [show ((p : heckeAlgebra M 2 S) : Module.End ℂ (V M)) = (p : Module.End ℂ (V M)) from
        map_natCast (heckeAlgebra M 2 S).val p, Module.End.natCast_apply, Nat.cast_smul_eq_nsmul]
    have h2 : (a : ℂ) = p := smul_left_injective ℂ hg0 (ha.symm.trans h1)
    have h3 : a = (p : integralClosure ℤ ℂ) := Subtype.ext (by rw [h2]; norm_cast)
    exact h3 ▸ hamem hp𝔪₂

  have hcong𝔐 : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ¬ ℓ ∣ M → Q ℓ →
      ∃ b : integralClosure ℤ ℂ, (b : ℂ) = qCoeff g ℓ - c ℓ ∧ b ∈ 𝔐 := by
    intro ℓ hℓ hℓS hℓM hQ
    obtain ⟨b, hb, hbmem⟩ := hsc (heckeAlgebra.T hℓ hℓM hℓS - ((c ℓ : ℤ) : heckeAlgebra M 2 S))
    refine ⟨b, ?_, hbmem (hT ℓ hℓ hℓS hℓM hQ)⟩
    have h1 : ((heckeAlgebra.T hℓ hℓM hℓS - ((c ℓ : ℤ) : heckeAlgebra M 2 S) :
        heckeAlgebra M 2 S) : Module.End ℂ (V M)) g = (qCoeff g ℓ - c ℓ) • g := by
      rw [Subalgebra.coe_sub, heckeAlgebra.coe_T,
        show (((c ℓ : ℤ) : heckeAlgebra M 2 S) : Module.End ℂ (V M)) =
          ((c ℓ : ℤ) : Module.End ℂ (V M)) from map_intCast (heckeAlgebra M 2 S).val (c ℓ),
        LinearMap.sub_apply, Module.End.intCast_apply,
        CuspForm.IsNormalizedEigenform.heckeTLin_apply_eq_qCoeff_smul M g hg ℓ hℓ hℓM,
        sub_smul, Int.cast_smul_eq_zsmul]
    exact smul_left_injective ℂ hg0 (hb.symm.trans h1)

  set 𝒪 : Subring ℂ := (theta hg).range with h𝒪def
  haveI h𝒪fin : Module.Finite ℤ 𝒪 := moduleFinite_range hg
  haveI : 𝔐.IsPrime := h𝔐.isPrime
  let Φ : 𝒪 →+* integralClosure ℤ ℂ ⧸ 𝔐 := (Ideal.Quotient.mk 𝔐).comp (iota hg)
  set 𝔫 : Ideal 𝒪 := RingHom.ker Φ with h𝔫def
  haveI h𝔫prime : 𝔫.IsPrime := RingHom.ker_isPrime Φ
  have hp𝔫 : ((p : ℕ) : 𝒪) ∈ 𝔫 := by
    rw [h𝔫def, RingHom.mem_ker, map_natCast]
    exact_mod_cast (Ideal.Quotient.eq_zero_iff_mem.mpr hp𝔐)
  let k : Type := 𝒪 ⧸ 𝔫
  letI hkRing : CommRing k := Ideal.Quotient.commRing 𝔫
  have hpk : (p : k) = 0 := by
    have : (Ideal.Quotient.mk 𝔫 ((p : ℕ) : 𝒪)) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hp𝔫
    simpa using this
  haveI : Module.Finite ℤ k :=
    Module.Finite.of_surjective (Ideal.Quotient.mk 𝔫).toAddMonoidHom.toIntLinearMap
      Ideal.Quotient.mk_surjective
  haveI hkfin : Finite k := finite_of_moduleFinite_of_natCast_eq_zero k hp hpk
  haveI h𝔫max : 𝔫.IsMaximal := Ideal.Quotient.maximal_of_isField 𝔫 (Finite.isField_of_domain k)
  let φ : 𝒪 →+* k := Ideal.Quotient.mk 𝔫
  have h𝒪 : ∀ ℓ : Nat.Primes, qCoeff g ℓ ∈ 𝒪 := fun ℓ => qCoeff_mem_range hg ℓ
  let a : Nat.Primes → k := fun ℓ => φ ⟨qCoeff g ℓ, h𝒪 ℓ⟩

  have hmax : (ModularCurve.eigenIdeal a).IsMaximal := by

    have e := Ideal.quotientKerEquivRange (MvPolynomial.aeval (R := ℤ) a)
    haveI : Finite (MvPolynomial.aeval (R := ℤ) a).range := Subtype.finite
    haveI : IsDomain k := Ideal.Quotient.isDomain 𝔫
    have hF : IsField (MvPolynomial.aeval (R := ℤ) a).range :=
      Finite.isField_of_domain _
    exact Ideal.Quotient.maximal_of_isField _ (MulEquiv.isField hF e.toMulEquiv)
  have hpm : ((p : ℕ) : ModularCurve.HeckeAlg) ∈ ModularCurve.eigenIdeal a := by
    rw [ModularCurve.mem_eigenIdeal_iff, map_natCast, hpk]
  have hcong : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ¬ ℓ ∣ M → Q ℓ →
      ModularCurve.heckeGen ⟨ℓ, hℓ⟩ - ((c ℓ : ℤ) : ModularCurve.HeckeAlg) ∈
        ModularCurve.eigenIdeal a := by
    intro ℓ hℓ hℓS hℓM hQ
    obtain ⟨b, hb, hbmem⟩ := hcong𝔐 ℓ hℓ hℓS hℓM hQ
    rw [ModularCurve.mem_eigenIdeal_iff, map_sub, ModularCurve.aeval_heckeGen, map_intCast]
    have hmem : (⟨qCoeff g ℓ, h𝒪 ⟨ℓ, hℓ⟩⟩ : 𝒪) - ((c ℓ : ℤ) : 𝒪) ∈ 𝔫 := by
      rw [h𝔫def, RingHom.mem_ker]
      show Ideal.Quotient.mk 𝔐 (iota hg (⟨qCoeff g ℓ, h𝒪 ⟨ℓ, hℓ⟩⟩ - ((c ℓ : ℤ) : 𝒪))) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      have : iota hg (⟨qCoeff g ℓ, h𝒪 ⟨ℓ, hℓ⟩⟩ - ((c ℓ : ℤ) : 𝒪)) = b := by
        apply Subtype.ext
        rw [hb, map_sub, map_intCast]
        push_cast
        rw [coe_iota]
      rw [this]
      exact hbmem
    have := (Ideal.Quotient.eq_zero_iff_mem (I := 𝔫)).mpr hmem
    rw [map_sub, map_intCast] at this
    exact this

  let hkField : Field k := Ideal.Quotient.field 𝔫
  have hEig : ModularCurve.IsEigenformIdeal M (ModularCurve.eigenIdeal a) :=
    ⟨g, hg, k, hkField, hkfin, 𝒪, h𝒪, φ, rfl⟩
  refine ⟨ModularCurve.eigenIdeal a, hmax, hEig, hpm, hcong, ?_⟩

  exact ModularCurve.eigenformSupportAt_jZero M p hp (ModularCurve.heckeInputsAll M)
    (ModularCurve.heckeOperatorsCommuteBar M) (ModularCurve.eigenIdeal a) hEig hpm

end S_ModularCurve_exists_isEigenformIdeal_heckeTorsion_jZero_ne_bot_of_isMaximal_heckeAlgebra_two
end P2MW
export P2MW.S_ModularCurve_exists_isEigenformIdeal_heckeTorsion_jZero_ne_bot_of_isMaximal_heckeAlgebra_two (solution)
